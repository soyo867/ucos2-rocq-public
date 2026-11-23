Require Export Ucos2Verify.VC.code.queue.spec.q_create_api_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem ConAssertion ArrayLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_borrow_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Flat-address consequence of the caller's legal C array-object / slice
    contract, including the representable one-past pointer stored in OSQEnd.
    This is an additional, explicitly approved caller obligation, NOT a
    theorem about PtrArray.mixed_full. A real caller must establish its
    array object's allocation and layout before using this interpretation.
    In particular QInit's static QCB layout says nothing about this array.

    These facts are needed only on the successful initialization path;
    the ISR and either pool-exhaustion return never evaluate &start[size]. *)
Definition q_create_buffer_bounds (start size : Z) : Prop :=
  0 < start /\ 0 <= size <= 65535 /\ start + size * 4 <= 4294967295.

Definition q_create_caller_buffer (start : Z) (slots : list (option addr)) : Assertion :=
  coq_prop (q_create_buffer_bounds start (Zlength slots)) &&
    PtrArray.mixed_full start (Zlength slots) slots.

(** A caller's real object may be larger than the Queue capacity. This
    arithmetic rule consumes the object's independently established extent;
    it neither allocates an object nor infers provenance from integer cells. *)
Lemma q_create_buffer_bounds_from_array_slice :
  forall base length offset size,
  0 < base -> 0 <= offset -> 0 <= size <= 65535 ->
  offset + size <= length -> base + length * 4 <= 4294967295 ->
  q_create_buffer_bounds (base + offset * 4) size.
Proof. intros; unfold q_create_buffer_bounds; lia. Qed.

Lemma q_create_buffer_bounds_pointer_values : forall start size,
  q_create_buffer_bounds start size ->
  valid_ptr_value start /\ valid_ptr_value (start + size * 4).
Proof.
  intros start size Hbounds; unfold q_create_buffer_bounds in Hbounds.
  change (0 <= start <= 4294967295 /\ 0 <= start + size * 4 <= 4294967295).
  lia.
Qed.

(** Function-local call packaging. These are the existing private bytes,
    not new ghost resources. The allocation is fixed only while this
    invocation is suspended; every source store changes the package before
    it is next passed to a call. A Queue package retains its actual QCB
    image, including the old OSQPtr field. *)
Inductive QCreateOwned : Type :=
| QCreateNoPrivate
| QCreatePrivateEvent (eid : EventID) (allocation : EventPrivateAllocation)
| QCreatePrivateQueue (eid : EventID) (allocation : EventPrivateAllocation)
    (qid : QueueID) (image : QCBStorage).

Definition q_create_owned (owned : QCreateOwned) sg state : Assertion :=
  match owned with
  | QCreateNoPrivate => emp
  | QCreatePrivateEvent eid allocation =>
      coq_prop (state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation) &&
      event_private_storage_rep sg eid allocation
  | QCreatePrivateQueue eid allocation qid image =>
      coq_prop (state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        allocation.(eventPrivateQueue) = Some qid) &&
      (event_private_storage_rep sg eid allocation ** qcb_storage_rep sg qid image)
  end.

Definition q_create_resources owned (buffer : Assertion) sg state : Assertion :=
  UCOS2_inv sg state ** q_create_owned owned sg state ** buffer.

Definition q_create_save_input environment (_ : CriticalRegionResources) owned buffer sg call mask state : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    (q_create_resources owned buffer) (fun _ => emp) sg
    (task_stack_call_active_key call) call mask state.

Definition q_create_restore_input environment critical owned buffer
  sg call saved acquired state : Assertion :=
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    (q_create_resources owned buffer) (fun _ => emp) critical sg
    (task_stack_call_active_key call) call saved acquired state.

(** The same modular C-call contract used by the delivered Task APIs.
    No new CPU field or all-clients frame axiom is introduced. Its selected
    C environment must implement the resource family at the returned heap;
    concrete spatial transport for the stated creator family is proved below,
    not an end-to-end realization of the ARM/BSP call. Boot/generic
    origins are retained: neither adapter requires a current Task. *)
Definition q_create_save_output environment critical owned buffer
  sg call mask saved state : Assertion :=
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    (q_create_resources owned buffer) (fun _ => emp) critical
    kernel_call_control_rely sg call mask saved state.

Definition q_create_restore_output environment critical owned buffer
  sg call saved state : Assertion :=
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    (q_create_resources owned buffer) (fun _ => emp) critical
    kernel_call_control_rely sg call (armv7a_irq_fiq_mask saved) state.

Lemma q_create_saved_continuation_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks key payload,
  kernel_saved_continuation_entry abi tasks (fun _ => emp) key payload --||--
  armv7a_task_stack_entry abi tasks key payload.
Proof.
  intros; unfold kernel_saved_continuation_entry, armv7a_task_stack_entry.
  split; Intros descriptor; Exists descriptor; entailer!.
Qed.

Lemma q_create_saved_continuation_map : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks,
  store_parked_continuations (kernel_saved_continuation_entry abi tasks (fun _ => emp)) stacks --||--
  armv7a_task_stack_continuations abi tasks stacks.
Proof.
  intros; unfold armv7a_task_stack_continuations, store_parked_continuations.
  split; apply TaskFieldStorage.store_map_mono; intros;
    apply q_create_saved_continuation_entry.
Qed.

Lemma q_create_save_input_open : forall environment critical owned buffer sg call mask state,
  q_create_save_input environment critical owned buffer sg call mask state --||--
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call mask **
     UCOS2_inv sg state ** armv7a_task_stack_continuations environment.(task_stack_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks) **
     q_create_owned owned sg state ** buffer).
Proof.
  intros; unfold q_create_save_input, kernel_continuation_call_closed,
    kernel_continuation_inv, q_create_resources.
  rewrite q_create_saved_continuation_map; split; entailer!.
Qed.

Lemma q_create_restore_input_open : forall environment critical owned buffer
  sg call saved acquired state,
  q_create_restore_input environment critical owned buffer sg call saved acquired state --||--
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(task_stack_call_external) call **
     UCOS2_inv sg state ** armv7a_task_stack_continuations environment.(task_stack_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks) **
     q_create_owned owned sg state ** buffer).
Proof.
  intros; unfold q_create_restore_input, kernel_continuation_call_masked,
    kernel_continuation_inv, q_create_resources.
  rewrite q_create_saved_continuation_map; split; entailer!.
Qed.

Lemma q_create_save_output_observation : forall environment critical owned buffer
  sg call mask saved before,
  q_create_save_output environment critical owned buffer sg call mask saved before |--
  EX returned current,
    coq_prop (critical_region_interval critical sg call.(os_sched_call_invocation) before current /\
      kernel_call_normal_return call before returned current /\
      kernel_call_control_rely sg before current /\ interrupt_saved_value mask saved) &&
    q_create_restore_input environment critical owned buffer sg returned saved current current.
Proof.
  intros; unfold q_create_save_output, kernel_call_modular_save_post; Intros returned current.
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before current) by tauto.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsource) as Hinterval.
  destruct Hsource as [_ [_ [_ [_ Hsaved]]]].
  unfold q_create_restore_input; Exists returned current; entailer!.
Qed.

Lemma q_create_restore_output_observation : forall environment critical owned buffer
  sg call saved before,
  q_create_restore_output environment critical owned buffer sg call saved before |--
  EX returned current,
    coq_prop (critical_region_interval critical sg call.(os_sched_call_invocation) before current /\
      kernel_call_normal_return call before returned current /\
      kernel_call_control_rely sg before current) &&
    q_create_save_input environment critical owned buffer sg returned (armv7a_irq_fiq_mask saved) current.
Proof.
  intros; unfold q_create_restore_output, kernel_call_modular_restore_post; Intros returned current.
  assert (Hsource : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) before false
    returned.(os_sched_call_origin) current) by tauto.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Hinterval _].
  unfold q_create_save_input; Exists returned current; entailer!.
Qed.

Definition q_create_buffer start size (slots : list (option addr)) : Assertion :=
  PtrArray.mixed_full start size slots.

(** The only new address obligation is needed at the reachable success
    prefix, immediately before the six private QCB stores. Ordinary callers
    discharge it using their real array extent. This guarded form also keeps
    the original ISR / pool-exhaustion domain when success is impossible;
    it does not require an error caller to own a fictitious extra cell. *)
Definition q_create_reservation_prefix critical sg invocation initial eid qid reserved : Prop :=
  initial.(IntrState).(intNesting) <= 0 /\
  exists entry image detached resumed free,
    critical_region_interval critical sg invocation initial entry /\
    event_create_allocate_critical entry (Some (eid, image)) detached /\
    q_create_private_interval critical sg invocation eid detached resumed /\
    queue_pool_partition sg resumed.(EventState) free /\
    q_create_reserve_critical sg eid free resumed (Some qid) reserved.

Definition q_create_buffer_contract critical sg invocation initial start size : Prop :=
  forall eid qid reserved,
    q_create_reservation_prefix critical sg invocation initial eid qid reserved ->
    q_create_buffer_bounds start size.

Lemma q_create_buffer_contract_from_bounds : forall critical sg invocation initial start size,
  q_create_buffer_bounds start size ->
  q_create_buffer_contract critical sg invocation initial start size.
Proof. intros; intros eid qid reserved Hprefix; assumption. Qed.

Lemma q_create_buffer_contract_isr : forall critical sg invocation initial start size,
  0 < initial.(IntrState).(intNesting) ->
  q_create_buffer_contract critical sg invocation initial start size.
Proof. intros critical sg invocation initial start size Hnest eid qid reserved [Hnot _]; lia. Qed.

Definition q_create_source_binding sg : Prop :=
  sem_create_source_binding sg /\
  &("OSQFreeList") = sg.(g_OSQFreeList) /\
  event_table_layout_prop sg /\
  queue_table_layout_prop sg sg.(g_OSQTbl) /\ queue_first_round_profile sg.

Definition q_create_input_facts critical sg call initial start size slots X : Prop :=
  q_create_source_binding sg /\ 0 < start /\ 0 <= size <= 65535 /\ Zlength slots = size /\
  q_create_buffer_contract critical sg call.(os_sched_call_invocation) initial start size /\
  q_create_safe critical sg call.(os_sched_call_invocation) start size slots initial X.

Definition q_create_call_pre environment critical sg call mask initial start size slots X : Assertion :=
  coq_prop (q_create_input_facts critical sg call initial start size slots X) &&
  q_create_save_input environment critical QCreateNoPrivate (q_create_buffer start size slots)
    sg call mask initial.

Definition q_create_return_safe current result (X : addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret result) X.

Definition q_create_result_buffer start size slots result : Assertion :=
  if Z.eq_dec result 0 then q_create_buffer start size slots else emp.

Definition q_create_call_post environment critical sg original mask start size slots result X : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ q_create_return_safe current result X) &&
    q_create_save_input environment critical QCreateNoPrivate (q_create_result_buffer start size slots result)
      sg returned mask current.

Definition q_create_without_nesting environment owned buffer sg call mask state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call mask **
     interrupt_inv_no_int_nesting sg state.(IntrState) ** UCOS2_raw_rep_missing_interrupt sg state **
     armv7a_task_stack_continuations environment.(task_stack_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks) **
     q_create_owned owned sg state ** buffer).

Lemma q_create_save_input_split_nesting : forall environment critical owned buffer sg call mask state,
  q_create_source_binding sg ->
  q_create_save_input environment critical owned buffer sg call mask state --||--
  &("OSIntNesting") # UChar |-> state.(IntrState).(intNesting) **
    q_create_without_nesting environment owned buffer sg call mask state.
Proof.
  intros environment critical owned buffer sg call mask state [[Haddress _] _].
  rewrite q_create_save_input_open, UCOS2_inv_split_interrupt.
  unfold q_create_without_nesting, interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  rewrite Haddress; split; entailer!.
Qed.

Lemma q_create_isr_return : forall environment critical sg call mask initial start size slots X,
  0 < initial.(IntrState).(intNesting) ->
  q_create_call_pre environment critical sg call mask initial start size slots X |--
  q_create_call_post environment critical sg call mask start size slots 0 X.
Proof.
  intros environment critical sg call mask initial start size slots X Hnest.
  unfold q_create_call_pre; Intros.
  assert (Hsafe : q_create_safe critical sg call.(os_sched_call_invocation) start size slots initial X)
    by (unfold q_create_input_facts in *; tauto).
  pose proof (q_create_api_safe_return critical sg call.(os_sched_call_invocation) start size slots
    initial initial 0 X (q_create_program_isr_return _ _ _ _ _ _ _ Hnest) Hsafe) as Hreturn.
  unfold q_create_call_post; Exists call initial.
  unfold q_create_result_buffer; destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.

Definition q_create_masked_control environment critical sg call saved acquired state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(task_stack_call_external) call **
     armv7a_task_stack_continuations environment.(task_stack_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks)).

Definition q_create_current_control environment (_ : StableGlobVars) call mask state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call mask **
     armv7a_task_stack_continuations environment.(task_stack_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks)).

Definition q_create_first_facts critical sg original initial mask saved call entry : Prop :=
  initial.(IntrState).(intNesting) <= 0 /\
  critical_region_interval critical sg original.(os_sched_call_invocation) initial entry /\
  task_tcb_init_stack_same_call call original /\ interrupt_saved_value mask saved /\
  UCOS2_state_inv sg entry.

Definition q_create_allocated_owner entry (result : option (EventID * EventStorage)) : QCreateOwned :=
  match result with
  | None => QCreateNoPrivate
  | Some (eid, image) => QCreatePrivateEvent eid (sem_create_allocation_identity entry image)
  end.

Definition q_create_allocation_cut environment critical sg original initial mask saved
  start size slots pointer : Assertion :=
  EX call entry result allocated,
    coq_prop (q_create_first_facts critical sg original initial mask saved call entry /\
      event_create_allocate_critical entry result allocated /\
      pointer = event_create_return_ptr sg result) &&
    q_create_restore_input environment critical (q_create_allocated_owner entry result)
      (q_create_buffer start size slots) sg call saved entry allocated.

Definition q_create_event_history critical sg invocation initial eid allocation current : Prop :=
  initial.(IntrState).(intNesting) <= 0 /\
  exists entry image detached,
    UCOS2_state_inv sg entry /\
    critical_region_interval critical sg invocation initial entry /\
    event_create_allocate_critical entry (Some (eid, image)) detached /\
    allocation = sem_create_allocation_identity entry image /\
    q_create_private_interval critical sg invocation eid detached current.

Definition q_create_error_history critical sg invocation initial current : Prop :=
  initial.(IntrState).(intNesting) <= 0 /\
  exists entry allocated detached,
    critical_region_interval critical sg invocation initial entry /\
    event_create_allocate_critical entry allocated detached /\
    match allocated with
    | None => critical_region_interval critical sg invocation detached current
    | Some (eid, image) => exists resumed free rolled_back,
        q_create_private_interval critical sg invocation eid detached resumed /\
        queue_pool_partition sg resumed.(EventState) free /\
        q_create_reserve_critical sg eid free resumed None rolled_back /\
        critical_region_interval critical sg invocation rolled_back current
    end.

(** At the first Restore return the pointer has exactly two meanings.
    The non-null branch retains the same allocation lookup and real bytes;
    the null branch retains the caller's untouched buffer. *)
Definition q_create_allocation_return environment critical sg original initial mask
  start size slots pointer : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original) &&
    (if Z.eq_dec pointer 0 then
      (coq_prop (q_create_error_history critical sg
        original.(os_sched_call_invocation) initial current) &&
      q_create_save_input environment critical QCreateNoPrivate (q_create_buffer start size slots)
        sg returned mask current) else
     (EX eid allocation,
      coq_prop (pointer = event_pool_addr sg eid /\ 0 < pointer /\
        q_create_event_history critical sg original.(os_sched_call_invocation)
          initial eid allocation current) &&
      q_create_save_input environment critical (QCreatePrivateEvent eid allocation)
        (q_create_buffer start size slots) sg returned mask current)).

Definition q_create_queue_pool_frame sg current : Assertion :=
  coq_prop (queue_published_storage_binding current.(EventState)) &&
  (event_raw_rep sg current.(TskState) current.(EventState) **
   store_map (published_queue_node_rep sg current.(EventState)) current.(EventState).(inUsedEventStates) **
   UCOS2_raw_rep_missing_event_queue sg current).

Definition q_create_success_history critical sg invocation initial eid allocation qid reserved : Prop :=
  exists resumed original free,
    q_create_event_history critical sg invocation initial eid original resumed /\
    queue_pool_partition sg resumed.(EventState) free /\
    q_create_reserve_critical sg eid free resumed (Some qid) reserved /\
    allocation = queue_allocation_with_qcb original qid.

Definition q_create_reservation_cut environment critical sg original initial mask saved
  start size slots pointer queue : Assertion :=
  EX call acquired reserved eid allocation qid image,
    coq_prop (task_tcb_init_stack_same_call call original /\ interrupt_saved_value mask saved /\
      pointer = event_pool_addr sg eid /\ queue = qcb_addr sg qid /\
      q_create_success_history critical sg original.(os_sched_call_invocation)
        initial eid allocation qid reserved) &&
    q_create_restore_input environment critical (QCreatePrivateQueue eid allocation qid image)
      (q_create_buffer start size slots) sg call saved acquired reserved.

(** The closed context is existential in the CURRENT world supplied by the
    actual modular returned resources, never by keeping the pre-Restore pool
    or inventing an Event observer. The physical ECB/QCB fields are separate
    from this context during initialization. The auxiliary source-family
    rules below preserve those actual bytes; they do not assert arbitrary
    instruction-level IRQ stability of the whole context. *)
Definition q_create_initialization_context environment critical sg original initial mask
  eid allocation qid reserved start size slots : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      q_create_success_history critical sg original.(os_sched_call_invocation)
        initial eid allocation qid reserved /\
      q_create_private_interval critical sg original.(os_sched_call_invocation) eid reserved current /\
      current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
      allocation.(eventPrivateQueue) = Some qid /\
      q_create_buffer_bounds start size /\ Zlength slots = size) &&
    (q_create_current_control environment sg returned mask current ** UCOS2_inv sg current **
     q_create_buffer start size slots).

Definition q_create_rollback_frame sg current eid allocation : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) allocation.(eventPrivateStorage) EventPtrField **
  store_map (used_event_rep sg current.(TskState)) current.(EventState).(inUsedEventStates) **
  event_free_storage_rep sg current.(EventState) **
  queue_storage_rep sg current.(EventState) ** UCOS2_raw_rep_missing_event_queue sg current.

Definition q_create_rollback_cut environment critical sg original initial mask saved
  start size slots : Assertion :=
  EX call acquired rolled_back,
    coq_prop (task_tcb_init_stack_same_call call original /\ interrupt_saved_value mask saved /\
      q_create_error_history critical sg original.(os_sched_call_invocation) initial rolled_back) &&
    q_create_restore_input environment critical QCreateNoPrivate (q_create_buffer start size slots)
      sg call saved acquired rolled_back.

Definition q_create_private_lookup state eid allocation : Prop :=
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.

Definition q_create_free_qcb_without_link sg qid next : Assertion :=
  qcb_storage_without_field sg qid (qcb_free_image next) QCBPtr.

Definition q_create_qcb_link sg qid (image : QCBStorage) : Assertion :=
  qcb_cell (qcb_addr sg qid) QCBPtr (image QCBPtr).

Lemma q_create_region_interval_trans : forall critical sg invocation before middle after,
  critical_region_interval critical sg invocation before middle ->
  critical_region_interval critical sg invocation middle after ->
  critical_region_interval critical sg invocation before after.
Proof.
  intros critical sg invocation before middle after Hfirst Hlast.
  eapply KernelResumptionTraceSegment with (stopped1 := false) (stopped2 := false).
  - eapply kernel_resumption_resource_trace_erases; exact Hfirst.
  - eapply kernel_resumption_resource_trace_timer_projection; exact Hfirst.
  - exact Hlast.
Qed.

Lemma q_create_error_history_extend : forall critical sg invocation initial before after,
  q_create_error_history critical sg invocation initial before ->
  critical_region_interval critical sg invocation before after ->
  q_create_error_history critical sg invocation initial after.
Proof.
  intros critical sg invocation initial before after [Hnest [entry [result [detached
    [Henter [Hallocate Htail]]]]]] Hinterval.
  split; [exact Hnest|]; exists entry, result, detached.
  split; [exact Henter|]; split; [exact Hallocate|].
  destruct result as [[eid image]|].
  - destruct Htail as [resumed [free [rolled_back [Hprivate [Hpool [Hreserve Hrestore]]]]]].
    exists resumed, free, rolled_back; split; [exact Hprivate|].
    split; [exact Hpool|]; split; [exact Hreserve|].
    eapply q_create_region_interval_trans; eassumption.
  - eapply q_create_region_interval_trans; eassumption.
Qed.

Lemma q_create_error_history_program : forall critical sg invocation initial current start size slots,
  q_create_error_history critical sg invocation initial current ->
  q_create_program critical sg invocation start size slots initial 0 current.
Proof.
  intros critical sg invocation initial current start size slots [Hnest [entry [result
    [detached [Henter [Hallocate Htail]]]]]].
  destruct result as [[eid image]|].
  - destruct Htail as [resumed [free [rolled_back [Hprivate [Hpool [Hreserve Hrestore]]]]]].
    eapply q_create_program_no_queue_return; eassumption.
  - eapply q_create_program_no_event_return; eassumption.
Qed.

Lemma q_create_event_history_private_facts : forall critical sg invocation initial eid allocation current,
  q_create_event_history critical sg invocation initial eid allocation current ->
  allocation.(eventPrivateQueue) = None /\ allocation.(eventPrivateMutexPCP) = None /\
  allocation.(eventPrivateStorage) EventTypeField = Some 0 /\
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation.
Proof.
  intros critical sg invocation initial eid allocation current [_ [entry [image [detached
    [Hvalid [Henter [Hallocate [-> Hprivate]]]]]]]].
  split; [reflexivity|]; split; [reflexivity|]; split.
  - eapply event_create_allocate_critical_image_type; eassumption.
  - eapply q_create_private_interval_lookup; [exact Hprivate|].
    exact (proj2 (event_create_allocate_critical_private_result _ _ _ _ Hallocate)).
Qed.

Lemma q_create_queue_head_null_iff : forall sg state free,
  UCOS2_state_inv sg state -> queue_pool_partition sg state.(EventState) free ->
  queue_free_head sg free = 0 <-> free = [].
Proof.
  intros sg state [|qid rest] Hvalid Hpool; [simpl; tauto|].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (valid_stable_address_pos sg sg.(g_OSQTbl) Hsg
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  destruct Hpool as [[_ Hrange] _]; inversion Hrange as [|head tail Hqid Hrest]; subst.
  unfold queue_free_head, qcb_addr, valid_queue_id, sizeof_OS_Q in *.
  split; [lia|discriminate].
Qed.

Lemma q_create_qcb_layout : forall sg qid,
  q_create_source_binding sg -> valid_queue_id sg qid ->
  queue_control_block_layout_prop sg qid
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQPtr"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQStart"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQEnd"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQIn"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQOut"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQSize"))
    (&(((qcb_addr (sg) (qid))) # "os_q" ->ₛ "OSQEntries")).
Proof.
  intros sg qid [_ [_ [_ [Hlayout [_ Hsize]]]]] Hqid.
  specialize (Hlayout qid Hqid).
  change (sizeof ("os_q")) with (sizeof_alias_type "os_q") in Hlayout.
  rewrite Hsize in Hlayout; exact Hlayout.
Qed.

Lemma q_create_success_history_prefix : forall critical sg invocation initial eid allocation qid reserved,
  q_create_success_history critical sg invocation initial eid allocation qid reserved ->
  q_create_reservation_prefix critical sg invocation initial eid qid reserved.
Proof.
  intros critical sg invocation initial eid allocation qid reserved
    [resumed [original [free [Hhistory [Hpool [Hreserve Hidentity]]]]]].
  destruct Hhistory as [Hnest [entry [image [detached
    [Hvalid [Henter [Hallocate [Horiginal Hprivate]]]]]]]].
  split; [exact Hnest|]; exists entry, image, detached, resumed, free.
  split; [exact Henter|]. split; [exact Hallocate|]. split; [exact Hprivate|].
  split; assumption.
Qed.

Lemma q_create_success_history_properties : forall critical sg invocation initial eid allocation qid reserved,
  q_create_success_history critical sg invocation initial eid allocation qid reserved ->
  UCOS2_state_inv sg reserved /\ valid_queue_id sg qid /\
  reserved.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
  allocation.(eventPrivateQueue) = Some qid.
Proof.
  intros critical sg invocation initial eid allocation qid reserved
    [resumed [original [free [Hhistory [Hpool [Hreserve ->]]]]]].
  pose proof (q_create_event_history_private_facts _ _ _ _ _ _ _ Hhistory)
    as [Hqueue [Hpcp [Htype Hget]]].
  assert (Hresumed : UCOS2_state_inv sg resumed).
  { destruct Hhistory as [_ [entry [image [detached
      [Hvalid [Henter [Hallocate [Hidentity Hprivate]]]]]]]].
    eapply (proj1 (critical_region_interval_transports_resources _ _ _ _ _ (proj1 Hprivate)
      (event_create_allocate_critical_preserves_validity _ _ _ _ Hvalid Hallocate))). }
  split.
  - eapply q_create_reserve_critical_preserves_validity; eassumption.
  - split.
    + pose proof (q_create_reserve_critical_result _ _ _ _ _ _ Hreserve) as Hhead.
      destruct free as [|head rest]; [discriminate|]; injection Hhead as ->.
      destruct Hpool as [[_ Hrange] _]; inversion Hrange; assumption.
    + split.
      * eapply q_create_reserve_critical_private_result; eassumption.
      * reflexivity.
Qed.

Definition q_create_qcb_initialization_pre sg qid image : Assertion :=
  q_create_qcb_link sg qid image **
  (qcb_addr sg qid + OSQStart_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQEnd_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQIn_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQOut_off) # Ptr |->_ **
  (qcb_addr sg qid + OSQSize_off) # UShort |->_ **
  (qcb_addr sg qid + OSQEntries_off) # UShort |->_ .

Definition q_create_qcb_initialization_post sg qid image start size : Assertion :=
  q_create_qcb_link sg qid image **
  (qcb_addr sg qid + OSQStart_off) # Ptr |-> start **
  (qcb_addr sg qid + OSQEnd_off) # Ptr |-> (start + size * 4) **
  (qcb_addr sg qid + OSQIn_off) # Ptr |-> start **
  (qcb_addr sg qid + OSQOut_off) # Ptr |-> start **
  (qcb_addr sg qid + OSQSize_off) # UShort |-> size **
  (qcb_addr sg qid + OSQEntries_off) # UShort |-> 0.

Lemma q_create_qcb_initialization_split : forall sg qid image,
  qcb_storage_rep sg qid image |-- q_create_qcb_initialization_pre sg qid image.
Proof.
  intros; unfold qcb_storage_rep, qcb_fields.
  repeat rewrite QueueFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite QueueFieldStorage.store_fields_nil.
  sep_apply_l_atomic (qcb_cell_forget_value (qcb_addr sg qid) QCBStart (image QCBStart)).
  sep_apply_l_atomic (qcb_cell_forget_value (qcb_addr sg qid) QCBEnd (image QCBEnd)).
  sep_apply_l_atomic (qcb_cell_forget_value (qcb_addr sg qid) QCBIn (image QCBIn)).
  sep_apply_l_atomic (qcb_cell_forget_value (qcb_addr sg qid) QCBOut (image QCBOut)).
  sep_apply_l_atomic (qcb_cell_forget_value (qcb_addr sg qid) QCBSize (image QCBSize)).
  sep_apply_l_atomic (qcb_cell_forget_value (qcb_addr sg qid) QCBEntries (image QCBEntries)).
  unfold q_create_qcb_initialization_pre, q_create_qcb_link, qcb_cell, qcb_field_offset; entailer!.
Qed.

Lemma q_create_qcb_initialization_merge : forall sg qid image start size,
  q_create_qcb_initialization_post sg qid image start size |--
  qcb_storage_rep sg qid (qcb_initialize image start size).
Proof.
  intros; unfold qcb_storage_rep, qcb_fields.
  repeat rewrite QueueFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite QueueFieldStorage.store_fields_nil.
  unfold q_create_qcb_initialization_post, q_create_qcb_link, qcb_cell, qcb_field_offset,
    qcb_initialize, qcb_write, field_update, QCBField_eq_dec; simpl; entailer!.
Qed.

Definition q_create_event_initialization_post base image queue : Assertion :=
  base # UChar |-> 2 ** (base + 8) # UShort |-> 0 ** (base + 4) # Ptr |-> queue **
  event_wait_list_init_post (base + 10) (base + 11) ** sem_create_initialization_frame base image.

Lemma q_create_event_initialization_merge : forall base image queue,
  q_create_event_initialization_post base image queue |--
  event_storage_rep false base (event_create_image false 2 0 queue 0 image).
Proof.
  intros base image queue.
  set (payload := event_write (event_write (event_write image EventTypeField (Some 2))
    EventCntField (Some 0)) EventPtrField (Some queue)).
  assert (Himage : event_wait_list_init_image payload = event_create_image false 2 0 queue 0 image)
    by reflexivity.
  assert (Hfields : forall field, payload field =
    match field with EventTypeField => Some 2 | EventCntField => Some 0 |
      EventPtrField => Some queue | _ => image field end)
    by (intro field; destruct field; reflexivity).
  rewrite <- Himage.
  sep_apply_r_atomic (event_wait_list_init_storage_merge false base payload).
  unfold q_create_event_initialization_post, sem_create_initialization_frame,
    event_wait_list_init_storage_frame; rewrite !Hfields.
  unfold event_cell, event_field_offset; replace (base + 0) with base by lia; entailer!.
Qed.

Lemma q_create_private_stores_interval_prefix : forall critical sg invocation eid writes before middle result after,
  q_create_private_interval critical sg invocation eid before middle ->
  q_create_private_stores_interleaved critical sg invocation eid writes middle result after ->
  q_create_private_stores_interleaved critical sg invocation eid writes before result after.
Proof.
  intros critical sg invocation eid [|[field value] writes] before middle result after Hprefix Htail.
  - destruct Htail as [-> Htail]; split; [reflexivity|].
    eapply q_create_private_interval_trans; eassumption.
  - destruct Htail as [entry [allocation [Hentry [Hget Htail]]]].
    exists entry, allocation; split; [|split; assumption].
    eapply q_create_private_interval_trans; eassumption.
Qed.

(** The stronger call-stack owner is never projected to a weak capsule
    map. Only the two actual ECB owners are inspected to derive separation. *)
Lemma q_create_private_allocations_disjoint : forall sg eid first other second,
  event_private_storage_rep sg eid first ** event_private_storage_rep sg other second |--
    coq_prop (eid <> other).
Proof.
  intros sg eid first other second; destruct (Z.eq_dec eid other) as [->|Hne]; [|entailer!].
  unfold event_private_storage_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg other) first.(eventPrivateStorage) EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg other) second.(eventPrivateStorage) EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  cbn [event_cell event_field_offset].
  destruct (first.(eventPrivateStorage) EventPtrField), (second.(eventPrivateStorage) EventPtrField).
  all: repeat match goal with
    | |- context [?p # Ptr |-> ?v] => sep_apply_l_atomic (store_ptr_undef_store_ptr p v)
    end.
  all: prop_apply (dup_undef_store_ptr (event_pool_addr sg other + 4)); entailer!.
Qed.

Lemma q_create_private_allocation_call_stack_step : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator sg cut state before next after
  eid allocation (frame : Assertion),
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_client_heap_step (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state ** (event_private_storage_rep sg eid allocation ** frame)) before ->
  exists returned,
    kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** (event_private_storage_rep sg eid allocation ** frame)) after.
Proof.
  intros external platform port abi focus payload creator sg cut state before next after eid allocation frame
    Hargs Hget Hsource Hpre.
  destruct Hsource as [before after Henter|before after Hexit|publication before after Hpublish|
    cut before next after Hextra].
  - exists (os_int_enter_state state); split; [constructor|]. split; [exact Hget|].
    eapply kernel_client_int_enter_keeps_call_stack; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|]. split; [exact Hget|].
    eapply kernel_client_int_exit_keeps_call_stack; eassumption.
  - destruct (kernel_client_publication_keeps_call_stack external platform port abi sg publication focus payload
      state (event_private_storage_rep sg eid allocation ** frame) before after Hpre Hpublish)
      as [[Hinput Hstate] Hafter].
    exists (task_create_stack_publication_state sg publication state).
    split; [constructor; exact Hinput|]. split; [exact Hget|exact Hafter].
  - destruct Hextra as [before cut after Hallocate|pointer before after Hwrites].
    + pose proof (mutex_del_creator_call_stack_resources_valid external platform port abi sg focus payload
        KernelClientHeapClosed state (event_private_storage_rep sg eid allocation ** frame) before Hpre)
        as [Hvalid _].
      destruct (mutex_del_creator_call_stack_allocate external platform port abi focus payload sg state before
        cut after (event_private_storage_rep sg eid allocation ** frame) Hallocate Hpre)
        as [returned [Heffect Hafter]].
      exists returned; split; [constructor; constructor; exact Heffect|]. split; [|exact Hafter].
      destruct Heffect; eapply mutex_del_allocate_keeps_existing_private; eassumption.
    + assert (Hdistinct : pointer <> event_pool_addr sg eid).
      { assert (Hseparate : kernel_client_call_stack_resources abi
          (mutex_del_creator_call_stack_pending abi focus payload) sg focus payload
          (KernelClientHeapExtra pointer) state ** (event_private_storage_rep sg eid allocation ** frame) |--
          coq_prop (pointer <> event_pool_addr sg eid)).
        { cbn [kernel_client_call_stack_resources]; unfold mutex_del_creator_call_stack_pending.
          Intros other current.
          assert (Hpointer : pointer = event_pool_addr sg other) by tauto.
          prop_apply (q_create_private_allocations_disjoint sg other current eid allocation).
          Intros.
          assert (Hdifferent : other <> eid) by tauto.
          entailer!; intro Hsame; apply Hdifferent;
            apply event_pool_addr_injective with (sg := sg); congruence. }
        exact (Hseparate before Hpre). }
      destruct (mutex_del_creator_call_stack_initialization external platform port abi focus payload sg creator
        pointer state before (event_private_storage_rep sg eid allocation ** frame) Hargs Hpre)
        as [other [current [initialized [final [produced
          [Hpointer [Hcurrent [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
      assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
      assert (Hdifferent : eid <> other) by congruence.
      exists (mutex_del_creator_published_state creator initialized other final).
      split; [constructor; econstructor; eassumption|]. split; [|exact Hafter].
      cbn [mutex_del_creator_published_state replace_EventS EventState event_publish eventLifecycle eventPrivate].
      rewrite kernel_map_set_other by exact Hdifferent.
      eapply mutex_del_creator_stores_keep_other_allocation; eassumption.
Qed.

(** SAME actual trace endpoint, strong parked-call map and original
    private lookup. Its frame can be the detached QCB and caller array,
    including mixed initialized/undefined slots. No end-of-interval pool
    list or unrelated heap is selected by this theorem. *)
Lemma q_create_private_allocation_call_stack_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator sg cut before next after
  eid allocation (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state ** (event_private_storage_rep sg eid allocation ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** (event_private_storage_rep sg eid allocation ** frame)) after.
Proof.
  intros external platform port abi focus payload creator sg cut before next after eid allocation frame Hargs Htrace.
  induction Htrace; intros state Hget Hpre.
  - exists state; split; [constructor|]. split; assumption.
  - destruct (q_create_private_allocation_call_stack_step external platform port abi focus payload creator sg
      cut state before middle_cut middle eid allocation frame Hargs Hget H Hpre)
      as [middle_state [Hstep [Hmiddle_get Hmiddle]]].
    destruct (IHHtrace middle_state Hmiddle_get Hmiddle) as [returned [Htail [Hreturned Hafter]]].
    exists returned; split; [econstructor; eassumption|]. split; assumption.
Qed.

Lemma q_create_buffer_bounds_zero : forall start,
  q_create_buffer_bounds start 0 <-> 0 < start <= 4294967295.
Proof. intros; unfold q_create_buffer_bounds; lia. Qed.

Lemma q_create_buffer_bounds_top_cell_rejected :
  ~ q_create_buffer_bounds 4294967292 1.
Proof. unfold q_create_buffer_bounds; lia. Qed.

(** Reindex the carried allocation at the SAME ordinary source endpoint.
    This consumes the source relation and exact lookup supplied together
    by the C-client producer; it proves no Some Event-observer history. *)
Lemma q_create_private_source_interval : forall external port critical sg original returned
  before after eid allocation,
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  after.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  q_create_private_interval critical sg original.(os_sched_call_invocation) eid before after.
Proof.
  intros external port critical sg original returned before after eid allocation Hsource Hbefore Hafter.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Hsource) as [Htrace _].
  split; [exact Htrace|exists allocation; split; assumption].
Qed.

(** One real returning TASK branch. The admitted client execution first
    produces the current strong world and exact ECB on [after]. The
    existing selected-call consumer then reads/takes that very descriptor
    and returns on [final]. No private owner is manufactured from a pure
    source trace, and no weak map is strengthened. The final selection is
    conditional: this is not an input requirement that every Create caller
    already be a running task, nor an eventual-return promise. Generic /
    boot calls keep their existing uninterrupted/resource-call branch. *)
Lemma q_create_private_allocation_call_stack_return : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus fragments creator sg cut before after
  state handler eid allocation (frame : Assertion),
  let incoming := focus.(armv7a_focus_call).(os_sched_call_stack) in
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before KernelClientHeapClosed after ->
  (kernel_client_call_stack_resources abi
      (mutex_del_creator_call_stack_pending abi focus (incoming.(stackLeaseRegion), fragments))
      sg focus (incoming.(stackLeaseRegion), fragments) cut state **
    (event_private_storage_rep sg eid allocation **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame))) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      cut state KernelClientHeapClosed returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (task_current_at returned incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
     tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg incoming.(stackLeaseSlot) ->
     let restored := os_int_exit_wrapper_restored_state returned incoming in
     exists saved,
       armv7a_irq_restore_pointer_reads sg after (task_slot_addr sg incoming.(stackLeaseSlot))
         saved.(armv7a_continuation_sp) /\
       armv7a_continuation_focus_binding focus saved /\
       task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
       (forall final, armv7a_restore_transition abi handler saved after final ->
         restored.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
         (kernel_call_execution_owned external platform
            (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
            (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
          task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
          (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
            restored.(TskState) restored.(TskState).(parkedTaskStacks) **
            (unmap_table_rep sg ** (event_private_storage_rep sg eid allocation ** frame)))) final)).
Proof.
  intros external platform port abi focus fragments creator sg cut before after state handler eid allocation
    frame incoming Hargs Hget Htrace Hpre.
  destruct (q_create_private_allocation_call_stack_trace external platform port abi focus
    (incoming.(stackLeaseRegion), fragments) creator sg cut before KernelClientHeapClosed after eid allocation
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)
    Hargs Htrace state Hget Hpre) as [returned [Heffect [Hlookup Hafter]]].
  exists returned; split; [exact Heffect|]. split; [exact Hlookup|]. intros Hcurrent Haddress restored.
  assert (Hopen : kernel_client_call_stack_resources abi
      (mutex_del_creator_call_stack_pending abi focus (incoming.(stackLeaseRegion), fragments))
      sg focus (incoming.(stackLeaseRegion), fragments) KernelClientHeapClosed returned **
      (event_private_storage_rep sg eid allocation **
        (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
         os_int_exit_context_resources port handler ** frame)) |--
    kernel_client_call_stack_world abi sg focus (incoming.(stackLeaseRegion), fragments) returned **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (event_private_storage_rep sg eid allocation ** frame))).
  { cbn [kernel_client_call_stack_resources]; entailer!. }
  destruct (kernel_client_call_stack_resume external platform port abi sg focus fragments returned handler
    (event_private_storage_rep sg eid allocation ** frame) after Hcurrent Haddress (Hopen after Hafter))
    as [saved [Hreads [Hfocus [Hcoverage Hreturn]]]].
  exists saved; split; [exact Hreads|]. split; [exact Hfocus|]. split; [exact Hcoverage|].
  intros final Hrestore; destruct (Hreturn final Hrestore) as [_ Hfinal].
  split; [exact Hlookup|exact Hfinal].
Qed.

(** The physical image below is independent of the lifecycle image. It is
    produced by the caller's actual C stores, so a partially initialized ECB
    remains a genuine exclusive frame while its ghost update is composed.
    No allocation lookup is inferred from these bytes. The same concrete
    registered creator family returns both that lookup and these exact bytes
    on the same final heap; no all-clients or CPU assumption is added. *)
Lemma q_create_private_storage_disjoint : forall sg eid first other second,
  event_private_storage_rep sg eid first ** event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg other) second |--
    coq_prop (eid <> other).
Proof.
  intros sg eid first other second; destruct (Z.eq_dec eid other) as [->|Hne]; [|entailer!].
  unfold event_private_storage_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg other) first.(eventPrivateStorage) EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg other) second EventPtrField
    ltac:(unfold event_fields; simpl; tauto)).
  cbn [event_cell event_field_offset].
  destruct (first.(eventPrivateStorage) EventPtrField), (second EventPtrField).
  all: repeat match goal with
    | |- context [?p # Ptr |-> ?v] => sep_apply_l_atomic (store_ptr_undef_store_ptr p v)
    end.
  all: prop_apply (dup_undef_store_ptr (event_pool_addr sg other + 4)); entailer!.
Qed.

Lemma q_create_private_storage_call_stack_step : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator sg cut state before next after
  eid allocation (image : EventStorage) (frame : Assertion),
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_client_heap_step (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame)) before ->
  exists returned,
    kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame)) after.
Proof.
  intros external platform port abi focus payload creator sg cut state before next after eid allocation image frame
    Hargs Hget Hsource Hpre.
  destruct Hsource as [before after Henter|before after Hexit|publication before after Hpublish|
    cut before next after Hextra].
  - exists (os_int_enter_state state); split; [constructor|]. split; [exact Hget|].
    eapply kernel_client_int_enter_keeps_call_stack; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|]. split; [exact Hget|].
    eapply kernel_client_int_exit_keeps_call_stack; eassumption.
  - destruct (kernel_client_publication_keeps_call_stack external platform port abi sg publication focus payload
      state (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame) before after Hpre Hpublish)
      as [[Hinput Hstate] Hafter].
    exists (task_create_stack_publication_state sg publication state).
    split; [constructor; exact Hinput|]. split; [exact Hget|exact Hafter].
  - destruct Hextra as [before cut after Hallocate|pointer before after Hwrites].
    + pose proof (mutex_del_creator_call_stack_resources_valid external platform port abi sg focus payload
        KernelClientHeapClosed state (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame) before Hpre)
        as [Hvalid _].
      destruct (mutex_del_creator_call_stack_allocate external platform port abi focus payload sg state before
        cut after (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame) Hallocate Hpre)
        as [returned [Heffect Hafter]].
      exists returned; split; [constructor; constructor; exact Heffect|]. split; [|exact Hafter].
      destruct Heffect; eapply mutex_del_allocate_keeps_existing_private; eassumption.
    + assert (Hdistinct : pointer <> event_pool_addr sg eid).
      { assert (Hseparate : kernel_client_call_stack_resources abi
          (mutex_del_creator_call_stack_pending abi focus payload) sg focus payload
          (KernelClientHeapExtra pointer) state ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame) |--
          coq_prop (pointer <> event_pool_addr sg eid)).
        { cbn [kernel_client_call_stack_resources]; unfold mutex_del_creator_call_stack_pending.
          Intros other current.
          assert (Hpointer : pointer = event_pool_addr sg other) by tauto.
          prop_apply (q_create_private_storage_disjoint sg other current eid image).
          Intros.
          assert (Hdifferent : other <> eid) by tauto.
          entailer!; intro Hsame; apply Hdifferent;
            apply event_pool_addr_injective with (sg := sg); congruence. }
        exact (Hseparate before Hpre). }
      destruct (mutex_del_creator_call_stack_initialization external platform port abi focus payload sg creator
        pointer state before (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame) Hargs Hpre)
        as [other [current [initialized [final [produced
          [Hpointer [Hcurrent [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
      assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
      assert (Hdifferent : eid <> other) by congruence.
      exists (mutex_del_creator_published_state creator initialized other final).
      split; [constructor; econstructor; eassumption|]. split; [|exact Hafter].
      cbn [mutex_del_creator_published_state replace_EventS EventState event_publish eventLifecycle eventPrivate].
      rewrite kernel_map_set_other by exact Hdifferent.
      eapply mutex_del_creator_stores_keep_other_allocation; eassumption.
Qed.

Lemma q_create_private_storage_call_stack_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator sg cut before next after
  eid allocation (image : EventStorage) (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame)) after.
Proof.
  intros external platform port abi focus payload creator sg cut before next after eid allocation image frame Hargs Htrace.
  induction Htrace; intros state Hget Hpre.
  - exists state; split; [constructor|]. split; assumption.
  - destruct (q_create_private_storage_call_stack_step external platform port abi focus payload creator sg
      cut state before middle_cut middle eid allocation image frame Hargs Hget H Hpre)
      as [middle_state [Hstep [Hmiddle_get Hmiddle]]].
    destruct (IHHtrace middle_state Hmiddle_get Hmiddle) as [returned [Htail [Hreturned Hafter]]].
    exists returned; split; [econstructor; eassumption|]. split; assumption.
Qed.

Lemma q_create_private_storage_call_stack_return : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus fragments creator sg cut before after
  state handler eid allocation (image : EventStorage) (frame : Assertion),
  let incoming := focus.(armv7a_focus_call).(os_sched_call_stack) in
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before KernelClientHeapClosed after ->
  (kernel_client_call_stack_resources abi
      (mutex_del_creator_call_stack_pending abi focus (incoming.(stackLeaseRegion), fragments))
      sg focus (incoming.(stackLeaseRegion), fragments) cut state **
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame))) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      cut state KernelClientHeapClosed returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (task_current_at returned incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
     tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg incoming.(stackLeaseSlot) ->
     let restored := os_int_exit_wrapper_restored_state returned incoming in
     exists saved,
       armv7a_irq_restore_pointer_reads sg after (task_slot_addr sg incoming.(stackLeaseSlot))
         saved.(armv7a_continuation_sp) /\
       armv7a_continuation_focus_binding focus saved /\
       task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
       (forall final, armv7a_restore_transition abi handler saved after final ->
         restored.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
         (kernel_call_execution_owned external platform
            (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
            (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
          task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
          (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
            restored.(TskState) restored.(TskState).(parkedTaskStacks) **
            (unmap_table_rep sg ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame)))) final)).
Proof.
  intros external platform port abi focus fragments creator sg cut before after state handler eid allocation
    image frame incoming Hargs Hget Htrace Hpre.
  destruct (q_create_private_storage_call_stack_trace external platform port abi focus
    (incoming.(stackLeaseRegion), fragments) creator sg cut before KernelClientHeapClosed after eid allocation image
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)
    Hargs Htrace state Hget Hpre) as [returned [Heffect [Hlookup Hafter]]].
  exists returned; split; [exact Heffect|]. split; [exact Hlookup|]. intros Hcurrent Haddress restored.
  assert (Hopen : kernel_client_call_stack_resources abi
      (mutex_del_creator_call_stack_pending abi focus (incoming.(stackLeaseRegion), fragments))
      sg focus (incoming.(stackLeaseRegion), fragments) KernelClientHeapClosed returned **
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
        (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
         os_int_exit_context_resources port handler ** frame)) |--
    kernel_client_call_stack_world abi sg focus (incoming.(stackLeaseRegion), fragments) returned **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame))).
  { cbn [kernel_client_call_stack_resources]; entailer!. }
  destruct (kernel_client_call_stack_resume external platform port abi sg focus fragments returned handler
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image ** frame) after Hcurrent Haddress (Hopen after Hafter))
    as [saved [Hreads [Hfocus [Hcoverage Hreturn]]]].
  exists saved; split; [exact Hreads|]. split; [exact Hfocus|]. split; [exact Hcoverage|].
  intros final Hrestore; destruct (Hreturn final Hrestore) as [_ Hfinal].
  split; [exact Hlookup|exact Hfinal].
Qed.

(** Generic/non-task resource cuts use their existing world; this is not
    a projection-and-reconstruction of the strong selected-Task map. *)
Lemma q_create_private_storage_creator_step : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut state before next after
  observer allocation (image : EventStorage) (frame : Assertion),
  mutex_del_creator_arguments creator -> UCOS2_state_inv sg state ->
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  mutex_del_creator_publication_step creator sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame)) before ->
  exists returned,
    mutex_del_creator_publication_effect creator sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame)) after.
Proof.
  intros external platform port abi creator sg cut state before next after observer allocation image frame
    Hargs Hvalid Hget Hsource Hpre.
  destruct Hsource as [before cut after Hallocate|pointer before after Hwrites].
  - destruct (mutex_del_creator_allocate_pending external platform port abi sg state before cut after
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame) Hallocate Hpre)
      as [returned [Heffect Hafter]].
    exists returned; split; [constructor; exact Heffect|]. split; [|exact Hafter].
    destruct Heffect; eapply mutex_del_allocate_keeps_existing_private; eassumption.
  - assert (Hdifferent : pointer <> event_pool_addr sg observer).
    { assert (Hseparate : kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg
        (KernelClientHeapExtra pointer) state ** (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame) |--
        coq_prop (pointer <> event_pool_addr sg observer)).
      { cbn [kernel_client_heap_resources]; unfold mutex_del_creator_pending.
        Intros other owned.
        assert (Hpointer : pointer = event_pool_addr sg other) by tauto.
        prop_apply (q_create_private_storage_disjoint sg other owned observer image).
        Intros.
        assert (Hdistinct : other <> observer) by tauto.
        entailer!; intro Heq; apply Hdistinct.
        apply event_pool_addr_injective with (sg := sg); congruence. }
      exact (Hseparate before Hpre). }
    destruct (mutex_del_creator_initialization_publish external platform port abi sg creator pointer state before
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame) Hargs Hpre)
      as [eid [current [initialized [final [produced [Hpointer [Hcurrent [Hstores [Hfinal [Hrun Hafter]]]]]]]]]].
    assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
    assert (Hdistinct : observer <> eid) by congruence.
    exists (mutex_del_creator_published_state creator initialized eid final).
    split; [econstructor; eassumption|]. split; [|exact Hafter].
    cbn [mutex_del_creator_published_state replace_EventS EventState event_publish eventLifecycle eventPrivate].
    rewrite kernel_map_set_other by exact Hdistinct.
    eapply mutex_del_creator_stores_keep_other_allocation; eassumption.
Qed.

Lemma q_create_private_storage_registered_step : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut state before next after
  observer allocation (image : EventStorage) (frame : Assertion),
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  kernel_client_heap_step (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame)) before ->
  exists returned,
    kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame)) after.
Proof.
  intros external platform port abi creator sg cut state before next after observer allocation image frame
    Hargs Hget Hsource Hpre.
  assert (Hvalid : UCOS2_state_inv sg state).
  { destruct Hpre as [owned [rest [_ [Howned _]]]].
    exact (mutex_del_creator_publication_cut_valid external platform port abi sg cut state owned Howned). }
  destruct Hsource as [before after Henter|before after Hexit|publication before after Hpublish|
    cut before next after Hregistered].
  - exists (os_int_enter_state state); split; [constructor|]. split; [exact Hget|].
    eapply kernel_client_int_enter_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|]. split; [exact Hget|]. eapply kernel_client_int_exit_resources; eassumption.
  - destruct (kernel_client_publication_resources external platform port abi sg publication state
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame) before after Hpre Hpublish)
      as [[Hinput Hstate] Hafter].
    exists (task_create_stack_publication_state sg publication state).
    split; [constructor; exact Hinput|]. split; [exact Hget|exact Hafter].
  - destruct (q_create_private_storage_creator_step external platform port abi creator sg
      cut state before next after observer allocation image frame Hargs Hvalid Hget Hregistered Hpre)
      as [returned [Heffect [Hlookup Hafter]]].
    exists returned; split; [constructor; exact Heffect|]. split; assumption.
Qed.

Lemma q_create_private_storage_registered_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut before next after
  observer allocation (image : EventStorage) (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state,
  state.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) observer = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg observer) image ** frame)) after.
Proof.
  intros external platform port abi creator sg cut before next after observer allocation image frame Hargs Hsource.
  induction Hsource; intros state Hget Hpre.
  - exists state; split; [constructor|]. split; assumption.
  - destruct (q_create_private_storage_registered_step external platform port abi creator sg
      cut state before middle_cut middle observer allocation image frame Hargs Hget H Hpre)
      as [middle_state [Hstep [Hlookup Hmiddle]]].
    destruct (IHHsource middle_state Hlookup Hmiddle) as [returned [Htail [Hget_returned Hafter]]].
    exists returned; split; [econstructor; eassumption|]. split; assumption.
Qed.

(** At a source store boundary, the written cell and all other original
    bytes first reconstruct the ACTUAL new physical image. The registered
    execution then transports that image on its own returned heap. This
    consumes the generic field-update rule also used for the C stores;
    neither the old lifecycle image nor a pure trace produces these bytes.
    [frame] may contain any partially initialized QCB and mixed buffer. *)
Lemma q_create_private_written_call_stack_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus payload creator sg cut before next after
  state eid allocation image field value (frame : Assertion),
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state **
    ((event_cell (event_pool_addr sg eid) field value **
      event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image field) **
     frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload next returned **
     (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
       (event_write image field value) ** frame)) after.
Proof.
  intros external platform port abi focus payload creator sg cut before next after state
    eid allocation image field value frame Hfield Hargs Hget Htrace Hpre.
  eapply q_create_private_storage_call_stack_trace; try eassumption.
  assert (Hreassemble :
    kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state **
    ((event_cell (event_pool_addr sg eid) field value **
      event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image field) ** frame)
    |-- kernel_client_call_stack_resources abi (mutex_del_creator_call_stack_pending abi focus payload)
      sg focus payload cut state **
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      (event_write image field value) ** frame)).
  { sep_apply_r_atomic (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image field value Hfield); entailer!. }
  exact (Hreassemble before Hpre).
Qed.

Lemma q_create_private_written_registered_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut before next after
  state eid allocation image field value (frame : Assertion),
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  mutex_del_creator_arguments creator ->
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    ((event_cell (event_pool_addr sg eid) field value **
      event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image field) **
     frame)) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
     (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
       (event_write image field value) ** frame)) after.
Proof.
  intros external platform port abi creator sg cut before next after state eid allocation image field value
    frame Hfield Hargs Hget Htrace Hpre.
  eapply q_create_private_storage_registered_trace; try eassumption.
  assert (Hreassemble : kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    ((event_cell (event_pool_addr sg eid) field value **
      event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image field) ** frame)
    |-- kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      (event_write image field value) ** frame)).
  { sep_apply_r_atomic (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) image field value Hfield); entailer!. }
  exact (Hreassemble before Hpre).
Qed.

(** The paired ECB/QCB and caller buffer are three separate physical
    resources. The allocation's Queue tag records their existing ownership
    pairing, not a second QCB image or a heap-producing pure certificate. *)
Definition q_create_private_pair sg eid allocation qid image start slots : Assertion :=
  coq_prop (allocation.(eventPrivateQueue) = Some qid) &&
    (event_private_storage_rep sg eid allocation **
     qcb_storage_rep sg qid image ** q_create_caller_buffer start slots).

(** Reuse an actual registered C-client producer. The carried ECB excludes
    a foreign creator's private ECB by separation of their real pointer
    fields (mutex_del_creator_pending_separate_allocation); that exclusion
    preserves the exact allocation lookup through allocation, writes and
    publication. QCB and buffer are the producer's actual instruction frame.

    The supplied execution may contain IntEnter, non-scheduling IntExit,
    Task publication, and the selected Sem/Mbox creator fragments. This
    theorem deliberately does NOT claim coverage of arbitrary registered
    clients, a complete Save/Restore interval, or a new platform law. *)
Lemma q_create_private_pair_registered_trace : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut before next after
  eid allocation qid image start slots (frame : Assertion),
  mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  forall state,
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
    q_create_private_pair sg eid allocation qid image start slots ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg
      cut state next returned /\
    returned.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      q_create_private_pair sg eid allocation qid image start slots ** frame) after.
Proof.
  intros external platform port abi creator sg cut before next after eid allocation qid image
    start slots frame Hargs Htrace state Hget Hpre.
  assert (Hopen : kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
      q_create_private_pair sg eid allocation qid image start slots ** frame |--
    coq_prop (allocation.(eventPrivateQueue) = Some qid) &&
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state **
      (event_private_storage_rep sg eid allocation **
        (qcb_storage_rep sg qid image ** q_create_caller_buffer start slots ** frame)))).
  { unfold q_create_private_pair; entailer!. }
  destruct (Hopen before Hpre) as [Hqueue Howned].
  destruct (mutex_del_creator_publication_registered_trace external platform port abi creator sg
    cut before next after eid allocation
    (qcb_storage_rep sg qid image ** q_create_caller_buffer start slots ** frame)
    Hargs Htrace state Hget Howned) as [returned [Heffect [Hcurrent Hafter]]].
  exists returned; split; [exact Heffect|]. split; [exact Hcurrent|].
  assert (Hclose : kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      (event_private_storage_rep sg eid allocation **
        (qcb_storage_rep sg qid image ** q_create_caller_buffer start slots ** frame)) |--
    kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned **
      q_create_private_pair sg eid allocation qid image start slots ** frame).
  { unfold q_create_private_pair; entailer!. }
  exact (Hclose after Hafter).
Qed.
