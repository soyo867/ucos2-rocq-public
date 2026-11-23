Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_program_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_entry_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Import UCOS2_C_Rules ListNotations KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The approved owner-use condition is established from the existing
    initializer endpoint's empty live Event map. Actual initializer posts
    and the single loaded table are consumed by the existing boot owner;
    this is not an extra OSInit/BSP execution theorem or an ABI assumption.
    Startup Memory/BSS/Timer/hook boundaries remain exactly that owner's. *)
Lemma mutex_del_boot_program_owner_use : forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  let state := UCOS2_boot_state sg task_name flag_name memory_name names in
  kernel_boot_initializer_post sg task_name flag_name memory_name names ** unmap_table_rep sg |--
  coq_prop (mutex_owner_event_unlinked state.(TskState) state.(EventState)) && kernel_program_inv sg state.
Proof.
  intros sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory state.
  assert (Huse : mutex_owner_event_unlinked state.(TskState) state.(EventState)).
  { apply mutex_owner_event_unlinked_empty; intros eid; reflexivity. }
  sep_apply_l_atomic (kernel_boot_initializer_post_establishes_program_inv
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  unfold state; entailer!.
Qed.

(** The newer stack-aware publication is not silently replaced by the old
    raw TaskPublish action. Its actual projection supplies the old action,
    while its new parked-map layer changes neither Event lookup nor the
    owner's EventPtr/MultiWait fields. No task/call owner is discarded. *)
Lemma mutex_del_stack_publication_preserves_owner_use : forall sg publication current after,
  kernel_client_step (task_create_stack_publication_client publication) sg current after ->
  mutex_owner_event_unlinked current.(TskState) current.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg publication current after Hstep Huse.
  destruct (task_create_stack_publication_raw_projection sg publication current after Hstep)
    as [Hraw Hafter].
  pose proof (task_creation_client_preserves_mutex_owner_event_unlinked _ sg current
    (task_create_stack_publication_raw_state sg publication current) Hraw Huse) as Hpublished.
  rewrite Hafter.
  change (mutex_owner_event_unlinked
    (task_create_stack_publication_raw_state sg publication current).(TskState)
    (task_create_stack_publication_raw_state sg publication current).(EventState)).
  exact Hpublished.
Qed.

(** Consume the real initialized buffer and concrete publication storage,
    not just a pure client certificate. The existing source owner produces
    the actual new state and FULL continuation map. The table is framed
    once across this protected publication cut, not across an unknown IRQ. *)
Lemma mutex_del_stack_publication_owner_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication current (frame : Assertion),
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  mutex_owner_event_unlinked current.(TskState) current.(EventState) ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_stack_publication_resources external platform port abi sg publication current **
    unmap_table_rep sg ** frame |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current after /\
    mutex_owner_event_unlinked after.(TskState) after.(EventState)) &&
  (kernel_program_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks) ** frame).
Proof.
  intros external platform port abi sg publication current frame Hvalid Hinput Huse after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current after)
    by (split; [exact Hinput|reflexivity]).
  pose proof (mutex_del_stack_publication_preserves_owner_use sg publication current after Hstep Huse) as Hafter.
  pose proof (task_create_stack_publication_source_post external platform port abi sg publication current
    Hvalid Hinput) as Hsource.
  cbv zeta in Hsource; fold after in Hsource; sep_apply_l_atomic Hsource.
  rewrite kernel_program_inv_split_unmap; entailer!.
Qed.

(** The real protected Type=Mutex load supplies the live lookup and fields.
    The separate owner-use protocol is consumed, not derived from Type or
    generic validity. This is the precise _11 resource conclusion before
    its old case-local wrapper, retaining the table and arbitrary frame. *)
Lemma mutex_del_owner_type_entry : forall sg state pe eid observed heap (frame : Assertion),
  pe = event_addr sg eid -> sem_query_public_slot state eid observed ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  (kernel_program_inv sg state ** frame) heap ->
  uchar_load (pe + OSEventType_off) 4 heap ->
  exists mutex,
    UCOS2_state_inv sg state /\ mutex_query_lookup state eid observed /\
    observed.(eventType) = OS_EVENT_TYPE_MUTEX /\ observed.(mutexFields) = Some mutex /\
    mutex_owner_event_unlinked state.(TskState) state.(EventState) /\
    (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame) heap.
Proof.
  intros sg state pe eid observed heap frame Haddress Hslot Huse Hpre Hload.
  pose proof (mutex_del_call_program_type_load sg state pe eid observed heap frame Haddress Hslot Hpre) as Htyped.
  assert (Htype : event_slot_type_value state.(EventState) eid = 4)
    by (eapply uchar_load_deterministic; eassumption).
  assert (Hopen : kernel_program_inv sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) && (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame)).
  { unfold kernel_program_inv, kernel_program_rep; entailer!. }
  destruct (Hopen heap Hpre) as [Hvalid Hraw].
  destruct Hslot as [Hlive|[Hnone Hfree]].
  - assert (Hmutex_type : observed.(eventType) = OS_EVENT_TYPE_MUTEX).
    { unfold event_slot_type_value in Htype; unfold mutex_query_lookup in Hlive; rewrite Hlive in Htype.
      destruct observed.(eventType); simpl in Htype; try lia; reflexivity. }
    pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
    destruct Hevents as [_ [_ [_ [Hfields _]]]].
    specialize (Hfields eid observed Hlive); unfold event_fields_consistency in Hfields; rewrite Hmutex_type in Hfields.
    destruct observed.(mutexFields) as [mutex|] eqn:Hmutex; [|destruct Hfields as [Hfalse _]; contradiction].
    exists mutex; split; [exact Hvalid|]. split; [exact Hlive|]. split; [exact Hmutex_type|].
    split; [reflexivity|]. split; assumption.
  - unfold event_slot_type_value in Htype; rewrite Hnone in Htype; discriminate.
Qed.

(** Actual publication-to-Del protected-read consumer. The before/after
    states are those of the existing source publication owner on THIS
    concrete heap; a free choice of a valid acquired state cannot supply
    this rule. Public-slot transport here follows Task publication's real
    unchanged Event map, not an exclusion of other creators or ABA. *)
Lemma mutex_del_stack_publication_type_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication current pe eid observed heap (frame : Assertion),
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  mutex_owner_event_unlinked current.(TskState) current.(EventState) ->
  pe = event_addr sg eid -> sem_query_public_slot current eid observed ->
  (task_create_stack_publication_resources external platform port abi sg publication current **
    unmap_table_rep sg ** frame) heap ->
  uchar_load (pe + OSEventType_off) 4 heap ->
  let after := task_create_stack_publication_state sg publication current in
  exists mutex,
    kernel_client_step (task_create_stack_publication_client publication) sg current after /\
    UCOS2_state_inv sg after /\ mutex_query_lookup after eid observed /\
    observed.(eventType) = OS_EVENT_TYPE_MUTEX /\ observed.(mutexFields) = Some mutex /\
    mutex_owner_event_unlinked after.(TskState) after.(EventState) /\
    (UCOS2_raw_rep sg after ** unmap_table_rep sg **
      (armv7a_task_continuations abi after.(TskState).(parkedTaskStacks) ** frame)) heap.
Proof.
  intros external platform port abi sg publication current pe eid observed heap frame
    Hvalid Hinput Huse Haddress Hslot Hpre Hload after.
  destruct (mutex_del_stack_publication_owner_resources external platform port abi sg publication current frame
    Hvalid Hinput Huse heap Hpre) as [[Hstep Hafter_use] Hafter].
  fold after in Hstep, Hafter_use, Hafter.
  assert (Hslot_after : sem_query_public_slot after eid observed) by exact Hslot.
  assert (Horder : kernel_program_inv sg after **
      armv7a_task_continuations abi after.(TskState).(parkedTaskStacks) ** frame |--
    kernel_program_inv sg after **
      (armv7a_task_continuations abi after.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
  destruct (mutex_del_owner_type_entry sg after pe eid observed heap _ Haddress Hslot_after Hafter_use
    (Horder heap Hafter) Hload) as [mutex Hentry].
  exists mutex; split; [exact Hstep|exact Hentry].
Qed.

(** Read-only source loop of OSMutex_EffectivePrio. Each tested table
    element is an actual pointer read. Only the exhausted loop reads the
    fallback TCB byte; no abstract scan result is assumed. The helper is
    called while masked and performs no shared-memory stores. *)
Inductive mutex_del_effective_priority_reads (sg : StableGlobVars)
  (pointer : Z) (heap : model) : Z -> Z -> Prop :=
| MutexDelEffectivePriorityHit : forall index,
    0 <= index < 64 ->
    pointer_load (sg.(g_OSTCBPrioTbl) + index * sizeof(PTR)) pointer heap ->
    mutex_del_effective_priority_reads sg pointer heap index index
| MutexDelEffectivePriorityNext : forall index observed result,
    0 <= index < 64 ->
    pointer_load (sg.(g_OSTCBPrioTbl) + index * sizeof(PTR)) observed heap ->
    observed <> pointer ->
    mutex_del_effective_priority_reads sg pointer heap (index + 1) result ->
    mutex_del_effective_priority_reads sg pointer heap index result
| MutexDelEffectivePriorityFallback : forall result,
    uchar_load (tcb_field_address pointer TCBPrio) result heap ->
    mutex_del_effective_priority_reads sg pointer heap 64 result.

Lemma mutex_del_priority_table_load : forall sg table index heap (frame : Assertion),
  0 <= index < 64 ->
  (PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** frame) heap ->
  pointer_load (sg.(g_OSTCBPrioTbl) + index * sizeof(PTR)) (Znth index table 0) heap.
Proof.
  intros sg table index heap frame Hrange Hpre.
  assert (Hopen : PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** frame |--
    (sg.(g_OSTCBPrioTbl) + index * sizeof(PTR)) # Ptr |-> Znth index table 0 **
      (PtrArray.missing_i sg.(g_OSTCBPrioTbl) index 0 64 table ** frame)).
  { sep_apply_l_atomic (PtrArray.full_split_to_missing_i sg.(g_OSTCBPrioTbl) index 64 table 0 Hrange);
    entailer!. }
  eapply framed_pointer_store_load; exact (Hopen heap Hpre).
Qed.

Lemma mutex_del_priority_field_load : forall pointer image priority heap (frame : Assertion),
  image TCBPrio = Some priority ->
  (tcb64_storage_rep pointer image ** frame) heap ->
  uchar_load (tcb_field_address pointer TCBPrio) priority heap.
Proof.
  intros pointer image priority heap frame Hvalue Hpre.
  assert (Hopen : tcb64_storage_rep pointer image ** frame |--
    (tcb_field_address pointer TCBPrio) # UChar |-> priority **
      (tcb64_storage_without pointer TCBPrio image ** frame)).
  { sep_apply_l_atomic (tcb64_storage_split pointer image TCBPrio).
    cbn [tcb_cell]; rewrite Hvalue; entailer!. }
  eapply framed_uchar_store_load; exact (Hopen heap Hpre).
Qed.

Lemma mutex_del_effective_priority_reads_result : forall sg pointer image table fallback heap
  (frame : Assertion) result,
  mutex_priority_fallback image fallback ->
  (tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** frame) heap ->
  mutex_del_effective_priority_reads sg pointer heap 0 result ->
  mutex_effective_priority_result table pointer fallback result.
Proof.
  intros sg pointer image table fallback heap frame result Hfallback Hpre Hsource.
  assert (Htable : forall index, 0 <= index < 64 ->
    pointer_load (sg.(g_OSTCBPrioTbl) + index * sizeof(PTR)) (Znth index table 0) heap).
  { intros index Hrange.
    assert (Horder : tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** frame |--
      PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** (tcb64_storage_rep pointer image ** frame)) by entailer!.
    eapply mutex_del_priority_table_load; [exact Hrange|exact (Horder heap Hpre)]. }
  assert (Hfield : uchar_load (tcb_field_address pointer TCBPrio) fallback heap).
  { assert (Horder : tcb64_storage_rep pointer image ** PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** frame |--
      tcb64_storage_rep pointer image ** (PtrArray.full sg.(g_OSTCBPrioTbl) 64 table ** frame)) by entailer!.
    eapply mutex_del_priority_field_load; [exact Hfallback|exact (Horder heap Hpre)]. }
  assert (Hloop : forall index returned,
    mutex_del_effective_priority_reads sg pointer heap index returned ->
    mutex_priority_no_match table pointer index ->
    mutex_effective_priority_result table pointer fallback returned).
  { intros index returned Hreads; induction Hreads as
      [index Hrange Hload | index observed returned Hrange Hload Hdifferent Htail IH | returned Hload];
      intros Hprevious.
    - assert (Hhit : Znth index table 0 = pointer)
        by (eapply pointer_load_deterministic; [apply Htable; exact Hrange|exact Hload]).
      right; split; [exact Hrange|]. split; [exact Hhit|].
      intros other Hother Hsame; destruct (Z_le_gt_dec index other); [assumption|].
      exfalso; apply (Hprevious other); [lia|exact Hsame].
    - apply IH; unfold mutex_priority_no_match in *; intros other Hother.
      destruct (Z.eq_dec other index) as [->|Hneq].
      + assert (Hvalue : Znth index table 0 = observed)
          by (eapply pointer_load_deterministic; [apply Htable; exact Hrange|exact Hload]).
        congruence.
      + apply Hprevious; lia.
    - assert (returned = fallback) by (eapply uchar_load_deterministic; eassumption).
      subst returned; apply mutex_effective_priority_no_alias; exact Hprevious. }
  eapply Hloop; [exact Hsource|]. unfold mutex_priority_no_match; intros; lia.
Qed.

(** Actual ceiling release shared by the held-owner call below. The input
    is the owned raw program, and the output is the existing transient
    released representation, not a claimed stable global invariant. *)
Lemma mutex_del_ceiling_store_resources : forall sg state ceiling before after (frame : Assertion),
  0 <= ceiling < 64 ->
  (kernel_program_rep sg state ** frame) before ->
  kernel_heap_execution
    (pointer_store_writes (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)) 0) before after ->
  (mutex_del_released_resources sg state ceiling ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state ceiling before after frame Hrange Hpre Hstore.
  set (slot := sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR)).
  set (residual := store_prio_tbl_missing_i sg state.(TskState).(prioTbl) ceiling **
    UCOS2_raw_rep_missing_priority_table sg state ** unmap_table_rep sg ** frame).
  assert (Hopen : kernel_program_rep sg state ** frame |-- slot # Ptr |->_ ** residual).
  { unfold kernel_program_rep, residual, slot; rewrite UCOS2_raw_rep_priority_table_equiv.
    sep_apply_l_atomic (store_prio_tbl_split_cell sg state.(TskState).(prioTbl) ceiling Hrange).
    sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + ceiling * sizeof(PTR))
      (prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) ceiling))); entailer!. }
  destruct (framed_pointer_store_execution slot 0 residual before ltac:(lia) (Hopen before Hpre))
    as [produced [Hwrite Hreleased]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  assert (Hclose : slot # Ptr |-> 0 ** residual |--
    mutex_del_released_resources sg state ceiling ** unmap_table_rep sg ** frame).
  { unfold slot, residual.
    sep_apply_l_atomic (mutex_del_released_resources_merge_cell sg state ceiling Hrange); entailer!. }
  exact (Hclose after Hreleased).
Qed.
