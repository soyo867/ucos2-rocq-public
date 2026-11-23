Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.event Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual six Flag fields and all non-Task/Scheduler resources are
    retained throughout the same reservation, free-pop and link stores. *)
Definition sem_pend_task_fields_frame sg state : Assertion :=
  flag_fields_configured_rep sg state.(FlagState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.

Lemma sem_pend_task_fields_frame_used_map_eq : forall sg state tasks,
  state.(TskState).(inUsedTaskStates) = tasks.(inUsedTaskStates) ->
  state.(TskState).(parkedTaskStacks) = tasks.(parkedTaskStacks) ->
  sem_pend_task_fields_frame sg state = sem_pend_task_fields_frame sg (replace_TskS tasks state).
Proof.
  intros sg state tasks Hused Hstacks.
  unfold sem_pend_task_fields_frame, UCOS2_raw_rep_missing_task_storage_sched_flag; simpl.
  rewrite Hstacks.
  rewrite (event_raw_rep_change_task_index sg state.(TskState) tasks state.(EventState)); [reflexivity|].
  apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin.
  rewrite Hused; reflexivity.
Qed.

Lemma sem_pend_task_fields_raw_split_task_sched : forall sg state,
  UCOS2_fields_raw_rep sg state --||--
  task_public_storage sg state.(TskState) ** sched_raw_rep sg state.(TskState) state.(SchedState) **
  sem_pend_task_fields_frame sg state.
Proof.
  intros; unfold UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag, UCOS2_raw_rep_missing_module,
    UCOS2_selected_rep, UCOS2_module_rep, task_shared_rep,
    sem_pend_task_fields_frame, UCOS2_raw_rep_missing_task_storage_sched_flag.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect]; split; entailer!.
Qed.

Definition sem_pend_task_fields_priority_frame sg state : Assertion :=
  task_public_storage_without_prio_tbl sg state.(TskState) **
  sched_raw_rep sg state.(TskState) state.(SchedState) ** sem_pend_task_fields_frame sg state.

Lemma sem_pend_task_fields_priority_equiv : forall sg state,
  UCOS2_fields_raw_rep sg state --||--
  store_prio_tbl sg state.(TskState).(prioTbl) ** sem_pend_task_fields_priority_frame sg state.
Proof.
  intros; rewrite sem_pend_task_fields_raw_split_task_sched, task_public_storage_prio_tbl_equiv.
  unfold sem_pend_task_fields_priority_frame; split; entailer!.
Qed.

Lemma sem_pend_task_fields_priority_reserve_eq : forall sg state p invocation origin,
  sem_pend_task_fields_priority_frame sg state = sem_pend_task_fields_priority_frame sg
    (replace_TskS (task_reserve state.(TskState) p invocation origin) state).
Proof.
  intros; unfold sem_pend_task_fields_priority_frame.
  rewrite (sched_raw_rep_change_task_index sg state.(TskState)
    (task_reserve state.(TskState) p invocation origin) state.(SchedState) eq_refl),
    (sem_pend_task_fields_frame_used_map_eq sg state
      (task_reserve state.(TskState) p invocation origin) eq_refl eq_refl); reflexivity.
Qed.

Lemma sem_pend_task_fields_split_priority_cell : forall sg state p,
  0 <= p < 64 -> UCOS2_fields_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
    ((sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |->
       prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) p) **
     store_prio_tbl_missing_i sg state.(TskState).(prioTbl) p **
     sem_pend_task_fields_priority_frame sg state).
Proof.
  intros sg state p Hp; unfold UCOS2_fields_inv.
  rewrite sem_pend_task_fields_priority_equiv; Intros.
  sep_apply_l_atomic (store_prio_tbl_split_cell sg state.(TskState).(prioTbl) p Hp); entailer!.
Qed.

Lemma sem_pend_task_fields_merge_reserved_priority : forall sg state p invocation origin,
  UCOS2_state_inv sg state -> task_reserve_guard sg state.(TskState) p invocation origin ->
  (sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |-> 1 **
    store_prio_tbl_missing_i sg state.(TskState).(prioTbl) p **
    sem_pend_task_fields_priority_frame sg state |--
  UCOS2_fields_inv sg (replace_TskS (task_reserve state.(TskState) p invocation origin) state).
Proof.
  intros sg state p invocation origin Hvalid Hguard.
  pose proof (UCOS2_task_reserve_preserves_validity sg state p invocation origin Hvalid Hguard) as Hpost.
  assert (Hp : 0 <= p < 64).
  { pose proof (proj1 Hguard) as Hp; pose proof (proj1 (proj1 Hvalid)) as Hsg.
    unfold task_priority_in_range in Hp; unfold valid_stable_glob_vars in Hsg; intuition lia. }
  pose proof (store_prio_tbl_merge_updated_cell sg state.(TskState).(prioTbl) p PTReserved Hp) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge; sep_apply_l_atomic Hmerge.
  unfold UCOS2_fields_inv; rewrite sem_pend_task_fields_priority_equiv.
  rewrite <- sem_pend_task_fields_priority_reserve_eq; entailer!.
Qed.

Definition sem_pend_task_fields_without_free_head sg state rest : Assertion :=
  task_public_storage_without_free_head sg state.(TskState) rest **
  sched_raw_rep sg state.(TskState) state.(SchedState) ** sem_pend_task_fields_frame sg state.

Lemma sem_pend_task_fields_detach_merge : forall sg args invocation origin acquired slot rest image,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_next sg rest **
    sem_pend_task_fields_without_free_head sg acquired rest |--
  UCOS2_fields_inv sg (task_tcb_init_detached_state args invocation origin acquired slot rest image).
Proof.
  intros sg args invocation origin acquired slot rest image Hentry Hdetach.
  pose proof (task_tcb_init_detach_preserves_validity _ _ _ _ _ _ _ _ Hentry Hdetach) as Hvalid.
  pose proof (proj1 (proj2 (proj1 Hentry))) as Htasks.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj1 Htasks))))) as Hnd.
  unfold sem_pend_task_fields_without_free_head, task_tcb_init_free_next.
  sep_apply_l_atomic (task_public_storage_merge_detached_free_head sg acquired.(TskState)
    args.(initPrio) (task_tcb_init_initial_entry invocation origin) slot rest image Hnd (proj1 Hdetach)).
  pose proof (sched_raw_rep_change_task_index sg acquired.(TskState)
    (task_detach_head acquired.(TskState) args.(initPrio)
      (task_tcb_init_initial_entry invocation origin) slot rest image) acquired.(SchedState) eq_refl) as Hsched.
  pose proof (sem_pend_task_fields_frame_used_map_eq sg acquired
    (task_detach_head acquired.(TskState) args.(initPrio)
      (task_tcb_init_initial_entry invocation origin) slot rest image) eq_refl eq_refl) as Hresidual.
  rewrite Hsched, Hresidual.
  unfold UCOS2_fields_inv; rewrite sem_pend_task_fields_raw_split_task_sched.
  unfold task_tcb_init_detached_state; entailer!.
Qed.

Lemma sem_pend_task_fields_raw_split_publication : forall sg state,
  UCOS2_fields_raw_rep sg state --||--
  sg.(g_OSTCBList) # Ptr |-> task_tcb_init_active_head sg state **
  task_tcb_init_used_storage sg state **
  sg.(g_OSTaskCtr) # UChar |-> task_tcb_init_count state **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group state **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows state) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg state) **
  task_tcb_init_publication_fields_other sg state.
Proof.
  intros; rewrite sem_pend_task_fields_raw_split_task_sched.
  unfold task_public_storage, task_tcb_init_active_head, task_tcb_init_used_storage, task_tcb_init_count,
    task_tcb_init_ready_group, task_tcb_init_ready_rows, task_tcb_init_priority_table,
    task_tcb_init_publication_fields_other, task_tcb_init_free_root, store_prio_tbl,
    sched_raw_rep, sem_pend_task_fields_frame.
  rewrite sched_rows_array_equiv; unfold sched_row_values; split; entailer!.
Qed.

Definition sem_pend_task_fields_link_globals sg current : Assertion :=
  sg.(g_OSTCBList) # Ptr |-> task_tcb_init_active_head sg current **
  sg.(g_OSTaskCtr) # UChar |-> task_tcb_init_count current **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group current **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows current) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg current) **
  task_tcb_init_publication_fields_other sg current.


Lemma sem_pend_task_fields_free_pop_execution :
  forall sg args invocation origin acquired slot rest (frame : Assertion) before,
  task_tcb_init_entry sg args invocation origin acquired ->
  acquired.(TskState).(unUsedTaskStates) = slot :: rest ->
  (UCOS2_fields_inv sg acquired ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation args invocation origin acquired slot rest image /\
    task_tcb_init_free_pop_fragment sg (task_slot_addr sg slot)
      (task_tcb_init_free_next sg rest) before after /\
    (UCOS2_fields_inv sg (task_tcb_init_detached_state args invocation origin acquired slot rest image) **
      task_slot_storage_rep sg slot image ** frame) after.
Proof.
  intros sg args invocation origin acquired slot rest frame before Hentry Hhead Hbefore.
  pose proof (proj1 Hentry) as Hvalid.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  assert (Hlinks : task_free_links sg acquired.(TskState).(taskLifecycle).(taskFreeStorage)
    acquired.(TskState).(unUsedTaskStates)) by (unfold task_in_range in Htasks; tauto).
  rewrite Hhead in Hlinks; destruct Hlinks as [image [Himage [Hnext Htail]]].
  assert (Hdetach : task_tcb_init_detach_observation args invocation origin acquired slot rest image).
  { unfold task_tcb_init_detach_observation, task_detach_guard.
    split; [exact Hhead|]; split; [exact (proj1 (proj2 (proj2 (proj2 Hentry))))|].
    split; [reflexivity|exact Himage]. }
  assert (Hslot : task_slot_in_range sg slot).
  { apply (proj2 (proj1 (proj1 Htasks) slot)); right; left; rewrite Hhead; left; reflexivity. }
  pose proof (task_slot_addr_positive__publication_and_returns sg slot (proj1 (proj1 Hvalid)) Hslot) as Hpositive.
  assert (Hsplit : UCOS2_fields_inv sg acquired ** frame |--
    sg.(g_OSTCBFreeList) # Ptr |-> task_slot_addr sg slot **
    (task_slot_storage_rep sg slot image ** sem_pend_task_fields_without_free_head sg acquired rest ** frame)).
  { unfold UCOS2_fields_inv; rewrite sem_pend_task_fields_raw_split_task_sched; Intros.
    sep_apply_l_atomic (task_public_storage_split_free_head sg acquired.(TskState) slot rest Hhead).
    Intros found. assert (found = image) by congruence; subst found.
    unfold sem_pend_task_fields_without_free_head; entailer!. }
  pose proof (Hsplit before Hbefore) as Howned.
  pose proof (framed_pointer_store_load _ _ _ before Howned) as Hroot_read.
  assert (Hnext_focus : sg.(g_OSTCBFreeList) # Ptr |-> task_slot_addr sg slot **
      (task_slot_storage_rep sg slot image ** sem_pend_task_fields_without_free_head sg acquired rest ** frame) |--
    (tcb_field_address (task_slot_addr sg slot) TCBNext) # Ptr |-> task_tcb_init_free_next sg rest ** TT).
  { unfold task_slot_storage_rep.
    sep_apply_l_atomic (tcb_configured_storage_split_field
      sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg slot) image (TCBCommonField TCBNext)
      (tcb_configured_common_field_in sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) TCBNext)).
    rewrite Hnext; cbn [tcb_layout_cell tcb_cell]; unfold task_tcb_init_free_next; entailer!; intros ? ?; exact I. }
  pose proof (framed_pointer_store_load _ _ _ before (Hnext_focus before Howned)) as Hnext_read.
  assert (Herase : sg.(g_OSTCBFreeList) # Ptr |-> task_slot_addr sg slot **
      (task_slot_storage_rep sg slot image ** sem_pend_task_fields_without_free_head sg acquired rest ** frame) |--
    sg.(g_OSTCBFreeList) # Ptr |->_ **
      (task_slot_storage_rep sg slot image ** sem_pend_task_fields_without_free_head sg acquired rest ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSTCBFreeList) (task_slot_addr sg slot)); entailer!. }
  destruct (framed_pointer_store_execution _ _ _ before (proj1 Hnext_read) (Herase before Howned))
    as [after [Hwrite Hafter]].
  exists image, after; split; [exact Hdetach|].
  split; [unfold task_tcb_init_free_pop_fragment; split; [exact Hroot_read|];
    split; [lia|]; split; assumption|].
  assert (Hmerge : sg.(g_OSTCBFreeList) # Ptr |-> task_tcb_init_free_next sg rest **
      (task_slot_storage_rep sg slot image ** sem_pend_task_fields_without_free_head sg acquired rest ** frame) |--
    UCOS2_fields_inv sg (task_tcb_init_detached_state args invocation origin acquired slot rest image) **
      task_slot_storage_rep sg slot image ** frame).
  { sep_apply_l_atomic (sem_pend_task_fields_detach_merge sg args invocation origin acquired slot rest image Hentry Hdetach).
    entailer!. }
  exact (Hmerge after Hafter).
Qed.

Lemma sem_pend_task_fields_links_execution :
  forall sg args current slot image (frame : Assertion) before,
  UCOS2_state_inv sg current -> 0 <= task_slot_addr sg slot < 4294967296 ->
  (task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) **
    UCOS2_fields_inv sg current ** frame) before ->
  exists after,
    task_tcb_init_link_fragment sg (task_slot_addr sg slot)
      (task_tcb_init_active_head sg current) before after /\
    (task_tcb_init_publication_fields_tail_storage sg args current slot image ** frame) after.
Proof.
  intros sg args current slot image frame before Hvalid Hpointer Hbefore.
  set (initialized := task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
    sg.(osKernelConfig).(cfgTaskProfile) args image).
  set (head := task_tcb_init_active_head sg current).
  assert (Hsplit : task_slot_storage_rep sg slot initialized ** UCOS2_fields_inv sg current ** frame |--
    task_slot_storage_rep sg slot initialized **
      (task_tcb_init_used_storage sg current ** sem_pend_task_fields_link_globals sg current ** frame)).
  { unfold UCOS2_fields_inv; Intros. rewrite sem_pend_task_fields_raw_split_publication.
    unfold sem_pend_task_fields_link_globals; entailer!. }
  pose proof (Hsplit before Hbefore) as Howned.
  assert (Hread_focus : forall contents,
    task_slot_storage_rep sg slot contents **
      (task_tcb_init_used_storage sg current ** sem_pend_task_fields_link_globals sg current ** frame) |--
    sg.(g_OSTCBList) # Ptr |-> head ** TT).
  { intros; unfold sem_pend_task_fields_link_globals, head; entailer!; intros ? ?; exact I. }
  pose proof (framed_pointer_store_load _ _ _ before (Hread_focus initialized before Howned)) as Hread.
  assert (Hstores : Forall (fun store =>
    In (fst store) (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)) /\
      0 <= snd store < task_tcb_init_field_bound (fst store))
    [(TCBCommonField TCBNext, head); (TCBCommonField TCBPrev, 0)]).
  { constructor; [split; [apply tcb_configured_common_field_in|exact (proj1 Hread)]|].
    constructor; [split; [apply tcb_configured_common_field_in|cbn; lia]|constructor]. }
  destruct (task_tcb_init_field_sequence_execution _ _ _ _ initialized _ before Hstores Howned)
    as [linked [Hlinks Hlinked]].
  assert (Hrun : kernel_heap_execution
    (pointer_store_writes (tcb_field_address (task_slot_addr sg slot) TCBNext) head ++
     pointer_store_writes (tcb_field_address (task_slot_addr sg slot) TCBPrev) 0) before linked).
  { cbn [task_tcb_init_field_sequence_writes flat_map task_tcb_init_field_writes
      task_tcb_init_field_address tcb_layout_field_width tcb_field_width fst snd] in Hlinks.
    rewrite app_nil_r in Hlinks; exact Hlinks. }
  change ((task_slot_storage_rep sg slot
      (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead) initialized) **
      (task_tcb_init_used_storage sg current ** sem_pend_task_fields_link_globals sg current ** frame)) linked) in Hlinked.
  pose proof (framed_pointer_store_load _ _ _ linked
    (Hread_focus _ linked Hlinked)) as Hguard.
  destruct (Z.eq_dec head 0) as [Hzero | Hnonzero].
  - exists linked; split.
    + exists linked; split; [exact Hread|]; split; [exact Hrun|]; split; [exact Hguard|].
      left; split; [exact Hzero|reflexivity].
    + assert (Hnone : current.(TskState).(tcbListHead) = None).
      { eapply task_tcb_init_active_head_zero__publication_and_returns; eassumption. }
      assert (Hmap : task_tcb_init_head_updated_map current slot = current.(TskState).(inUsedTaskStates)).
      { apply functional_extensionality; intro tid; unfold task_tcb_init_head_updated_map; rewrite Hnone.
        destruct (current.(TskState).(inUsedTaskStates) tid); reflexivity. }
      assert (Hmerge : task_slot_storage_rep sg slot
          (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead) initialized) **
          (task_tcb_init_used_storage sg current ** sem_pend_task_fields_link_globals sg current ** frame) |--
        task_tcb_init_publication_fields_tail_storage sg args current slot image ** frame).
      { unfold task_tcb_init_publication_fields_tail_storage, sem_pend_task_fields_link_globals,
          task_tcb_init_used_with_head_prev, task_tcb_init_used_storage.
        rewrite Hmap; unfold initialized; entailer!. }
      exact (Hmerge linked Hlinked).
  - set (node := task_slot_storage_rep sg slot
      (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead) initialized)).
    assert (Hfocus : node **
        (task_tcb_init_used_storage sg current ** sem_pend_task_fields_link_globals sg current ** frame) |--
      (tcb_field_address head TCBPrev) # Ptr |->_ **
        (task_tcb_init_used_without_head_prev sg current ** node **
         sem_pend_task_fields_link_globals sg current ** frame)).
    { sep_apply_l_atomic (task_tcb_init_used_split_head_prev__publication_and_returns sg current Hvalid Hnonzero).
      Intros previous; cbn [tcb_cell]. fold head.
      sep_apply_l_atomic (store_ptr_undef_store_ptr (tcb_field_address head TCBPrev) previous); entailer!. }
    destruct (framed_pointer_store_execution _ _ _ linked Hpointer (Hfocus linked Hlinked))
      as [after [Hwrite Hafter]].
    exists after; split.
    + exists linked; split; [exact Hread|]; split; [exact Hrun|]; split; [exact Hguard|].
      right; split; assumption.
    + assert (Hmerge : (tcb_field_address head TCBPrev) # Ptr |-> task_slot_addr sg slot **
          (task_tcb_init_used_without_head_prev sg current ** node **
           sem_pend_task_fields_link_globals sg current ** frame) |--
        task_tcb_init_publication_fields_tail_storage sg args current slot image ** frame).
      { change (tcb_cell (task_tcb_init_active_head sg current) TCBPrev (Some (task_slot_addr sg slot)) **
          (task_tcb_init_used_without_head_prev sg current ** node **
           sem_pend_task_fields_link_globals sg current ** frame) |--
          task_tcb_init_publication_fields_tail_storage sg args current slot image ** frame).
        sep_apply_l_atomic (task_tcb_init_used_merge_head_prev__publication_and_returns sg current slot).
        unfold task_tcb_init_publication_fields_tail_storage, node, initialized, sem_pend_task_fields_link_globals; entailer!. }
      exact (Hmerge after Hafter).
Qed.

Lemma sem_pend_task_fields_tcb_preparation_execution :
  forall sg args invocation origin acquired slot rest (frame : Assertion) before,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_parameters_in_range args ->
  acquired.(TskState).(unUsedTaskStates) = slot :: rest ->
  (UCOS2_fields_inv sg acquired ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation args invocation origin acquired slot rest image /\
    task_tcb_init_preparation_fragment sg args (task_slot_addr sg slot)
      (task_tcb_init_free_next sg rest) (task_tcb_init_active_head sg acquired) before after /\
    (task_tcb_init_publication_fields_tail_storage sg args
       (task_tcb_init_detached_state args invocation origin acquired slot rest image) slot image ** frame) after.
Proof.
  intros sg args invocation origin acquired slot rest frame before Hentry Hrange Hhead Hbefore.
  destruct (sem_pend_task_fields_free_pop_execution sg args invocation origin acquired slot rest frame before
    Hentry Hhead Hbefore) as [image [detached [Hdetach [Hpop Hdetached]]]].
  set (current := task_tcb_init_detached_state args invocation origin acquired slot rest image).
  assert (Hfocus : UCOS2_fields_inv sg current ** task_slot_storage_rep sg slot image ** frame |--
    task_slot_storage_rep sg slot image ** (UCOS2_fields_inv sg current ** frame)) by entailer!.
  destruct (task_tcb_init_private_initialization_execution sg args slot image _ detached Hrange
    (Hfocus detached Hdetached)) as [initialized [Hinit Hinitialized]].
  assert (Hlinks_input : task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) ** (UCOS2_fields_inv sg current ** frame) |--
    task_slot_storage_rep sg slot
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) args image) ** UCOS2_fields_inv sg current ** frame) by entailer!.
  pose proof (task_tcb_init_detach_preserves_validity sg args invocation origin acquired slot rest image Hentry Hdetach)
    as Hvalid.
  destruct (sem_pend_task_fields_links_execution sg args current slot image frame initialized Hvalid
    (proj1 (proj1 Hpop)) (Hlinks_input initialized Hinitialized)) as [after [Hlink Hafter]].
  exists image, after; split; [exact Hdetach|]; split; [|exact Hafter].
  exists detached, initialized, initialized.
  split; [exact Hpop|]; split; [exact Hinit|]; split; [|exact Hlink].
  exists initialized; split; (split; [constructor|split; reflexivity]).
Qed.

Lemma sem_pend_task_fields_reserve_execution :
  forall sg args name call initial (frame : Assertion) before,
  task_create_stack_entry sg args name call initial ->
  task_priority_in_range sg args.(createPriority) ->
  initial.(IntrState).(intNesting) = 0 ->
  initial.(TskState).(prioTbl) args.(createPriority) = PTFree ->
  (UCOS2_fields_inv sg initial ** frame) before ->
  exists after,
    task_create_stack_reserve_fragment sg args.(createPriority) before after /\
    (UCOS2_fields_inv sg (task_create_stack_reserved args call initial) ** frame) after.
Proof.
  intros sg args name call initial frame before Hentry Hpriority Hnest Hfree Hbefore.
  pose proof (proj1 Hentry) as Hvalid.
  assert (Hp : 0 <= args.(createPriority) < 64).
  { pose proof (proj1 (proj1 Hvalid)) as Hstable.
    unfold valid_stable_glob_vars in Hstable; unfold task_priority_in_range in Hpriority; intuition lia. }
  assert (Hnest_focus : UCOS2_fields_inv sg initial ** frame |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT).
  { unfold UCOS2_fields_inv; rewrite sem_pend_task_fields_raw_split_task_sched.
    unfold sem_pend_task_fields_frame, UCOS2_raw_rep_missing_task_storage_sched_flag,
      interrupt_inv, store_int_state; rewrite Hnest.
    entailer!; intros ? ?; exact I. }
  pose proof (framed_uchar_store_load _ _ _ before (Hnest_focus before Hbefore)) as Hnest_read.
  assert (Hsplit : UCOS2_fields_inv sg initial ** frame |--
    (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 0 **
    (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
     sem_pend_task_fields_priority_frame sg initial ** frame)).
  { sep_apply_l_atomic (sem_pend_task_fields_split_priority_cell sg initial args.(createPriority) Hp).
    Intros; rewrite Hfree; cbn [prio_tbl_entry_to_addr]; entailer!. }
  pose proof (Hsplit before Hbefore) as Howned.
  pose proof (framed_pointer_store_load _ _ _ before Howned) as Hpriority_read.
  assert (Herase : (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 0 **
      (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
       sem_pend_task_fields_priority_frame sg initial ** frame) |--
    (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |->_ **
      (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
       sem_pend_task_fields_priority_frame sg initial ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr
      (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) 0); entailer!. }
  destruct (framed_pointer_store_execution _ 1 _ before ltac:(lia) (Herase before Howned))
    as [after [Hwrite Hafter]].
  assert (Hguard : task_reserve_guard sg initial.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { destruct Hentry as [_ [Hactive [Hempty _]]].
    unfold task_reserve_guard, task_invocation_active in *; tauto. }
  assert (Hmerge : (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 1 **
      (store_prio_tbl_missing_i sg initial.(TskState).(prioTbl) args.(createPriority) **
       sem_pend_task_fields_priority_frame sg initial ** frame) |--
    UCOS2_fields_inv sg (task_create_stack_reserved args call initial) ** frame).
  { sep_apply_l_atomic (sem_pend_task_fields_merge_reserved_priority sg initial args.(createPriority)
      call.(os_sched_call_invocation) call.(os_sched_call_origin) Hvalid Hguard).
    unfold task_create_stack_reserved; entailer!. }
  exists after; split; [unfold task_create_stack_reserve_fragment; split; [exact Hnest_read|]; split; assumption|].
  exact (Hmerge after Hafter).
Qed.

Lemma sem_pend_task_fields_preparation_execution :
  forall sg input slot rest (frame : Assertion) before,
  task_create_stack_input_facts sg input ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (UCOS2_fields_inv sg input.(stack_input_state) **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image /\
    task_create_stack_preparation_fragment sg input slot rest before after /\
    (task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
       (task_create_stack_input_detached input slot rest image) slot image **
      task_stack_storage input.(stack_input_region)
        (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) ** frame) after.
Proof.
  intros sg input slot rest frame before [Hentry [Hbasic [Hpriority [Hbuffer Hparameters]]]] Hnest Hfree Hhead Hbefore.
  destruct Hbuffer as [Hlayout [Hlength [Hentry_pc [Hargument Hreturn]]]].
  set (buffer := task_stack_storage input.(stack_input_region)
    (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper))).
  assert (Hfocus : UCOS2_fields_inv sg input.(stack_input_state) ** buffer ** frame |--
    UCOS2_fields_inv sg input.(stack_input_state) ** (buffer ** frame)) by entailer!.
  destruct (sem_pend_task_fields_reserve_execution sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) _ before Hentry Hpriority Hnest Hfree
    (Hfocus before Hbefore)) as [reserved [Hreserve Hreserved]].
  set (acquired := task_create_stack_input_acquired input).
  assert (Hstack_focus : UCOS2_fields_inv sg acquired ** (buffer ** frame) |--
    buffer ** (UCOS2_fields_inv sg acquired ** frame)) by entailer!.
  destruct (task_create_stack_init_store_execution input.(stack_input_region) input.(stack_input_args)
    input.(stack_input_return) input.(stack_input_lower) input.(stack_input_old_frame) input.(stack_input_upper)
    _ reserved Hlayout Hlength Hentry_pc Hargument Hreturn (Hstack_focus reserved Hreserved))
    as [initialized [Hstack Hinitialized]].
  set (words := task_create_stack_image TaskStackNoVFP input.(stack_input_args) input.(stack_input_return)
    input.(stack_input_lower) input.(stack_input_upper)).
  assert (Hinit_focus : task_stack_storage input.(stack_input_region) words ** (UCOS2_fields_inv sg acquired ** frame) |--
    UCOS2_fields_inv sg acquired ** (task_stack_storage input.(stack_input_region) words ** frame)) by entailer!.
  pose proof (task_create_stack_reserved_entry sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) Hentry Hpriority Hfree) as Hacquired.
  destruct (sem_pend_task_fields_tcb_preparation_execution sg (task_create_stack_input_args input)
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    acquired slot rest _ initialized Hacquired Hparameters Hhead (Hinit_focus initialized Hinitialized))
    as [image [after [Hdetach [Hprepare Hafter]]]].
  exists image, after; split; [exact Hdetach|]; split.
  - exists reserved, initialized; split; [exact Hreserve|]; split; assumption.
  - assert (Hmerge : task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
        (task_create_stack_input_detached input slot rest image) slot image **
        (task_stack_storage input.(stack_input_region) words ** frame) |--
      task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
        (task_create_stack_input_detached input slot rest image) slot image **
        task_stack_storage input.(stack_input_region)
          (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) ** frame).
    { unfold words, task_create_stack_publication_words, task_create_stack_prepared_publication; cbn; entailer!. }
    exact (Hmerge after Hafter).
Qed.

(** The existing creation policy supplies emp only for an actual initial
    continuation (None); saved calls retain their supplied local owner. *)
Definition sem_pend_task_prepare_fields_input {external platform port}
  (abi : Armv7aContinuationABI external platform port) saved_local sg input state : Assertion :=
  coq_prop (state = input.(stack_input_state) /\ task_create_stack_input_facts sg input) &&
  (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg state **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper))).

Definition sem_pend_task_prepare_fields_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) saved_local sg
  (cut : KernelClientHeapCut TaskCreateStackInput) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_fields_publication abi (task_create_continuation_local saved_local) sg publication state
  | KernelClientHeapExtra input => sem_pend_task_prepare_fields_input abi saved_local sg input state
  end.

Lemma sem_pend_task_prepare_fields_assign : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg input,
  task_create_stack_input_facts sg input ->
  kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg input.(stack_input_state) **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) |--
  sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state).
Proof. intros; unfold sem_pend_task_prepare_fields_input; entailer!. Qed.

Lemma sem_pend_task_prepare_fields_publication : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg input slot rest (frame : Assertion) before,
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame) before ->
  exists image after,
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image /\
    task_create_stack_preparation_fragment sg input slot rest before after /\
    (kernel_client_continuation_fields_publication abi (task_create_continuation_local saved_local) sg
      (task_create_stack_prepared_publication input slot image)
      (task_create_stack_input_detached input slot rest image) ** frame) after.
Proof.
  intros external platform port abi saved_local sg input slot rest frame before Hnest Hfree Hhead Hbefore.
  set (local := task_create_continuation_local saved_local).
  assert (Hsplit : sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame |--
    coq_prop (task_create_stack_input_facts sg input /\ task_stack_live_coverage input.(stack_input_state).(TskState) None) &&
    (UCOS2_fields_inv sg input.(stack_input_state) **
      task_stack_storage input.(stack_input_region)
        (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper)) **
      (store_parked_continuations (kernel_saved_continuation_entry abi input.(stack_input_state).(TskState) local)
        input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold sem_pend_task_prepare_fields_input, kernel_client_continuation_fields_world, kernel_continuation_inv.
    rewrite kernel_program_fields_inv_split_unmap; unfold local; entailer!. }
  destruct (Hsplit before Hbefore) as [[Hfacts Hcoverage] Howned].
  destruct (sem_pend_task_fields_preparation_execution sg input slot rest _ before Hfacts Hnest Hfree Hhead Howned)
    as [image [after [Hdetach [Hsource Hafter]]]].
  destruct (task_create_stack_prepared_publication_input sg input slot rest image Hfacts Hfree Hdetach)
    as [Hvalid Hinput].
  assert (Hpointer : 0 <= task_slot_addr sg slot < 4294967296).
  { destruct Hsource as [reserved [initialized [_ [_ [detached [ready [hooked [Hpop _]]]]]]]].
    exact (proj1 (proj1 Hpop)). }
  assert (Hpriority : 0 <= (task_create_stack_input_args input).(initPrio) < 64).
  { exact (proj1 (proj2 (proj2 (proj2 (proj2 Hfacts))))). }
  assert (Hmerge : task_tcb_init_publication_fields_tail_storage sg (task_create_stack_input_args input)
      (task_create_stack_input_detached input slot rest image) slot image **
      task_stack_storage input.(stack_input_region)
        (task_create_stack_publication_words (task_create_stack_prepared_publication input slot image)) **
      (store_parked_continuations (kernel_saved_continuation_entry abi input.(stack_input_state).(TskState) local)
        input.(stack_input_state).(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) |--
    kernel_client_continuation_fields_publication abi local sg (task_create_stack_prepared_publication input slot image)
      (task_create_stack_input_detached input slot rest image) ** frame).
  { sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq external platform port abi
      input.(stack_input_state).(TskState) (task_create_stack_input_detached input slot rest image).(TskState)
      local input.(stack_input_state).(TskState).(parkedTaskStacks) eq_refl).
    assert (Hinitial : local (task_create_stack_publication_continuation
      (task_create_stack_prepared_publication input slot image)) = emp) by reflexivity.
    unfold kernel_client_continuation_fields_publication; rewrite Hinitial.
    cbn [task_create_stack_prepared_publication]; entailer!. }
  exists image, after; split; [exact Hdetach|]; split; [exact Hsource|exact (Hmerge after Hafter)].
Qed.

Lemma sem_pend_task_prepare_fields_extra : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg cut before next after state (frame : Assertion),
  task_create_stack_heap_step sg cut before next after ->
  (sem_pend_task_prepare_fields_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    task_create_stack_heap_effect sg cut state next returned /\
    (sem_pend_task_prepare_fields_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local sg cut before next after state frame Hsource Hpre.
  destruct Hsource as [input slot rest image before after Hnest Hfree Hhead Himage Hrun].
  assert (Hstate : state = input.(stack_input_state)).
  { assert (Hopen : sem_pend_task_prepare_fields_resources abi saved_local sg (KernelClientHeapExtra input) state ** frame |--
      coq_prop (state = input.(stack_input_state)) && TT).
    { cbn [sem_pend_task_prepare_fields_resources]; unfold sem_pend_task_prepare_fields_input; entailer!. }
    exact (proj1 (Hopen before Hpre)). }
  subst state.
  destruct (sem_pend_task_prepare_fields_publication external platform port abi saved_local sg input slot rest frame before
    Hnest Hfree Hhead Hpre) as [actual [produced [Hdetach [Hprepare Hpost]]]].
  assert (Hactual : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some actual)
    by exact (proj2 (proj2 (proj2 Hdetach))).
  assert (actual = image) by congruence; subst actual.
  assert (produced = after) by (eapply task_create_stack_preparation_final_eq; eassumption); subst produced.
  exists (task_create_stack_input_detached input slot rest image); split; [constructor|exact Hpost].
Qed.

Inductive sem_pend_task_prepare_source_client : KernelClientAction -> Prop :=
| SemPendTaskPrepareEnter : sem_pend_task_prepare_source_client (kernel_full_profile_cut_client KernelFullIntEnter)
| SemPendTaskPrepareExit : forall running,
    sem_pend_task_prepare_source_client (kernel_full_profile_cut_client (KernelFullIntExitCounter running))
| SemPendTaskPreparePublish : forall publication,
    sem_pend_task_prepare_source_client (task_create_stack_publication_client publication)
| SemPendTaskPrepareReserve : forall priority invocation origin,
    sem_pend_task_prepare_source_client (task_create_reserve_client priority invocation origin)
| SemPendTaskPrepareDetach : forall priority entry slot rest image,
    sem_pend_task_prepare_source_client (task_creation_client (TaskDetachFreeHead priority entry slot rest image)).

(** Only the actual caller/actor binding is recorded here. Extra itself is
    not redefined to promise a desired history or future valid states. *)
Definition sem_pend_task_prepare_observer_cut observer (cut : KernelClientHeapCut TaskCreateStackInput) : Prop :=
  match cut with
  | KernelClientHeapExtra input => input.(stack_input_call).(os_sched_call_invocation) <> observer
  | _ => kernel_client_heap_observer_cut observer cut
  end.

Lemma sem_pend_task_prepare_call_receipts : forall external sg input slot rest image,
  task_create_stack_input_facts sg input ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image ->
  sem_pend_source_state_facts sg input.(stack_input_state) /\
  tmr_task_source_call_receipt external
    (task_create_reserve_client input.(stack_input_args).(createPriority)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin))
    sg input.(stack_input_state) (task_create_stack_input_acquired input) /\
  sem_pend_source_state_facts sg (task_create_stack_input_acquired input) /\
  tmr_task_source_call_receipt external
    (task_creation_client (TaskDetachFreeHead (task_create_stack_input_args input).(initPrio)
      (task_tcb_init_initial_entry input.(stack_input_call).(os_sched_call_invocation)
        input.(stack_input_call).(os_sched_call_origin)) slot rest image))
    sg (task_create_stack_input_acquired input) (task_create_stack_input_detached input slot rest image).
Proof.
  intros external sg input slot rest image [Hentry [Hbasic [Hpriority [Hbuffer Hparameters]]]] Hfree Hhead Himage.
  assert (Hguard : task_reserve_guard sg input.(stack_input_state).(TskState)
    input.(stack_input_args).(createPriority) input.(stack_input_call).(os_sched_call_invocation)
    input.(stack_input_call).(os_sched_call_origin)).
  { destruct Hentry as [Hvalid [Hactive [Hempty Hname]]].
    unfold task_reserve_guard, task_invocation_active in *; tauto. }
  pose proof (task_create_stack_reserved_entry sg input.(stack_input_args) input.(stack_input_name)
    input.(stack_input_call) input.(stack_input_state) Hentry Hpriority Hfree) as Hacquired.
  assert (Hdetach : task_tcb_init_detach_observation (task_create_stack_input_args input)
    input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
    (task_create_stack_input_acquired input) slot rest image).
  { unfold task_tcb_init_detach_observation, task_detach_guard.
    split; [exact Hhead|]; split; [exact (proj1 (proj2 (proj2 (proj2 Hacquired))))|].
    split; [reflexivity|exact Himage]. }
  split; [apply sem_pend_source_state_facts_from_valid; exact (proj1 Hentry)|].
  split.
  - apply TmrTaskCallNontimer; [constructor|split; [exact Hguard|reflexivity]].
  - split; [apply sem_pend_source_state_facts_from_valid; exact (proj1 Hacquired)|].
    apply TmrTaskCallNontimer; [constructor|]. split; [exact Hdetach|split; [exact I|reflexivity]].
Qed.

Lemma sem_pend_task_prepare_client_receipt : forall external port sg observer origin input slot rest image,
  input.(stack_input_call).(os_sched_call_invocation) <> observer ->
  task_create_stack_input_facts sg input ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image ->
  exists trace : kernel_client_task_source_trace external port sem_pend_task_prepare_source_client
    sg observer None origin input.(stack_input_state) false origin (task_create_stack_input_detached input slot rest image),
    sem_pend_client_source_local_receipt external port sem_pend_task_prepare_source_client
      sg observer None origin input.(stack_input_state) false origin (task_create_stack_input_detached input slot rest image) trace.
Proof.
  intros external port sg observer origin input slot rest image Hforeign Hfacts Hfree Hhead Himage.
  destruct (sem_pend_task_prepare_call_receipts external sg input slot rest image Hfacts Hfree Hhead Himage)
    as [Hinitial [Hreserve [Hacquired Hdetach]]].
  destruct (sem_pend_dispatch_framed_step_receipt external port sem_pend_task_prepare_source_client sg observer None origin
    (task_create_reserve_client input.(stack_input_args).(createPriority)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin))
    input.(stack_input_state) (task_create_stack_input_acquired input)
    ltac:(constructor) ltac:(cbn [task_create_reserve_client kernel_client_actor]; congruence)
    ltac:(intros; discriminate) (tmr_task_source_call_receipt_step _ _ _ _ _ Hreserve)
    eq_refl Hreserve Hinitial) as [prefix Hprefix].
  destruct (sem_pend_dispatch_framed_step_receipt external port sem_pend_task_prepare_source_client sg observer None origin
    (task_creation_client (TaskDetachFreeHead (task_create_stack_input_args input).(initPrio)
      (task_tcb_init_initial_entry input.(stack_input_call).(os_sched_call_invocation)
        input.(stack_input_call).(os_sched_call_origin)) slot rest image))
    (task_create_stack_input_acquired input) (task_create_stack_input_detached input slot rest image)
    ltac:(constructor) ltac:(cbn [task_creation_client kernel_client_actor task_lifecycle_action_actor
      task_tcb_init_initial_entry creationInvocation]; congruence)
    ltac:(intros; discriminate) (tmr_task_source_call_receipt_step _ _ _ _ _ Hdetach)
    eq_refl Hdetach Hacquired) as [suffix Hsuffix].
  exact (sem_pend_dispatch_client_receipt_append external port sem_pend_task_prepare_source_client sg observer None
    origin input.(stack_input_state) false origin (task_create_stack_input_acquired input) prefix Hprefix
    false origin (task_create_stack_input_detached input slot rest image) suffix Hsuffix).
Qed.

Lemma sem_pend_task_prepare_fields_valid : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg cut state heap (frame : Assertion),
  (sem_pend_task_prepare_fields_resources abi saved_local sg cut state ** frame) heap -> UCOS2_state_inv sg state.
Proof.
  intros external platform port abi saved_local sg cut state heap frame Hpre.
  assert (Hopen : sem_pend_task_prepare_fields_resources abi saved_local sg cut state ** frame |--
    coq_prop (UCOS2_state_inv sg state) && TT).
  { destruct cut; cbn [sem_pend_task_prepare_fields_resources].
    - unfold kernel_client_continuation_fields_world, kernel_continuation_inv, kernel_program_fields_inv; entailer!.
    - unfold kernel_client_continuation_fields_publication; entailer!.
    - unfold sem_pend_task_prepare_fields_input, kernel_client_continuation_fields_world,
        kernel_continuation_inv, kernel_program_fields_inv; entailer!. }
  exact (proj1 (Hopen heap Hpre)).
Qed.

(** All actual Prepare executions produce these call receipts, without
    choosing or excluding an observer. The same physical factory supplies
    the image, endpoint and publication owner used by the dispatcher. *)
Lemma sem_pend_task_prepare_fields_produces_calls : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg input slot rest (frame : Assertion) before,
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame) before ->
  exists image after,
    task_create_stack_heap_step sg (KernelClientHeapExtra input) before
      (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image)) after /\
    task_tcb_init_detach_observation (task_create_stack_input_args input)
      input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin)
      (task_create_stack_input_acquired input) slot rest image /\
    tmr_task_source_call_receipt external
      (task_create_reserve_client input.(stack_input_args).(createPriority)
        input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin))
      sg input.(stack_input_state) (task_create_stack_input_acquired input) /\
    tmr_task_source_call_receipt external
      (task_creation_client (TaskDetachFreeHead (task_create_stack_input_args input).(initPrio)
        (task_tcb_init_initial_entry input.(stack_input_call).(os_sched_call_invocation)
          input.(stack_input_call).(os_sched_call_origin)) slot rest image))
      sg (task_create_stack_input_acquired input) (task_create_stack_input_detached input slot rest image) /\
    (kernel_client_continuation_fields_publication abi (task_create_continuation_local saved_local) sg
      (task_create_stack_prepared_publication input slot image)
      (task_create_stack_input_detached input slot rest image) ** frame) after.
Proof.
  intros external platform port abi saved_local sg input slot rest frame before Hnest Hfree Hhead Hpre.
  assert (Hfacts : task_create_stack_input_facts sg input).
  { destruct Hpre as [owned [rest_heap [Hjoin [[[Hstate Hfacts] Howned] Hframe]]]]; exact Hfacts. }
  destruct (sem_pend_task_prepare_fields_publication external platform port abi saved_local sg input slot rest frame before
    Hnest Hfree Hhead Hpre) as [image [after [Hdetach [Hrun Hpost]]]].
  assert (Himage : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image)
    by exact (proj2 (proj2 (proj2 Hdetach))).
  destruct (sem_pend_task_prepare_call_receipts external sg input slot rest image Hfacts Hfree Hhead Himage)
    as [Hinitial [Hreserve [Hacquired Hcall]]].
  exists image, after; split; [econstructor; eassumption|].
  split; [exact Hdetach|]. split; [exact Hreserve|]. split; assumption.
Qed.

Lemma sem_pend_task_prepare_builtin_receipt : forall external port sg observer cut state next returned origin,
  sem_pend_task_prepare_observer_cut observer cut -> UCOS2_state_inv sg state ->
  @kernel_client_heap_state_step TaskCreateStackInput (fun _ _ _ _ _ => False) sg cut state next returned ->
  sem_pend_task_prepare_observer_cut observer next /\
  exists trace : kernel_client_task_source_trace external port sem_pend_task_prepare_source_client
    sg observer None origin state false origin returned,
    sem_pend_client_source_local_receipt external port sem_pend_task_prepare_source_client
      sg observer None origin state false origin returned trace.
Proof.
  intros * Hobserver Hvalid Hstep.
  pose proof (sem_pend_source_state_facts_from_valid sg state Hvalid) as Hfacts.
  destruct Hstep.
  - split; [exact I|].
    eapply sem_pend_dispatch_framed_step_receipt with (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + exact Hfacts.
  - split; [exact I|].
    eapply sem_pend_dispatch_framed_step_receipt with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + constructor.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + apply TmrTaskCallProfile; split; [exact I|reflexivity].
    + exact Hfacts.
  - split; [exact I|].
    eapply sem_pend_dispatch_framed_step_receipt with (action := task_create_stack_publication_client publication).
    + constructor.
    + cbn [task_create_stack_publication_client kernel_client_actor].
      cbn [sem_pend_task_prepare_observer_cut kernel_client_heap_observer_cut] in Hobserver; congruence.
    + intros; discriminate.
    + split; [exact H|reflexivity].
    + apply task_create_stack_publication_current_pointer_eq.
    + apply TmrTaskCallNontimer; [constructor|split; [exact H|reflexivity]].
    + exact Hfacts.
  - contradiction.
Qed.

Lemma sem_pend_task_prepare_fields_step_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg observer cut before next after state origin (frame : Assertion),
  sem_pend_task_prepare_observer_cut observer cut ->
  kernel_client_heap_step task_create_stack_heap_step sg cut before next after ->
  (sem_pend_task_prepare_fields_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_step task_create_stack_heap_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port sem_pend_task_prepare_source_client
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port sem_pend_task_prepare_source_client
        sg observer None origin state false origin returned trace) /\
    sem_pend_task_prepare_observer_cut observer next /\
    (sem_pend_task_prepare_fields_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local sg observer cut before next after state origin frame Hobserver Hstep Hpre.
  pose proof (sem_pend_task_prepare_fields_valid external platform port abi saved_local sg cut state before frame Hpre) as Hvalid.
  destruct Hstep.
  - exists (os_int_enter_state state); split; [constructor|].
    destruct (sem_pend_task_prepare_builtin_receipt external port sg observer KernelClientHeapClosed state
      KernelClientHeapClosed (os_int_enter_state state) origin Hobserver Hvalid ltac:(constructor)) as [Hnext Hreceipt].
    split; [exact Hreceipt|]. split; [exact Hnext|].
    eapply kernel_client_int_enter_continuation_fields_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    destruct (sem_pend_task_prepare_builtin_receipt external port sg observer KernelClientHeapClosed state
      KernelClientHeapClosed (os_int_exit_counter_state state.(SchedState).(isRunning) state)
      origin Hobserver Hvalid ltac:(constructor)) as [Hnext Hreceipt].
    split; [exact Hreceipt|]. split; [exact Hnext|].
    eapply kernel_client_int_exit_continuation_fields_resources; eassumption.
  - assert (Hbuiltin : @kernel_client_heap_step TaskCreateStackInput (fun _ _ _ _ _ => False) sg
      (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after) by (constructor; exact H).
    destruct (kernel_client_builtin_fields_resource_guarantee_proof external platform port TaskCreateStackInput abi
      (task_create_continuation_local saved_local) sg (KernelClientHeapTaskPublication publication) before
      KernelClientHeapClosed after state frame Hbuiltin Hpre) as [returned [Heffect Hpost]].
    destruct (sem_pend_task_prepare_builtin_receipt external port sg observer (KernelClientHeapTaskPublication publication)
      state KernelClientHeapClosed returned origin Hobserver Hvalid Heffect) as [Hnext Hreceipt].
    exists returned; split.
    + inversion Heffect; subst; [constructor; assumption|contradiction].
    + split; [exact Hreceipt|]. split; assumption.
  - destruct H as [input slot rest image before after Hnest Hfree Hhead Himage Hrun].
    assert (Hbinding : state = input.(stack_input_state) /\ task_create_stack_input_facts sg input).
    { destruct Hpre as [owned [rest_heap [Hjoin [[Hbinding Howned] Hframe]]]]; exact Hbinding. }
    destruct Hbinding as [-> Hfacts].
    destruct (sem_pend_task_prepare_fields_publication external platform port abi saved_local sg input slot rest frame before
      Hnest Hfree Hhead Hpre) as [actual [produced [Hdetach [Hprepare Hpost]]]].
    assert (Hactual : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some actual)
      by exact (proj2 (proj2 (proj2 Hdetach))).
    assert (actual = image) by congruence; subst actual.
    assert (produced = after) by (eapply task_create_stack_preparation_final_eq; eassumption); subst produced.
    exists (task_create_stack_input_detached input slot rest image); split; [constructor; constructor|].
    split.
    + eapply sem_pend_task_prepare_client_receipt; eassumption.
    + split; [exact Hobserver|exact Hpost].
Qed.

Lemma sem_pend_task_prepare_fields_trace_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg observer cut before next after (frame : Assertion),
  kernel_client_heap_trace task_create_stack_heap_step sg cut before next after ->
  forall state origin,
  sem_pend_task_prepare_observer_cut observer cut ->
  (sem_pend_task_prepare_fields_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace task_create_stack_heap_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port sem_pend_task_prepare_source_client
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port sem_pend_task_prepare_source_client
        sg observer None origin state false origin returned trace) /\
    sem_pend_task_prepare_observer_cut observer next /\
    (sem_pend_task_prepare_fields_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local sg observer cut before next after frame Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state; split; [constructor|]. split.
    + exists (@KernelClientTaskSourceNil external port sem_pend_task_prepare_source_client sg observer None origin state); constructor.
    + split; assumption.
  - destruct (sem_pend_task_prepare_fields_step_receipt external platform port abi saved_local sg observer
      cut before middle_cut middle state origin frame Hobserver H Hpre)
      as [middle_state [Hstep [[head Hhead] [Hmiddle_observer Hmiddle]]]].
    destruct (IHHtrace middle_state origin Hmiddle_observer Hmiddle)
      as [returned [Htail [[tail Htail_receipt] [Hfinal Hpost]]]].
    exists returned; split; [econstructor; eassumption|]. split; [|split; assumption].
    exact (sem_pend_dispatch_client_receipt_append external port sem_pend_task_prepare_source_client
      sg observer None origin state false origin middle_state head Hhead false origin returned tail Htail_receipt).
Qed.

Lemma sem_pend_task_publication_fields_produces : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg publication state (frame : Assertion) before,
  (kernel_client_continuation_fields_publication abi local sg publication state ** frame) before ->
  exists after,
    task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before after /\
    tmr_task_source_call_receipt external (task_create_stack_publication_client publication) sg state
      (task_create_stack_publication_state sg publication state) /\
    (kernel_client_continuation_fields_world abi local sg
      (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi local sg publication state frame before Hpre.
  assert (Hsplit : kernel_client_continuation_fields_publication abi local sg publication state ** frame |--
    coq_prop (UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) None /\
      task_create_stack_publication_input sg publication state /\
      0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
      0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
    (task_tcb_init_publication_fields_tail_storage sg (task_create_stack_publication_args publication)
      state publication.(stack_publication_slot) publication.(stack_publication_image) **
     (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
      local (task_create_stack_publication_continuation publication) **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold kernel_client_continuation_fields_publication; entailer!. }
  destruct (Hsplit before Hpre) as [[Hvalid [Hcoverage [Hinput [Hpriority Hpointer]]]] Howned].
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
  destruct (task_tcb_init_publication_tail_fields_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid Hbinding Hpriority Hpointer Howned)
    as [after [Hrun Hpost]].
  destruct (kernel_task_publication_continuation_fields_source external platform port abi sg publication state local None
    frame before after Hvalid Hinput Hcoverage Hpriority Hpointer Howned Hrun) as [Hstep [Hcovered Hafter]].
  exists after; split; [exact Hrun|]. split.
  - apply TmrTaskCallNontimer; [constructor|exact Hstep].
  - assert (Hclose : kernel_program_fields_inv sg (task_create_stack_publication_state sg publication state) **
      store_parked_continuations (kernel_saved_continuation_entry abi
        (task_create_stack_publication_state sg publication state).(TskState) local)
        (task_create_stack_publication_state sg publication state).(TskState).(parkedTaskStacks) ** frame |--
      kernel_client_continuation_fields_world abi local sg (task_create_stack_publication_state sg publication state) ** frame).
    { unfold kernel_client_continuation_fields_world, kernel_continuation_inv; entailer!. }
    exact (Hclose after Hafter).
Qed.

(** This actual factory has no observer restriction. Its three real
    lifecycle calls, original heap/state traces and final strong fields
    owner are returned together, preserving the whole Prepare domain. *)
Lemma sem_pend_task_prepare_fields_produces_closed : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg input slot rest (frame : Assertion) before,
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame) before ->
  exists image after,
    let current := task_create_stack_input_detached input slot rest image in
    let publication := task_create_stack_prepared_publication input slot image in
    let published := task_create_stack_publication_state sg publication current in
    kernel_client_heap_trace task_create_stack_heap_step sg
      (KernelClientHeapExtra input) before KernelClientHeapClosed after /\
    kernel_client_heap_state_trace task_create_stack_heap_effect sg
      (KernelClientHeapExtra input) input.(stack_input_state) KernelClientHeapClosed published /\
    tmr_task_source_call_receipt external
      (task_create_reserve_client input.(stack_input_args).(createPriority)
        input.(stack_input_call).(os_sched_call_invocation) input.(stack_input_call).(os_sched_call_origin))
      sg input.(stack_input_state) (task_create_stack_input_acquired input) /\
    tmr_task_source_call_receipt external
      (task_creation_client (TaskDetachFreeHead (task_create_stack_input_args input).(initPrio)
        (task_tcb_init_initial_entry input.(stack_input_call).(os_sched_call_invocation)
          input.(stack_input_call).(os_sched_call_origin)) slot rest image))
      sg (task_create_stack_input_acquired input) current /\
    tmr_task_source_call_receipt external (task_create_stack_publication_client publication) sg current published /\
    (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg published ** frame) after.
Proof.
  intros external platform port abi saved_local sg input slot rest frame before Hnest Hfree Hhead Hpre.
  destruct (sem_pend_task_prepare_fields_produces_calls external platform port abi saved_local sg input slot rest frame before
    Hnest Hfree Hhead Hpre) as [image [prepared [Hprepare [Hdetach [Hreserve [Hcall Howned]]]]]].
  destruct (sem_pend_task_publication_fields_produces external platform port abi
    (task_create_continuation_local saved_local) sg (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image) frame prepared Howned)
    as [after [Hpublish [Hpublication Hpost]]].
  pose proof (tmr_task_source_call_receipt_step _ _ _ _ _ Hpublication) as Hstep.
  exists image, after; cbv zeta.
  split.
  - eapply KernelClientHeapTraceCons; [apply KernelClientHeapRegistered; exact Hprepare|].
    eapply KernelClientHeapTraceCons; [apply KernelClientHeapPublish; exact Hpublish|constructor].
  - split.
    + eapply KernelClientHeapStateTraceCons; [apply KernelClientHeapExtraState; constructor|].
      eapply KernelClientHeapStateTraceCons; [apply KernelClientHeapPublishState; exact (proj1 Hstep)|constructor].
    + split; [exact Hreserve|]. split; [exact Hcall|]. split; assumption.
Qed.
