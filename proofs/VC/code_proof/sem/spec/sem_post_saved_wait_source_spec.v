Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_wake_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_saved_post_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_wake_selection_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wait_history_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation KernelHeapStorage Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The SemPost OS_EventTaskRdy instance: NULL message, SEM mask 1,
    PendOK result 0. Reuse the existing field-store, ready-bitmap and
    waiter-remove source proofs, whose statements are independent of the
    original Mutex caller. The read-only selector sees the identical
    storage precondition; its mask/result bounds have no heap contents. *)
Definition sem_post_waiter_prefix_execution (pointer : Z) (before after : model) : Prop :=
  exists delayed messaged status_written bits,
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBDly) 0) before delayed /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address pointer TCBMsg) 0) delayed messaged /\
    uchar_load (tcb_field_address pointer TCBStat) bits messaged /\
    kernel_heap_execution [(tcb_field_address pointer TCBStat, event_task_remove_cleared bits 1)]
      messaged status_written /\
    kernel_heap_execution [(tcb_field_address pointer TCBStatPend, 0)] status_written after.

Lemma sem_post_waiter_prefix_resources : forall sg task pointer before after (frame : Assertion),
  (tcb64_storage_rep pointer (task_tcb64_image sg task) ** frame) before ->
  sem_post_waiter_prefix_execution pointer before after ->
  (tcb64_storage_rep pointer (event_task_rdy_before_remove_image sg task 0 1 0) ** frame) after.
Proof.
  intros sg task pointer before after frame Hpre
    (delayed & messaged & status_written & bits & Hdly & Hmsg & Hbits & Hstat & Hpend).
  pose proof (mutex_del_wake_tcb_store pointer (task_tcb64_image sg task) TCBDly 0 before delayed frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hpre Hdly) as Hd.
  pose proof (mutex_del_wake_tcb_store pointer (tcb_write (task_tcb64_image sg task) TCBDly (Some 0))
    TCBMsg 0 delayed messaged frame ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hd Hmsg) as Hm.
  pose proof (mutex_del_wake_tcb_byte_load pointer
    (tcb_write (tcb_write (task_tcb64_image sg task) TCBDly (Some 0)) TCBMsg (Some 0))
    TCBStat (encode_task_status task.(stat)) messaged frame ltac:(cbn; auto) eq_refl Hm) as Hactual.
  assert (bits = encode_task_status task.(stat)) by (eapply uchar_load_deterministic; eassumption); subst bits.
  assert (Eclear : event_task_remove_cleared (encode_task_status task.(stat)) 1 =
    task_status_clear_wait (encode_task_status task.(stat)) 1).
  { symmetry; apply task_status_clear_wait_byte_complement; lia. }
  rewrite Eclear in Hstat.
  pose proof (mutex_del_wake_tcb_store pointer
    (tcb_write (tcb_write (task_tcb64_image sg task) TCBDly (Some 0)) TCBMsg (Some 0))
    TCBStat (task_status_clear_wait (encode_task_status task.(stat)) 1) messaged status_written frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    (task_status_clear_wait_in_range _ _ (proj1 Hactual)) Hm Hstat) as Hs.
  exact (mutex_del_wake_tcb_store pointer _ TCBStatPend 0 status_written after frame
    ltac:(unfold mutex_del_wake_tcb_writable; cbn; auto)
    ltac:(unfold mutex_del_wake_tcb_value_in_range; cbn; lia) Hs Hpend).
Qed.

Definition sem_post_waiter_execution (sg : StableGlobVars) (pe returned : Z)
  (before after : model) : Prop :=
  exists pointer row prefixed readied,
    mutex_del_wake_selection_execution sg pe pointer row returned before /\
    sem_post_waiter_prefix_execution pointer before prefixed /\
    mutex_del_waiter_ready_execution pointer sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) row prefixed readied /\
    mutex_del_waiter_remove_execution pointer (pe + OSEventGrp_off) (pe + OSEventTbl_off) readied after.

Lemma sem_post_waiter_source_post : forall sg tasks eid event tid task group rows returned
  before after (frame : Assertion),
  (event_task_rdy_pre sg tasks eid event tid task 1 0 group rows ** frame) before ->
  sem_post_waiter_execution sg (event_addr sg eid) returned before after ->
  (event_task_rdy_post sg tasks eid event tid task 0 1 0 group rows returned ** frame) after.
Proof.
  intros sg tasks eid event tid task group rows returned before after frame Hpre
    (pointer & row & prefixed & readied & Hselection & Hprefix & Hready & Hremove).
  assert (Hselection_pre : (event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame) before).
  { assert (Hbounds : event_task_rdy_pre sg tasks eid event tid task 1 0 group rows ** frame |--
      event_task_rdy_pre sg tasks eid event tid task 16 2 group rows ** frame).
    { unfold event_task_rdy_pre; entailer!; lia. }
    exact (Hbounds before Hpre). }
  destruct (mutex_del_wake_selection_resources sg tasks eid event tid task group rows pointer row returned
    before frame Hselection_pre Hselection) as [Epointer [Erow Ereturned]].
  subst pointer row returned.
  set (image := event_task_rdy_before_remove_image sg task 0 1 0).
  set (bits := task_status_clear_wait (encode_task_status task.(stat)) 1).
  set (ready_group := event_task_rdy_ready_group bits group (tcb_bit_y_of_prio task.(curPrio))).
  set (ready_rows := event_task_rdy_ready_rows bits (tcb_y_of_prio task.(curPrio))
    (tcb_bit_x_of_prio task.(curPrio)) rows).
  set (prefix_frame := event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) ** unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
    sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows ** frame).
  assert (Hopen : event_task_rdy_pre sg tasks eid event tid task 1 0 group rows ** frame |--
    coq_prop (event_task_rdy_entry sg tasks eid event tid task) &&
    (tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg task) ** prefix_frame)).
  { unfold event_task_rdy_pre, prefix_frame; entailer!; tauto. }
  destruct (Hopen before Hpre) as [Hentry Howned].
  pose proof (sem_post_waiter_prefix_resources sg task (task_slot_addr sg tid) before prefixed
    prefix_frame Howned Hprefix) as Hprefixed.
  destruct (event_task_rdy_selection sg tasks eid event tid task Hentry)
    as [Hpriority [Htable [Hvalid [Hrange _]]]].
  pose proof (proj1 (proj2 (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    task.(curPrio) Hrange))) as Hrow.
  set (ready_frame := event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) ** unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) ** frame).
  assert (Hready_order : tcb64_storage_rep (task_slot_addr sg tid) image ** prefix_frame |--
    tcb64_storage_rep (task_slot_addr sg tid) image ** sg.(g_OSRdyGrp) # UChar |-> group **
    UCharArray.full sg.(g_OSRdyTbl) 8 rows ** ready_frame)
    by (unfold prefix_frame, ready_frame; entailer!).
  pose proof (mutex_del_waiter_ready_resources (task_slot_addr sg tid) image sg.(g_OSRdyGrp) sg.(g_OSRdyTbl)
    (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
    bits group rows prefixed readied ready_frame Hrow eq_refl eq_refl eq_refl
    (Hready_order prefixed Hprefixed) Hready) as Hreadied.
  set (remove_frame := unmap_table_rep sg ** store_prio_tbl sg tasks.(prioTbl) **
    sg.(g_OSRdyGrp) # UChar |-> ready_group ** UCharArray.full sg.(g_OSRdyTbl) 8 ready_rows ** frame).
  set (remove_rest :=
    event_task_remove_tcb_frame (task_slot_addr sg tid) image **
    event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_image sg tasks event) (tcb_y_of_prio task.(curPrio)) ** remove_frame).
  set (remove_pre := event_task_remove_pre (task_slot_addr sg tid) (event_addr sg eid + 10)
    (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
    (tcb_bit_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    (encode_event_wait_grp event.(waitList) tasks)).
  assert (Hremove_open : tcb64_storage_rep (task_slot_addr sg tid) image **
      sg.(g_OSRdyGrp) # UChar |-> ready_group ** UCharArray.full sg.(g_OSRdyTbl) 8 ready_rows ** ready_frame |--
    remove_pre ** remove_rest).
  { eapply derivable1_trans with (y :=
      (tcb64_storage_rep (task_slot_addr sg tid) image **
       event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid) (event_image sg tasks event)) **
      remove_frame).
    { unfold ready_frame, remove_frame; entailer!. }
    unfold remove_pre, remove_rest.
    sep_apply_l_atomic (event_task_remove_storage_split sg.(osKernelConfig).(cfgEventNames)
      (task_slot_addr sg tid) (event_addr sg eid) image (event_image sg tasks event)
      (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) Hrow eq_refl eq_refl eq_refl
      (event_table_image_eq sg tasks event _ Hrow) eq_refl); entailer!. }
  pose proof (mutex_del_waiter_remove_resources (task_slot_addr sg tid) (event_addr sg eid + 10)
    (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
    (tcb_bit_y_of_prio task.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
    (encode_event_wait_grp event.(waitList) tasks) readied after remove_rest
    (Hremove_open readied Hreadied) Hremove) as Hremoved.
  destruct Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hconsistency [Hhead Hlookup]]]]]].
  assert (Hunique : task_priority_unique tasks) by (unfold task_in_range in Htasks; tauto).
  assert (Hcanonical : event_waitList_canonical sg tasks event.(waitList)) by (exact (proj1 Hconsistency)).
  assert (Hclose : event_task_remove_post (task_slot_addr sg tid) (event_addr sg eid + 10)
      (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
      (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) ** remove_rest |--
    event_task_rdy_post sg tasks eid event tid task 0 1 0 group rows task.(curPrio) ** frame).
  { unfold remove_rest.
    eapply derivable1_trans with (y :=
      (event_task_remove_post (task_slot_addr sg tid) (event_addr sg eid + 10)
        (event_addr sg eid + 11) (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio))
        (tcb_bit_y_of_prio task.(curPrio))
        (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
        (encode_event_wait_grp event.(waitList) tasks) **
       event_task_remove_tcb_frame (task_slot_addr sg tid) image **
       event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
         (event_image sg tasks event) (tcb_y_of_prio task.(curPrio))) ** remove_frame).
    { entailer!. }
    unfold remove_frame, event_task_rdy_post.
    sep_apply_l_atomic (event_task_remove_storage_merge_updated sg.(osKernelConfig).(cfgEventNames)
      (task_slot_addr sg tid) (event_addr sg eid) image (event_image sg tasks event)
      (tcb_y_of_prio task.(curPrio)) (tcb_bit_x_of_prio task.(curPrio)) (tcb_bit_y_of_prio task.(curPrio))
      (encode_event_wait_tbl_at_or event.(waitList) tasks (tcb_y_of_prio task.(curPrio)))
      (encode_event_wait_grp event.(waitList) tasks) eq_refl eq_refl eq_refl eq_refl).
    unfold tcb_bit_x_of_prio, tcb_bit_y_of_prio, tcb_x_of_prio, tcb_y_of_prio.
    rewrite <- (event_remove_waiter_image_eq sg tasks event tid task Hsg Hunique Hcanonical Hvalid Hlookup).
    unfold image, ready_group, ready_rows, bits, event_task_rdy_task_image; entailer!; lia. }
  exact (Hclose after Hremoved).
Qed.

(** Registered OSSemPost entry through its literal type read, first Save,
    group read and actual EventTaskRdy execution. The arbitrary frame
    retains the waiter's exact saved-entry map, rather than a weakened
    projection. The source relation above has only actual loads/stores;
    its desired resource postcondition is derived here. *)
Lemma sem_post_saved_wait_entry_source : forall external platform critical arch
  (save : Armv7aSaveSuffixABI external platform critical arch)
  sg entry context mask eid event tid old priority before registers final_registers acquired saved_heap
  woken_heap (frame : Assertion),
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_SEM -> event_addr sg eid <> 0 ->
  sem_post_group entry event <> 0 -> event_object_layout_prop sg eid ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  (kernel_call_execution_owned external platform context mask ** UCOS2_inv sg entry **
    unmap_table_rep sg ** frame) before ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry before
    final_registers acquired saved_heap ->
  sem_post_waiter_execution sg (event_addr sg eid) priority saved_heap woken_heap ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 before /\
  kernel_call_save_uninterrupted_execution arch registers entry before final_registers acquired saved_heap /\
  acquired = entry /\
  uchar_load (event_addr sg eid + OSEventGrp_off) (sem_post_group entry event) saved_heap /\
  (critical_region_masked platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
   os_sched_context_resources external context **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid ** frame) woken_heap.
Proof.
  intros external platform critical arch save sg entry context mask eid event tid old priority before
    registers final_registers acquired saved_heap woken_heap frame Hvalid Hlookup Htype Hnonnull
    Hgroup Hlayout Hentry Hpre Hreturn Hcpsr Hmask Hsave Hwake.
  assert (Htype_read : uchar_load (event_addr sg eid + OSEventType_off) 3 before).
  { match type of Hpre with ?P before => assert (Hcell : P |--
      (event_addr sg eid + OSEventType_off) # UChar |-> 3 ** TT) end.
    { sep_apply_l_atomic (sem_post_field_split_full sg entry eid event EventTypeField
        Hlookup ltac:(cbn; tauto)).
      cbn [event_cell event_image event_field_offset]; rewrite Htype; cbn [encode_event_type].
      unfold OSEventType_off; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hcell before Hpre). }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  assert (Hopen : (kernel_call_execution_owned external platform context
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (UCOS2_inv sg entry ** unmap_table_rep sg ** frame)) before).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    match type of Hpre with ?P before => match goal with |- ?Q before =>
      assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder before Hpre). }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch save sg context
    (kernel_save_read_cpsr registers) entry before final_registers acquired saved_heap _
    Hsaved Hopen Hsave) as [Hacquired [Hmemory [Hlr [Hr0 Hafter]]]].
  assert (Hsource : kernel_call_save_uninterrupted_execution arch registers entry before
    final_registers acquired saved_heap).
  { unfold kernel_call_save_uninterrupted_execution; econstructor.
    - constructor; [exact Hreturn|reflexivity].
    - exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Htype_read|]. split; [exact Hsource|]. split; [exact Hacquired|].
  assert (Hgroup_read : uchar_load (event_addr sg eid + OSEventGrp_off)
    (sem_post_group entry event) saved_heap).
  { match type of Hafter with ?P saved_heap => assert (Hcell : P |--
      (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group entry event ** TT) end.
    { sep_apply_l_atomic (sem_post_field_split_full sg entry eid event EventGrpField
        Hlookup ltac:(cbn; tauto)).
      cbn [event_cell event_image event_field_offset]; unfold sem_post_group, OSEventGrp_off.
      entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hcell saved_heap Hafter). }
  split; [exact Hgroup_read|].
  set (retained := critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
    os_sched_context_resources external context ** sem_post_wake_frame sg entry eid tid ** frame).
  assert (Hwake_pre : (event_task_rdy_pre sg entry.(TskState) eid event tid old 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) ** retained) saved_heap).
  { match type of Hafter with ?P saved_heap => match goal with |- ?Q saved_heap =>
      assert (Hsplit : P |-- Q) end end.
    { eapply derivable1_trans with (y := (UCOS2_inv sg entry ** unmap_table_rep sg) **
        (critical_region_masked platform critical sg context.(os_sched_call_invocation)
          context.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
         os_sched_context_resources external context ** frame)); [entailer!|].
      sep_apply_l_atomic (sem_post_wake_split_full sg entry eid event Hvalid Hlookup Htype Hgroup Hlayout).
      Intros actual_tid actual_old.
      assert (Hactual : event_task_rdy_entry sg entry.(TskState) eid event actual_tid actual_old) by tauto.
      pose proof Hentry as (_ & _ & _ & _ & _ & Hhead & Hold).
      pose proof Hactual as (_ & _ & _ & _ & _ & Hhead' & Hold').
      assert (actual_tid = tid) by congruence; subst actual_tid.
      assert (actual_old = old) by congruence; subst actual_old.
      unfold retained; entailer!. }
    exact (Hsplit saved_heap Hafter). }
  pose proof (sem_post_waiter_source_post sg entry.(TskState) eid event tid old
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority
    saved_heap woken_heap retained Hwake_pre Hwake) as Hpost.
  match type of Hpost with ?P woken_heap => match goal with |- ?Q woken_heap =>
    assert (Horder : P |-- Q) by (unfold retained; entailer!) end end.
  exact (Horder woken_heap Hpost).
Qed.

(** Direct consumer of the prefix above and the already checked exact
    saved-call public return. No EventTaskRdy post-state premise survives:
    the actual SemPost loads/Save and same-heap EventTaskRdy execution
    establish it. Original wait history, exact parked owner and poster
    retained pair are unchanged. The source family remains highest
    unsuspended / uninterrupted / no-write-hook. *)
Lemma sem_post_saved_wait_public_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg entry eid event tid old priority context node call saved acquired descriptor focus
  old_sp cpsr values lr prefix suffix first old_words publication before (frame : Assertion)
  poster_mask post_before post_registers post_final_registers post_acquired post_saved_heap
  cursor restore_written middle final_cursor released registers final_registers next_acquired saved_heap
  public_call mask initial observed pevent timeout waiting perr X,
  let poster_saved := post_final_registers.(kernel_save_r0) in
  let abi := environment.(task_stack_call_continuations) in
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp selected context.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments call.(os_sched_call_stack) updated in
  let returned := kernel_selected_call descriptor current in
  let retained := interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
    critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint ** frame in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  interrupt_saved_value mask saved ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (Some environment) critical sg public_call pevent timeout))
      sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting call entry ->
  critical.(critical_region_clients) (sem_pend_post_source_client context.(os_sched_call_invocation) eid) ->
  context.(os_sched_call_invocation) <> public_call.(os_sched_call_invocation) ->
  sem_post_group entry event <> 0 ->
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  task_status_is_suspended
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
  (forall slot ready, In slot entry.(SchedState).(readyList) ->
    entry.(TskState).(inUsedTaskStates) slot = Some ready -> old.(curPrio) < ready.(curPrio)) ->
  sched_current_ready_at entry.(TskState) entry.(SchedState) context.(os_sched_call_stack).(stackLeaseSlot) node ->
  entry.(IntrState).(intNesting) = 0 -> entry.(IntrState).(lockNesting) = 0 ->
  tid = call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  node.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  (task_stack_key context.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus context lr lr) ->
  context.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication
    context.(os_sched_call_stack).(stackLeaseSlot) context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) context poster_mask **
   UCOS2_inv sg entry ** unmap_table_rep sg **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
     entry.(TskState).(parkedTaskStacks) ** (perr # UChar |->_ ** frame)) post_before ->
  post_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr post_registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask post_registers.(kernel_save_cpsr) = poster_mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr post_registers) entry post_before
    post_final_registers post_acquired post_saved_heap ->
  sem_post_waiter_execution sg (event_addr sg eid) priority post_saved_heap before ->
  cursor.(kernel_restore_r0) = poster_saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before restore_written middle ->
  armv7a_restore_suffix_transition restore restore_written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask poster_saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers next_acquired saved_heap ->
  uchar_load (event_addr sg eid + OSEventType_off) 3 post_before /\
  kernel_call_save_uninterrupted_execution arch post_registers entry post_before
    post_final_registers post_acquired post_saved_heap /\ post_acquired = entry /\
  uchar_load (event_addr sg eid + OSEventGrp_off) (sem_post_group entry event) post_saved_heap /\
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers next_acquired saved_heap /\
  next_acquired = checkpoint /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    selected.(SchedState).(highRdyTid) = Some tid /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        (forall restored restore_start restore_word restore_middle restore_exit return_heap
          next_registers second_registers second_acquired second_heap,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          restore_start.(kernel_restore_r0) = saved ->
          armv7a_irq_fiq_mask restore_start.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore restore_start restored restore_word restore_middle ->
          armv7a_restore_suffix_transition restore restore_word restore_middle restore_exit return_heap ->
          next_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr next_registers.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask next_registers.(kernel_save_cpsr) = mask ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr next_registers) current return_heap
            second_registers second_acquired second_heap ->
          kernel_stack_call_same_call returned public_call /\
          sem_pend_wait_selected_at (Some environment) critical sg public_call mask initial observed eid timeout
            waiting returned current /\
          current.(TskState).(inUsedTaskStates) tid = Some (task_event_wake_single old PendSem 0 PendOK) /\
          kernel_call_restore_uninterrupted_execution arch restore_start restored restore_exit return_heap /\
          kernel_call_save_uninterrupted_execution arch next_registers current return_heap
            second_registers second_acquired second_heap /\ second_acquired = current /\
          exists resumed result_node branch_heap cleaned,
            sem_pend_resume_branch_fragment sg resumed eid public_call.(os_sched_call_stack).(stackLeaseSlot)
              result_node second_heap branch_heap /\
            result_node.(statPend) = PendOK /\
            sem_pend_cleanup_fragment sg perr 0 branch_heap cleaned /\
            (forall last_start last_word last_middle last_exit last_heap,
              last_start.(kernel_restore_r0) = second_registers.(kernel_save_r0) ->
              armv7a_irq_fiq_mask last_start.(kernel_restore_current_cpsr) = 192 ->
              armv7a_restore_prefix_transition restore last_start cleaned last_word last_middle ->
              armv7a_restore_suffix_transition restore last_word last_middle last_exit last_heap ->
              kernel_call_restore_uninterrupted_execution arch last_start cleaned last_exit last_heap /\
              (sem_pend_stack_call_post environment.(task_stack_call_external)
                environment.(task_stack_call_platform) (Some environment) critical sg public_call mask
                pevent timeout perr initial X ** retained) last_heap))).
Proof.
  intros environment critical arch task_abi restore save sg entry eid event tid old priority context node
    call saved acquired descriptor focus old_sp cpsr values lr prefix suffix first old_words
    publication before frame poster_mask post_before post_registers post_final_registers post_acquired post_saved_heap
    cursor restore_written middle final_cursor released registers final_registers
    next_acquired saved_heap public_call mask initial observed pevent timeout waiting perr X poster_saved abi checkpoint
    selected fragments outgoing updated current returned retained Hnonnull Haddress_event Heid Hslot Hlayout
    Hordered Hsaved Hexec Hwait Hin Hforeign Hgroup Hvalid Hlookup Htype Hentry Hcoverage Hunsuspended
    Hhighest Hcurrent Hnest Hlock Htid Hparked Hid Hgeneration Hnone Hfocus Hfragments Hregion Hgeometry
    Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hsaved_mask Hsp32 Hsp Haddress Hpre
    Hpost_return Hpost_cpsr Hpost_mask Hpost_save Hpost_wake
    Hr0 Hmask Hrestore_prefix Hrestore_suffix Hreturn Hregisters_cpsr Hnextmask Hsave.
  assert (Hentry_pre : (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) context poster_mask ** UCOS2_inv sg entry **
      unmap_table_rep sg **
      (store_parked_continuations
        (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
        entry.(TskState).(parkedTaskStacks) ** (perr # UChar |->_ ** frame))) post_before).
  { match type of Hpre with ?P post_before => match goal with |- ?Q post_before =>
      assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder post_before Hpre). }
  destruct (sem_post_saved_wait_entry_source _ _ critical arch save sg entry context poster_mask eid event
    tid old priority post_before post_registers post_final_registers post_acquired post_saved_heap before
    (store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
      entry.(TskState).(parkedTaskStacks) ** (perr # UChar |->_ ** frame))
    Hvalid Hlookup Htype ltac:(congruence) Hgroup Hlayout Hentry Hentry_pre Hpost_return Hpost_cpsr Hpost_mask
    Hpost_save Hpost_wake)
    as (Htype_read & Hpost_source & Hpost_acquired & Hgroup_read & Hwake_pre).
  assert (Hconsumer_pre :
    (critical_region_masked environment.(task_stack_call_platform) critical sg context.(os_sched_call_invocation)
       context.(os_sched_call_origin) poster_saved entry **
     os_sched_context_resources environment.(task_stack_call_external) context **
     event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
       (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
       (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
     sem_post_wake_frame sg entry eid tid **
     store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
       entry.(TskState).(parkedTaskStacks) ** (perr # UChar |->_ ** frame)) before).
  { match type of Hwake_pre with ?P before => match goal with |- ?Q before =>
      assert (Horder : P |-- Q) by (unfold poster_saved; entailer!) end end.
    exact (Horder before Hwake_pre). }
  split; [exact Htype_read|]. split; [exact Hpost_source|]. split; [exact Hpost_acquired|].
  split; [exact Hgroup_read|].
  exact (sem_pend_saved_post_public_return_source environment critical arch task_abi restore save
    sg entry eid event tid old priority context node poster_saved call saved acquired descriptor focus
    old_sp cpsr values lr prefix suffix first old_words publication before frame cursor restore_written middle
    final_cursor released registers final_registers next_acquired saved_heap public_call mask initial observed
    pevent timeout waiting perr X Hnonnull Haddress_event Heid Hslot Hlayout Hordered Hsaved Hexec Hwait
    Hin Hforeign Hgroup Hvalid Hlookup Htype Hentry Hcoverage Hunsuspended Hhighest Hcurrent Hnest Hlock
    Htid Hparked Hid Hgeneration Hnone Hfocus Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength
    Hcpsr Hlr Hranges Hsaved_mask Hsp32 Hsp Haddress Hconsumer_pre Hr0 Hmask Hrestore_prefix Hrestore_suffix
    Hreturn Hregisters_cpsr Hnextmask Hsave).
Qed.

