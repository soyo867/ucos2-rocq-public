Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** ARMv7-A/GNU non-VFP os_cpu_a_vfp-none.S:238-252 and 284-298.
    The input is the ACTUAL post-OSTaskSwHook heap. The two cache reads
    occur in source order, each followed by its real store. The selected
    pointer is retained for LDR SP,[R2]; it is not looked up afresh.

    This is the masked memory-effect fragment only. Address materialization
    and the 32-bit little-endian layout use the existing port/ABI boundary.
    No hook stability, register restoration, transfer receipt, or unmasked
    interference law is supplied here. A four-byte list is one typed STR,
    not four independently interruptible instructions. *)
Definition sched_install_cache_fragment (sg : StableGlobVars)
  (before after : model) (destination : Z) : Prop :=
  exists middle priority,
    uchar_load sg.(g_OSPrioHighRdy) priority before /\
    kernel_heap_execution [(sg.(g_OSPrioCur), priority)] before middle /\
    pointer_load sg.(g_OSTCBHighRdy) destination middle /\
    kernel_heap_execution (pointer_store_writes sg.(g_OSTCBCur) destination) middle after.

Definition sched_install_heap_fragment (sg : StableGlobVars)
  (before after : model) (destination sp : Z) : Prop :=
  sched_install_cache_fragment sg before after destination /\
  pointer_load destination sp after.

Lemma sched_install_cache_fragment_deterministic :
  forall sg before first second destination destination',
  sched_install_cache_fragment sg before first destination ->
  sched_install_cache_fragment sg before second destination' ->
  first = second /\ destination = destination'.
Proof.
  intros sg before first second destination destination'
    [middle [priority [Hp [Hb [Hd Hw]]]]]
    [middle' [priority' [Hp' [Hb' [Hd' Hw']]]]].
  assert (priority = priority') by (eapply uchar_load_deterministic; eassumption); subst priority'.
  assert (middle = middle') by (eapply kernel_heap_execution_deterministic; eassumption); subst middle'.
  assert (destination = destination') by (eapply pointer_load_deterministic; eassumption); subst destination'.
  split; [eapply kernel_heap_execution_deterministic; eassumption|reflexivity].
Qed.

Lemma sched_install_heap_fragment_deterministic :
  forall sg before first second destination sp destination' sp',
  sched_install_heap_fragment sg before first destination sp ->
  sched_install_heap_fragment sg before second destination' sp' ->
  first = second /\ destination = destination' /\ sp = sp'.
Proof.
  intros sg before first second destination sp destination' sp' [Hfirst Hsp] [Hsecond Hsp'].
  destruct (sched_install_cache_fragment_deterministic _ _ _ _ _ _ Hfirst Hsecond)
    as [Hheap Hdest]; subst second destination'.
  split; [reflexivity|]. split; [reflexivity|eapply pointer_load_deterministic; eassumption].
Qed.

Lemma sched_install_heap_fragment_frame : forall sg before after destination sp frame whole,
  sched_install_heap_fragment sg before after destination sp -> join before frame whole ->
  exists final, sched_install_heap_fragment sg whole final destination sp /\ join after frame final.
Proof.
  intros sg before after destination sp frame whole
    [[middle [priority [Hp [Hb [Hd Hw]]]]] Hsp] Hjoin.
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hb Hjoin) as [mid [Hmid Hjoinmid]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hw Hjoinmid) as [final [Hfinal Hjoinfinal]].
  exists final; split; [split|exact Hjoinfinal].
  - exists mid, priority.
    split; [eapply uchar_load_frame; eassumption|]. split; [exact Hmid|].
    split; [eapply pointer_load_frame; eassumption|exact Hfinal].
  - eapply pointer_load_frame; eassumption.
Qed.

(** A partial-store representation. Only the current-cache cells vary;
    all high caches, counters and running bytes retain their input values.
    This is not a fictional full invariant between the two stores. *)
Definition sched_install_cache_rep (sg : StableGlobVars)
  (state : SchedAbstractState) (current pointer : Z) : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> current **
  sg.(g_OSTCBCur) # Ptr |-> pointer **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if state.(isRunning) then 1 else 0).

Lemma sched_install_cache_rep_entry : forall sg state,
  sched_physical_rep sg state --||--
  sched_install_cache_rep sg state (sched_priority_byte state.(curSchedPrio))
    (encode_task_link sg state.(curTaskID)).
Proof. intros; unfold sched_physical_rep, sched_install_cache_rep; split; entailer!. Qed.

Lemma sched_install_cache_rep_merge : forall sg state,
  sched_install_cache_rep sg state (sched_priority_byte state.(highRdyPrio))
    (encode_task_link sg state.(highRdyTid)) --||--
  sched_physical_rep sg (sched_install_selected state).
Proof.
  intros; unfold sched_install_cache_rep, sched_physical_rep, sched_install_selected;
    cbn; split; entailer!.
Qed.

Lemma sched_install_cache_rep_post : forall sg state current pointer (frame : Assertion) heap,
  (sched_install_cache_rep sg state current pointer ** frame) heap ->
  exists final,
    sched_install_cache_fragment sg heap final (encode_task_link sg state.(highRdyTid)) /\
    (sched_install_cache_rep sg state (sched_priority_byte state.(highRdyPrio))
       (encode_task_link sg state.(highRdyTid)) ** frame) final.
Proof.
  intros sg state current pointer frame heap Hbefore.
  assert (Hpriority : uchar_load sg.(g_OSPrioHighRdy)
    (sched_priority_byte state.(highRdyPrio)) heap).
  { assert (Hfocus : sched_install_cache_rep sg state current pointer ** frame |--
      sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) ** TT).
    { unfold sched_install_cache_rep; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hfocus heap Hbefore). }
  assert (Hsplit : sched_install_cache_rep sg state current pointer ** frame |--
    sg.(g_OSPrioCur) # UChar |-> current **
    (sg.(g_OSTCBCur) # Ptr |-> pointer **
     sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) **
     sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) **
     sg.(g_OSCtxSwCtr) # UInt |-> state.(ctxSwCtr) **
     sg.(g_OSRunning) # UChar |-> (if state.(isRunning) then 1 else 0) ** frame)).
  { unfold sched_install_cache_rep; entailer!. }
  destruct (kernel_heap_framed_uchar_store _ _ _ _ heap (proj1 Hpriority)
    (Hsplit heap Hbefore)) as [middle [Hbyte Hmiddle]].
  assert (Hmid : (sched_install_cache_rep sg state
    (sched_priority_byte state.(highRdyPrio)) pointer ** frame) middle).
  { assert (Hpack : sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(highRdyPrio) **
      (sg.(g_OSTCBCur) # Ptr |-> pointer **
       sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) **
       sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) **
       sg.(g_OSCtxSwCtr) # UInt |-> state.(ctxSwCtr) **
       sg.(g_OSRunning) # UChar |-> (if state.(isRunning) then 1 else 0) ** frame) |--
      sched_install_cache_rep sg state (sched_priority_byte state.(highRdyPrio)) pointer ** frame).
    { unfold sched_install_cache_rep; entailer!. }
    exact (Hpack middle Hmiddle). }
  assert (Hpointer : pointer_load sg.(g_OSTCBHighRdy)
    (encode_task_link sg state.(highRdyTid)) middle).
  { assert (Hfocus : sched_install_cache_rep sg state
      (sched_priority_byte state.(highRdyPrio)) pointer ** frame |--
      sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) ** TT).
    { unfold sched_install_cache_rep; entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hfocus middle Hmid). }
  assert (Hwrite : sched_install_cache_rep sg state
      (sched_priority_byte state.(highRdyPrio)) pointer ** frame |--
    sg.(g_OSTCBCur) # Ptr |->_ **
    (sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(highRdyPrio) **
     sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) **
     sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) **
     sg.(g_OSCtxSwCtr) # UInt |-> state.(ctxSwCtr) **
     sg.(g_OSRunning) # UChar |-> (if state.(isRunning) then 1 else 0) ** frame)).
  { unfold sched_install_cache_rep.
    sep_apply_l_atomic (store_ptr_undef_store_ptr sg.(g_OSTCBCur) pointer); entailer!. }
  destruct (framed_pointer_store_execution _ _ _ middle (proj1 Hpointer)
    (Hwrite middle Hmid)) as [final [Hptr Hfinal]].
  exists final; split.
  - exists middle, (sched_priority_byte state.(highRdyPrio)).
    split; [exact Hpriority|]. split; [exact Hbyte|]. split; assumption.
  - assert (Hmerge : sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(highRdyTid) **
      (sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(highRdyPrio) **
       sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) **
       sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) **
       sg.(g_OSCtxSwCtr) # UInt |-> state.(ctxSwCtr) **
       sg.(g_OSRunning) # UChar |-> (if state.(isRunning) then 1 else 0) ** frame) |--
      sched_install_cache_rep sg state (sched_priority_byte state.(highRdyPrio))
        (encode_task_link sg state.(highRdyTid)) ** frame).
    { unfold sched_install_cache_rep; entailer!. }
    exact (Hmerge final Hfinal).
Qed.

Lemma sched_install_cache_raw_post : forall sg state heap,
  UCOS2_raw_rep sg state heap ->
  exists final,
    sched_install_cache_fragment sg heap final (encode_task_link sg state.(SchedState).(highRdyTid)) /\
    UCOS2_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) final.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_raw_rep sg state |--
    sched_install_cache_rep sg state.(SchedState)
      (sched_priority_byte state.(SchedState).(curSchedPrio))
      (encode_task_link sg state.(SchedState).(curTaskID)) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state)).
  { rewrite (UCOS2_raw_rep_split_module sg state SchedModule); cbn [UCOS2_module_rep].
    unfold sched_raw_rep; rewrite sched_install_cache_rep_entry; entailer!. }
  destruct (sched_install_cache_rep_post _ _ _ _ _ heap (Hsplit heap Hraw))
    as [final [Hrun Hfinal]].
  exists final; split; [exact Hrun|].
  assert (Hmerge : sched_install_cache_rep sg state.(SchedState)
      (sched_priority_byte state.(SchedState).(highRdyPrio))
      (encode_task_link sg state.(SchedState).(highRdyTid)) **
    (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
     sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
     UCOS2_raw_rep_missing_sched sg state) |--
    UCOS2_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state)).
  { rewrite (UCOS2_raw_rep_split_module sg (replace_SchedS (sched_install_selected state.(SchedState)) state)
      SchedModule); cbn [UCOS2_module_rep].
    change (sched_install_cache_rep sg state.(SchedState)
      (sched_priority_byte state.(SchedState).(highRdyPrio))
      (encode_task_link sg state.(SchedState).(highRdyTid)) **
      (sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
       sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
       UCOS2_raw_rep_missing_sched sg state) |--
      sched_raw_rep sg state.(TskState) (sched_install_selected state.(SchedState)) **
      UCOS2_raw_rep_missing_sched sg state).
    rewrite sched_install_cache_rep_merge.
    unfold sched_raw_rep; cbn [sched_install_selected readyList]; entailer!. }
  exact (Hmerge final Hfinal).
Qed.

Lemma sched_install_heap_raw_post : forall sg state slot node heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_raw_rep sg state heap ->
  exists final,
    sched_install_heap_fragment sg heap final (task_slot_addr sg slot) node.(tcbStkPtr) /\
    UCOS2_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) final.
Proof.
  intros sg state slot node heap Hhigh Hnode Haddress Hraw.
  destruct (sched_install_cache_raw_post sg state heap Hraw) as [final [Hrun Hfinal]].
  exists final; split; [split|exact Hfinal].
  - rewrite Hhigh in Hrun; exact Hrun.
  - eapply (armv7a_irq_raw_live_stack_pointer_load sg
      (replace_SchedS (sched_install_selected state.(SchedState)) state) slot node final);
      [exact Hnode|exact Haddress|exact Hfinal].
Qed.

Lemma sched_install_heap_raw_frame_post : forall sg state slot node (frame : Assertion) heap,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  (UCOS2_raw_rep sg state ** frame) heap ->
  exists final,
    sched_install_heap_fragment sg heap final (task_slot_addr sg slot) node.(tcbStkPtr) /\
    (UCOS2_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) ** frame) final.
Proof.
  intros sg state slot node frame heap Hhigh Hnode Haddress
    [owned [rest [Hjoin [Hraw Hframe]]]].
  destruct (sched_install_heap_raw_post sg state slot node owned Hhigh Hnode Haddress Hraw)
    as [after [Hrun Hafter]].
  destruct (sched_install_heap_fragment_frame _ _ _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

Lemma sched_install_heap_raw_preservation : forall sg state slot node before after destination sp,
  state.(SchedState).(highRdyTid) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_raw_rep sg state before ->
  sched_install_heap_fragment sg before after destination sp ->
  destination = task_slot_addr sg slot /\ sp = node.(tcbStkPtr) /\
    UCOS2_raw_rep sg (replace_SchedS (sched_install_selected state.(SchedState)) state) after.
Proof.
  intros sg state slot node before after destination sp Hhigh Hnode Haddress Hraw Hsource.
  destruct (sched_install_heap_raw_post _ _ _ _ _ Hhigh Hnode Haddress Hraw)
    as [final [Hrun Hpost]].
  destruct (sched_install_heap_fragment_deterministic _ _ _ _ _ _ _ _ Hsource Hrun)
    as [Hheap [Hdest Hsp]]; subst after destination sp.
  split; [reflexivity|]. split; [reflexivity|exact Hpost].
Qed.

(** This internal after-hook consumer does not demand the earlier chosen
    destination survive the hook. It reads the current high cache, installs
    it, reads that SAME TCB's SP, then removes precisely its existing parked
    fragments. It supplies neither a new running CPU token nor execution
    of the register/PC restore. The existing restore-source observation is
    retained for that later resource consumer, not synthesized here. *)
Lemma os_int_exit_install_heap_take_destination : forall external sg transfer heap,
  os_int_exit_destination_binding external transfer ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  UCOS2_inv sg transfer.(os_int_exit_hooked_state) heap ->
  exists final,
    sched_install_heap_fragment sg heap final
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    (coq_prop (task_current_at (os_int_exit_installed_state transfer)
        transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
        transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) transfer.(os_int_exit_incoming_stack)
        transfer.(os_int_exit_incoming_sp) transfer.(os_int_exit_incoming_fragments)) &&
     (UCOS2_inv sg (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
        transfer.(os_int_exit_incoming_fragments))) final.
Proof.
  intros external sg transfer heap
    [Hhigh [[node [Hnode [Hgeneration [Hpriority Hsp]]]] [Hlive [Hparked Harch]]]]
    Haddress [Hvalid Hraw].
  destruct (sched_install_heap_raw_post sg transfer.(os_int_exit_hooked_state)
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) node heap Hhigh Hnode Haddress Hraw)
    as [final [Hrun Hfinal]].
  assert (Hindex : forall p, transfer.(os_int_exit_hooked_state).(SchedState).(highRdyPrio) = Some p ->
    task_priority_in_range sg p).
  { intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    assert (Hpriorities : forall tid t,
      transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio)) by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode. }
  assert (Hcached : UCOS2_inv sg (replace_SchedS
    (sched_install_selected transfer.(os_int_exit_hooked_state).(SchedState))
    transfer.(os_int_exit_hooked_state)) final).
  { split; [apply os_int_exit_install_cache_preserves_validity; assumption|exact Hfinal]. }
  assert (Hcurrent : task_current_at (os_int_exit_installed_state transfer)
    transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
    transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration)).
  { split; [exact Hhigh|]; exists node; split; assumption. }
  exists final; split; [rewrite <- Hsp; exact Hrun|].
  split; [split; assumption|].
  exact (os_int_exit_take_destination_resources sg transfer Hparked final Hcached).
Qed.

(** The frame is the same owned heap fragment across the actual two stores
    and SP read. It may contain the handler context, unmap table or borrowed
    client cells; no fresh copy is inferred from an invocation identifier. *)
Lemma os_int_exit_install_heap_take_destination_frame : forall external sg transfer
  (frame : Assertion) heap,
  os_int_exit_destination_binding external transfer ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) ** frame) heap ->
  exists final,
    sched_install_heap_fragment sg heap final
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    (coq_prop (task_current_at (os_int_exit_installed_state transfer)
        transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
        transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) transfer.(os_int_exit_incoming_stack)
        transfer.(os_int_exit_incoming_sp) transfer.(os_int_exit_incoming_fragments)) &&
     (UCOS2_inv sg (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
        transfer.(os_int_exit_incoming_fragments) ** frame)) final.
Proof.
  intros external sg transfer frame heap Hbinding Haddress
    [owned [rest [Hjoin [Hinv Hframe]]]].
  destruct (os_int_exit_install_heap_take_destination _ _ _ _ Hbinding Haddress Hinv)
    as [after [Hrun [Hfacts Hafter]]].
  destruct (sched_install_heap_fragment_frame _ _ _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|]. split; [exact Hfacts|].
  exists after, rest; split; [exact Hfinal|]; split; assumption.
Qed.

(** The task-level path has an outgoing saved frame outside the parked
    map. Consume that actual owner when parking, then take the post-hook
    destination. [store_parked_stacks_switch_fragments] also covers aliasing
    outgoing/incoming keys; no distinct-task assumption or duplicated frame
    is introduced. Saving registers/SP and preserving the outgoing frame
    through the hook are earlier, still explicit source obligations. *)
Lemma os_sched_install_heap_take_destination :
  forall external sg context saved hooked incoming resumed heap,
  os_sched_saved_stack_binding context saved hooked ->
  os_sched_destination_binding external context saved hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_inv sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) heap ->
  exists final sp,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    (coq_prop (task_current_at (os_sched_install_context context saved incoming hooked)
        incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) incoming sp resumed) &&
     (UCOS2_inv sg (os_sched_install_context context saved incoming hooked) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed)) final.
Proof.
  intros external sg context saved hooked incoming resumed heap Hsaved
    [Hhigh [[node [Hnode [Hgeneration [Hpriority Harch]]]] [Hlive Hparked]]]
    Haddress Hbefore.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { destruct Hbefore as [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]]; exact Hvalid. }
  assert (Hraw : (UCOS2_raw_rep sg hooked **
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) heap).
  { assert (Hforget : UCOS2_inv sg hooked **
        task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved |--
      UCOS2_raw_rep sg hooked **
        task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved).
    { unfold UCOS2_inv; entailer!. }
    exact (Hforget heap Hbefore). }
  destruct (sched_install_heap_raw_frame_post sg hooked incoming.(stackLeaseSlot) node _ heap
    Hhigh Hnode Haddress Hraw) as [final [Hrun Hfinal]].
  assert (Hindex : forall p, hooked.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p).
  { intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
    pose proof (proj1 (proj2 Hvalid)) as Htasks.
    assert (Hpriorities : forall tid t, hooked.(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio)) by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode. }
  assert (Hcached : UCOS2_state_inv sg
    (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)).
  { apply os_int_exit_install_cache_preserves_validity; assumption. }
  assert (Hnone : hooked.(TskState).(parkedTaskStacks)
    (task_stack_key context.(os_sched_call_stack)) = None).
  { unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  assert (Hconsistent : parked_stacks_consistent hooked.(TskState)
    (task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) saved) incoming)).
  { apply task_stack_take_preserves_consistency.
    apply os_sched_park_saved_context_preserves_consistency; [|exact Hsaved].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Htake : UCOS2_raw_rep sg
      (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked) **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved |--
    UCOS2_inv sg (os_sched_install_context context saved incoming hooked) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed).
  { assert (Hsplit : forall state, UCOS2_raw_rep sg state --||--
      store_parked_stacks state.(TskState).(parkedTaskStacks) **
      UCOS2_raw_rep_missing_parked_stacks sg state).
    { intros; unfold UCOS2_raw_rep, UCOS2_raw_rep_missing_parked_stacks, task_shared_rep;
        split; entailer!. }
    rewrite (Hsplit (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)).
    sep_apply_l_atomic (store_parked_stacks_switch_fragments hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) incoming saved resumed Hnone Hparked).
    sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg
      (replace_SchedS (sched_install_selected hooked.(SchedState)) hooked)
      (task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
        context.(os_sched_call_stack) saved) incoming) Hcached Hconsistent).
    unfold os_sched_install_context; entailer!. }
  assert (Hcurrent : task_current_at (os_sched_install_context context saved incoming hooked)
    incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration)).
  { split; [exact Hhigh|]; exists node; split; assumption. }
  exists final, node.(tcbStkPtr); split; [exact Hrun|].
  split; [split; assumption|exact (Htake final Hfinal)].
Qed.

(** Actual successor resource consumer on the branch where the freshly
    read post-hook destination is the exact saved invocation. The three
    equalities identify this branch; they do not constrain every hook or
    every interrupt switch. Only the entry-issued linear escrow recovers
    the CPU/architecture owner. A different destination has no such receipt
    here and is not silently mapped to the interrupted invocation.

    The architectural frame-return observation remains the approved port
    input. The theorem proves its memory/resource handoff, not LDM/MSR/PC
    execution and not the poststate of the next OS_CPU_SR_Save. *)
Lemma armv7a_irq_install_resumes_saved_call :
  forall external platform port sg context transfer restored_pc heap,
  os_int_exit_destination_binding external transfer ->
  transfer.(os_int_exit_incoming_stack) = context.(os_int_exit_interrupted_stack) ->
  transfer.(os_int_exit_incoming_sp) = context.(os_int_exit_interrupted_sp) ->
  transfer.(os_int_exit_incoming_fragments) = context.(os_int_exit_interrupted_fragments) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
    armv7a_irq_handler_frame external platform port context ** unmap_table_rep sg) heap ->
  exists final,
    sched_install_heap_fragment sg heap final
      (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
      context.(os_int_exit_interrupted_sp) /\
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc) /\
      task_current_at (os_int_exit_installed_state transfer)
        transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)
        transfer.(os_int_exit_incoming_stack).(stackLeaseGeneration)) &&
     (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
        context.(os_int_exit_interrupted_mask) **
      UCOS2_inv sg (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep context.(os_int_exit_handler_stack)
        context.(os_int_exit_handler_fragments) ** unmap_table_rep sg)) final.
Proof.
  intros external platform port sg context transfer restored_pc heap Hdestination
    Hstack Hsp Hfragments Haddress Hpc Hbefore.
  assert (Hsplit : UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      armv7a_irq_handler_frame external platform port context ** unmap_table_rep sg |--
    UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      (armv7a_irq_handler_frame external platform port context ** unmap_table_rep sg)).
  { entailer!. }
  destruct (os_int_exit_install_heap_take_destination_frame external sg transfer _ heap
    Hdestination Haddress (Hsplit heap Hbefore)) as [final [Hrun [Hfacts Hafter]]].
  destruct Hfacts as [Hcurrent Harch].
  assert (Hresume : UCOS2_inv sg (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep transfer.(os_int_exit_incoming_stack).(stackLeaseRegion)
        transfer.(os_int_exit_incoming_fragments) **
      (armv7a_irq_handler_frame external platform port context ** unmap_table_rep sg) |--
    coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
         context.(os_int_exit_interrupted_mask) **
       UCOS2_inv sg (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments) ** unmap_table_rep sg)).
  { rewrite Hstack, Hfragments.
    unfold armv7a_irq_handler_frame, os_int_exit_context_resources.
    pose proof (os_int_exit_consume_continuation_escrow external platform port context
      restored_pc Hpc) as Hconsume.
    unfold os_int_exit_resume_register_input in Hconsume.
    sepcon_right_assoc; sep_apply_l_atomic Hconsume; Intros; entailer!. }
  pose proof (Hresume final Hafter) as [Hrestored Hresources].
  exists final; split; [rewrite Hstack, Hsp in Hrun; exact Hrun|].
  split; [split; assumption|exact Hresources].
Qed.
