Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Common tail of all three switch arms, after timeout's EventTaskRemove
    when applicable. Every OSTCBCur read and all four C stores are physical.
    The error value and cleaning state come from the actual branch join. *)
Definition sem_pend_cleanup_fragment sg perr error (before after : model) : Prop :=
  exists current error_written status_written pending_written,
    kernel_heap_execution [(perr, error)] before error_written /\
    pointer_load sg.(g_OSTCBCur) current error_written /\
    kernel_heap_execution [(tcb_field_address current TCBStat, 0)] error_written status_written /\
    pointer_load sg.(g_OSTCBCur) current status_written /\
    kernel_heap_execution [(tcb_field_address current TCBStatPend, 0)] status_written pending_written /\
    pointer_load sg.(g_OSTCBCur) current pending_written /\
    kernel_heap_execution (pointer_store_writes (tcb_field_address current TCBEventPtr) 0)
      pending_written after.

Definition sem_pend_success_cleanup_fragment sg perr (before after : model) : Prop :=
  (exists current, pointer_load sg.(g_OSTCBCur) current before /\
    uchar_load (tcb_field_address current TCBStatPend) 0 before) /\
  sem_pend_cleanup_fragment sg perr 0 before after.

Definition sem_pend_cleanup_cells sg state tid old : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  sem_pend_cleanup_frame sg state tid old.

Lemma sem_pend_error_store : forall perr error (frame : Assertion) before,
  0 <= error < 256 ->
  (perr # UChar |->_ ** frame) before ->
  exists after, kernel_heap_execution [(perr, error)] before after /\
    (perr # UChar |-> error ** frame) after.
Proof.
  intros perr error frame before Hrange Hpre.
  assert (Hopen : perr # UChar |->_ ** frame |--
    coq_prop (isvalidptr_char perr) && (store_byte_noninit perr ** frame)).
  { unfold undef_store_uchar; entailer!. }
  destruct (Hopen before Hpre) as [Haddress Hbytes].
  destruct (framed_byte_noninit_store_execution perr error frame before Hrange Hbytes)
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hclose : store_byte perr error ** frame |-- perr # UChar |-> error ** frame).
  { unfold store_uchar; entailer!; change (error <= 255); lia. }
  exact (Hclose after Hafter).
Qed.

(** This is the shared semantic consumer after the three TCB cleanup
    stores. Canonical which_implies_wit_20 and the physical source tail
    below both consume this lemma. Its origin is established separately
    by the success/abort guards or the actual timeout callee post. *)
Lemma sem_pend_cleanup_return_merge : forall external critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_cleanup_origin external critical sg context mask before observed eid timeout error cleaning tid node ->
  sem_pend_cleanup_cells sg cleaning tid node |--
  coq_prop (sem_pend_c_result external critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node)) &&
  UCOS2_inv sg (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros external critical sg context mask before observed eid pevent timeout error cleaning tid node
    Hnonnull Haddress Hid Hslot Hordered Horigin.
  pose proof (sem_pend_cleanup_origin_result external critical sg context mask before observed eid
    pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin) as Hresult.
  unfold sem_pend_cleanup_cells.
  sep_apply_l_atomic (sem_pend_cleanup_merge sg cleaning tid node (proj1 Horigin)); entailer!.
Qed.

(** Exact timeout call-return cut, shared with canonical which18. The
    callee result is its existing proved EventTaskRemove contract, not a
    new predicate claiming a chosen abstract poststate. *)
Lemma sem_pend_timeout_remove_cleanup : forall external critical sg context mask before observed eid
  timeout resumed tid old current,
  sem_pend_resume_origin external critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old |--
  coq_prop (sem_pend_cleanup_origin external critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None)) &&
  UCOS2_inv sg (event_task_remove_state resumed eid current tid old).
Proof.
  intros external critical sg context mask before observed eid timeout resumed tid old current
    Horigin Htimeout Hlookup Hlayout.
  pose proof (sem_pend_resume_cleanup_timeout external critical sg context mask before observed eid
    timeout resumed tid old current Horigin Htimeout Hlookup) as Hcleanup.
  sep_apply_l_atomic (sem_pend_remove_call_merge sg resumed eid current tid old
    (proj1 Horigin) Htimeout Hlookup Hlayout); entailer!.
Qed.

Lemma sem_pend_cleanup_stores_source : forall sg state tid old perr error
  (frame : Assertion) before,
  sem_pend_cleanup_entry sg state tid old -> 0 <= error < 256 ->
  (UCOS2_inv sg state ** perr # UChar |->_ ** frame) before ->
  exists after,
    sem_pend_cleanup_fragment sg perr error before after /\
    (sem_pend_cleanup_cells sg state tid old ** perr # UChar |-> error ** frame) after.
Proof.
  intros sg state tid old perr error frame before Hentry Hrange Hpre.
  pose proof Hentry as [Hvalid [Hcurrent [Hold [Hregistration [Hmulti [Hflag Hready]]]]]].
  set (base := task_slot_addr sg tid).
  set (tail := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some (encode_task_status old.(stat))) **
    tcb_cell base TCBStatPend (Some (encode_pend_status old.(statPend))) ** tcb_cell base TCBEventPtr (Some 0) **
    sem_pend_cleanup_frame sg state tid old ** frame).
  assert (Hsplit : UCOS2_inv sg state ** perr # UChar |->_ ** frame |--
    perr # UChar |->_ ** tail).
  { sep_apply_l_atomic (sem_pend_cleanup_split sg state tid old Hvalid Hcurrent Hold).
    rewrite Hregistration; cbn [encode_event_link].
    unfold tail, base; entailer!. }
  destruct (sem_pend_error_store perr error tail before Hrange (Hsplit before Hpre))
    as [error_written [Herror Herror_post]].
  set (stat_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStatPend (Some (encode_pend_status old.(statPend))) ** tcb_cell base TCBEventPtr (Some 0) **
    sem_pend_cleanup_frame sg state tid old ** perr # UChar |-> error ** frame).
  assert (Hstat : perr # UChar |-> error ** tail |--
    tcb_field_address base TCBStat # UChar |-> encode_task_status old.(stat) ** stat_frame).
  { unfold tail, stat_frame; cbn [tcb_cell]; entailer!. }
  assert (Hread_error : pointer_load sg.(g_OSTCBCur) base error_written).
  { eapply framed_pointer_store_load.
    assert (Hr : perr # UChar |-> error ** tail |-- sg.(g_OSTCBCur) # Ptr |-> base ** TT).
    { unfold tail; entailer!; intros ? ?; exact I. }
    exact (Hr error_written Herror_post). }
  destruct (kernel_heap_framed_uchar_store (tcb_field_address base TCBStat)
    (encode_task_status old.(stat)) 0 stat_frame error_written ltac:(lia)
    (Hstat error_written Herror_post)) as [status_written [Hstatus Hstatus_post]].
  set (pend_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some 0) ** tcb_cell base TCBEventPtr (Some 0) **
    sem_pend_cleanup_frame sg state tid old ** perr # UChar |-> error ** frame).
  assert (Hpend : tcb_field_address base TCBStat # UChar |-> 0 ** stat_frame |--
    tcb_field_address base TCBStatPend # UChar |-> encode_pend_status old.(statPend) ** pend_frame).
  { unfold stat_frame, pend_frame; cbn [tcb_cell]; entailer!. }
  assert (Hread_status : pointer_load sg.(g_OSTCBCur) base status_written).
  { eapply framed_pointer_store_load.
    assert (Hr : tcb_field_address base TCBStat # UChar |-> 0 ** stat_frame |--
      sg.(g_OSTCBCur) # Ptr |-> base ** TT).
    { unfold stat_frame; entailer!; intros ? ?; exact I. }
    exact (Hr status_written Hstatus_post). }
  destruct (kernel_heap_framed_uchar_store (tcb_field_address base TCBStatPend)
    (encode_pend_status old.(statPend)) 0 pend_frame status_written ltac:(lia) (Hpend status_written Hstatus_post))
    as [pending_written [Hpending Hpending_post]].
  set (event_frame := sg.(g_OSTCBCur) # Ptr |-> base **
    tcb_cell base TCBStat (Some 0) ** tcb_cell base TCBStatPend (Some 0) **
    sem_pend_cleanup_frame sg state tid old ** perr # UChar |-> error ** frame).
  assert (Hevent : tcb_field_address base TCBStatPend # UChar |-> 0 ** pend_frame |--
    tcb_field_address base TCBEventPtr # Ptr |->_ ** event_frame).
  { unfold pend_frame, event_frame; cbn [tcb_cell].
    sep_apply_l_atomic (store_ptr_undef_store_ptr (tcb_field_address base TCBEventPtr) 0).
    entailer!. }
  assert (Hread_pending : pointer_load sg.(g_OSTCBCur) base pending_written).
  { eapply framed_pointer_store_load.
    assert (Hr : tcb_field_address base TCBStatPend # UChar |-> 0 ** pend_frame |--
      sg.(g_OSTCBCur) # Ptr |-> base ** TT).
    { unfold pend_frame; entailer!; intros ? ?; exact I. }
    exact (Hr pending_written Hpending_post). }
  destruct (framed_pointer_store_execution (tcb_field_address base TCBEventPtr) 0
    event_frame pending_written ltac:(lia) (Hevent pending_written Hpending_post))
    as [after [Hclear Hafter]].
  exists after; split.
  - exists base, error_written, status_written, pending_written; tauto.
  - assert (Hclose : tcb_field_address base TCBEventPtr # Ptr |-> 0 ** event_frame |--
      sem_pend_cleanup_cells sg state tid old ** perr # UChar |-> error ** frame).
    { unfold sem_pend_cleanup_cells, event_frame, base; cbn [tcb_cell]; entailer!. }
    exact (Hclose after Hafter).
Qed.

(** Compatibility specialization for the already checked success source
    consumer. The physical four-store producer is now shared by all arms. *)
Lemma sem_pend_success_cleanup_source : forall sg state eid tid old perr
  (frame : Assertion) before,
  sem_pend_resume_entry sg state eid tid old -> old.(statPend) = PendOK ->
  (UCOS2_inv sg state ** perr # UChar |->_ ** frame) before ->
  exists after,
    sem_pend_success_cleanup_fragment sg perr before after /\
    sem_pend_resume_critical sg eid state OS_ERR_NONE (event_pend_cleanup_state sg false state tid old) /\
    (UCOS2_inv sg (event_pend_cleanup_state sg false state tid old) ** perr # UChar |-> 0 ** frame) after.
Proof.
  intros sg state eid tid old perr frame before Hresume Hsuccess Hpre.
  pose proof Hresume as [Hvalid [Hcurrent [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  rewrite Hsuccess in Hregistration.
  assert (Hentry : sem_pend_cleanup_entry sg state tid old) by (unfold sem_pend_cleanup_entry; tauto).
  assert (Hreads : pointer_load sg.(g_OSTCBCur) (task_slot_addr sg tid) before /\
    uchar_load (tcb_field_address (task_slot_addr sg tid) TCBStatPend) 0 before).
  { assert (Hsplit : UCOS2_inv sg state ** perr # UChar |->_ ** frame |--
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
      tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0 ** TT).
    { sep_apply_l_atomic (sem_pend_cleanup_split sg state tid old Hvalid Hcurrent Hold).
      rewrite Hsuccess; cbn [tcb_cell encode_pend_status]; entailer!; intros ? ?; exact I. }
    split.
    - eapply framed_pointer_store_load.
      assert (Horder : sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
        tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0 ** (TT) |--
        sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid ** TT)
        by (entailer!; intros ? ?; exact I).
      exact (Horder before (Hsplit before Hpre)).
    - eapply framed_uchar_store_load.
      assert (Horder : sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
        tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0 ** (TT) |--
        tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> 0 ** TT)
        by (entailer!; intros ? ?; exact I).
      exact (Horder before (Hsplit before Hpre)). }
  destruct (sem_pend_cleanup_stores_source sg state tid old perr 0 frame before Hentry ltac:(lia) Hpre)
    as [after [Hsource Hafter]].
  exists after; split.
  - split; [exists (task_slot_addr sg tid); exact Hreads|exact Hsource].
  - split.
    + exists tid, old; rewrite Hsuccess; repeat split; assumption || reflexivity.
    + assert (Hclose : sem_pend_cleanup_cells sg state tid old ** perr # UChar |-> 0 ** frame |--
        UCOS2_inv sg (event_pend_cleanup_state sg false state tid old) ** perr # UChar |-> 0 ** frame).
      { unfold sem_pend_cleanup_cells; sepcon_assoc_change.
        sep_apply_l_atomic (sem_pend_cleanup_merge sg state tid old Hentry); entailer!. }
      exact (Hclose after Hafter).
Qed.

(** The final Restore consumes the second Save's actual token, retaining
    the updated invariant and caller error cell. The supplied transitions
    are the local no-intervening-IRQ branch; existence/progress is not
    asserted by this resource theorem. *)
Lemma sem_pend_success_uninterrupted_return : forall external platform critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg state eid tid old call saved perr (frame : Assertion) before,
  sem_pend_resume_entry sg state eid tid old -> old.(statPend) = PendOK ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved state ** os_sched_context_resources external call **
   UCOS2_inv sg state ** perr # UChar |->_ ** frame) before ->
  exists cleaned,
    sem_pend_success_cleanup_fragment sg perr before cleaned /\
    sem_pend_resume_critical sg eid state OS_ERR_NONE (event_pend_cleanup_state sg false state tid old) /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor cleaned written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved) **
       UCOS2_inv sg (event_pend_cleanup_state sg false state tid old) **
       perr # UChar |-> 0 ** frame) after).
Proof.
  intros external platform critical arch restore sg state eid tid old call saved perr frame before
    Hresume Hsuccess Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    UCOS2_inv sg state ** perr # UChar |->_ **
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved state ** os_sched_context_resources external call ** frame))
      by entailer! end.
  destruct (sem_pend_success_cleanup_source sg state eid tid old perr _ before
    Hresume Hsuccess (Horder before Hpre)) as [cleaned [Hsource [Hresult Hcleaned]]].
  exists cleaned; split; [exact Hsource|]. split; [exact Hresult|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  match type of Hcleaned with ?P cleaned => assert (Hclose : P |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved state ** os_sched_context_resources external call **
    (UCOS2_inv sg (event_pend_cleanup_state sg false state tid old) ** perr # UChar |-> 0 ** frame))
      by entailer! end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch
    restore sg call saved state cursor cleaned written middle final_cursor after _ Hr0 Hmask
    (Hclose cleaned Hcleaned) Hprefix Hsuffix) as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hreorder : P |-- Q) by entailer! end end.
  exact (Hreorder after Hafter).
Qed.

(** Full common success/abort/timeout suffix from the actual branch join.
    which16/17 establish its origin for the two non-timeout guards;
    sem_pend_timeout_remove_cleanup establishes it from the timeout callee
    post. The same origin and final cells feed canonical which20. The
    critical token remains indexed by its real acquisition state, which
    may differ from the cleaning state after EventTaskRemove. *)
Lemma sem_pend_cleanup_uninterrupted_return : forall external platform critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg context mask original observed eid pevent timeout cleaning tid node error
  call saved acquired perr (frame : Assertion) before,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot original eid observed ->
  sem_pend_context_error (event_slot_type_value original.(EventState) eid)
    original.(IntrState).(intNesting) original.(IntrState).(lockNesting) = None ->
  sem_pend_cleanup_origin external critical sg context mask original observed eid timeout error cleaning tid node ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
   UCOS2_inv sg cleaning ** perr # UChar |->_ ** frame) before ->
  exists cleaned,
    sem_pend_cleanup_fragment sg perr error before cleaned /\
    sem_pend_c_result external critical sg context pevent timeout original error
      (event_pend_cleanup_state sg false cleaning tid node) /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor cleaned written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (kernel_call_execution_owned external platform call (armv7a_irq_fiq_mask saved) **
       UCOS2_inv sg (event_pend_cleanup_state sg false cleaning tid node) **
       perr # UChar |-> error ** frame) after).
Proof.
  intros external platform critical arch restore sg context mask original observed eid pevent timeout
    cleaning tid node error call saved acquired perr frame before
    Hnonnull Haddress Hid Hslot Hordered Horigin Hpre.
  assert (Hrange : 0 <= error < 256).
  { destruct Horigin as [_ [resumed [old [code [Hresume [Herror Hstep]]]]]].
    destruct Hstep as [slot [task [_ [_ [Hcode Hstep]]]]].
    rewrite Herror, Hcode; destruct task.(statPend); cbn; lia. }
  match type of Hpre with ?P before => assert (Horder : P |--
    UCOS2_inv sg cleaning ** perr # UChar |->_ **
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call ** frame))
      by entailer! end.
  destruct (sem_pend_cleanup_stores_source sg cleaning tid node perr error _ before
    (proj1 Horigin) Hrange (Horder before Hpre)) as [cleaned [Hsource Hcells]].
  match type of Hcells with ?P cleaned => assert (Hmerge : P |--
    coq_prop (sem_pend_c_result external critical sg context pevent timeout original error
      (event_pend_cleanup_state sg false cleaning tid node)) &&
    (critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external call **
     (UCOS2_inv sg (event_pend_cleanup_state sg false cleaning tid node) **
      perr # UChar |-> error ** frame))) end.
  { sep_apply_l_atomic (sem_pend_cleanup_return_merge external critical sg context mask original
      observed eid pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin).
    entailer!. }
  destruct (Hmerge cleaned Hcells) as [Hresult Hcleaned].
  exists cleaned; split; [exact Hsource|]. split; [exact Hresult|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch
    restore sg call saved acquired cursor cleaned written middle final_cursor after _ Hr0 Hmask
    Hcleaned Hprefix Hsuffix) as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hreorder : P |-- Q) by entailer! end end.
  exact (Hreorder after Hafter).
Qed.
