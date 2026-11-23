Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_timeout_remove_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_nonswitch_phase_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Import Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The actual common C stores establish the current checkpoint relation.
    Its final continuation executes MSR/BX and consumes that same checkpoint
    in the public post. Acquired is the second Save's checkpoint; cleaning
    may already include the timeout branch's actual EventTaskRemove. *)
Lemma sem_pend_observed_cleanup_restore_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid pevent timeout cleaning tid node error
  call saved acquired perr (frame : Assertion) before X,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  sem_pend_observed_cleanup_origin (Some environment) critical sg original mask initial observed
    eid timeout error cleaning tid node ->
  interrupt_saved_value mask saved -> kernel_stack_call_same_call call original ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
   os_sched_context_resources environment.(task_stack_call_external) call ** UCOS2_inv sg cleaning **
   sem_pend_optional_stack_resources environment.(task_stack_call_external)
     environment.(task_stack_call_platform) (Some environment) call cleaning **
   perr # UChar |->_ ** unmap_table_rep sg ** frame) before ->
  exists cleaned,
    sem_pend_cleanup_fragment sg perr error before cleaned /\
    sem_pend_checkpoint_result (Some environment) critical sg original pevent timeout initial error
      (event_pend_cleanup_state sg false cleaning tid node) /\
    (task_tcb_init_stack_restore_input environment critical sg call saved acquired
       (event_pend_cleanup_state sg false cleaning tid node) **
     unmap_table_rep sg ** perr # UChar |-> error ** frame) cleaned /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor cleaned written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
      (sem_pend_stack_call_post environment.(task_stack_call_external)
        environment.(task_stack_call_platform) (Some environment) critical sg original mask
        pevent timeout perr initial X ** frame) after).
Proof.
  intros environment critical arch restore sg original mask initial observed eid pevent timeout cleaning tid node
    error call saved acquired perr frame before X Hnonnull Haddress Hid Hslot Hordered Horigin Hsaved Hsame Hexec Hpre.
  assert (Hrange : 0 <= error < 256).
  { destruct Horigin as [_ [resumed [old [code [Hresume [Herror Hstep]]]]]].
    destruct Hstep as [slot [task [_ [_ [Hcode Hstep]]]]].
    rewrite Herror, Hcode; destruct task.(statPend); cbn; lia. }
  set (tail := critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    sem_pend_optional_stack_resources environment.(task_stack_call_external)
      environment.(task_stack_call_platform) (Some environment) call cleaning ** unmap_table_rep sg ** frame).
  match type of Hpre with ?P before => assert (Horder : P |--
    UCOS2_inv sg cleaning ** perr # UChar |->_ ** tail) by (unfold tail; entailer!) end.
  destruct (sem_pend_cleanup_stores_source sg cleaning tid node perr error tail before
    (proj1 Horigin) Hrange (Horder before Hpre)) as [cleaned [Hstores Hcells]].
  assert (Hmerge : sem_pend_cleanup_cells sg cleaning tid node ** perr # UChar |-> error ** tail |--
    coq_prop (sem_pend_checkpoint_result (Some environment) critical sg original pevent timeout initial error
      (event_pend_cleanup_state sg false cleaning tid node)) &&
    (task_tcb_init_stack_restore_input environment critical sg call saved acquired
      (event_pend_cleanup_state sg false cleaning tid node) ** unmap_table_rep sg **
      perr # UChar |-> error ** frame)).
  { pose proof (sem_pend_observed_cleanup_result (Some environment) critical sg original mask initial
      observed eid pevent timeout error cleaning tid node Hnonnull Haddress Hid Hslot Hordered Horigin) as Hresult.
    unfold tail, sem_pend_optional_stack_resources; Intros.
    assert (Hcoverage : task_stack_live_coverage cleaning.(TskState) (task_stack_call_active_key call)) by tauto.
    unfold task_tcb_init_stack_capsules.
    sep_apply_l_atomic (sem_pend_cleanup_stack_merge environment critical sg call saved acquired cleaning tid node
      (proj1 Horigin) Hcoverage); entailer!. }
  destruct (Hmerge cleaned Hcells) as [Hresult Hready].
  exists cleaned; split; [exact Hstores|]. split; [exact Hresult|]. split; [exact Hready|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  assert (Hready_frame : (task_tcb_init_stack_restore_input environment critical sg call saved acquired
      (event_pend_cleanup_state sg false cleaning tid node) ** unmap_table_rep sg **
      (perr # UChar |-> error ** frame)) cleaned).
  { match type of Hready with ?P cleaned => match goal with |- ?Q cleaned =>
      assert (Hreorder : P |-- Q) by entailer! end end; exact (Hreorder cleaned Hready). }
  destruct (sem_pend_uninterrupted_restore_phase environment critical arch restore SemPendReturnPhase sg call
    saved acquired (event_pend_cleanup_state sg false cleaning tid node) cursor cleaned written middle final_cursor after
    (perr # UChar |-> error ** frame) I Hr0 Hmask Hready_frame Hprefix Hsuffix) as [Hrun Hafter].
  split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hfinish : P |-- Q) end end.
  { rewrite <- sem_pend_phase_restore_return_output.
    rewrite (proj2 Hsaved).
    match goal with |- ?P |-- _ => assert (Hpad : P |--
      (TT ** sem_pend_stack_restore_source_output environment.(task_stack_call_external)
        environment.(task_stack_call_platform) (Some environment) critical sg call mask
        (event_pend_cleanup_state sg false cleaning tid node) ** unmap_table_rep sg **
        perr # UChar |-> error) ** frame) by (entailer!; apply derivable1_truep_intros) end.
    eapply derivable1_trans; [exact Hpad|].
    sep_apply_l_atomic (sem_pend_stack_call_post_from_restore
      environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment) critical sg
      original call mask pevent timeout perr initial (event_pend_cleanup_state sg false cleaning tid node)
      error eid X Hresult Hnonnull Haddress Hordered Hsame Hexec).
    entailer!. }
  exact (Hfinish after Hafter).
Qed.

(** The exact switch discriminator is read from the resumed task. Only
    timeout invokes EventTaskRemove; success and abort reach cleanup with
    the same heap. The original wait/generation remains in the origin. *)
Definition sem_pend_resume_branch_fragment sg resumed eid tid node (before after : model) : Prop :=
  pointer_load sg.(g_OSTCBCur) (task_slot_addr sg tid) before /\
  uchar_load (tcb_field_address (task_slot_addr sg tid) TCBStatPend)
    (encode_pend_status node.(statPend)) before /\
  match node.(statPend) with
  | PendTimeout => exists current,
      mutex_query_lookup resumed eid current /\
      sem_pend_timeout_remove_fragment (task_slot_addr sg tid)
        &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
        &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
        (node.(curPrio) / 8) (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))
        (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (node.(curPrio) / 8))
        (encode_event_wait_grp current.(waitList) resumed.(TskState)) before after
  | _ => after = before
  end.

Lemma sem_pend_observed_resume_branch_source : forall environment critical sg original mask initial observed
  eid timeout resumed tid node call saved acquired perr (frame : Assertion) before,
  sem_pend_observed_resume_origin (Some environment) critical sg original mask initial observed
    eid timeout resumed tid node ->
  event_object_layout_prop sg eid ->
  (task_tcb_init_stack_restore_input environment critical sg call saved acquired resumed **
    unmap_table_rep sg ** perr # UChar |->_ ** frame) before ->
  exists cleaning clean_node branch_heap,
    sem_pend_resume_branch_fragment sg resumed eid tid node before branch_heap /\
    sem_pend_observed_cleanup_origin (Some environment) critical sg original mask initial observed eid timeout
      (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) cleaning tid clean_node /\
    (task_tcb_init_stack_restore_input environment critical sg call saved acquired cleaning **
      unmap_table_rep sg ** perr # UChar |->_ ** frame) branch_heap.
Proof.
  intros environment critical sg original mask initial observed eid timeout resumed tid node call saved acquired
    perr frame before Horigin Hlayout Hpre.
  pose proof (proj1 Horigin) as Hentry.
  pose proof Hentry as [Hvalid [Hcurrent [Hnode [Hregistration Hready]]]].
  assert (Hreads : pointer_load sg.(g_OSTCBCur) (task_slot_addr sg tid) before /\
    uchar_load (tcb_field_address (task_slot_addr sg tid) TCBStatPend)
      (encode_pend_status node.(statPend)) before).
  { assert (Hsplit : task_tcb_init_stack_restore_input environment critical sg call saved acquired resumed **
      unmap_table_rep sg ** perr # UChar |->_ ** frame |--
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
      tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status node.(statPend) ** TT).
    { unfold task_tcb_init_stack_restore_input; Intros.
      sep_apply_l_atomic (sem_pend_cleanup_split sg resumed tid node Hvalid Hcurrent Hnode).
      cbn [tcb_cell]; entailer!; intros ? ?; exact I. }
    pose proof (Hsplit before Hpre) as Hcells.
    split.
    - eapply framed_pointer_store_load.
      match type of Hcells with ?P before => assert (Hfocus : P |--
        sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid ** TT)
        by (entailer!; intros ? ?; exact I) end; exact (Hfocus before Hcells).
    - eapply framed_uchar_store_load.
      match type of Hcells with ?P before => assert (Hfocus : P |--
        tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status node.(statPend) ** TT)
        by (entailer!; intros ? ?; exact I) end; exact (Hfocus before Hcells). }
  destruct node.(statPend) eqn:Hstatus.
  all: try solve [exists resumed, node, before; split;
    [unfold sem_pend_resume_branch_fragment; rewrite Hstatus; tauto|]; split;
    [rewrite <- Hstatus; apply sem_pend_observed_resume_cleanup_without_timeout;
      [exact Horigin|rewrite Hstatus; discriminate]|exact Hpre]].
  assert (Hptr : node.(eventPtr) = Some eid).
  { destruct Hregistration as [_ [_ Hregistration]]; rewrite Hstatus in Hregistration; exact Hregistration. }
  destruct (sem_pend_resume_timeout_event sg resumed eid tid node Hvalid Hnode Hptr)
    as [current [Hlookup Hin]].
  set (remove_frame := sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    sem_pend_remove_call_frame sg resumed eid current tid node **
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    task_tcb_init_stack_capsules environment resumed ** unmap_table_rep sg ** perr # UChar |->_ ** frame).
  set (pre := event_task_remove_pre (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (node.(curPrio) / 8) (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (node.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState))).
  assert (Hsplit : task_tcb_init_stack_restore_input environment critical sg call saved acquired resumed **
      unmap_table_rep sg ** perr # UChar |->_ ** frame |--
    coq_prop (task_stack_live_coverage resumed.(TskState) (task_stack_call_active_key call)) &&
    (pre ** remove_frame)).
  { unfold task_tcb_init_stack_restore_input, pre, remove_frame; Intros.
    sep_apply_l_atomic (sem_pend_cleanup_split sg resumed tid node Hvalid Hcurrent Hnode).
    sep_apply_l_atomic (sem_pend_resume_split_remove_call sg resumed eid tid node current Hentry Hlookup Hlayout).
    entailer!. }
  destruct (Hsplit before Hpre) as [Hcoverage Hremove_pre].
  unfold pre in Hremove_pre.
  destruct (sem_pend_timeout_remove_source _ _ _ _ _ _ _ _ remove_frame before Hremove_pre)
    as [removed [Hremove Hpost]].
  pose proof (sem_pend_observed_resume_cleanup_timeout (Some environment) critical sg original mask initial
    observed eid timeout resumed tid node current Horigin Hstatus Hlookup) as Hcleanup.
  exists (event_task_remove_state resumed eid current tid node), (task_set_event_ptr node None), removed.
  split.
  - unfold sem_pend_resume_branch_fragment; rewrite Hstatus.
    split; [exact (proj1 Hreads)|]. split; [exact (proj2 Hreads)|]. exists current; tauto.
  - split; [exact Hcleanup|].
    match type of Hpost with ?P removed => match goal with |- ?Q removed => assert (Hmerge : P |-- Q) end end.
    { unfold remove_frame; sepcon_assoc_change.
      sep_apply_l_atomic (sem_pend_observed_timeout_remove_cleanup (Some environment) critical sg original mask
        initial observed eid timeout resumed tid node current Horigin Hstatus Hlookup Hlayout).
      unfold task_tcb_init_stack_capsules.
      sep_apply_l_atomic (sem_pend_task_field_update_stacks _ _ _ environment.(task_stack_call_continuations)
        resumed.(TskState) (task_stack_call_active_key call) tid node (task_set_event_ptr node None)
        Hnode eq_refl eq_refl Hcoverage).
      unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_capsules.
      cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!. }
    exact (Hmerge removed Hpost).
Qed.

(** Consume a proved second-Save phase output, including the same original
    wait. The only three pending statuses are dispatched on the actual
    byte, and every branch reaches the public return on the same heap
    chain. The exposed Restore input also permits the already proved IRQ
    returning families to consume this exact cleanup checkpoint. *)
Lemma sem_pend_saved_wait_return_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid pevent timeout waiting call scheduled saved perr
  (frame : Assertion) before X,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  (sem_pend_phase_save_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
     environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
     critical sg call mask saved scheduled ** unmap_table_rep sg ** perr # UChar |->_ ** frame) before ->
  exists returned resumed node cleaning clean_node branch_heap cleaned,
    sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot) node before branch_heap /\
    sem_pend_cleanup_fragment sg perr
      (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) branch_heap cleaned /\
    sem_pend_checkpoint_result (Some environment) critical sg original pevent timeout initial
      (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend))))
      (event_pend_cleanup_state sg false cleaning original.(os_sched_call_stack).(stackLeaseSlot) clean_node) /\
    kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved /\
    (task_tcb_init_stack_restore_input environment critical sg returned saved resumed
      (event_pend_cleanup_state sg false cleaning original.(os_sched_call_stack).(stackLeaseSlot) clean_node) **
      unmap_table_rep sg ** perr # UChar |->
        encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend))) ** frame) cleaned /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor cleaned written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
      (sem_pend_stack_call_post environment.(task_stack_call_external)
        environment.(task_stack_call_platform) (Some environment) critical sg original mask
        pevent timeout perr initial X ** frame) after).
Proof.
  intros environment critical arch restore sg original mask initial observed eid pevent timeout waiting call scheduled
    saved perr frame before X Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec Hpre.
  assert (Hview : sem_pend_phase_save_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
      critical sg call mask saved scheduled ** unmap_table_rep sg ** perr # UChar |->_ ** frame |--
    EX returned resumed node,
      coq_prop (sem_pend_observed_resume_origin (Some environment) critical sg original mask initial observed
        eid timeout resumed original.(os_sched_call_stack).(stackLeaseSlot) node /\
        kernel_stack_call_same_call returned original /\ interrupt_saved_value mask saved) &&
      (task_tcb_init_stack_restore_input environment critical sg returned saved resumed resumed **
        unmap_table_rep sg ** perr # UChar |->_ ** frame)).
  { unfold sem_pend_phase_save_output; Intros returned resumed.
    assert (Hwait : sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed
      eid timeout waiting returned resumed) by tauto.
    destruct (sem_pend_wait_selected_resume_origin _ _ _ _ _ _ _ _ _ _ _ _ Hwait) as [node Horigin].
    assert (Hsame : kernel_stack_call_same_call returned original).
    { destruct Hwait as [[owned [Howned [Hsame _]]] _]; exact Hsame. }
    assert (Hcall : kernel_stack_call_same_call returned call)
      by (unfold sem_pend_stack_save_observation in *; tauto).
    assert (Hsaved : interrupt_saved_value mask saved)
      by (unfold sem_pend_stack_save_observation in *; tauto).
    pose proof Hcall as [Hi [Ho Hstack]].
    Exists returned resumed node.
    unfold task_tcb_init_stack_restore_input, sem_pend_optional_stack_resources.
    rewrite Hi, Ho; entailer!. }
  destruct (Hview before Hpre) as [returned [resumed [node [[Horigin [Hsame Hsaved]] Hready]]]].
  destruct (sem_pend_observed_resume_branch_source environment critical sg original mask initial observed eid timeout
    resumed original.(os_sched_call_stack).(stackLeaseSlot) node returned saved resumed perr frame before
    Horigin Hlayout Hready) as [cleaning [clean_node [branch_heap [Hbranch [Hcleanup Hbranch_post]]]]].
  assert (Hcleanup_pre :
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved resumed **
     os_sched_context_resources environment.(task_stack_call_external) returned ** UCOS2_inv sg cleaning **
     sem_pend_optional_stack_resources environment.(task_stack_call_external)
       environment.(task_stack_call_platform) (Some environment) returned cleaning **
     perr # UChar |->_ ** unmap_table_rep sg ** frame) branch_heap).
  { match type of Hbranch_post with ?P branch_heap => match goal with |- ?Q branch_heap =>
      assert (Horder : P |-- Q) by
        (unfold task_tcb_init_stack_restore_input, sem_pend_optional_stack_resources; entailer!) end end.
    exact (Horder branch_heap Hbranch_post). }
  destruct (sem_pend_observed_cleanup_restore_source environment critical arch restore sg original mask initial
    observed eid pevent timeout cleaning original.(os_sched_call_stack).(stackLeaseSlot) clean_node
    (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend))))
    returned saved resumed perr frame branch_heap X Hnonnull Haddress Hid Hslot Hordered Hcleanup Hsaved Hsame Hexec
    Hcleanup_pre) as [cleaned [Hstores [Hresult [Hrestore Htail]]]].
  exists returned, resumed, node, cleaning, clean_node, branch_heap, cleaned; tauto.
Qed.

(** An actual uninterrupted second Save produces the phase output above.
    This theorem joins it immediately to all result branches and final
    Restore. It assumes source transitions, with no future ready/post
    premise added to the public admission. *)
Lemma sem_pend_second_save_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid pevent timeout waiting call state perr (frame : Assertion) X
  registers before final_registers acquired saved_heap,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed eid timeout waiting call state ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_stack_save_input environment.(task_stack_call_external) environment.(task_stack_call_platform)
     (Some environment) critical sg call mask state ** unmap_table_rep sg ** perr # UChar |->_ ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists resumed node branch_heap cleaned,
    sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot) node saved_heap branch_heap /\
    sem_pend_cleanup_fragment sg perr
      (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) branch_heap cleaned /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor cleaned written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
      (sem_pend_stack_call_post environment.(task_stack_call_external)
        environment.(task_stack_call_platform) (Some environment) critical sg original mask
        pevent timeout perr initial X ** frame) after).
Proof.
  intros environment critical arch save restore sg original mask initial observed eid pevent timeout waiting call state
    perr frame X registers before final_registers acquired saved_heap Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec
    Hselected Hreturn Hcpsr Hmask Hpre Hsave.
  assert (Hphase_pre :
    (sem_pend_phase_save_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
      critical sg call mask state ** unmap_table_rep sg ** (perr # UChar |->_ ** frame)) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before =>
      assert (Hpack : P |-- Q) by (unfold sem_pend_phase_save_input, sem_pend_save_phase_pre; entailer!) end end.
    exact (Hpack before Hpre). }
  destruct (sem_pend_uninterrupted_save_phase environment critical arch save
    (SemPendWaitPhase original mask initial observed eid timeout waiting) sg call mask state
    registers before final_registers acquired saved_heap (perr # UChar |->_ ** frame)
    Hreturn Hcpsr Hmask Hphase_pre Hsave) as [Hsource [Hstate Hsaved]].
  split; [exact Hsource|]. split; [exact Hstate|].
  assert (Hordered_save :
    (sem_pend_phase_save_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
      critical sg call mask final_registers.(kernel_save_r0) state **
      unmap_table_rep sg ** perr # UChar |->_ ** frame) saved_heap).
  { match type of Hsaved with ?P saved_heap => match goal with |- ?Q saved_heap =>
      assert (Hpack : P |-- Q) by entailer! end end; exact (Hpack saved_heap Hsaved). }
  destruct (sem_pend_saved_wait_return_source environment critical arch restore sg original mask initial observed eid
    pevent timeout waiting call state final_registers.(kernel_save_r0) perr frame saved_heap X
    Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec Hordered_save)
    as [returned [resumed [node [cleaning [clean_node [branch_heap [cleaned
      [Hbranch [Hcleanup [Hcheckpoint [Hreturned_same [Hsaved_mask [Hrestore Htail]]]]]]]]]]]]].
  exists resumed, node, branch_heap, cleaned; tauto.
Qed.

(** Compose the real enabled/no-switch Scheduler body with the second
    Save, all pending-result branches, and final Restore. These are source
    family guards at the Scheduler entry, already established by the
    same-priority first-Restore producer. They are not public admission
    conditions. Locked/nested and selected-switch families keep their own
    source proofs rather than being asserted to have this guard. *)
Lemma sem_pend_nonswitch_wait_return_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid pevent timeout waiting call state perr (frame : Assertion) X
  registers before final_registers acquired saved_heap,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed -> event_object_layout_prop sg eid ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg original pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call state ->
  kernel_call_task_source call state -> sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true -> os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (task_tcb_init_stack_covered_save_input environment critical sg call mask state **
    unmap_table_rep sg ** (perr # UChar |->_ ** frame)) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\ exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall sched_cursor sched_written sched_middle sched_final scheduled_heap,
      sched_cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask sched_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore sched_cursor prefix_heap sched_written sched_middle ->
      armv7a_restore_suffix_transition restore sched_written sched_middle sched_final scheduled_heap ->
      kernel_call_restore_uninterrupted_execution arch sched_cursor prefix_heap sched_final scheduled_heap /\
      (forall second second_final second_acquired second_heap,
        second.(kernel_save_return_word) = None -> valid_os_cpu_sr second.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask second.(kernel_save_cpsr) = mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr second) (os_sched_prefix_state state)
          scheduled_heap second_final second_acquired second_heap ->
        kernel_call_save_uninterrupted_execution arch second (os_sched_prefix_state state)
          scheduled_heap second_final second_acquired second_heap /\
        second_acquired = os_sched_prefix_state state /\
        exists resumed node branch_heap cleaned,
          sem_pend_resume_branch_fragment sg resumed eid original.(os_sched_call_stack).(stackLeaseSlot)
            node second_heap branch_heap /\
          sem_pend_cleanup_fragment sg perr
            (encode_os_err_code (sem_pend_resume_error (encode_pend_status node.(statPend)))) branch_heap cleaned /\
          (forall cursor written middle final_cursor after,
            cursor.(kernel_restore_r0) = second_final.(kernel_save_r0) ->
            armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
            armv7a_restore_prefix_transition restore cursor cleaned written middle ->
            armv7a_restore_suffix_transition restore written middle final_cursor after ->
            kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
            (sem_pend_stack_call_post environment.(task_stack_call_external)
              environment.(task_stack_call_platform) (Some environment) critical sg original mask
              pevent timeout perr initial X ** frame) after))).
Proof.
  intros environment critical arch save restore sg original mask initial observed eid pevent timeout waiting call state
    perr frame X registers before final_registers acquired saved_heap Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec
    Hwait Hsource Hcache Hen Hnoswitch Hnonempty Hreturn Hcpsr Hmask Hpre Hsave.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hfacts : P |-- coq_prop (UCOS2_state_inv sg state) && TT)
      by (unfold task_tcb_init_stack_covered_save_input; entailer!; intros ? ?; exact I) end.
    exact (proj1 (Hfacts before Hpre)). }
  destruct (sem_pend_nonswitch_scheduler_phase_source environment critical arch save restore sg original mask
    initial observed eid timeout waiting call state registers before final_registers acquired saved_heap
    (perr # UChar |->_ ** frame) Hwait Hreturn Hcpsr Hmask Hnoswitch ltac:(intros; exact Hnonempty) Hpre Hsave)
    as [Hsave_run [Hstate [prefix_heap [Hprefix Hscheduler]]]].
  split; [exact Hsave_run|]. split; [exact Hstate|]. exists prefix_heap; split; [exact Hprefix|].
  intros sched_cursor sched_written sched_middle sched_final scheduled_heap Hsr0 Hsmask Hsprefix Hssuffix.
  destruct (Hscheduler sched_cursor sched_written sched_middle sched_final scheduled_heap Hsr0 Hsmask Hsprefix Hssuffix)
    as [Hsrun [Hwait_after [Hscheduled Hphase]]].
  split; [exact Hsrun|].
  intros second second_final second_acquired second_heap Hsecond_return Hsecond_cpsr Hsecond_mask Hsecond.
  pose proof (sem_pend_enabled_nonswitch_wait_selected environment critical sg original mask initial observed eid timeout
    waiting call state Hwait_after Hvalid Hsource Hcache Hen Hnoswitch Hnonempty) as Hselected.
  assert (Hsecond_input :
    (sem_pend_stack_save_input environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg call mask (os_sched_prefix_state state) **
      unmap_table_rep sg ** perr # UChar |->_ ** frame) scheduled_heap).
  { match type of Hscheduled with ?P scheduled_heap => match goal with |- ?Q scheduled_heap =>
      assert (Hpack : P |-- Q) end end.
    { rewrite sem_pend_stack_save_input_owned.
      unfold task_tcb_init_stack_covered_save_input, task_tcb_init_stack_save_input,
        task_tcb_init_stack_covered_capsules, task_tcb_init_stack_capsules; entailer!. }
    exact (Hpack scheduled_heap Hscheduled). }
  exact (sem_pend_second_save_return_source environment critical arch save restore sg original mask initial observed eid
    pevent timeout waiting call (os_sched_prefix_state state) perr frame X second scheduled_heap second_final
    second_acquired second_heap Hnonnull Haddress Hid Hslot Hlayout Hordered Hexec Hselected Hsecond_return
    Hsecond_cpsr Hsecond_mask Hsecond_input Hsecond).
Qed.

