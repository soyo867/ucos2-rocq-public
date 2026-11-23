Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_world_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_task_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_return_observation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The callable scheduler return preserves the CURRENT world and the
    ordinary invocation source supplied by the wait prefix. Neither an
    old flat scheduler history nor readiness is needed to enter Save.
    This is a consumer of the modular interface; complete source branch
    producers of that interface remain separate from total coverage. *)
Lemma sem_pend_sched_return_save_input : forall environment critical sg original mask waiting,
  kernel_call_task_source original waiting ->
  os_sched_stack_return_post environment kernel_program_inv sg original mask waiting |--
  EX returned current,
    coq_prop (kernel_stack_call_same_call returned original /\
      kernel_call_task_source returned current /\ UCOS2_state_inv sg current) &&
    (task_tcb_init_stack_save_input environment critical sg returned mask current ** unmap_table_rep sg).
Proof.
  intros environment critical sg original mask waiting Hsource.
  unfold os_sched_stack_return_post, kernel_stack_call_history_restore_post; Intros returned current.
  assert (Hsame : kernel_stack_call_same_call returned original) by tauto.
  assert (Hreturned : kernel_call_task_source returned current) by tauto.
  assert (Hactive : task_stack_call_active_key original = task_stack_call_active_key returned).
  { unfold task_stack_call_active_key; destruct Hsame as [Hi [Ho Hs]]; rewrite Ho; reflexivity. }
  rewrite Hactive, <- task_tcb_init_stack_save_input_closed_world.
  Exists returned current; unfold task_tcb_init_stack_save_input; entailer!.
Qed.

(** The second Save's no-IRQ branch consumes that SAME returned heap.
    The result deliberately stops short of resume_registration: physical
    current/lease ownership alone cannot prove that a waiter was woken. *)
Lemma sem_pend_sched_return_save_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask waiting before (frame : Assertion),
  kernel_call_task_source original waiting ->
  (os_sched_stack_return_post environment kernel_program_inv sg original mask waiting ** frame) before ->
  exists returned current,
    kernel_stack_call_same_call returned original /\ kernel_call_task_source returned current /\
    (forall registers final_registers acquired after,
      registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current before
        final_registers acquired after ->
      kernel_call_save_uninterrupted_execution arch registers current before final_registers acquired after /\
      acquired = current /\
      kernel_call_save_history environment critical sg returned current returned acquired /\
      kernel_call_task_source returned acquired /\
      (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
        (task_stack_call_active_key returned) returned final_registers.(kernel_save_r0) acquired acquired ** frame) after).
Proof.
  intros environment critical arch save sg original mask waiting before frame Hsource Hpre.
  assert (Hopen : os_sched_stack_return_post environment kernel_program_inv sg original mask waiting ** frame |--
    EX returned current,
      coq_prop (kernel_stack_call_same_call returned original /\
        kernel_call_task_source returned current /\ UCOS2_state_inv sg current) &&
      (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
        (task_stack_call_active_key returned) returned mask current ** frame)).
  { sep_apply_l_atomic (sem_pend_sched_return_save_input environment critical sg original mask waiting Hsource).
    Intros returned current; Exists returned current.
    rewrite <- task_tcb_init_stack_save_input_closed_world; entailer!. }
  destruct (Hopen before Hpre) as [returned [current [[Hsame [Hreturned Hvalid]] Howned]]].
  exists returned, current; split; [exact Hsame|]. split; [exact Hreturned|].
  intros registers final_registers acquired after Hreturn Hcpsr Hmask Hrun.
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  match type of Howned with ?P before => assert (Horder : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      returned (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
      (task_stack_call_active_key returned) current ** frame)) end.
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; unfold kernel_stack_call_closed; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg returned
    (kernel_save_read_cpsr registers) current before final_registers acquired after _
    Hsaved (Horder before Howned) Hrun) as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  split.
  - unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hrun).
  - split; [exact Hstate|]. subst acquired; split.
    + eapply KernelCallSaveUninterrupted; eassumption.
    + split; [exact Hreturned|].
      match type of Hafter with ?P after => match goal with |- ?Q after =>
        assert (Hclose : P |-- Q) by (unfold kernel_stack_call_masked; entailer!) end end.
      exact (Hclose after Hafter).
Qed.

(** The actual cells read after SemPend's second Save, with the current
    strong stack map retained. This is a resource postcondition, not a
    new caller premise or an extra lifecycle/ABI record. *)
Definition sem_pend_resume_stack_resources environment critical sg call saved state eid tid node : Assertion :=
  coq_prop (sem_pend_resume_entry sg state eid tid node /\
    task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg
     call.(os_sched_call_invocation) call.(os_sched_call_origin) saved state **
   os_sched_context_resources environment.(task_stack_call_external) call **
   sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
   tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status node.(stat))) **
   tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status node.(statPend))) **
   tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
   sem_pend_cleanup_frame sg state tid node **
   armv7a_task_stack_continuations environment.(task_stack_call_continuations)
     state.(TskState) state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg).

(** Reassemble the read-only view before executing the chosen cleanup
    arm. The same TCB is merged unchanged; this is not a cleanup effect. *)
Lemma sem_pend_resume_stack_merge : forall environment critical sg call saved state eid tid node,
  sem_pend_resume_stack_resources environment critical sg call saved state eid tid node |--
  coq_prop (sem_pend_resume_entry sg state eid tid node) &&
  kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key call) call saved state state.
Proof.
  intros; unfold sem_pend_resume_stack_resources; Intros.
  assert (Hresume : sem_pend_resume_entry sg state eid tid node) by tauto.
  destruct Hresume as [Hvalid [Hcurrent [Hnode [Hregistration Hready]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold sem_pend_cleanup_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic (sem_pend_tcb_merge_cleanup_unchanged sg tid node).
  assert (Hmerge : tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg node) **
    store_prio_tbl sg state.(TskState).(prioTbl) ** sem_post_task_frame sg state.(TskState) tid |--
    task_public_storage sg state.(TskState)).
  { rewrite task_slot_addr_tcb64 by assumption.
    rewrite <- used_task_rep_tcb64 by assumption.
    eapply derivable1_trans; [|apply task_public_storage_merge_task; exact Hnode].
    unfold sem_post_task_frame, task_public_storage_without_task,
      task_public_storage_without_used_map; entailer!. }
  sep_apply_l_atomic Hmerge.
  unfold kernel_stack_call_masked, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched,
    sem_pend_sched_without_current, sched_raw_rep, sched_physical_rep.
  rewrite Hcurrent; cbn [encode_task_link]; unfold sem_pend_resume_entry; entailer!.
Qed.

(** The two real cleanup mutations below leave the parked map, generation
    and saved SP unchanged. Reindex both coverage and the strong entries;
    retaining the old-state entries in an opaque frame would be too weak
    for the next callable runtime interface. *)
Lemma sem_pend_task_field_update_stacks : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks active tid old current,
  tasks.(inUsedTaskStates) tid = Some old ->
  current.(taskGeneration) = old.(taskGeneration) -> current.(tcbStkPtr) = old.(tcbStkPtr) ->
  task_stack_live_coverage tasks active ->
  armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) |--
  coq_prop (task_stack_live_coverage (glob_task_set_usedtask tasks tid current) active) &&
  armv7a_task_stack_continuations abi (glob_task_set_usedtask tasks tid current) tasks.(parkedTaskStacks).
Proof.
  intros external platform port abi tasks active tid old current Hold Hgen Hsp Hcoverage.
  assert (Hnodes : forall slot node,
    (glob_task_set_usedtask tasks tid current).(inUsedTaskStates) slot = Some node ->
    exists previous, tasks.(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode; cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; auto.
    - exists node; auto. }
  assert (Hcovered : task_stack_live_coverage (glob_task_set_usedtask tasks tid current) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := tasks);
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hg Hp]]].
    exists previous; auto. }
  assert (Hstacks : armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi (glob_task_set_usedtask tasks tid current) tasks.(parkedTaskStacks)).
  { apply armv7a_task_stack_continuations_reindex.
    intros key payload node Hpayload Hnode Hg; exact (Hnodes _ _ Hnode). }
  sep_apply_l_atomic Hstacks; entailer!.
Qed.

Lemma sem_pend_cleanup_stack_merge : forall environment critical sg call saved acquired state tid node,
  sem_pend_cleanup_entry sg state tid node ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources environment.(task_stack_call_external) call **
  sem_pend_cleanup_cells sg state tid node **
  armv7a_task_stack_continuations environment.(task_stack_call_continuations)
    state.(TskState) state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg |--
  task_tcb_init_stack_restore_input environment critical sg call saved acquired
    (event_pend_cleanup_state sg false state tid node) ** unmap_table_rep sg.
Proof.
  intros environment critical sg call saved acquired state tid node Hentry Hcoverage.
  pose proof Hentry as [Hvalid [Hcurrent [Hnode _]]].
  pose proof (sem_pend_task_field_update_stacks _ _ _ environment.(task_stack_call_continuations)
    state.(TskState) (task_stack_call_active_key call) tid node
    (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) false node)
    Hnode ltac:(destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity)
    ltac:(destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity) Hcoverage) as Hstacks.
  unfold sem_pend_cleanup_cells; sep_apply_l_atomic (sem_pend_cleanup_merge sg state tid node Hentry).
  sep_apply_l_atomic Hstacks.
  unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_capsules.
  cbn [event_pend_cleanup_state replace_TskS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!.
Qed.

(** These are local branch facts. They use the actual resumed wait
    registration, not the old public program's flat scheduling history. *)
Lemma sem_pend_resume_cleanup_entry : forall sg state eid tid node,
  sem_pend_resume_entry sg state eid tid node -> node.(statPend) <> PendTimeout ->
  sem_pend_cleanup_entry sg state tid node /\
  sem_pend_resume_critical sg eid state (sem_pend_resume_error (encode_pend_status node.(statPend)))
    (event_pend_cleanup_state sg false state tid node).
Proof.
  intros sg state eid tid node [Hvalid [Hcurrent [Hnode [[Hmulti [Hflag Hregistration]] Hready]]]] Hstatus.
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]. split; [exact Hcurrent|]. split; [exact Hnode|].
    split; [destruct node.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]. split; assumption.
  - exists tid, node; split; [exact Hcurrent|]. split; [exact Hnode|]. split; [reflexivity|].
    destruct node.(statPend); reflexivity || contradiction.
Qed.

Lemma sem_pend_timeout_cleanup_entry : forall sg state eid tid node event,
  sem_pend_resume_entry sg state eid tid node -> node.(statPend) = PendTimeout ->
  mutex_query_lookup state eid event ->
  sem_pend_cleanup_entry sg (event_task_remove_state state eid event tid node) tid (task_set_event_ptr node None) /\
  sem_pend_resume_critical sg eid state OS_ERR_TIMEOUT
    (event_pend_cleanup_state sg false (event_task_remove_state state eid event tid node)
      tid (task_set_event_ptr node None)).
Proof.
  intros sg state eid tid node event [Hvalid [Hcurrent [Hnode [[Hmulti [Hflag Hregistration]] Hready]]]] Hstatus Hevent.
  rewrite Hstatus in Hregistration.
  destruct (sem_pend_resume_timeout_event sg state eid tid node Hvalid Hnode Hregistration)
    as [found [Hfound Hin]].
  assert (found = event) by congruence; subst found.
  split.
  - unfold sem_pend_cleanup_entry; split.
    + eapply UCOS2_event_task_remove_preserves_validity; eassumption.
    + split; [exact Hcurrent|]. split.
      * cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
        rewrite Z.eqb_refl; reflexivity.
      * split; [reflexivity|]. split; [exact Hmulti|]. split; assumption.
  - exists tid, node; split; [exact Hcurrent|]. split; [exact Hnode|].
    rewrite Hstatus; split; [reflexivity|]. exists event; auto.
Qed.

(** Exact timeout caller frame across its ordinary, already proved
    EventTaskRemove contract. It contains no duplicate kernel world. *)
Definition sem_pend_timeout_call_frame environment critical sg call saved state eid tid node event : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid ** sem_pend_remove_call_frame sg state eid event tid node **
  critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved state ** os_sched_context_resources environment.(task_stack_call_external) call **
  armv7a_task_stack_continuations environment.(task_stack_call_continuations)
    state.(TskState) state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg.

Lemma sem_pend_timeout_call_stack_merge : forall environment critical sg call saved state eid tid node event,
  sem_pend_resume_entry sg state eid tid node -> node.(statPend) = PendTimeout ->
  mutex_query_lookup state eid event -> event_object_layout_prop sg eid ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (node.(curPrio) / 8) (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))
    (encode_event_wait_tbl_at_or event.(waitList) state.(TskState) (node.(curPrio) / 8))
    (encode_event_wait_grp event.(waitList) state.(TskState)) **
  sem_pend_timeout_call_frame environment critical sg call saved state eid tid node event |--
  kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key call) call saved state (event_task_remove_state state eid event tid node).
Proof.
  intros environment critical sg call saved state eid tid node event Hresume Hstatus Hevent Hlayout Hcoverage.
  pose proof Hresume as [Hvalid [Hcurrent [Hnode _]]].
  pose proof (sem_pend_task_field_update_stacks _ _ _ environment.(task_stack_call_continuations)
    state.(TskState) (task_stack_call_active_key call) tid node (task_set_event_ptr node None)
    Hnode eq_refl eq_refl Hcoverage) as Hstacks.
  unfold sem_pend_timeout_call_frame; sepcon_assoc_change.
  sep_apply_l_atomic (sem_pend_remove_call_merge sg state eid event tid node Hresume Hstatus Hevent Hlayout).
  sep_apply_l_atomic Hstacks.
  unfold kernel_stack_call_masked, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
  cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!.
Qed.

(** Actual common stores and final Restore, with the current strong world
    returned to the caller. This endpoint is shared by success/abort and
    by timeout AFTER its separately checked EventTaskRemove call. *)
Definition sem_pend_cleanup_stack_return environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call saved state tid node perr error before (frame : Assertion) : Prop :=
  exists cleaned,
    sem_pend_cleanup_fragment sg perr error before cleaned /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor cleaned written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor cleaned final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (sem_pend_restore_call_post environment critical sg call (armv7a_irq_fiq_mask saved)
        (event_pend_cleanup_state sg false state tid node) perr error ** frame) after).

Lemma sem_pend_cleanup_stack_return_source : forall environment critical arch restore
  sg call saved acquired state tid node perr error before (frame : Assertion),
  sem_pend_cleanup_entry sg state tid node -> 0 <= error < 256 ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key call) call saved acquired state ** perr # UChar |->_ ** frame) before ->
  sem_pend_cleanup_stack_return environment critical arch restore sg call saved state tid node
    perr error before frame.
Proof.
  intros environment critical arch restore sg call saved acquired state tid node perr error before frame
    Hentry Hrange Hpre.
  set (rest := critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources environment.(task_stack_call_external) call **
    armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      state.(TskState) state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (UCOS2_inv sg state ** perr # UChar |->_ ** rest)) end.
  { unfold kernel_stack_call_masked, kernel_stack_inv, rest; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (sem_pend_cleanup_stores_source sg state tid node perr error rest before Hentry Hrange Howned)
    as [cleaned [Hstores Hcells]].
  exists cleaned; split; [exact Hstores|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  match type of Hcells with ?P cleaned => assert (Hclose : P |--
    task_tcb_init_stack_restore_input environment critical sg call saved acquired
      (event_pend_cleanup_state sg false state tid node) ** unmap_table_rep sg **
    (perr # UChar |-> error ** frame)) end.
  { unfold rest; sepcon_assoc_change.
    sep_apply_l_atomic (sem_pend_cleanup_stack_merge environment critical sg call saved acquired state tid node
      Hentry Hcoverage); entailer!. }
  destruct (sem_pend_wait_first_restore_source environment critical arch restore sg call saved acquired
    (event_pend_cleanup_state sg false state tid node) cursor cleaned written middle final_cursor after
    (perr # UChar |-> error ** frame) Hr0 Hmask (Hclose cleaned Hcells) Hprefix Hsuffix)
    as [Hsource [Hreturn [Hhistory Hreturned]]].
  split; [exact Hsource|]. split; [exact Hreturn|].
  match type of Hreturned with ?P after => match goal with |- ?Q after =>
    assert (Hpost : P |-- Q) end end.
  { sepcon_assoc_change.
    sep_apply_l_atomic (sem_pend_restore_call_post_intro environment critical sg call call
      (armv7a_irq_fiq_mask saved) (event_pend_cleanup_state sg false state tid node)
      (event_pend_cleanup_state sg false state tid node) perr error Hhistory
      ltac:(unfold kernel_stack_call_same_call; auto)); entailer!. }
  exact (Hpost after Hreturned).
Qed.

(** The C switch and all three arms. Timeout exposes the exact pre/post
    of the existing EventTaskRemove call and its disjoint frame; its
    callback then executes the same common stores and final Restore.
    This is a caller source continuation, NOT a new callee Ensure. *)
Definition sem_pend_resume_stack_return environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call saved state eid tid node perr before (frame : Assertion) : Prop :=
  (pointer_load sg.(g_OSTCBCur) (task_slot_addr sg tid) before /\
    uchar_load (tcb_field_address (task_slot_addr sg tid) TCBStatPend)
      (encode_pend_status node.(statPend)) before) /\
  match node.(statPend) with
  | PendTimeout => exists event,
      mutex_query_lookup state eid event /\
      sem_pend_resume_critical sg eid state OS_ERR_TIMEOUT
        (event_pend_cleanup_state sg false (event_task_remove_state state eid event tid node)
          tid (task_set_event_ptr node None)) /\
      (event_task_remove_pre (task_slot_addr sg tid)
        &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
        &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
        (node.(curPrio) / 8) (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))
        (encode_event_wait_tbl_at_or event.(waitList) state.(TskState) (node.(curPrio) / 8))
        (encode_event_wait_grp event.(waitList) state.(TskState)) **
       sem_pend_timeout_call_frame environment critical sg call saved state eid tid node event **
       perr # UChar |->_ ** frame) before /\
      (forall removed,
        (event_task_remove_post (task_slot_addr sg tid)
          &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
          &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
          (node.(curPrio) / 8) (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio))
          (encode_event_wait_tbl_at_or event.(waitList) state.(TskState) (node.(curPrio) / 8))
          (encode_event_wait_grp event.(waitList) state.(TskState)) **
         sem_pend_timeout_call_frame environment critical sg call saved state eid tid node event **
         perr # UChar |->_ ** frame) removed ->
        sem_pend_cleanup_stack_return environment critical arch restore sg call saved
          (event_task_remove_state state eid event tid node) tid (task_set_event_ptr node None)
          perr 10 removed frame)
  | status =>
      sem_pend_resume_critical sg eid state (sem_pend_resume_error (encode_pend_status status))
        (event_pend_cleanup_state sg false state tid node) /\
      sem_pend_cleanup_stack_return environment critical arch restore sg call saved state tid node
        perr (encode_os_err_code (sem_pend_resume_error (encode_pend_status status))) before frame
  end.

Lemma sem_pend_resume_stack_return_source : forall environment critical arch restore
  sg call saved state eid tid node perr before (frame : Assertion),
  event_object_layout_prop sg eid ->
  (sem_pend_resume_stack_resources environment critical sg call saved state eid tid node **
    perr # UChar |->_ ** frame) before ->
  sem_pend_resume_stack_return environment critical arch restore sg call saved state eid tid node perr before frame.
Proof.
  intros environment critical arch restore sg call saved state eid tid node perr before frame Hlayout Hpre.
  match type of Hpre with ?P before => assert (Hfacts : P |--
    coq_prop (sem_pend_resume_entry sg state eid tid node /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) && TT) end.
  { unfold sem_pend_resume_stack_resources; entailer!; intros ? ?; exact I. }
  destruct (proj1 (Hfacts before Hpre)) as [Hresume Hcoverage].
  assert (Howned : (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
    critical sg (task_stack_call_active_key call) call saved state state ** perr # UChar |->_ ** frame) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hmerge : P |-- Q) end end.
    { sep_apply_l_atomic (sem_pend_resume_stack_merge environment critical sg call saved state eid tid node); entailer!. }
    exact (Hmerge before Hpre). }
  unfold sem_pend_resume_stack_return; split.
  - split.
    + eapply framed_pointer_store_load.
      match type of Hpre with ?P before => assert (Hread : P |--
        sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid ** TT) end.
      { unfold sem_pend_resume_stack_resources; entailer!; intros ? ?; exact I. }
      exact (Hread before Hpre).
    + eapply framed_uchar_store_load.
      match type of Hpre with ?P before => assert (Hread : P |--
        tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status node.(statPend) ** TT) end.
      { unfold sem_pend_resume_stack_resources; cbn [tcb_cell]; entailer!; intros ? ?; exact I. }
      exact (Hread before Hpre).
  - destruct node.(statPend) eqn:Hstatus.
    + destruct (sem_pend_resume_cleanup_entry sg state eid tid node Hresume ltac:(congruence)) as [Hentry Hresult].
      rewrite Hstatus in Hresult; split; [exact Hresult|].
      eapply sem_pend_cleanup_stack_return_source; [exact Hentry|cbn; lia|exact Howned].
    + pose proof Hresume as [Hvalid [Hcurrent [Hnode [[Hmulti [Hflag Hregistration]] Hready]]]].
      rewrite Hstatus in Hregistration.
      destruct (sem_pend_resume_timeout_event sg state eid tid node Hvalid Hnode Hregistration)
        as [event [Hevent Hin]].
      destruct (sem_pend_timeout_cleanup_entry sg state eid tid node event Hresume Hstatus Hevent)
        as [Hentry Hresult].
      exists event; split; [exact Hevent|]. split; [exact Hresult|]. split.
      * match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hcall : P |-- Q) end end.
        { unfold sem_pend_resume_stack_resources; Intros; sepcon_assoc_change.
          sep_apply_l_atomic (sem_pend_resume_split_remove_call sg state eid tid node event Hresume Hevent Hlayout).
          unfold sem_pend_timeout_call_frame; entailer!. }
        exact (Hcall before Hpre).
      * intros removed Hpost.
        eapply sem_pend_cleanup_stack_return_source with (acquired := state); [exact Hentry|lia|].
        match type of Hpost with ?P removed => match goal with |- ?Q removed => assert (Hmerge : P |-- Q) end end.
        { sep_apply_l_atomic (sem_pend_timeout_call_stack_merge environment critical sg call saved state eid tid node event
            Hresume Hstatus Hevent Hlayout Hcoverage); entailer!. }
        exact (Hmerge removed Hpost).
    + destruct (sem_pend_resume_cleanup_entry sg state eid tid node Hresume ltac:(congruence)) as [Hentry Hresult].
      rewrite Hstatus in Hresult; split; [exact Hresult|].
      eapply sem_pend_cleanup_stack_return_source; [exact Hentry|cbn; lia|exact Howned].
Qed.

(** Complete the local final-Restore / next-Save branch on one heap.
    The resumed waiting task was already established by the actual
    selector, not by the CPU token. An intervening IRQ requires its own
    current source world and is deliberately not represented as a frame. *)
Lemma sem_pend_masked_resume_restore_save : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call saved entry state eid tid node cursor before written middle final_cursor returned_heap
  registers final_registers acquired after (frame : Assertion),
  sem_pend_resume_entry sg state eid tid node ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
     critical sg (task_stack_call_active_key call) call saved entry state ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor returned_heap ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state returned_heap
    final_registers acquired after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor returned_heap /\
  kernel_call_save_uninterrupted_execution arch registers state returned_heap final_registers acquired after /\
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  (sem_pend_resume_stack_resources environment critical sg call
    final_registers.(kernel_save_r0) acquired eid tid node ** frame) after.
Proof.
  intros environment critical arch restore save sg call saved entry state eid tid node cursor before
    written middle final_cursor returned_heap registers final_registers acquired after frame
    Hresume Hr0 Hmask Hreturn Hvalid Hnextmask Hpre Hprefix Hsuffix Hsave.
  assert (Hopen : kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
      critical sg (task_stack_call_active_key call) call saved entry state ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv
       sg (task_stack_call_active_key call) state ** frame)).
  { unfold kernel_stack_call_masked; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call saved
    entry cursor before written middle final_cursor returned_heap _ Hr0 Hmask
    (Hopen before Hpre) Hprefix Hsuffix) as [Hrestore [Hlr [Hmemory Hclosed]]].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hvalid|reflexivity]. }
  rewrite <- Hnextmask in Hclosed.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state returned_heap final_registers acquired after _
    Hsaved Hclosed Hsave) as [Hstate [Hmemory_after [Hreturned [Hvalue Hpost]]]].
  split; [exact Hrestore|]. split.
  - unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. split; [exact Hvalue|]. split; [exact Hreturned|]. subst acquired.
    destruct Hresume as [Hstate_inv [Hcurrent [Hnode [Hregistration Hready]]]].
    match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
      sep_apply_l_atomic (sem_pend_cleanup_split sg state tid node Hstate_inv Hcurrent Hnode).
      unfold sem_pend_resume_stack_resources, sem_pend_resume_entry; entailer!. }
    exact (Hclose after Hpost).
Qed.

(** Ordinary OS_Sched return to the blocked SemPend invocation, followed
    by its final Restore and the caller's second Save. The actual install
    and frame reads produce readiness and registers. The waiting instance
    is the observation transported by the same preceding client trace.
    Unlike a first-Save continuation, the saved PC here is inside OS_Sched;
    it is not incorrectly constrained to the second Save's CPSID address.
    The caller's existing error cell and Event layout now continue through
    success, abort, or timeout's exact EventTaskRemove boundary, then the
    common stores and final Restore. This connects a real returning
    branch, not every enabled client/IRQ path, and does not install an
    unproved public callee Ensure. The actual restore's same-call result
    remains available to subsequent ordinary-source consumers. *)
Lemma sem_pend_sched_pending_resume_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg context outgoing hooked original suspended saved entry eid waiting perr heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  hooked.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  event_object_layout_prop sg eid ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) -> hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
     critical_region_inside critical sg original.(os_sched_call_invocation) entry ** unmap_table_rep sg **
     (perr # UChar |->_ ** frame)))) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored cursor written middle final_cursor returned_heap registers final_registers acquired after,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      cursor.(kernel_restore_r0) = saved -> cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
      armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
      armv7a_restore_prefix_transition restore cursor restored written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor returned_heap ->
      armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) current returned_heap
        final_registers acquired after ->
      kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor returned_heap /\
      kernel_call_save_uninterrupted_execution arch registers current returned_heap final_registers acquired after /\
      acquired = current /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
      final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
      (sem_pend_resume_stack_resources environment critical sg
        (armv7a_continuation_resumed_call selected original) final_registers.(kernel_save_r0)
        acquired eid original.(os_sched_call_stack).(stackLeaseSlot) waiting ** (perr # UChar |->_ ** frame)) after /\
      sem_pend_resume_stack_return environment critical arch restore sg
        (armv7a_continuation_resumed_call selected original) final_registers.(kernel_save_r0)
        acquired eid original.(os_sched_call_stack).(stackLeaseSlot) waiting perr after frame /\
      kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original).
Proof.
  intros environment critical arch task_abi restore save sg context outgoing hooked original suspended saved
    entry eid waiting perr heap frame abi focus current Horigin Hbinding Hcall Hslice Hmask Hwaiting Hwait Hlayout
    Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre.
  destruct (task_create_sched_pending_return_source environment critical arch task_abi restore sg context
    outgoing hooked original suspended saved entry heap (perr # UChar |->_ ** frame) Horigin Hbinding Hcall Hslice Hmask Hsaved
    Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre)
    as [installed [selected [node [Hinstall [Hreads [Hsp [Hcpsr [Hregisters Hrestore]]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored cursor written middle final_cursor returned_heap registers final_registers acquired after
    Hrun Hr0 Hcursor Hreturn Hvalid Hnextmask Hprefix Hsuffix Hsave.
  destruct (Hrestore restored Hrun) as [Hsame [Hsource [Hselected [Hmasked Hlocal]]]].
  assert (Hcurrent_waiting : current.(TskState).(inUsedTaskStates)
    original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting) by exact Hwaiting.
  match type of Hselected with ?P restored => assert (Hexpose : P |--
    coq_prop (sem_pend_resume_entry sg current eid original.(os_sched_call_stack).(stackLeaseSlot) waiting) && TT) end.
  { sep_apply_l_atomic (sem_pend_selected_source_resume_entry _ _ _
      environment.(task_stack_call_continuations) sg
      (armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr))
      original.(os_sched_call_stack) selected node
      (os_sched_install_context context outgoing original.(os_sched_call_stack) hooked) eid
      original.(os_sched_call_stack).(stackLeaseGeneration) waiting Hcurrent_waiting Hwait).
    Intros; entailer!; intros ? ?; exact I. }
  pose proof (proj1 (Hexpose restored Hselected)) as Hresume.
  assert (Hmask_cursor : armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192)
    by (rewrite Hcursor, Hcpsr; exact Hmask).
  destruct (sem_pend_masked_resume_restore_save environment critical arch restore save sg
    (armv7a_continuation_resumed_call selected original) saved entry current eid
    original.(os_sched_call_stack).(stackLeaseSlot) waiting cursor restored written middle final_cursor
    returned_heap registers final_registers acquired after (perr # UChar |->_ ** frame)
    Hresume Hr0 Hmask_cursor Hreturn Hvalid Hnextmask Hmasked Hprefix Hsuffix Hsave)
    as [Hrestore_run [Hsave_run [Hacquired [Hvalue [Hreturn_word Hresources]]]]].
  split; [exact Hrestore_run|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
  split; [exact Hvalue|]. split; [exact Hreturn_word|]. split; [exact Hresources|].
  split.
  - eapply sem_pend_resume_stack_return_source; [exact Hlayout|].
    match type of Hresources with ?P after => match goal with |- ?Q after =>
      assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder after Hresources).
  - exact Hsame.
Qed.

Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.

(** The canonical timeout/remove and final cleanup consumers use this
    map-preserving form. No descriptor's existing local owner is lost. *)
Lemma sem_pend_task_field_update_continuations : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local tasks active tid old current,
  tasks.(inUsedTaskStates) tid = Some old ->
  current.(taskGeneration) = old.(taskGeneration) -> current.(tcbStkPtr) = old.(tcbStkPtr) ->
  task_stack_live_coverage tasks active ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) tasks.(parkedTaskStacks) |--
  coq_prop (task_stack_live_coverage (glob_task_set_usedtask tasks tid current) active) &&
  store_parked_continuations (kernel_saved_continuation_entry abi (glob_task_set_usedtask tasks tid current) local) tasks.(parkedTaskStacks).
Proof.
  intros external platform port abi local tasks active tid old current Hold Hgen Hsp Hcoverage.
  assert (Hnodes : forall slot node,
    (glob_task_set_usedtask tasks tid current).(inUsedTaskStates) slot = Some node ->
    exists previous, tasks.(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode; cbn [glob_task_set_usedtask inUsedTaskStates] in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; auto.
    - exists node; auto. }
  assert (Hcovered : task_stack_live_coverage (glob_task_set_usedtask tasks tid current) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := tasks);
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hprevious [Hg Hp]]].
    exists previous; auto. }
  assert (Hstacks : store_parked_continuations (kernel_saved_continuation_entry abi tasks local) tasks.(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi (glob_task_set_usedtask tasks tid current) local) tasks.(parkedTaskStacks)).
  { apply kernel_saved_continuation_map_reindex.
    intros key payload node Hpayload Hnode Hg; exact (Hnodes _ _ Hnode). }
  sep_apply_l_atomic Hstacks; entailer!.
Qed.
