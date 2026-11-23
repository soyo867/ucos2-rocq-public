Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_sequential_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_entry_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_saved_wait_source_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Fresh registration changes the invocation ledger, not used TCBs or
    their SPs. Validity supplies freshness, preserving the original saved
    invocation's active registration. The exact map is transported once;
    it is never replaced by the weaker generic continuation map. *)
Lemma sem_pend_saved_call_map_begin_invocation : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired descriptor
  state origin focus,
  UCOS2_state_inv sg state ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
    state.(TskState).(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor
      (task_begin_invocation origin state.(TskState)) focus)
    (task_begin_invocation origin state.(TskState)).(parkedTaskStacks).
Proof.
  apply kernel_saved_sched_call_map_begin_invocation.
Qed.

(** Interpret a real initial-frame TaskRestore using the already approved
    first-C-entry ABI. This consumes initial execution and its owned stack
    bytes, then records the actual registration event in the waiting
    invocation's history. None alone supplies no execution authority.
    The stage below is the first task entry; calling Post still needs the
    separate actual sequential application boundary in the next theorem. *)
Lemma sem_pend_saved_initial_call_source : forall environment critical
  (entry_abi : Armv7aInitialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  sg state original saved acquired descriptor focus previous selected node installed restored
  public_call mask initial observed eid timeout waiting (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let current := armv7a_initial_call_registered selected state in
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting original state ->
  selected.(armv7a_continuation_call) = None -> armv7a_initial_frame_binding selected ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key selected.(armv7a_continuation_stack))) ->
  armv7a_task_restore_transition task_abi previous selected installed restored ->
  (armv7a_task_restored_execution environment.(task_stack_call_external)
     environment.(task_stack_call_platform) environment.(task_stack_call_port) abi selected **
   kernel_program_inv sg state ** store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) restored ->
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting original current /\
  kernel_call_task_source call current /\
  sched_current_ready_at current.(TskState) current.(SchedState)
    call.(os_sched_call_stack).(stackLeaseSlot) node /\
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_stack_live_coverage current.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
     call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
   kernel_program_inv sg current ** store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor current.(TskState) focus)
     current.(TskState).(parkedTaskStacks) ** frame) restored.
Proof.
  intros environment critical entry_abi task_abi sg state original saved acquired descriptor focus previous selected
    node installed restored public_call mask initial observed eid timeout waiting frame abi current call
    Hwait Hnone Hbinding Hready Hgen Hcoverage Hrestore Hpre.
  assert (Hgeometry : task_stack_fragments_in_range
    selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords)
    0 selected.(armv7a_continuation_fragments)).
  { destruct Hbinding as [top [task_entry [argument [task_return [lower [upper [Heq [Hregion Hrest]]]]]]]].
    rewrite Heq; cbn [armv7a_initial_continuation armv7a_continuation_stack armv7a_continuation_fragments].
    apply task_stack_complete_fragments_in_range; exact Hregion. }
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P restored => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve restored Hpre)). }
  assert (Hcurrent : task_current_at state selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { split; [exact (proj1 (proj2 Hready))|]. exists node; exact (conj (proj1 Hready) Hgen). }
  assert (Hhistory : sem_pend_wait_source_history environment critical sg public_call eid
    public_call.(os_sched_call_stack).(stackLeaseGeneration) state current).
  { eapply (@SemPendWaitSourceInitialEntry environment critical sg public_call eid
      public_call.(os_sched_call_stack).(stackLeaseGeneration) entry_abi task_abi state previous selected
      installed restored).
    - exact Hrestore.
    - exact Hnone.
    - exact Hbinding.
    - exact Hgeometry.
    - exact Hcurrent.
    - match type of Hpre with ?P restored => assert (Hinput : P |--
        UCOS2_inv sg state ** armv7a_initial_execution abi selected **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) **
        (unmap_table_rep sg ** store_parked_continuations
          (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
          state.(TskState).(parkedTaskStacks) ** frame)) end.
      { unfold armv7a_task_restored_execution; rewrite Hnone, kernel_program_inv_split_unmap; entailer!. }
      exact (Hinput restored Hpre). }
  match type of Hpre with ?P restored => assert (Hregister : P |--
    coq_prop (kernel_call_task_source call current) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
       call (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) ** kernel_program_inv sg current **
     store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor current.(TskState) focus)
       current.(TskState).(parkedTaskStacks) ** frame)) end.
  { unfold armv7a_task_restored_execution; rewrite Hnone, !kernel_program_inv_split_unmap.
    pose proof (armv7a_initial_call_register_resources _ _ _ abi entry_abi sg state selected
      selected.(armv7a_continuation_fragments) Hbinding Hgeometry Hcurrent) as Hinitial_register.
    cbv zeta in Hinitial_register; sep_apply_l_atomic Hinitial_register; Intros.
    sep_apply_l_atomic (sem_pend_saved_call_map_begin_invocation _ _ _ abi critical sg original saved acquired
      descriptor state (RunningInvocation selected.(armv7a_continuation_stack).(stackLeaseSlot)
        selected.(armv7a_continuation_stack).(stackLeaseGeneration)) focus Hvalid).
    fold current call; entailer!. }
  destruct (Hregister restored Hpre) as [Hsource Hregistered].
  split.
  - destruct Hwait as [owned [Howned [Hsame [Hobserved Hpath]]]]; inversion Howned; subst owned.
    exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hobserved|].
    eapply SemPendWaitSourceTrans; eassumption.
  - exact (conj Hsource (conj Hready (conj Hgen (conj Hcoverage Hregistered)))).
Qed.

(** Independent ordinary Post entry after a genuinely completed previous
    API. The linked program supplies the actual sequential boundary and
    the previous call's registered execution owner. Fresh registration
    preserves the same waiting history and exact saved map, and the
    existing concrete SemPost prefix immediately consumes these resources.

    This theorem is separate from initial task entry above. Application
    execution from an initial task to its first API remains a source
    obligation; the sequential ABI does not interpret that nested call.
    The endpoint is EventTaskRdy's physical post, ready for the separately
    proved saved-Post return consumer and its stated path conditions. *)
Lemma sem_pend_saved_post_entry_source : forall environment critical arch
  (boundary : KernelSequentialCallABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform))
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state original saved acquired descriptor focus previous node before entered
  public_call mask execution_mask initial observed eid timeout waiting event tid old priority
  registers final_registers post_acquired saved_heap woken_heap (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let poster := kernel_sequential_call previous state.(TskState).(taskLifecycle).(taskNextInvocation) in
  let entry := replace_TskS (task_begin_invocation previous.(os_sched_call_origin) state.(TskState)) state in
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting original state ->
  kernel_call_task_source previous state ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    previous.(os_sched_call_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = previous.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key previous.(os_sched_call_stack))) ->
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
     previous execution_mask ** kernel_program_inv sg state ** store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  kernel_sequential_call_source boundary previous state.(TskState).(taskLifecycle).(taskNextInvocation)
    before entered ->
  sem_post_lookup state eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_addr sg eid <> 0 -> sem_post_group state event <> 0 -> event_object_layout_prop sg eid ->
  event_task_rdy_entry sg state.(TskState) eid event tid old ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = execution_mask ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) entry entered
    final_registers post_acquired saved_heap ->
  sem_post_waiter_execution sg (event_addr sg eid) priority saved_heap woken_heap ->
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting original entry /\
  kernel_call_task_source poster entry /\
  sched_current_ready_at entry.(TskState) entry.(SchedState) poster.(os_sched_call_stack).(stackLeaseSlot) node /\
  node.(taskGeneration) = poster.(os_sched_call_stack).(stackLeaseGeneration) /\
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key poster.(os_sched_call_stack))) /\
  uchar_load (event_addr sg eid + OSEventType_off) 3 entered /\
  kernel_call_save_uninterrupted_execution arch registers entry entered final_registers post_acquired saved_heap /\
  post_acquired = entry /\
  uchar_load (event_addr sg eid + OSEventGrp_off) (sem_post_group entry event) saved_heap /\
  (critical_region_masked environment.(task_stack_call_platform) critical sg poster.(os_sched_call_invocation)
      poster.(os_sched_call_origin) final_registers.(kernel_save_r0) entry **
   os_sched_context_resources environment.(task_stack_call_external) poster **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor entry.(TskState) focus)
     entry.(TskState).(parkedTaskStacks) ** frame) woken_heap.
Proof.
  intros environment critical arch boundary save sg state original saved acquired descriptor focus previous node
    before entered public_call mask execution_mask initial observed eid timeout waiting event tid old priority
    registers final_registers post_acquired saved_heap woken_heap frame abi poster entry
    Hwait Hsource Hready Hgen Hcoverage Hpre Hboundary Hlookup Htype Hnonnull Hgroup Hlayout Hwaiter
    Hreturn Hcpsr Hmask Hsave Hwake.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  assert (Hlive : task_invocation_origin_live state.(TskState) previous.(os_sched_call_origin))
    by exact (proj2 (proj2 (proj1 (proj2 Hsource)))).
  match type of Hpre with ?P before => assert (Horder : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      previous execution_mask ** (kernel_program_inv sg state ** store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
  destruct (kernel_sequential_call_owned_entry _ _ boundary previous
    state.(TskState).(taskLifecycle).(taskNextInvocation) execution_mask before entered _ Hboundary
    (Horder before Hpre)) as [Hmemory Hentered].
  fold poster in Hentered.
  assert (Hentry_valid : UCOS2_state_inv sg entry)
    by (apply UCOS2_begin_task_invocation_preserves_validity; assumption).
  assert (Hentry_source : kernel_call_task_source poster entry).
  { pose proof Hsource as [Horigin [Hactive Hcurrent]].
    unfold kernel_call_task_source, poster, kernel_sequential_call; cbn.
    split; [exact Horigin|]. split; [apply task_begin_invocation_active; exact Hlive|exact Hcurrent]. }
  assert (Hentry_wait : sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    waiting original entry).
  { destruct Hwait as [owned [Howned [Hsame [Hobserved Hpath]]]]; inversion Howned; subst owned.
    exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hobserved|].
    eapply SemPendWaitSourceTrans; [exact Hpath|].
    eapply SemPendWaitSourceSequentialEntry; [exact Hlive|exact Hboundary]. }
  match type of Hentered with ?P entered => assert (Hregistered : P |--
    kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
      poster execution_mask ** UCOS2_inv sg entry ** unmap_table_rep sg **
    (store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor entry.(TskState) focus)
      entry.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg state previous.(os_sched_call_origin) Hlive).
    sep_apply_l_atomic (sem_pend_saved_call_map_begin_invocation _ _ _ abi critical sg original saved acquired
      descriptor state previous.(os_sched_call_origin) focus Hvalid); fold entry; entailer!. }
  assert (Hwaiter_entry : event_task_rdy_entry sg entry.(TskState) eid event tid old).
  { destruct Hwaiter as [Hsg [Hlayout' [Hmulti [Htasks [Hconsistency [Hhead Hold]]]]]].
    exact (conj Hsg (conj Hlayout' (conj Hmulti
      (conj (proj1 (proj2 Hentry_valid))
        (conj Hconsistency (conj Hhead Hold)))))). }
  assert (Hentry_group : sem_post_group entry event <> 0).
  { unfold sem_post_group in *.
    rewrite <- (proj1 (event_wait_encoding_priority_ext event.(waitList) state.(TskState)
      entry.(TskState) ltac:(intros; reflexivity))); exact Hgroup. }
  destruct (sem_post_saved_wait_entry_source _ _ critical arch save sg entry poster execution_mask
    eid event tid old priority entered registers final_registers post_acquired saved_heap woken_heap
    (store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor entry.(TskState) focus)
      entry.(TskState).(parkedTaskStacks) ** frame)
    Hentry_valid Hlookup Htype Hnonnull Hentry_group Hlayout Hwaiter_entry (Hregistered entered Hentered)
    Hreturn Hcpsr Hmask Hsave Hwake) as [Htype_read [Hsave_run [Hacquired [Hgroup_read Hpost]]]].
  split; [exact Hentry_wait|]. split; [exact Hentry_source|].
  split; [exact Hready|]. split; [exact Hgen|]. split; [exact Hcoverage|].
  split; [exact Htype_read|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
  split; [exact Hgroup_read|].
  match type of Hpost with ?P woken_heap => match goal with |- ?Q woken_heap =>
    assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose woken_heap Hpost).
Qed.
