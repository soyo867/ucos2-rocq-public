Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.event Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_switch_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_scheduled_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_mrs_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_first_acquire_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.

(** Consume the actual acquisition cells and stack world as the exact
    phase-indexed Save post used by the canonical C caller. *)
Lemma sem_pend_owned_acquire_phase_output : forall environment critical sg original returned
  pevent mask saved start acquired eid observed event focus (frame : Assertion),
  sem_pend_acquire_observation environment critical sg original returned mask saved start acquired
    eid observed event ->
  sem_pend_task_call_stage sg returned acquired ->
  task_stack_live_coverage acquired.(TskState) (Some (task_stack_key returned.(os_sched_call_stack))) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg
    returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) returned **
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value event **
  sem_post_count_frame sg acquired eid event **
  armv7a_task_call_stacks environment.(task_stack_call_continuations) acquired.(TskState) focus
    acquired.(TskState).(parkedTaskStacks) ** frame |--
  sem_pend_phase_save_output (SemPendAcquirePhase pevent eid observed)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical sg original mask saved start ** frame.
Proof.
  intros * Hobservation Hstage Hcoverage.
  pose proof Hobservation as [_ [Hsame [Hsaved [Hvalid [_ [Hlookup [_ [Htype _]]]]]]]].
  pose proof Hsame as [Hi [Ho Hs]].
  assert (Horiginal_stage : sem_pend_task_call_stage sg original acquired).
  { unfold sem_pend_task_call_stage, kernel_call_task_source in Hstage |- *.
    rewrite Hi, Ho, Hs in Hstage; exact Hstage. }
  assert (Hbase : sem_pend_stack_save_observation critical sg original returned
    (Some environment) mask saved start acquired).
  { split; [exact Hsame|]. split; [exact Hsaved|discriminate]. }
  assert (Hphase : sem_pend_save_phase_observation (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg original returned mask saved start acquired).
  { exists event; split; [exact Hobservation|intros; exact Horiginal_stage]. }
  pose proof (proj1 (proj1 Hstage)) as Horigin.
  assert (Hactive : task_stack_call_active_key returned = Some (task_stack_key returned.(os_sched_call_stack))).
  { unfold task_stack_call_active_key; rewrite Horigin; reflexivity. }
  sep_apply_l_atomic (sem_pend_count_merge_unchanged sg acquired eid event Hvalid Hlookup Htype).
  sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ environment.(task_stack_call_continuations)
    acquired.(TskState) focus acquired.(TskState).(parkedTaskStacks)).
  unfold sem_pend_phase_save_output; Exists returned acquired.
  unfold sem_pend_optional_stack_resources, task_tcb_init_stack_capsules.
  rewrite Hactive, Hi, Ho; entailer!.
Qed.

(** For the uninterrupted branch the actual source execution retains the
    state. The admitted nonblocking alternative supplies no task stage;
    a zero observed count excludes that alternative at this same cut. *)
Lemma sem_pend_phase_uninterrupted_save_observation : forall phase environment critical sg
  call mask saved state,
  sem_pend_save_phase_pre phase (Some environment) critical sg call mask state ->
  UCOS2_state_inv sg state -> interrupt_saved_value mask saved ->
  kernel_call_save_history environment critical sg call state call state ->
  sem_pend_save_phase_observation phase (Some environment) critical sg call call mask saved state state.
Proof.
  intros phase environment critical sg call mask saved state Hphase Hvalid Hsaved Hhistory.
  destruct phase as [pevent eid observed|original initial_mask initial observed eid timeout waiting|];
    cbn [sem_pend_save_phase_pre sem_pend_save_phase_observation] in *; [|tauto|contradiction].
  destruct Hphase as [Hinput [Hnonnull [Hclear Hadmission]]].
  destruct (sem_pend_call_input_nonnull _ _ _ _ _ _ _ Hinput Hnonnull)
    as [Haddress [Hid [Hslot Hprotocol]]].
  assert (Htype : event_slot_type_value state.(EventState) eid = 3).
  { destruct (Z.eq_dec (event_slot_type_value state.(EventState) eid) 3) as [Heq|Hne];
      [exact Heq|].
    rewrite (sem_pend_context_error_type_first _ _ _ Hne) in Hclear; discriminate. }
  destruct (sem_query_public_slot_is_sem state eid observed Hslot Htype) as [Hlookup Hsem].
  assert (Hobservation : sem_pend_acquire_observation environment critical sg call call
    mask saved state state eid observed observed).
  { unfold sem_pend_acquire_observation, kernel_stack_call_same_call.
    repeat first [assumption | split | reflexivity]. }
  exists observed; split; [exact Hobservation|].
  intros Hzero.
  assert (Hordered : sem_pend_precritical_error pevent (event_slot_type_value state.(EventState) eid)
    state.(IntrState).(intNesting) state.(IntrState).(lockNesting) = None).
  { unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); exact Hclear. }
  destruct (Hadmission Hordered) as [Hstage|Hpositive]; [exact Hstage|].
  specialize (Hpositive call mask saved state observed observed Hobservation); lia.
Qed.

(** The literal MRS/CPSID/DSB/BX branch produces the exact Save Ensure for
    either C call site. No scheduling or interference is silently framed
    through this branch; its state equality follows from the source ABI. *)
Lemma sem_pend_uninterrupted_save_phase : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  phase sg call mask state registers before final_registers acquired after (frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_phase_save_input phase environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call mask state **
    unmap_table_rep sg ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  acquired = state /\
  (sem_pend_phase_save_output phase environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call mask
    final_registers.(kernel_save_r0) state ** unmap_table_rep sg ** frame) after.
Proof.
  intros environment critical arch save phase sg call mask state registers before final_registers acquired
    after frame Hreturn Hcpsr Hmask Hpre Hrun.
  assert (Hopen : sem_pend_phase_save_input phase environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call mask state **
    unmap_table_rep sg ** frame |--
    coq_prop (sem_pend_save_phase_pre phase (Some environment) critical sg call mask state /\
      UCOS2_state_inv sg state) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
     (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
       (task_stack_call_active_key call) state ** frame))).
  { unfold sem_pend_phase_save_input; Intros.
    rewrite sem_pend_stack_save_input_owned.
    sep_apply_l_atomic (proj1 (task_tcb_init_stack_save_input_closed_world environment critical sg call mask state)).
    unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
    unfold UCOS2_inv; Intros; cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; entailer!. }
  destruct (Hopen before Hpre) as [[Hphase Hvalid] Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired after _ Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  assert (Hexecution : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hrun). }
  split; [exact Hexecution|]. split; [exact Hstate|]. subst acquired.
  assert (Hfinal_saved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hr0; cbn [kernel_save_read_cpsr kernel_save_r0]; split; [exact Hcpsr|exact Hmask]. }
  assert (Hhistory : kernel_call_save_history environment critical sg call state call state).
  { eapply KernelCallSaveUninterrupted; eassumption. }
  pose proof (sem_pend_phase_uninterrupted_save_observation phase environment critical sg call mask
    final_registers.(kernel_save_r0) state Hphase Hvalid Hfinal_saved Hhistory) as Hphase_after.
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold sem_pend_phase_save_output; Exists call state.
    unfold sem_pend_stack_save_observation, kernel_stack_call_same_call,
      sem_pend_optional_stack_resources, task_tcb_init_stack_capsules, kernel_stack_inv.
    rewrite kernel_program_inv_split_unmap; entailer!; discriminate. }
  exact (Hclose after Hafter).
Qed.

(** Actual MSR/BX return, preserving the same waiting phase when this is
    the first Restore. Final Restore uses the same producer with the
    return phase. Interrupted returning branches require their own path. *)
Lemma sem_pend_uninterrupted_restore_phase : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  phase sg call saved acquired released cursor before written middle final_cursor after (frame : Assertion),
  sem_pend_restore_phase_pre phase (Some environment) critical sg call (armv7a_irq_fiq_mask saved) released ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (task_tcb_init_stack_restore_input environment critical sg call saved acquired released **
    unmap_table_rep sg ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (sem_pend_phase_restore_output phase environment.(task_stack_call_external)
    environment.(task_stack_call_platform) (Some environment) critical sg call
      (armv7a_irq_fiq_mask saved) released ** unmap_table_rep sg ** frame) after.
Proof.
  intros environment critical arch restore phase sg call saved acquired released cursor before written middle
    final_cursor after frame Hphase Hr0 Hmask Hpre Hprefix Hsuffix.
  destruct (sem_pend_wait_first_restore_source environment critical arch restore sg call saved acquired released
    cursor before written middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix)
    as [Hrun [Hreturn [Hhistory Hafter]]].
  split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
    unfold sem_pend_phase_restore_output; Exists call released.
    rewrite mutex_query_closed_equiv.
    unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
      kernel_stack_call_same_call, sem_pend_optional_stack_resources,
      task_tcb_init_stack_capsules, kernel_call_execution_owned.
    entailer!; try discriminate; try tauto. }
  exact (Hclose after Hafter).
Qed.

(** Extend the same wait with the concrete C selector and OSCtxSw path.
    This carries the source edge even though only wait-field preservation
    is needed by the eventual cleanup proof. *)
Lemma sem_pend_wait_phase_switch_source : forall environment critical sg original mask initial observed
  eid timeout waiting call entry
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  context old_sp cpsr registers lr saved incoming selected before prefix after,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call entry ->
  os_sched_source_switch_prefix_execution sg before prefix ->
  os_sched_source_switch_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) task_abi sg (os_sched_prefix_state entry)
    context old_sp cpsr registers lr saved incoming selected prefix after ->
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call
    (os_sched_install_context context saved.(armv7a_continuation_fragments) incoming
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp))).
Proof.
  intros * [owned [Howned [Hsame [Hwait Hpath]]]] Hprefix Hswitch.
  inversion Howned; subst owned.
  exists environment; split; [reflexivity|]. split; [exact Hsame|]. split; [exact Hwait|].
  eapply SemPendWaitSourceTrans; [exact Hpath|]. eapply SemPendWaitSourceSwitch; eassumption.
Qed.

(** An actual selected post provides readiness, while the same registered
    and switching path above identifies the waiter. The real final MSR/BX
    of OS_Sched then produces the canonical phase post on the returned
    heap. Both resource views below are outputs of the same selected
    source producer, not extra public caller requirements. *)
Lemma sem_pend_selected_scheduler_phase_return : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid timeout waiting call scheduler_entry current focus incoming selected node
  saved acquired cursor before written middle final_cursor after (selected_frame frame : Assertion),
  let returned := armv7a_continuation_resumed_call selected call in
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call current ->
  incoming = original.(os_sched_call_stack) -> interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg focus incoming selected node current ** selected_frame) before ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key returned) returned saved acquired current ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (sem_pend_phase_sched_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical sg call mask scheduler_entry ** frame) after.
Proof.
  intros environment critical arch restore sg original mask initial observed eid timeout waiting call
    scheduler_entry current focus incoming selected node saved acquired cursor before written middle final_cursor
    after selected_frame frame returned Hwait Hincoming Hsaved Hr0 Hmask Hselected Howned Hprefix Hsuffix.
  assert (Hselected_wait : sem_pend_wait_selected_at (Some environment) critical sg original mask initial
    observed eid timeout waiting call current).
  { assert (Hexpose : os_sched_source_selected_post environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) sg focus incoming selected node current ** selected_frame |--
      coq_prop (sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed
        eid timeout waiting call current) && TT).
    { sep_apply_l_atomic (sem_pend_wait_at_selected_source environment critical sg original mask initial observed
        eid timeout waiting call current focus incoming selected node Hwait Hincoming).
      Intros; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hselected)). }
  assert (Hcall_lease : call.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { destruct Hwait as [owned [Henv [Hcall Hrest]]]; exact (proj2 (proj2 Hcall)). }
  assert (Hselected_lease : selected.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { assert (Hlease_view : os_sched_source_selected_post environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) sg focus incoming selected node current ** selected_frame |--
      coq_prop (selected.(armv7a_continuation_stack) = incoming) && TT).
    { unfold os_sched_source_selected_post; Intros; entailer!; intros ? ?; exact I. }
    rewrite Hcall_lease, <- Hincoming; exact (proj1 (Hlease_view before Hselected)). }
  assert (Hsame : kernel_stack_call_same_call returned call).
  { unfold kernel_stack_call_same_call, returned, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack]; repeat split; auto. }
  assert (Hreturned_wait : sem_pend_wait_selected_at (Some environment) critical sg original mask initial
    observed eid timeout waiting returned current).
  { destruct Hselected_wait as [[owned [Henv [Hcall [Hhistory Hpath]]]] Hresume].
    split; [exists owned; split; [exact Henv|]; split|exact Hresume].
    - unfold kernel_stack_call_same_call in *; intuition congruence.
    - split; assumption. }
  assert (Hinput : kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
    critical sg (task_stack_call_active_key returned) returned saved acquired current ** frame |--
    task_tcb_init_stack_restore_input environment critical sg returned saved acquired current **
      unmap_table_rep sg ** frame).
  { rewrite <- task_tcb_init_stack_restore_input_masked_world; entailer!. }
  destruct (sem_pend_wait_first_restore_source environment critical arch restore sg returned saved acquired
    current cursor before written middle final_cursor after frame Hr0 Hmask (Hinput before Howned) Hprefix Hsuffix)
    as [Hexecution [Hreturn [Hhistory Hafter]]].
  split; [exact Hexecution|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { cbn [sem_pend_phase_sched_output]; Exists returned current.
    rewrite (proj2 Hsaved), <- task_tcb_init_stack_save_input_closed_world.
    rewrite <- sem_pend_stack_save_input_owned; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Compose the SAME concrete switch and selected-return heaps. The
    existing wait observation may have been transported by the registered
    trace, but no post-switch wait path is supplied independently here. *)
Lemma sem_pend_switch_scheduler_phase_return : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original mask initial observed eid timeout waiting call scheduler_entry entry
  context old_sp cpsr registers lr outgoing incoming selected node focus selector_heap prefix before
  saved acquired cursor written middle final_cursor after (selected_frame frame : Assertion),
  let current := os_sched_install_context context outgoing.(armv7a_continuation_fragments) incoming
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      context.(os_sched_call_stack).(stackLeaseSlot) outgoing.(armv7a_continuation_sp)) in
  let returned := armv7a_continuation_resumed_call selected call in
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call entry ->
  os_sched_source_switch_prefix_execution sg selector_heap prefix ->
  os_sched_source_switch_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) task_abi sg (os_sched_prefix_state entry)
    context old_sp cpsr registers lr outgoing incoming selected prefix before ->
  incoming = original.(os_sched_call_stack) -> interrupt_saved_value mask saved ->
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (os_sched_source_selected_post environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) sg focus incoming selected node current ** selected_frame) before ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key returned) returned saved acquired current ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  (sem_pend_phase_sched_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical sg call mask scheduler_entry ** frame) after.
Proof.
  intros environment critical arch task_abi restore sg original mask initial observed eid timeout waiting
    call scheduler_entry entry context old_sp cpsr registers lr outgoing incoming selected node focus selector_heap
    prefix before saved acquired cursor written middle final_cursor after selected_frame frame current returned
    Hwait Hprefix Hswitch Hincoming Hsaved Hr0 Hmask Hselected Howned Hrestore_prefix Hrestore_suffix.
  pose proof (sem_pend_wait_phase_switch_source environment critical sg original mask initial observed
    eid timeout waiting call entry task_abi context old_sp cpsr registers lr outgoing incoming selected
    selector_heap prefix before Hwait Hprefix Hswitch) as Hcurrent_wait.
  exact (sem_pend_selected_scheduler_phase_return environment critical arch restore sg original mask
    initial observed eid timeout waiting call scheduler_entry current focus incoming selected node saved acquired
    cursor before written middle final_cursor after selected_frame frame Hcurrent_wait Hincoming Hsaved Hr0 Hmask
    Hselected Howned Hrestore_prefix Hrestore_suffix).
Qed.

(** The canonical first-Save post now consumes the complete source producer. *)
Lemma sem_pend_scheduled_first_save_phase : forall environment critical arch Extra
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (registers_source : Armv7aIRQRegisterSave environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
    KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop)
  sg original start first_registers before irq_input handler suspended saved_heap registry_heap
  payload (parked_frame : Assertion) entry_heap entry stopped returned_origin checkpoint
  context old_sp cpsr task_registers lr saved written stored captured hooked_heap
  eid observed (pevent : Z) (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original (armv7a_save_entry_address save + 4)
    suspended.(armv7a_continuation_lr) in
  let parked := armv7a_irq_live_parked_state start original suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let hooked := os_sched_save_current_sp (os_sched_prefix_state entry)
    context.(os_sched_call_stack).(stackLeaseSlot) saved.(armv7a_continuation_sp) in
  valid_os_cpu_sr first_registers.(kernel_save_cpsr) ->
  kernel_call_save_instruction_step arch SaveReadCPSR first_registers start before
    (kernel_save_read_cpsr first_registers) start irq_input ->
  handler.(os_int_exit_interrupted_call) = original ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address save + 4 ->
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr) ->
  armv7a_irq_register_save registers_source
    (kernel_save_read_cpsr first_registers).(kernel_save_r0)
    (kernel_save_read_cpsr first_registers).(kernel_save_lr)
    handler suspended irq_input saved_heap ->
  armv7a_task_frame_slice suspended ->
  kernel_heap_execution (armv7a_irq_live_entry_writes sg start
    original.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
    saved_heap registry_heap ->
  (kernel_client_call_stack_world abi sg focus payload parked ** parked_frame) registry_heap ->
  kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
    KernelClientHeapClosed entry_heap ->
  kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked
    KernelClientHeapClosed entry ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    parked stopped returned_origin entry ->
  os_sched_source_switch_prefix_execution sg entry_heap checkpoint ->
  kernel_heap_execution (armv7a_task_save_writes old_sp cpsr task_registers lr) checkpoint written ->
  pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written ->
  kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
    saved.(armv7a_continuation_sp)) written stored ->
  armv7a_task_capture_transition task_abi context saved stored captured ->
  kernel_heap_execution [] captured hooked_heap ->
  kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg hooked hooked ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  sem_pend_call_fields sg original.(os_sched_call_stack).(stackLeaseSlot) hooked ->
  os_sched_saved_stack_binding context saved.(armv7a_continuation_fragments) hooked ->
  os_sched_destination_binding environment.(task_stack_call_external) context
    saved.(armv7a_continuation_fragments) hooked original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  mutex_query_handle_protocol critical sg original.(os_sched_call_invocation) eid ->
  mutex_query_lookup start eid observed -> observed.(eventType) = OS_EVENT_TYPE_SEM ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved.(armv7a_continuation_fragments) **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) hooked_heap ->
  let current := os_sched_install_context context saved.(armv7a_continuation_fragments)
    original.(os_sched_call_stack) hooked in
  exists installed selected,
    sched_install_heap_fragment sg hooked_heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    (forall restored registers final_registers acquired after,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      armv7a_save_suffix_transition save registers current restored final_registers acquired after ->
      let returned := armv7a_continuation_resumed_call selected original in
      acquired = current /\
      final_registers.(kernel_save_r0) = first_registers.(kernel_save_cpsr) /\
      kernel_save_after_mrs_execution arch registers current restored final_registers acquired after /\
      (sem_pend_phase_save_output (SemPendAcquirePhase pevent eid observed)
        environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
        critical sg original (armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr))
        final_registers.(kernel_save_r0) start ** frame) after).
Proof.
  intros environment critical arch Extra save task_abi registers_source extra_step extra_effect
    sg original start first_registers before irq_input handler suspended saved_heap registry_heap
    payload parked_frame entry_heap entry stopped returned_origin checkpoint context old_sp cpsr
    task_registers lr saved written stored captured hooked_heap eid observed pevent frame abi focus parked hooked
    Hvalid_registers Hmrs Hhandler Hhandler_pc Hhandler_mask Hcapture_irq Hslice Hentry Hworld
    Hheap_trace Hstate_trace Hsource_trace Hprefix Hwrites Hload Hstore Hcapture Hhook_heap Hhook
    Horigin Hactive Hfields Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage
    Hprotocol Hlookup Htype Hpre current.
  destruct (sem_pend_scheduled_first_acquire_source environment critical arch Extra save task_abi
    registers_source extra_step extra_effect sg original start first_registers before irq_input handler
    suspended saved_heap registry_heap payload parked_frame entry_heap entry stopped returned_origin
    checkpoint context old_sp cpsr task_registers lr saved written stored captured hooked_heap eid observed frame
    Hvalid_registers Hmrs Hhandler Hhandler_pc Hhandler_mask Hcapture_irq Hslice Hentry Hworld
    Hheap_trace Hstate_trace Hsource_trace Hprefix Hwrites Hload Hstore Hcapture Hhook_heap Hhook
    Horigin Hactive Hfields Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage
    Hprotocol Hlookup Htype Hpre) as [installed [selected [Hinstall [Hreads Hreturn]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored registers final_registers acquired after Hrun Hcpsr Hr0 Hlr Hsuffix returned.
  destruct (Hreturn restored registers final_registers acquired after Hrun Hcpsr Hr0 Hlr Hsuffix)
    as [Hstate [Hvalue [Hexecution [event [Hfacts Howned]]]]].
  destruct Hfacts as [Hobservation [Hstage [Hcovered Hrest]]].
  split; [exact Hstate|]. split; [exact Hvalue|]. split; [exact Hexecution|].
  exact (sem_pend_owned_acquire_phase_output environment critical sg original returned pevent
    (armv7a_irq_fiq_mask first_registers.(kernel_save_cpsr)) final_registers.(kernel_save_r0)
    start acquired eid observed event focus frame Hobservation Hstage Hcovered after Howned).
Qed.
