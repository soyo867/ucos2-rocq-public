Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_checkpoint_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The public error checks constrain the SAME state acquired on the
    uninterrupted first-Save branch. Waiting changes Task/Event/ready
    storage and leaves these two interrupt counters untouched. Their
    lower bounds come from the physical interrupt owner. No statement
    about an arbitrary later registered trace is used here. *)
Lemma sem_pend_wait_clear_scheduler_counts : forall sg entry eid event tid node timeout,
  sem_pend_context_error (event_slot_type_value entry.(EventState) eid)
    entry.(IntrState).(intNesting) entry.(IntrState).(lockNesting) = None ->
  let waiting := event_pend_state sg entry eid event tid node PendSem timeout in
  UCOS2_inv sg waiting |--
  coq_prop (waiting.(IntrState).(intNesting) = 0 /\
    waiting.(IntrState).(lockNesting) = 0 /\ os_sched_selection_enabled waiting = true) &&
  UCOS2_inv sg waiting.
Proof.
  intros sg entry eid event tid node timeout Hclear waiting.
  assert (Hupper : entry.(IntrState).(intNesting) <= 0 /\
    entry.(IntrState).(lockNesting) <= 0).
  { unfold sem_pend_context_error in Hclear.
    destruct (negb (Z.eqb (event_slot_type_value entry.(EventState) eid)
      (encode_event_type OS_EVENT_TYPE_SEM))); [discriminate|].
    destruct (0 <? entry.(IntrState).(intNesting)) eqn:Hi; [discriminate|].
    destruct (0 <? entry.(IntrState).(lockNesting)) eqn:Hl; [discriminate|].
    apply Z.ltb_ge in Hi; apply Z.ltb_ge in Hl; auto. }
  rewrite (UCOS2_inv_split_module sg waiting InterruptModule).
  cbn [UCOS2_module_rep]; unfold interrupt_inv; Intros.
  assert (Hcounts : waiting.(IntrState).(intNesting) = 0 /\
    waiting.(IntrState).(lockNesting) = 0).
  { assert (Hrange : interrupt_in_range waiting.(IntrState)) by tauto.
    unfold interrupt_in_range in Hrange.
    change (entry.(IntrState).(intNesting) = 0 /\ entry.(IntrState).(lockNesting) = 0).
    change (0 <= entry.(IntrState).(intNesting) /\ 0 <= entry.(IntrState).(lockNesting)) in Hrange.
    lia. }
  assert (Henabled : os_sched_selection_enabled waiting = true).
  { apply os_sched_selection_enabled_iff; exact Hcounts. }
  entailer!.
Qed.

(** Consume the canonical Scheduler entry at the actual MRS/CPSID/DSB/BX
    cut. The two following C guard reads refer to the saved heap, and the
    wait observation still names this same invocation and world. *)
Lemma sem_pend_scheduler_save_guard_source : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original call mask initial observed eid timeout waiting state registers before
  final_registers acquired after (frame : Assertion),
  os_sched_selection_enabled state = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (sem_pend_phase_sched_input (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  acquired = state /\
  uchar_load sg.(g_OSIntNesting) 0 after /\ uchar_load sg.(g_OSLockNesting) 0 after /\
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout
    waiting call acquired /\
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
    (task_stack_call_active_key call) call final_registers.(kernel_save_r0) acquired acquired ** frame) after.
Proof.
  intros environment critical arch save sg original call mask initial observed eid timeout waiting state
    registers before final_registers acquired after frame Henabled Hreturn Hcpsr Hmask Hpre Hrun.
  assert (Hopen : sem_pend_phase_sched_input
      (SemPendWaitPhase original mask initial observed eid timeout waiting)
      environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
      critical sg call mask state ** frame |--
    coq_prop (sem_pend_wait_at (Some environment) critical sg original mask initial observed
      eid timeout waiting call state) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
       call (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
     (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
        (task_stack_call_active_key call) state ** frame))).
  { cbn [sem_pend_phase_sched_input]; unfold sem_pend_stack_sched_input, os_sched_stack_pre,
      kernel_stack_call_closed; cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; entailer!. }
  destruct (Hopen before Hpre) as [Hwait Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired after _ Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hrun).
  - split; [exact Hstate|]. subst acquired.
    destruct (proj1 (os_sched_selection_enabled_iff state) Henabled) as [Hints Hlocks].
    assert (Hguards : uchar_load sg.(g_OSIntNesting) 0 after /\ uchar_load sg.(g_OSLockNesting) 0 after).
    { match type of Hafter with ?P after => assert (Hi : P |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT) end.
      { unfold kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
        sep_apply_l_atomic (sem_pend_interrupt_split sg state); rewrite Hints.
        entailer!; intros ? ?; exact I. }
      match type of Hafter with ?P after => assert (Hl : P |-- sg.(g_OSLockNesting) # UChar |-> 0 ** TT) end.
      { unfold kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
        sep_apply_l_atomic (sem_pend_interrupt_split sg state); rewrite Hlocks.
        entailer!; intros ? ?; exact I. }
      split; eapply framed_uchar_store_load; [exact (Hi after Hafter)|exact (Hl after Hafter)]. }
    split; [exact (proj1 Hguards)|]. split; [exact (proj2 Hguards)|]. split; [exact Hwait|].
    match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q)
      by (unfold kernel_stack_call_masked; entailer!) end end.
    exact (Hclose after Hafter).
Qed.

(** The real wait stores and the first uninterrupted Restore produce the
    canonical Scheduler input, with the SAME observed wait, invocation
    source and current-priority cache. The original and acquired state
    coincide only in this first-Save family. IRQ acquisition/Restore
    families keep their separate source producers.

    No nonempty-ready premise occurs here: this endpoint proves the
    Scheduler's two C guards and entry ownership. Selecting a valid next
    task still needs the independently established ready/Idle protocol. *)
Lemma sem_pend_wait_restore_scheduler_entry_source : forall environment critical arch
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg original call mask saved entry observed eid event tid node timeout
  before (frame : Assertion),
  sem_pend_observed_wait_origin (Some environment) critical sg original call mask saved
    entry observed entry eid event tid node ->
  sem_pend_context_error (event_slot_type_value entry.(EventState) eid)
    entry.(IntrState).(intNesting) entry.(IntrState).(lockNesting) = None ->
  task_stack_live_coverage entry.(TskState) (task_stack_call_active_key call) ->
  0 <= timeout < 4294967296 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) call **
   sem_pend_wait_prefix_cells sg entry tid node (encode_task_status node.(stat))
     (encode_pend_status node.(statPend)) node.(dly) **
   task_tcb_init_stack_covered_capsules environment entry ** unmap_table_rep sg ** frame) before ->
  let waiting := event_pend_state sg entry eid event tid node PendSem timeout in
  exists waited,
    sem_pend_wait_fragment sg entry eid event tid node timeout before waited /\
    sem_pend_wait_at (Some environment) critical sg original mask entry observed eid timeout waiting call waiting /\
    kernel_call_task_source call waiting /\
    sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
    waiting.(IntrState).(intNesting) = 0 /\ waiting.(IntrState).(lockNesting) = 0 /\
    os_sched_selection_enabled waiting = true /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor waited written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor waited final_cursor after /\
      kernel_call_restore_history environment critical sg call waiting call waiting /\
      uchar_load sg.(g_OSIntNesting) 0 after /\ uchar_load sg.(g_OSLockNesting) 0 after /\
      (sem_pend_phase_restore_output (SemPendWaitPhase original mask entry observed eid timeout waiting)
        environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
        critical sg call mask waiting ** unmap_table_rep sg ** frame) after /\
      (sem_pend_phase_sched_input (SemPendWaitPhase original mask entry observed eid timeout waiting)
        environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
        critical sg call mask waiting ** frame) after /\
      (forall (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
          environment.(task_stack_call_platform) critical arch)
        registers final_registers acquired saved_heap,
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) waiting after
          final_registers acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers waiting after final_registers acquired saved_heap /\
        acquired = waiting /\
        uchar_load sg.(g_OSIntNesting) 0 saved_heap /\ uchar_load sg.(g_OSLockNesting) 0 saved_heap /\
        sem_pend_wait_at (Some environment) critical sg original mask entry observed eid timeout
          waiting call acquired /\
        (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv critical sg
          (task_stack_call_active_key call) call final_registers.(kernel_save_r0) acquired acquired ** frame) saved_heap)).
Proof.
  intros environment critical arch restore sg original call mask saved entry observed eid event tid node timeout
    before frame Horigin Hclear Hcoverage Htimeout Hpre waiting.
  pose proof Horigin as [Hacquire [Hentry [Horiginal [Hsource Hcache]]]].
  change (sem_pend_acquire_observation environment critical sg original call mask saved
    entry entry eid observed event) in Hacquire.
  pose proof Hacquire as [Hsave [Hsame [Hsaved Hrest]]].
  assert (Hcall_source : kernel_call_task_source call entry).
  { destruct Hsame as [Hi [Ho Hs]].
    unfold kernel_call_task_source in *; rewrite Hi, Ho, Hs; exact Hsource. }
  destruct (sem_pend_wait_first_restore_input environment critical sg original entry call saved entry
    eid event tid node timeout frame before Hsave Hentry Hcall_source Hcache Hcoverage Htimeout Hpre)
    as [waited [Hstores [Hhistory [Hfirst [Hwaiting_source [Hwaiting_cache Hinput]]]]]].
  pose proof (sem_pend_observed_wait_origin_history (Some environment) critical sg original call mask saved
    entry observed entry eid event tid node timeout Horigin) as Hwait_history.
  assert (Hwait : sem_pend_wait_at (Some environment) critical sg original mask entry observed
    eid timeout waiting call waiting).
  { apply sem_pend_wait_at_waiting; [exists environment; reflexivity|exact Hsame|exact Hwait_history]. }
  assert (Hcounts : waiting.(IntrState).(intNesting) = 0 /\
    waiting.(IntrState).(lockNesting) = 0 /\ os_sched_selection_enabled waiting = true).
  { pose proof (sem_pend_wait_clear_scheduler_counts sg entry eid event tid node timeout Hclear) as Hcount_owner.
    cbv zeta in Hcount_owner.
    match type of Hinput with ?P waited => assert (Hobserve : P |--
      coq_prop (waiting.(IntrState).(intNesting) = 0 /\ waiting.(IntrState).(lockNesting) = 0 /\
        os_sched_selection_enabled waiting = true) && TT) end.
    { unfold task_tcb_init_stack_restore_input; Intros.
      sep_apply_l_atomic Hcount_owner.
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve waited Hinput)). }
  exists waited; split; [exact Hstores|]. split; [exact Hwait|].
  split; [exact Hwaiting_source|]. split; [exact Hwaiting_cache|].
  split; [exact (proj1 Hcounts)|]. split; [exact (proj1 (proj2 Hcounts))|].
  split; [exact (proj2 (proj2 Hcounts))|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (sem_pend_wait_first_restore_source environment critical arch restore sg call saved entry
    waiting cursor waited written middle final_cursor after frame Hr0 Hmask Hinput Hprefix Hsuffix)
    as [Hexecution [Hreturn [Hrestore Hclosed]]].
  pose proof (proj2 Hsaved) as Hsaved_mask.
  rewrite Hsaved_mask in Hclosed.
  assert (Hguards : uchar_load sg.(g_OSIntNesting) 0 after /\ uchar_load sg.(g_OSLockNesting) 0 after).
  { match type of Hclosed with ?P after => assert (Hi : P |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
      sep_apply_l_atomic (sem_pend_interrupt_split sg waiting).
      rewrite (proj1 Hcounts); entailer!; intros ? ?; exact I. }
    match type of Hclosed with ?P after => assert (Hl : P |-- sg.(g_OSLockNesting) # UChar |-> 0 ** TT) end.
    { unfold kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap; Intros.
      sep_apply_l_atomic (sem_pend_interrupt_split sg waiting).
      rewrite (proj1 (proj2 Hcounts)); entailer!; intros ? ?; exact I. }
    split; eapply framed_uchar_store_load; [exact (Hi after Hclosed)|exact (Hl after Hclosed)]. }
  split; [exact Hexecution|]. split; [exact Hrestore|]. split; [exact (proj1 Hguards)|].
  split; [exact (proj2 Hguards)|]. split.
  - pose proof (sem_pend_uninterrupted_restore_phase environment critical arch restore
      (SemPendWaitPhase original mask entry observed eid timeout waiting) sg call saved entry waiting
      cursor waited written middle final_cursor after frame
      ltac:(cbn [sem_pend_restore_phase_pre]; rewrite Hsaved_mask; auto)
      Hr0 Hmask Hinput Hprefix Hsuffix) as [_ Hphase].
    rewrite Hsaved_mask in Hphase; exact Hphase.
  - assert (Hsched : kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv sg
        (task_stack_call_active_key call) call mask waiting ** frame |--
      sem_pend_phase_sched_input (SemPendWaitPhase original mask entry observed eid timeout waiting)
        environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
        critical sg call mask waiting ** frame).
    { cbn [sem_pend_phase_sched_input]; unfold sem_pend_stack_sched_input, os_sched_stack_pre; entailer!. }
    pose proof (Hsched after Hclosed) as Hscheduler.
    split; [exact Hscheduler|]. intros save registers final_registers acquired saved_heap Hnext_return Hcpsr Hnext_mask Hsave_run.
    eapply sem_pend_scheduler_save_guard_source;
      [exact (proj2 (proj2 Hcounts))|exact Hnext_return|exact Hcpsr|exact Hnext_mask|exact Hscheduler|exact Hsave_run].
Qed.
