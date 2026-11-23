Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The three REAL C no-switch branches after Save. Nesting guards bypass
    all selection writes; the enabled branch performs the selector/cache
    writes and observes equal priority bytes. There is no invented ready
    or running test and no OSCtxSwCtr increment in these branches. *)
Definition os_sched_source_nonswitch_prefix_execution (sg : StableGlobVars)
  (before after : model) : Prop :=
  (exists ints, uchar_load sg.(g_OSIntNesting) ints before /\ ints <> 0 /\
    kernel_heap_execution [] before after) \/
  (uchar_load sg.(g_OSIntNesting) 0 before /\
    exists locks, uchar_load sg.(g_OSLockNesting) locks before /\ locks <> 0 /\
      kernel_heap_execution [] before after) \/
  (uchar_load sg.(g_OSIntNesting) 0 before /\ uchar_load sg.(g_OSLockNesting) 0 before /\
    os_int_exit_selection_heap_fragment sg before after /\
    exists priority, uchar_load sg.(g_OSPrioHighRdy) priority after /\
      uchar_load sg.(g_OSPrioCur) priority after).

(** This is local masked C execution, so the same disjoint frame can carry
    saved return-word/inside handles, call authority and the strong stack
    world. No framing across interrupts or scheduling is asserted here. *)
Lemma os_sched_source_nonswitch_prefix_resources : forall sg state (frame : Assertion) before,
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (UCOS2_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_nonswitch_prefix_execution sg before after /\
    (UCOS2_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hnoswitch Hnonempty Hpre.
  assert (Hopen : UCOS2_inv sg state ** unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame)) by (unfold UCOS2_inv; entailer!).
  destruct (Hopen before Hpre) as [Hvalid Hraw].
  assert (Hints : uchar_load sg.(g_OSIntNesting) state.(IntrState).(intNesting) before).
  { match type of Hraw with ?P before => assert (Hcell : P |--
      sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) ** TT) end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hcell before Hraw). }
  assert (Hlocks : uchar_load sg.(g_OSLockNesting) state.(IntrState).(lockNesting) before).
  { match type of Hraw with ?P before => assert (Hcell : P |--
      sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) ** TT) end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hcell before Hraw). }
  assert (Hempty : kernel_heap_execution [] before before) by (split; [constructor|auto]).
  destruct (Z.eq_dec state.(IntrState).(intNesting) 0) as [Hint0|Hintne].
  - rewrite Hint0 in Hints.
    destruct (Z.eq_dec state.(IntrState).(lockNesting) 0) as [Hlock0|Hlockne].
    + rewrite Hlock0 in Hlocks.
      assert (Hselection : os_sched_selection_enabled state = true)
        by (apply os_sched_selection_enabled_iff; auto).
      assert (Hequal : sched_selected_priority state.(TskState) state.(SchedState) =
        sched_priority_byte state.(SchedState).(curSchedPrio)).
      { destruct (Z.eq_dec (sched_selected_priority state.(TskState) state.(SchedState))
          (sched_priority_byte state.(SchedState).(curSchedPrio))) as [Heq|Hne]; [exact Heq|].
        assert (Hswitch : os_sched_requests_switch state = true)
          by (apply os_sched_requests_switch_iff; auto); congruence. }
      assert (Hsg : valid_stable_glob_vars sg).
      { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
      assert (Hregistered : task_current_prio_registered state.(TskState)).
      { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
      destruct (os_int_exit_selection_raw_frame_post sg state frame before Hsg
        (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered (Hnonempty Hselection) Hraw)
        as [after [Hrun [Hhighread [Hcurrentread Hafter]]]].
      assert (Hstate : os_int_exit_selection_state state = os_sched_prefix_state state).
      { unfold os_int_exit_selection_state, os_sched_prefix_state, os_sched_ready_checkpoint.
        rewrite Hselection, Hnoswitch; reflexivity. }
      assert (Hvalid_after : UCOS2_state_inv sg (os_sched_prefix_state state))
        by (apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid).
      exists after; split.
      * right; right; split; [exact Hints|]. split; [exact Hlocks|]. split; [exact Hrun|].
        exists (sched_priority_byte state.(SchedState).(curSchedPrio)); rewrite Hequal in Hhighread; auto.
      * rewrite Hstate in Hafter.
        match type of Hafter with ?P after => assert (Hclose : P |--
          UCOS2_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) end.
        { unfold UCOS2_inv; entailer!. }
        exact (Hclose after Hafter).
    + assert (Hselection : os_sched_selection_enabled state = false).
      { unfold os_sched_selection_enabled; rewrite Hint0, Z.eqb_refl.
        apply Z.eqb_neq in Hlockne; exact Hlockne. }
      assert (Hstate : os_sched_prefix_state state = state).
      { unfold os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Hselection.
        destruct state; reflexivity. }
      exists before; split.
      * right; left; split; [exact Hints|]. exists state.(IntrState).(lockNesting); auto.
      * rewrite Hstate; exact Hpre.
  - assert (Hselection : os_sched_selection_enabled state = false).
    { unfold os_sched_selection_enabled; apply Z.eqb_neq in Hintne; rewrite Hintne; reflexivity. }
    assert (Hstate : os_sched_prefix_state state = state).
    { unfold os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Hselection.
      destruct state; reflexivity. }
    exists before; split.
    + left; exists state.(IntrState).(intNesting); auto.
    + rewrite Hstate; exact Hpre.
Qed.

(** Complete the no-switch, no-intervening-IRQ call path on ONE heap:
    MRS/CPSID/DSB/BX -> actual C guards/selector -> DSB/MSR/BX. The
    unchanged strong world enters from its source producer and is returned;
    no future acquisition-safety quantifier or opaque arch-save inverse is
    required. This theorem does not hide the interrupting branches: those
    require their own current world and a distinct released/current join. *)
Lemma os_sched_source_uninterrupted_nonswitch_call_resources : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call mask state registers before final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (task_tcb_init_stack_covered_save_input environment critical sg call mask state **
   unmap_table_rep sg ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (task_tcb_init_stack_covered_save_input environment critical sg call mask
         (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after).
Proof.
  intros environment critical arch save restore sg call mask state registers before final_registers
    acquired saved_heap frame Hreturn Hcpsr Hmask Hnoswitch Hnonempty Hpre Hsave.
  assert (Hopen : task_tcb_init_stack_covered_save_input environment critical sg call mask state **
      unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call
       (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
     (UCOS2_inv sg state ** task_tcb_init_stack_covered_capsules environment state **
      unmap_table_rep sg ** frame))).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    unfold task_tcb_init_stack_covered_save_input, critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [[Hvalid Hcoverage] Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  assert (Hexecution : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired saved_heap _ Hsaved Howned Hsave)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter_save]]]].
  split; [exact Hexecution|]. split; [exact Hstate|]. subst acquired.
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask).
  { rewrite Hr0; exact Hmask. }
  match type of Hafter_save with ?P saved_heap => assert (Hprefix_input : P |--
    UCOS2_inv sg state ** unmap_table_rep sg **
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
     task_tcb_init_stack_context environment call **
     task_tcb_init_stack_covered_capsules environment state ** frame)) end.
  { unfold task_tcb_init_stack_context; entailer!. }
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ saved_heap
    Hnoswitch Hnonempty (Hprefix_input saved_heap Hafter_save)) as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hcursor_r0 Hcursor_mask Hrestore_prefix Hrestore_suffix.
  match type of Hafter_prefix with ?P prefix_heap => assert (Hrestore_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
    task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state state) **
    task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state state) **
    unmap_table_rep sg ** frame) end.
  { change (task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state state)) with
      (task_tcb_init_stack_covered_capsules environment state); entailer!. }
  assert (Horder : critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin)
      final_registers.(kernel_save_r0) state **
      task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state state) **
      task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state state) **
      unmap_table_rep sg ** frame |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin)
      final_registers.(kernel_save_r0) state **
      task_tcb_init_stack_context environment call ** UCOS2_inv sg (os_sched_prefix_state state) **
      task_tcb_init_stack_covered_capsules environment (os_sched_prefix_state state) **
      (unmap_table_rep sg ** frame)) by entailer!.
  destruct (task_tcb_init_stack_covered_uninterrupted_restore environment critical arch restore sg call
    final_registers.(kernel_save_r0) state (os_sched_prefix_state state)
    cursor prefix_heap written middle final_cursor after _
    Hcoverage Hcursor_r0 Hcursor_mask (Horder prefix_heap (Hrestore_input prefix_heap Hafter_prefix))
    Hrestore_prefix Hrestore_suffix) as [Hrestore [Hreturn_word Hpost]].
  split; [exact Hrestore|]. rewrite Hsaved_mask in Hpost.
  match type of Hpost with ?P after => assert (Hclose : P |--
    task_tcb_init_stack_covered_save_input environment critical sg call mask
      (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) by entailer! end.
  exact (Hclose after Hpost).
Qed.

(** Keep the previous existential public post for its existing consumers.
    The source producer above retains the actual returned call and state,
    so a following Save can use their observations on this same heap. *)
Lemma os_sched_source_uninterrupted_nonswitch_call : forall environment critical arch
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg call mask state registers before final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (task_tcb_init_stack_covered_save_input environment critical sg call mask state **
   unmap_table_rep sg ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (os_sched_covered_call_post environment critical sg call mask state ** frame) after).
Proof.
  intros environment critical arch save restore sg call mask state registers before final_registers
    acquired saved_heap frame Hreturn Hcpsr Hmask Hnoswitch Hnonempty Hpre Hsave.
  destruct (os_sched_source_uninterrupted_nonswitch_call_resources environment critical arch save restore
    sg call mask state registers before final_registers acquired saved_heap frame
    Hreturn Hcpsr Hmask Hnoswitch Hnonempty Hpre Hsave) as [Hsave_run [Hstate [prefix_heap [Hprefix Hrestore]]]].
  split; [exact Hsave_run|]. split; [exact Hstate|]. exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix.
  destruct (Hrestore cursor written middle final_cursor after Hr0 Hmasked Hrestore_prefix Hrestore_suffix)
    as [Hrun Hafter].
  split; [exact Hrun|].
  assert (Hpost : task_tcb_init_stack_covered_save_input environment critical sg call mask
      (os_sched_prefix_state state) ** unmap_table_rep sg ** frame |--
    os_sched_covered_call_post environment critical sg call mask state ** frame).
  { assert (Hinterval : critical_region_interval critical sg call.(os_sched_call_invocation) state state)
      by constructor.
    assert (Hreturn_source : os_sched_c_return environment.(task_stack_call_external) critical sg
      state call call (os_sched_prefix_state state)).
    { unfold os_sched_c_return; rewrite Hnoswitch; auto. }
    unfold os_sched_covered_call_post; Exists state call (os_sched_prefix_state state); entailer!. }
  exact (Hpost after Hafter).
Qed.

(** Scheduler guards and high-ready cache writes leave both the active
    invocation and OSTCBCur unchanged. The original source cut, rather
    than an arbitrary CPU token, supplies the task's identity. This also
    covers a locked self-suspend: no readiness is asserted here. *)
Lemma os_sched_prefix_preserves_task_source : forall call state,
  kernel_call_task_source call state ->
  kernel_call_task_source call (os_sched_prefix_state state).
Proof.
  intros call state [Horigin [Hactive Hcurrent]].
  split; [exact Horigin|]. split; [exact Hactive|].
  unfold task_execution_current in *; rewrite Horigin in *.
  change ((os_sched_ready_checkpoint state).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)).
  rewrite (proj1 (proj2 (os_sched_ready_checkpoint_frame state))); exact Hcurrent.
Qed.

(** Equality of the actual selector byte identifies the ready head only
    when the current-priority cache is tied to this source-stage TCB.
    That relation is NOT part of UCOS2_state_inv or task_source: a locked
    ChangePrio may leave OSPrioCur stale. Blocking-source consumers must
    establish it from their real preceding writes/observations. *)
Lemma os_sched_nonswitch_current_ready_at : forall sg call state,
  UCOS2_state_inv sg state ->
  kernel_call_task_source call state ->
  sched_current_consistency state.(TskState) state.(SchedState) ->
  os_sched_selection_enabled state = true ->
  os_sched_requests_switch state = false ->
  state.(SchedState).(readyList) <> [] ->
  exists node,
    sched_current_ready_at (os_sched_prefix_state state).(TskState)
      (os_sched_prefix_state state).(SchedState) call.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros sg call state Hvalid Hsource Hconsistent Hen Hnoswitch Hnonempty.
  destruct (kernel_call_task_source_current_at call state Hsource)
    as [Hcurrent [node [Hnode Hgeneration]]].
  pose proof (proj1 (proj1 (proj2 (proj2 Hvalid)))) as Hready.
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  unfold sched_current_consistency in Hconsistent; rewrite Hcurrent in Hconsistent.
  destruct Hconsistent as [current [Hget Hpriority]].
  rewrite Hnode in Hget; inversion Hget; subst current.
  destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  assert (Hhead_in : In head state.(SchedState).(readyList)) by (rewrite Hlist; left; reflexivity).
  destruct (proj1 Hready head Hhead_in) as [head_node [Hhead [_ Heffective]]].
  assert (Hequal : sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio)).
  { destruct (Z.eq_dec (sched_selected_priority state.(TskState) state.(SchedState))
      (sched_priority_byte state.(SchedState).(curSchedPrio))) as [Heq|Hne]; [exact Heq|].
    assert (Hswitch : os_sched_requests_switch state = true)
      by (apply os_sched_requests_switch_iff; auto); congruence. }
  rewrite (sched_selected_priority_eq_head sg _ _ head tail head_node
    Hsg Hready Hlist Hhead), Hpriority in Hequal.
  cbn [sched_priority_byte] in Hequal.
  assert (Hhead_slot : head = call.(os_sched_call_stack).(stackLeaseSlot)).
  { eapply task_registration_implies_priority_unique; eassumption. }
  rewrite Hhead_slot, Hnode in Hhead; inversion Hhead; subst head_node.
  exists node; split; [|exact Hgeneration].
  unfold sched_current_ready_at; cbn [os_sched_prefix_state replace_SchedS TskState SchedState].
  destruct (os_sched_ready_checkpoint_frame state) as [Hrdy [Hcur [Hprio Hrunning]]].
  rewrite Hrdy, Hcur, Hprio; repeat split; try assumption.
  rewrite <- Hhead_slot; exact Hhead_in.
Qed.
