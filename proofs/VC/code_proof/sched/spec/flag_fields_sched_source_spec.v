Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_selected_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source fragments for the fields global owner. The SAME original state
    relations, parked keys, descriptors and local policies are used throughout.
    Supplementary padding, if actually owned, remains a disjoint frame.

    Prefix readiness is conditional on the real selection guards. No outgoing
    current-ready or clean-registration premise is added. Physical frame
    geometry, current invocation history, absent outgoing key and actual
    capture/restore transitions remain explicit as in the checked source chain.

    The selection endpoint below uses the existing explicit empty heap-effect
    hook plus matching client step. The final saved-call return begins at an
    actual current selection; it does not create the intervening client trace,
    exclude stop paths, promise eventual selection, or establish a public API
    contract. Existing C carriers still require their original full world. *)

(** Fields spatial counterpart of [os_sched_source_nonswitch_prefix_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_nonswitch_prefix_resources : forall sg state (frame : Assertion) before,
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_nonswitch_prefix_execution sg before after /\
    (UCOS2_fields_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hnoswitch Hnonempty Hpre.
  assert (Hopen : UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (UCOS2_fields_raw_rep sg state ** unmap_table_rep sg ** frame)) by (unfold UCOS2_fields_inv; entailer!).
  destruct (Hopen before Hpre) as [Hvalid Hraw].
  assert (Hints : uchar_load sg.(g_OSIntNesting) state.(IntrState).(intNesting) before).
  { match type of Hraw with ?P before => assert (Hcell : P |--
      sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) ** TT) end.
    { rewrite (UCOS2_fields_raw_rep_split_module sg state InterruptModule) by discriminate;
      cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!; intros ? ?; exact I. }
    eapply framed_uchar_store_load; exact (Hcell before Hraw). }
  assert (Hlocks : uchar_load sg.(g_OSLockNesting) state.(IntrState).(lockNesting) before).
  { match type of Hraw with ?P before => assert (Hcell : P |--
      sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) ** TT) end.
    { rewrite (UCOS2_fields_raw_rep_split_module sg state InterruptModule) by discriminate;
      cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!; intros ? ?; exact I. }
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
      destruct (os_int_exit_selection_fields_raw_frame_post sg state frame before Hsg
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
          UCOS2_fields_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) end.
        { unfold UCOS2_fields_inv; entailer!. }
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

(** Fields spatial counterpart of [kernel_sched_switch_prefix_frame_source].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_switch_prefix_frame_source : forall sg state (frame : Assertion) before,
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  (UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
      (os_sched_prefix_state state).(SchedState) /\
    (UCOS2_fields_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hswitch Hnonempty Hpre.
  destruct (proj1 (os_sched_requests_switch_iff state) Hswitch) as [Hselection Hdifferent].
  destruct (proj1 (os_sched_selection_enabled_iff state) Hselection) as [Hints Hlocks].
  assert (Hopen : UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state) && (UCOS2_fields_raw_rep sg state ** unmap_table_rep sg ** frame))
    by (unfold UCOS2_fields_inv; entailer!).
  destruct (Hopen before Hpre) as [Hvalid Hraw].
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hguards : uchar_load sg.(g_OSIntNesting) 0 before /\ uchar_load sg.(g_OSLockNesting) 0 before).
  { match type of Hraw with ?P before => assert (Hi : P |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT) end.
    { rewrite (UCOS2_fields_raw_rep_split_module sg state InterruptModule) by discriminate;
      cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; rewrite Hints; entailer!; intros ? ?; exact I. }
    match type of Hraw with ?P before => assert (Hl : P |-- sg.(g_OSLockNesting) # UChar |-> 0 ** TT) end.
    { rewrite (UCOS2_fields_raw_rep_split_module sg state InterruptModule) by discriminate;
      cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; rewrite Hlocks; entailer!; intros ? ?; exact I. }
    split; eapply framed_uchar_store_load; [exact (Hi before Hraw)|exact (Hl before Hraw)]. }
  destruct (os_int_exit_selection_fields_raw_frame_post sg state frame before Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty Hraw)
    as [selected [Hselect [Hhighread [Hcurrentread Hselected]]]].
  destruct Hselected as [selected_owned [rest [Hjoin
    [[raw [unmap [Hselected_join [Hselected_raw Hunmap]]]] Hrest]]]].
  destruct (os_sched_profile_global_fields_raw_post sg (os_int_exit_selection_state state) raw Hselected_raw)
    as [counted [Hcounter Hcounted]].
  destruct (os_sched_profile_global_fragment_frame sg raw counted unmap selected_owned Hcounter Hselected_join)
    as [counted_owned [Hcounter_owned Hcounted_join]].
  destruct (os_sched_profile_global_fragment_frame sg selected_owned counted_owned rest selected Hcounter_owned Hjoin)
    as [after [Hcounter_whole Hafter_join]].
  assert (Hstate : os_sched_profile_global_state (os_int_exit_selection_state state) = os_sched_prefix_state state).
  { unfold os_sched_profile_global_state, os_int_exit_selection_state, os_sched_prefix_state,
      os_sched_ready_checkpoint; rewrite Hselection, Hswitch; reflexivity. }
  assert (Hvalid_after : UCOS2_state_inv sg (os_sched_prefix_state state))
    by (apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid).
  exists after; split.
  - split; [exact (proj1 Hguards)|]. split; [exact (proj2 Hguards)|].
    exists selected, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_priority_byte state.(SchedState).(curSchedPrio)).
    exact (conj Hselect (conj Hhighread (conj Hcurrentread (conj Hdifferent Hcounter_whole)))).
  - split.
    + apply os_sched_ready_checkpoint_high_consistency with (sg := sg);
        [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hselection].
    + exists counted_owned, rest; split; [exact Hafter_join|]. split; [|exact Hrest].
      exists counted, unmap; split; [exact Hcounted_join|]. split; [|exact Hunmap].
      split; [exact Hvalid_after|rewrite <- Hstate; exact Hcounted].
Qed.

(** Fields spatial counterpart of [os_sched_modular_prefix_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_modular_prefix_resources : forall sg state (frame : Assertion) before,
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (UCOS2_fields_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (UCOS2_fields_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hnonempty Hpre.
  unfold os_sched_modular_prefix_execution.
  destruct (os_sched_requests_switch state) eqn:Hswitch.
  - destruct (proj1 (os_sched_requests_switch_iff state) Hswitch) as [Henabled _].
    destruct (os_sched_fields_switch_prefix_frame_source sg state frame before
      Hswitch (Hnonempty Henabled) Hpre) as [after [Hrun [Hhigh Hpost]]].
    exists after; split; [exact Hrun|]. split; [intros _; exact Hhigh|exact Hpost].
  - destruct (os_sched_fields_nonswitch_prefix_resources sg state frame before
      Hswitch Hnonempty Hpre) as [after [Hrun Hpost]].
    exists after; split; [exact Hrun|]. split; [discriminate|exact Hpost].
Qed.

(** Fields spatial counterpart of [os_sched_modular_prefix_continuation_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_modular_prefix_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  local critical sg active call saved acquired state before (frame : Assertion),
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active
    call saved acquired state ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active
      call saved acquired (os_sched_prefix_state state) ** frame) after.
Proof.
  intros external platform port abi local critical sg active call saved acquired state before frame
    Hnonempty Hpre.
  set (prefix_frame :=
    critical_region_masked platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources external call **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** frame).
  assert (Hopen :
    kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active
      call saved acquired state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) active) &&
    (UCOS2_fields_inv sg state ** unmap_table_rep sg ** prefix_frame)).
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, prefix_frame.
    rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Hphysical].
  destruct (os_sched_fields_modular_prefix_resources sg state prefix_frame before Hnonempty Hphysical)
    as [after [Hrun [Hhigh Hafter]]].
  exists after; split; [exact Hrun|]. split; [exact Hhigh|].
  assert (Hclose :
    UCOS2_fields_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** prefix_frame |--
    kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active
      call saved acquired (os_sched_prefix_state state) ** frame).
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, prefix_frame.
    rewrite kernel_program_fields_inv_split_unmap.
    change (os_sched_prefix_state state).(TskState) with state.(TskState).
    entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Fields spatial counterpart of [os_sched_modular_nonswitch_continuation_call].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_modular_nonswitch_continuation_call :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (save : Armv7aSaveSuffixABI external platform critical arch)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    local sg active call mask state registers before
    final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_continuation_call_closed abi kernel_program_fields_inv local sg active
    call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (kernel_continuation_call_closed abi kernel_program_fields_inv local sg active
        call mask (os_sched_prefix_state state) ** frame) after).
Proof.
  intros external platform port critical arch abi save restore local sg active call mask state
    registers before final_registers acquired saved_heap frame Hreturn Hvalid Hmask
    Hnoswitch Hnonempty Hpre Hsave.
  destruct (kernel_continuation_call_uninterrupted_save external platform port critical arch
    abi save kernel_program_fields_inv local sg active call state mask registers before
    final_registers acquired saved_heap frame Hreturn Hvalid Hmask Hpre Hsave)
    as [Hstate [Hr0 [Hsave_run Hmasked]]].
  split; [exact Hstate|]. split; [exact Hsave_run|]. subst acquired.
  destruct (os_sched_fields_modular_prefix_continuation_resources external platform port abi local
    critical sg active call final_registers.(kernel_save_r0) state state saved_heap frame
    Hnonempty Hmasked) as [prefix_heap [Hprefix [_ Hafter_prefix]]].
  unfold os_sched_modular_prefix_execution in Hprefix; rewrite Hnoswitch in Hprefix.
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hrestore_r0 Hrestore_mask Hprefix_run Hsuffix_run.
  destruct (kernel_continuation_call_uninterrupted_restore external platform port critical arch
    abi restore kernel_program_fields_inv local sg active call final_registers.(kernel_save_r0)
    state (os_sched_prefix_state state) cursor prefix_heap written middle final_cursor after frame
    Hrestore_r0 Hrestore_mask Hafter_prefix Hprefix_run Hsuffix_run)
    as [Hrestore_run [Hword Hclosed]].
  rewrite Hr0, Hmask in Hclosed.
  split; assumption.
Qed.

(** Fields spatial counterpart of [flag_source_sched_prefix_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma flag_fields_source_sched_prefix_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  local critical sg active call saved acquired state before (current_local frame : Assertion),
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (flag_source_restore_input abi kernel_program_fields_inv local critical sg active call saved acquired state
    current_local ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (flag_source_restore_input abi kernel_program_fields_inv local critical sg active call saved acquired
      (os_sched_prefix_state state) current_local ** frame) after.
Proof.
  intros external platform port abi local critical sg active call saved acquired state before current_local frame
    Hnonempty Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    kernel_continuation_call_masked abi kernel_program_fields_inv local critical sg active call saved acquired state **
      (current_local ** frame)) end.
  { unfold flag_source_restore_input; entailer!. }
  destruct (os_sched_fields_modular_prefix_continuation_resources external platform port abi local critical sg active
    call saved acquired state before (current_local ** frame) Hnonempty (Hopen before Hpre))
    as [after [Hrun [Hhigh Hafter]]].
  exists after; split; [exact Hrun|]. split; [exact Hhigh|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold flag_source_restore_input; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Fields spatial counterpart of [flag_source_sched_nonswitch_return_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma flag_fields_source_sched_nonswitch_return_resources : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  local sg active call saved acquired state before (current_local frame : Assertion),
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (flag_source_restore_input abi kernel_program_fields_inv local critical sg active call saved acquired state
    current_local ** frame) before ->
  exists prefix_heap,
    os_sched_modular_prefix_execution sg state before prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      os_sched_c_return external critical sg state call call (os_sched_prefix_state state) /\
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (flag_source_save_input abi kernel_program_fields_inv local sg active call (armv7a_irq_fiq_mask saved)
        (os_sched_prefix_state state) current_local ** frame) after.
Proof.
  intros external platform port critical arch abi restore local sg active call saved acquired state before
    current_local frame Hnoswitch Hnonempty Hpre.
  destruct (flag_fields_source_sched_prefix_resources external platform port abi local critical sg active call saved
    acquired state before current_local frame Hnonempty Hpre) as [prefix_heap [Hprefix [Hhigh Howned]]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix.
  split.
  - unfold os_sched_c_return; rewrite Hnoswitch; auto.
  - exact (flag_source_uninterrupted_restore_resources external platform port critical arch abi restore
      kernel_program_fields_inv local sg active call saved acquired (os_sched_prefix_state state) cursor prefix_heap
      written middle final_cursor after current_local frame Hr0 Hmask Howned Hwrite Hsuffix).
Qed.

(** Fields spatial counterpart of [kernel_saved_continuation_store_live_sp_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma kernel_saved_continuation_fields_store_live_sp_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state lease node sp
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) before,
  state.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
  node.(taskID) = lease.(stackLeaseSlot) ->
  node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key lease) = None ->
  tcb_field_address (task_slot_addr sg lease.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg lease.(stackLeaseSlot) ->
  0 <= sp < 4294967296 ->
  (UCOS2_fields_inv sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg lease.(stackLeaseSlot)) sp) before after /\
    (UCOS2_fields_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
     store_parked_continuations
       (kernel_saved_continuation_entry abi
         (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState) local)
       (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state lease node sp local frame before
    Hnode Hid Hgen Hnone Haddress Hsp Hbefore.
  match type of Hbefore with ?P before => assert (Hopen : P |--
    coq_prop (UCOS2_state_inv sg state) &&
      (UCOS2_fields_raw_rep sg state **
       (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** frame))) end.
  { unfold UCOS2_fields_inv; entailer!. }
  destruct (Hopen before Hbefore) as [Hvalid [owned [rest [Hjoin [Hraw Hrest]]]]].
  destruct (armv7a_irq_store_live_sp_fields_raw_post sg state lease.(stackLeaseSlot) node sp owned
    Hnode Haddress Hsp Hraw) as [written [Hwrite Hwritten]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hwrite Hjoin) as [after [Hrun Hafter]].
  assert (Hupdated : UCOS2_state_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp)).
  { unfold os_sched_save_current_sp; rewrite Hnode.
    exact (os_sched_save_live_sp_preserves_validity sg state node sp lease Hvalid Hnode Hid Hgen Hnone). }
  assert (Hclose : UCOS2_fields_raw_rep sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
      (store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
         state.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_fields_inv sg (os_sched_save_current_sp state lease.(stackLeaseSlot) sp) **
    store_parked_continuations
      (kernel_saved_continuation_entry abi
        (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState) local)
      (os_sched_save_current_sp state lease.(stackLeaseSlot) sp).(TskState).(parkedTaskStacks) ** frame).
  { unfold UCOS2_fields_inv.
    sep_apply_l_atomic (kernel_saved_continuation_map_save_sp external platform port abi
      state.(TskState) node sp lease local state.(TskState).(parkedTaskStacks) Hnode Hgen Hnone).
    unfold os_sched_save_current_sp in Hupdated |- *; rewrite Hnode in Hupdated |- *.
    cbn [replace_TskS TskState glob_task_set_usedtask parkedTaskStacks]; entailer!. }
  exists after; split; [exact Hrun|].
  apply Hclose; exists written, rest; tauto.
Qed.

(** Fields spatial counterpart of [kernel_task_save_continuation_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma kernel_task_save_continuation_fields_resources :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg state node call old_sp cpsr registers lr prefix suffix first old_words
    (local : Armv7aContinuation -> Assertion) (frame : Assertion) before,
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_call_execution_owned external platform call 192 ** UCOS2_fields_inv sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks) ** local descriptor ** frame) before ->
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call descriptor stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
      (UCOS2_fields_inv sg updated **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       kernel_saved_continuation_entry abi updated.(TskState) local
         (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       armv7a_task_switch_control task_abi call ** frame) captured).
Proof.
  intros external platform port abi task_abi sg state node call old_sp cpsr registers lr prefix suffix first
    old_words local frame before fragments descriptor updated Hcurrent Hnode Hid Hgen Hnone Hcoverage Hfragments
    Hlength Hcpsr Hlr Hranges Hmask Hsprange Hsp Haddress Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) **
    (UCOS2_fields_inv sg state **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) **
     interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
     external.(os_sched_arch_running) call ** local descriptor ** frame)) end.
  { unfold kernel_call_execution_owned, os_sched_context_resources; rewrite Hfragments; entailer!. }
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr registers lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp (Horder before Hpre))
    as [written [Hwrites [Hwritten [Hreads Hslice]]]].
  fold fragments descriptor in Hwritten, Hreads, Hslice.
  assert (Hload : pointer_load sg.(g_OSTCBCur)
    (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written).
  { match type of Hwritten with ?P written => assert (Hraw_owner : P |--
      UCOS2_fields_raw_rep sg state ** TT) end.
    { unfold UCOS2_fields_inv; entailer!; intros ? ?; exact I. }
    destruct (Hraw_owner written Hwritten) as [owned [rest [Hjoin [Hraw Hrest]]]].
    pose proof (armv7a_irq_fields_raw_current_pointer_load sg state owned Hraw) as Hread.
    rewrite Hcurrent in Hread; cbn [encode_task_link] in Hread.
    eapply pointer_load_frame; [exact Hread|exact Hjoin]. }
  match type of Hwritten with ?P written => assert (Hstore_input : P |--
    UCOS2_fields_inv sg state **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) **
    (task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
       descriptor.(armv7a_continuation_fragments) **
     interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
     external.(os_sched_arch_running) call ** local descriptor ** frame)) end.
  { unfold descriptor, armv7a_task_save_image; cbn; entailer!. }
  destruct (kernel_saved_continuation_fields_store_live_sp_resources external platform port abi sg state
    call.(os_sched_call_stack) node descriptor.(armv7a_continuation_sp) local _ written
    Hnode Hid Hgen Hnone Haddress Hsprange (Hstore_input written Hwritten))
    as [stored [Hstore Hstored]].
  fold updated in Hstored.
  assert (Hbinding : armv7a_continuation_binding descriptor)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive : task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack))
    descriptor.(armv7a_continuation_sp)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    intros other Hother Hothergen;
      cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates task_stack_key fst] in Hother.
    rewrite Z.eqb_refl in Hother; injection Hother as Hother; subst other; reflexivity. }
  assert (Hcovered : task_stack_live_coverage updated.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    apply task_stack_save_sp_preserves_coverage; assumption. }
  assert (Hstored_reads : armv7a_continuation_restore_reads descriptor stored).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hstored with ?P stored => assert (Hfocus : P |--
      task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
        descriptor.(armv7a_continuation_fragments) **
      (UCOS2_fields_inv sg updated **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** local descriptor ** frame)) by entailer! end.
    exact (Hfocus stored Hstored). }
  exists written, stored.
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  split; [exact Hcovered|]. intros captured Hcapture.
  match type of Hstored with ?P stored => assert (Hcapture_input : P |--
    interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
    external.(os_sched_arch_running) call ** local descriptor **
    (UCOS2_fields_inv sg updated **
     store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
       updated.(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
       descriptor.(armv7a_continuation_fragments) ** frame)) by entailer! end.
  assert (Hdescriptor_mask : armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192).
  { unfold descriptor, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  destruct (kernel_saved_continuation_capture_source external platform port abi task_abi
    updated.(TskState) local call descriptor _ stored captured
    eq_refl Hbinding Hslice Hlive Hstored_reads Hdescriptor_mask
    (Hcapture_input stored Hstored) Hcapture)
    as [Hmemory [Hsource Hcaptured]].
  match type of Hcaptured with ?P captured => assert (Hclose : P |--
    UCOS2_fields_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
      updated.(TskState).(parkedTaskStacks) ** armv7a_task_switch_control task_abi call ** frame) end.
  { assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack))
      by reflexivity.
    assert (Hdescriptor_fragments : descriptor.(armv7a_continuation_fragments) = fragments)
      by reflexivity.
    rewrite Hlease, Hdescriptor_fragments; entailer!. }
  exact (conj Hmemory (conj Hsource (Hclose captured Hcaptured))).
Qed.

(** Fields spatial counterpart of [os_sched_modular_switch_capture].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_modular_switch_capture :
  forall external platform port critical
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg state node call saved acquired other old_sp cpsr registers lr prefix suffix first old_words
    before (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  let local := kernel_sched_saved_local_at platform critical sg checkpoint.(TskState)
    call saved acquired other in
  os_sched_requests_switch state = true ->
  state.(SchedState).(readyList) <> [] ->
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_call_masked abi kernel_program_fields_inv other critical sg
    (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state ** frame) before ->
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg before prefix_heap /\
    sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState) /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call descriptor stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
      (UCOS2_fields_inv sg updated **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       kernel_saved_continuation_entry abi updated.(TskState) local
         (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       armv7a_task_switch_control task_abi call ** (unmap_table_rep sg ** frame)) captured).
Proof.
  intros external platform port critical abi task_abi sg state node call saved acquired other old_sp cpsr
    registers lr prefix suffix first old_words before frame checkpoint fragments descriptor updated local
    Hswitch Hnonempty Hsource Hnode Hid Hgeneration Habsent Hfragments Hlength Hcpsr Hlr Hranges Hmask
    Hsprange Hsp Haddress Hpre.
  destruct (os_sched_fields_modular_prefix_continuation_resources external platform port abi other critical sg
    (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state before frame
    (fun _ => Hnonempty) Hpre) as [prefix_heap [Hprefix [Hhigh Hmasked]]].
  unfold os_sched_modular_prefix_execution in Hprefix; rewrite Hswitch in Hprefix.
  specialize (Hhigh Hswitch); fold checkpoint in Hhigh, Hmasked.
  assert (Hsource_checkpoint : kernel_call_task_source call checkpoint).
  { apply os_sched_prefix_preserves_task_source; exact Hsource. }
  pose proof (proj1 (kernel_call_task_source_current_at call checkpoint Hsource_checkpoint)) as Hcurrent.
  assert (Hcoverage : task_stack_live_coverage checkpoint.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hmasked with ?P prefix_heap => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage checkpoint.(TskState)
        (Some (task_stack_key call.(os_sched_call_stack)))) && TT) end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve prefix_heap Hmasked)). }
  assert (Hlocal : interrupt_platform_saved platform
      (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) acquired |-- local descriptor).
  { unfold local; rewrite kernel_sched_saved_local_at_selected by reflexivity.
    exact (kernel_sched_saved_image_local_resources platform critical sg checkpoint call saved acquired
      old_sp cpsr registers lr fragments Hsource_checkpoint Hmask). }
  assert (Hmap : store_parked_continuations
      (kernel_saved_continuation_entry abi checkpoint.(TskState) other)
      checkpoint.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
      checkpoint.(TskState).(parkedTaskStacks)).
  { unfold local; apply kernel_saved_continuation_map_focus_absent; exact Habsent. }
  match type of Hmasked with ?P prefix_heap => assert (Hsave_input : P |--
    kernel_call_execution_owned external platform call 192 ** UCOS2_fields_inv sg checkpoint **
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
      checkpoint.(TskState).(parkedTaskStacks) ** local descriptor ** (unmap_table_rep sg ** frame)) end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, critical_region_masked,
      kernel_call_execution_owned; rewrite kernel_program_fields_inv_split_unmap.
    Intros.
    sep_apply_l_atomic Hmap; sep_apply_l_atomic Hlocal; entailer!. }
  destruct (kernel_task_save_continuation_fields_resources external platform port abi task_abi sg checkpoint node call
    old_sp cpsr registers lr prefix suffix first old_words local (unmap_table_rep sg ** frame) prefix_heap
    Hcurrent Hnode Hid Hgeneration Habsent Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hmask
    Hsprange Hsp Haddress (Hsave_input prefix_heap Hmasked))
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  exists prefix_heap, written, stored.
  exact (conj Hprefix (conj Hhigh (conj Hwrites (conj Hload (conj Hstore (conj Hcovered Hcapture)))))).
Qed.

(** Fields spatial counterpart of [task_stack_framed_live_sp_load].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma task_stack_fields_framed_live_sp_load : forall sg state slot node (frame : Assertion) heap,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  (UCOS2_fields_inv sg state ** frame) heap ->
  pointer_load (task_slot_addr sg slot) node.(tcbStkPtr) heap.
Proof.
  intros sg state slot node frame heap Hnode Haddress
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  eapply pointer_load_frame; [|exact Hjoin].
  eapply armv7a_irq_fields_raw_live_stack_pointer_load; eassumption.
Qed.

(** Fields spatial counterpart of [os_sched_install_continuation_map_resources].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_install_fields_continuation_map_resources :
  forall external sg context saved hooked incoming resumed
    (resource : (TaskID * nat) -> (TaskStackRegion * TaskStackFragments) -> Assertion)
    (frame : Assertion) heap,
  os_sched_saved_stack_binding context saved hooked ->
  os_sched_destination_binding external context saved hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (UCOS2_fields_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame) heap ->
  exists final sp,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot)) sp /\
    (coq_prop (task_current_at (os_sched_install_context context saved incoming hooked)
        incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
      external.(os_sched_arch_restore_source) incoming sp resumed) &&
     (UCOS2_fields_inv sg (os_sched_install_context context saved incoming hooked) **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
      resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
      store_parked_continuations resource
        (os_sched_install_context context saved incoming hooked).(TskState).(parkedTaskStacks) **
      frame)) final.
Proof.
  intros external sg context saved hooked incoming resumed resource frame heap
    Hsaved Hdestination Haddress Hbefore.
  assert (Hnone : hooked.(TskState).(parkedTaskStacks)
    (task_stack_key context.(os_sched_call_stack)) = None).
  { unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  pose proof Hdestination as [_ [_ [_ Hparked]]].
  assert (Horder : UCOS2_fields_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved **
      resource (task_stack_key context.(os_sched_call_stack))
        (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
      store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame |--
    (UCOS2_fields_inv sg hooked **
      task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) saved) **
    (resource (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
     store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame)) by entailer!.
  destruct (os_sched_install_fields_heap_take_destination_frame external sg context saved hooked incoming
    resumed _ heap Hsaved Hdestination Haddress (Horder heap Hbefore))
    as [final [sp [Hrun [Hfacts Hafter]]]].
  assert (Hswitch :
    (UCOS2_fields_inv sg (os_sched_install_context context saved incoming hooked) **
     task_stack_fragments_rep incoming.(stackLeaseRegion) resumed) **
    (resource (task_stack_key context.(os_sched_call_stack))
       (context.(os_sched_call_stack).(stackLeaseRegion), saved) **
     store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_fields_inv sg (os_sched_install_context context saved incoming hooked) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
    resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
    store_parked_continuations resource
      (os_sched_install_context context saved incoming hooked).(TskState).(parkedTaskStacks) ** frame).
  { sepcon_assoc_change.
    sep_apply_l_atomic (store_parked_continuations_switch resource hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) incoming saved resumed Hnone Hparked).
    unfold os_sched_install_context.
    cbn [replace_SchedS replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    entailer!. }
  exists final, sp; split; [exact Hrun|]. split; [exact Hfacts|exact (Hswitch final Hafter)].
Qed.

(** Fields spatial counterpart of [kernel_saved_continuation_install_source].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma kernel_saved_continuation_fields_install_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg call outgoing hooked incoming resumed local before (frame : Assertion),
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context call outgoing incoming hooked in
  os_sched_saved_stack_binding call outgoing hooked ->
  os_sched_destination_binding external call outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at current incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming)) /\
    (forall restored,
      armv7a_task_restore_transition task_abi call selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected ** local selected **
       kernel_program_fields_inv sg current **
       store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
         current.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi task_abi sg call outgoing hooked incoming resumed local before frame
    resource current Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (os_sched_install_fields_continuation_map_resources external sg call outgoing hooked incoming resumed resource
    _ before Hsaved Hdestination Haddress Hpre) as [installed [sp [Hrun [[Hcurrent Harch] Hinstalled]]]].
  fold current in Hcurrent, Hinstalled.
  match type of Hinstalled with ?P installed => assert (Hextract : P |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\ armv7a_task_frame_slice selected /\
        task_stack_live_sp hooked.(TskState) (task_stack_key incoming) selected.(armv7a_continuation_sp)) &&
      (UCOS2_fields_inv sg current **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       local selected ** store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) end.
  { unfold resource at 1; unfold kernel_saved_continuation_entry at 1; Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct selected.(armv7a_continuation_stack), incoming; cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    Exists selected; rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hextract installed Hinstalled) as
    [selected [[Hbinding [Hlease [Hfragments [Hslice Hlive]]]] Howned]].
  pose proof Hdestination as [Hhigh [[node [Hnode [Hgen [Hprio Hsource]]]] Hrest]].
  assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  assert (Hload : pointer_load (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) installed).
  { eapply task_stack_fields_framed_live_sp_load with (state := current); [exact Hnode|exact Haddress|].
    match type of Howned with ?P installed => assert (Horder : P |-- UCOS2_fields_inv sg current **
      (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
       local selected ** store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hsp : sp = selected.(armv7a_continuation_sp)).
  { rewrite <- Hnode_sp; eapply pointer_load_deterministic; [exact (proj2 Hrun)|exact Hload]. }
  rewrite Hsp in Hrun.
  assert (Hreads : armv7a_continuation_restore_reads selected installed).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Howned with ?P installed => assert (Horder : P |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_fields_inv sg current ** armv7a_task_continuation_resource abi selected ** local selected **
       store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hcovered : task_stack_live_coverage current.(TskState) (Some (task_stack_key incoming))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) outgoing))
      incoming (task_stack_park_covers_active hooked.(TskState) call.(os_sched_call_stack) outgoing Hcoverage)). }
  exists installed, selected; split; [exact Hrun|]. split; [exact Hreads|]. split; [exact Hbinding|].
  split; [exact Hlease|]. split; [exact Hfragments|]. split; [exact Hcurrent|]. split; [exact Hcovered|].
  intros restored Hrestore.
  match type of Howned with ?P installed => assert (Hrestore_input : P |--
    armv7a_task_switch_control task_abi call **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
    (local selected ** kernel_program_fields_inv sg current **
     store_parked_continuations resource current.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_fields_inv_split_unmap; entailer!. }
  destruct (armv7a_task_restore_resources _ _ _ abi task_abi call selected _ installed restored
    Hreads (Hrestore_input installed Howned) Hrestore) as [Hmemory [Hresume_source Hrestored]].
  split; [exact Hmemory|]. split; [exact Hresume_source|].
  match type of Hrestored with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) end end.
  { change (kernel_saved_continuation_entry abi current.(TskState) local) with resource; entailer!. }
  exact (Hclose restored Hrestored).
Qed.

(** Fields spatial counterpart of [os_sched_continuation_high_destination].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_continuation_high_destination : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg call outgoing hooked local (frame : Assertion) heap,
  os_sched_saved_stack_binding call outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked **
   kernel_saved_continuation_entry abi hooked.(TskState) local
     (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations (kernel_saved_continuation_entry abi hooked.(TskState) local)
     hooked.(TskState).(parkedTaskStacks) ** frame) heap ->
  exists incoming resumed node,
    os_sched_destination_binding external call outgoing hooked incoming resumed /\
    hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
    is_effectively_ready node.(stat) node.(dly) = true.
Proof.
  intros external platform port abi task_abi initial sg call outgoing hooked local frame heap
    Hsaved Hhigh Hnonempty Hcoverage Hpre.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_fields_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hpre)). }
  destruct (os_sched_covered_high_destination sg call outgoing hooked Hvalid Hsaved Hhigh Hnonempty Hcoverage)
    as [incoming [resumed [node [Hselected [Hnode [Hgen [Hpriority [Hlive [Hlookup [Hin Hready]]]]]]]]]].
  assert (Habsent : hooked.(TskState).(parkedTaskStacks)
    (task_stack_key call.(os_sched_call_stack)) = None) by (unfold os_sched_saved_stack_binding in Hsaved; tauto).
  assert (Hentry : kernel_saved_continuation_entry abi hooked.(TskState) local
      (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) |--
    coq_prop (os_sched_destination_binding external call outgoing hooked incoming resumed) && TT).
  { unfold kernel_saved_continuation_entry; Intros descriptor.
    assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (descriptor.(armv7a_continuation_stack).(stackLeaseRegion),
      descriptor.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : descriptor.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct descriptor.(armv7a_continuation_stack), incoming;
        cbn in *; congruence. }
    assert (Hfragments : descriptor.(armv7a_continuation_fragments) = resumed) by congruence.
    assert (Hsp : node.(tcbStkPtr) = descriptor.(armv7a_continuation_sp)).
    { assert (Hlive_sp : task_stack_live_sp hooked.(TskState) (task_stack_key incoming)
        descriptor.(armv7a_continuation_sp)) by tauto.
      apply Hlive_sp; assumption. }
    sep_apply_l_atomic (armv7a_task_continuation_restore_source external platform port abi task_abi initial descriptor).
    Intros.
    assert (Harch : external.(os_sched_arch_restore_source) incoming node.(tcbStkPtr) resumed).
    { rewrite Hsp, <- Hlease, <- Hfragments; assumption. }
    assert (Hdestination : os_sched_destination_binding external call outgoing hooked incoming resumed).
    { unfold os_sched_destination_binding; split; [exact Hselected|].
      split; [exists node; tauto|]. split; assumption. }
    entailer!; intros ? ?; exact I. }
  match type of Hpre with ?P heap => assert (Hobserve : P |--
    coq_prop (os_sched_destination_binding external call outgoing hooked incoming resumed) && TT) end.
  { sep_apply_l_atomic (store_parked_continuations_switch
      (kernel_saved_continuation_entry abi hooked.(TskState) local)
      hooked.(TskState).(parkedTaskStacks) call.(os_sched_call_stack) incoming outgoing resumed Habsent Hlookup).
    sep_apply_l_atomic Hentry; entailer!; intros ? ?; exact I. }
  exists incoming, resumed, node; split; [exact (proj1 (Hobserve heap Hpre))|]; tauto.
Qed.

(** Fields spatial counterpart of [os_sched_modular_switch_continuation_selection].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_modular_switch_continuation_selection :
  forall external platform port critical
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (initial : Armv7aInitialEntryABI external platform port abi)
    sg state node call saved acquired other old_sp cpsr registers lr prefix suffix first old_words
    publication before (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  let local := kernel_sched_saved_local_at platform critical sg checkpoint.(TskState) call saved acquired other in
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length registers = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_call_masked abi kernel_program_fields_inv other critical sg
     (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state ** frame) before ->
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg before prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call descriptor stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists incoming resumed selected_node,
        external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
        os_sched_saved_stack_binding call fragments updated /\
        os_sched_destination_binding external call fragments updated incoming resumed /\
        updated.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some selected_node /\
        selected_node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
        In incoming.(stackLeaseSlot) updated.(SchedState).(readyList) /\
        is_effectively_ready selected_node.(stat) selected_node.(dly) = true /\
        task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
        (UCOS2_fields_inv sg updated **
         task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
         kernel_saved_continuation_entry abi updated.(TskState) local
           (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
         store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
           updated.(TskState).(parkedTaskStacks) **
         (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) hooked /\
        (tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
            task_slot_addr sg incoming.(stackLeaseSlot) ->
         exists installed selected,
           sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           armv7a_continuation_restore_reads selected installed /\
           armv7a_continuation_binding selected /\
           selected.(armv7a_continuation_stack) = incoming /\
           selected.(armv7a_continuation_fragments) = resumed /\
           task_current_at (os_sched_install_context call fragments incoming updated)
             incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
           task_stack_live_coverage (os_sched_install_context call fragments incoming updated).(TskState)
             (Some (task_stack_key incoming)) /\
           (forall restored,
             armv7a_task_restore_transition task_abi call selected installed restored ->
             restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
             armv7a_task_restored_source external selected /\
             (armv7a_task_restored_execution external platform port abi selected ** local selected **
              kernel_program_fields_inv sg (os_sched_install_context call fragments incoming updated) **
              store_parked_continuations
                (kernel_saved_continuation_entry abi
                  (os_sched_install_context call fragments incoming updated).(TskState) local)
                (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks) ** frame) restored))).
Proof.
  intros external platform port critical abi task_abi initial sg state node call saved acquired other
    old_sp cpsr registers lr prefix suffix first old_words publication before frame
    checkpoint fragments descriptor updated local Hswitch Hnonempty Hsource Hnode Hid Hgen Habsent
    Hfragments Hregion Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp Haddress Hpre.
  destruct (os_sched_fields_modular_switch_capture external platform port critical abi task_abi sg state node call
    saved acquired other old_sp cpsr registers lr prefix suffix first old_words before frame
    Hswitch Hnonempty Hsource Hnode Hid Hgen Habsent Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp
    Haddress Hpre) as [prefix_heap [written [stored [Hprefix [Hhigh [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]]]]].
  fold checkpoint fragments descriptor updated local in Hhigh, Hstore, Hcovered, Hcapture.
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hready_checkpoint : checkpoint.(SchedState).(readyList) = state.(SchedState).(readyList)).
  { exact (proj1 (os_sched_ready_checkpoint_frame state)). }
  assert (Hnonempty_updated : updated.(SchedState).(readyList) <> []).
  { change (checkpoint.(SchedState).(readyList) <> []); rewrite Hready_checkpoint; exact Hnonempty. }
  assert (Hhigh_updated : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; change checkpoint.(TskState) with state.(TskState); rewrite Hnode.
    cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct checkpoint.(SchedState).(readyList) as [|head tail] eqn:Hlist.
    - exfalso; apply Hnonempty; congruence.
    - destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
      destruct (Z.eqb head call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
      + apply Z.eqb_eq in Heq; subst head.
        change (state.(TskState).(inUsedTaskStates)
          call.(os_sched_call_stack).(stackLeaseSlot) = Some high) in Hlookup.
        assert (high = node) by congruence; subst high.
        exists (task_set_saved_sp node descriptor.(armv7a_continuation_sp)); split; [|exact Hpriority].
        cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
      + exists high; split; [|exact Hpriority].
        cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step.
  assert (Hunchanged : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked; destruct (Hcapture captured Hcaptured) as [Hmemory [Hsave_source Howned]].
  match type of Howned with ?P captured => assert (Hselect : P |--
    UCOS2_fields_inv sg updated **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
      updated.(TskState).(parkedTaskStacks) **
    (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
     armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) by entailer! end.
  destruct (os_sched_fields_continuation_high_destination external platform port abi task_abi initial sg call fragments
    updated local _ captured Hsaved Hhigh_updated Hnonempty_updated Hcovered (Hselect captured Howned))
    as [incoming [resumed [selected_node [Hdestination [Hselected [Hgeneration [Hin Hready]]]]]]].
  exists incoming, resumed, selected_node.
  split; [exact Hsave_source|]. split; [exact Hsaved|]. split; [exact Hdestination|].
  split; [exact Hselected|]. split; [exact Hgeneration|]. split; [exact Hin|]. split; [exact Hready|].
  split; [exact Hcovered|].
  assert (Hordered : (UCOS2_fields_inv sg updated **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
    kernel_saved_continuation_entry abi updated.(TskState) local
      (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
      updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) captured).
  { match type of Howned with ?P captured => match goal with |- ?Q captured =>
      assert (Horder : P |-- Q) by entailer! end end.
    exact (Horder captured Howned). }
  split; [exact Hordered|]. intro Hselected_address.
  exact (kernel_saved_continuation_fields_install_source external platform port abi task_abi sg call fragments
    updated incoming resumed local captured frame Hsaved Hdestination Hselected_address Hcovered Hordered).
Qed.

(** Fields spatial counterpart of [kernel_saved_sched_continuation_return_source].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma kernel_saved_sched_continuation_fields_return_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg context outgoing hooked original saved acquired other resumed before (frame : Assertion),
  let local := kernel_sched_saved_local_at platform critical sg hooked.(TskState)
    original saved acquired other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask saved) **
         kernel_program_fields_inv sg current **
         store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
           current.(TskState).(parkedTaskStacks) ** frame) after)).
Proof.
  intros external platform port abi critical arch task_abi restore sg context outgoing hooked original
    saved acquired other resumed before frame local resource current Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (kernel_saved_continuation_fields_install_source external platform port abi task_abi sg context
    outgoing hooked original.(os_sched_call_stack) resumed local before frame
    Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold current in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hmemory [Hsource Howned]].
  assert (Hlocal : local selected = kernel_sched_saved_local platform critical sg hooked.(TskState)
    original saved acquired selected).
  { unfold local; apply kernel_sched_saved_local_at_selected; exact Hlease. }
  rewrite Hlocal in Howned.
  assert (Hfacts : selected.(armv7a_continuation_call) = Some original /\
      armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
      original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
        original.(os_sched_call_stack).(stackLeaseGeneration) /\
      task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { match type of Howned with ?P restored => assert (Hexpose : P |-- coq_prop
      (selected.(armv7a_continuation_call) = Some original /\
       armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr) = 192 /\
       original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
         original.(os_sched_call_stack).(stackLeaseGeneration) /\
       task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin)) && TT) end.
    { unfold kernel_sched_saved_local; entailer!; try tauto; intros ? ?; exact I. }
    exact (proj1 (Hexpose restored Howned)). }
  destruct Hfacts as [Hcall [Hmask [Horigin Hactive]]].
  assert (Hactive_current : task_invocation_active current.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { exact Hactive. }
  assert (Hselected_current : task_current_at current selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { rewrite Hlease; exact Hcurrent. }
  assert (Hreturned_source : kernel_call_task_source returned current).
  { unfold returned; eapply kernel_selected_saved_call_source; eassumption. }
  assert (Hreturned : returned = armv7a_continuation_resumed_call selected original).
  { unfold returned, kernel_selected_call; rewrite Hcall; reflexivity. }
  split; [exact Hcall|]. split; [exact Hreturned_source|].
  intros cursor written middle final_cursor after Hr0 Hcurrent_mask Hprefix Hsuffix.
  match type of Howned with ?P restored => assert (Hopen : P |--
    critical_region_masked platform critical sg returned.(os_sched_call_invocation)
      returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
    (kernel_program_fields_inv sg current **
     store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
       current.(TskState).(parkedTaskStacks) ** frame)) end.
  { unfold armv7a_task_restored_execution; rewrite Hcall, Hmask, Hreturned.
    unfold kernel_sched_saved_local, kernel_call_execution_owned, critical_region_masked,
      armv7a_continuation_resumed_call; cbn [os_sched_call_invocation os_sched_call_origin]; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical arch restore
    sg returned saved acquired cursor restored written middle final_cursor after _ Hr0 Hcurrent_mask
    (Hopen restored Howned) Hprefix Hsuffix) as [Hrun [Hlr [Hheap Hafter]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hheap|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose after Hafter).
Qed.

(** Fields spatial counterpart of [os_sched_modular_saved_call_return].
    The original pure premises, source execution relations, ABI and conclusions
    are retained. Only the global spatial family is replaced. *)
Lemma os_sched_fields_modular_saved_call_return :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg context outgoing hooked source_tasks original saved acquired other resumed before
    (frame : Assertion),
  let local := kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    (forall restored,
      armv7a_task_restore_transition task_abi context selected installed restored ->
      let returned := kernel_selected_call selected current in
      selected.(armv7a_continuation_call) = Some original /\
      returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_continuation_call_closed abi kernel_program_fields_inv other sg
           (Some (task_stack_key original.(os_sched_call_stack))) returned
           (armv7a_irq_fiq_mask saved) current ** frame) after)).
Proof.
  intros external platform port critical arch abi task_abi restore sg context outgoing hooked source_tasks
    original saved acquired other resumed before frame local resource current
    Hactive Hsaved Hdestination Haddress Hcoverage Hpre.
  set (current_local := kernel_sched_saved_local_at platform critical sg hooked.(TskState)
    original saved acquired other).
  set (current_resource := kernel_saved_continuation_entry abi hooked.(TskState) current_local).
  assert (Hentry : forall key payload, resource key payload |-- current_resource key payload).
  { intros key payload; unfold resource, current_resource, kernel_saved_continuation_entry.
    Intros descriptor; Exists descriptor.
    unfold local, current_local, kernel_sched_saved_local_at.
    destruct task_stack_key_eq_dec; [unfold kernel_sched_saved_local; entailer!|entailer!]. }
  assert (Hmap : store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) |--
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks)).
  { unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
    intros key payload Hlookup; apply Hentry. }
  match type of Hpre with ?P before => assert (Hconvert : P |--
    UCOS2_fields_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    current_resource (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) end.
  { sep_apply_l_atomic (Hentry (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
    sep_apply_l_atomic Hmap; entailer!. }
  destruct (kernel_saved_sched_continuation_fields_return_source external platform port abi critical arch
    task_abi restore sg context outgoing hooked original saved acquired other resumed before frame
    Hsaved Hdestination Haddress Hcoverage (Hconvert before Hpre))
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  fold current current_local in Hrestore.
  assert (Hcovered : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  assert (Habsent : current.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None) by apply task_stack_take_lookup.
  assert (Hunfocus : store_parked_continuations
      (kernel_saved_continuation_entry abi current.(TskState) current_local)
      current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) other)
      current.(TskState).(parkedTaskStacks)).
  { unfold current_local; apply kernel_saved_continuation_map_unfocus_absent; exact Habsent. }
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hcall [Hsource Htail]].
  fold returned in Hsource, Htail.
  assert (Hsame : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold armv7a_continuation_resumed_call; cbn; auto. }
  split; [exact Hcall|]. destruct Hsame as [Hi [Ho Hs]].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hmemory|].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic Hunfocus.
    unfold kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
  exact (Hclose after Howned).
Qed.
