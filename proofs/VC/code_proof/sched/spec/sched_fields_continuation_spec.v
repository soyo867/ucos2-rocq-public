Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_irq_register_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_save_irq_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Export Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Export Ucos2Verify.lib.flag_fields_resources.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** C-call interface for the actual Scheduler using six-field Flag nodes.
    Pure source histories, guards and endpoints are unchanged. The generic
    local family is the caller's actual saved-entry resource, including any
    real initial-entry resource; this interface does not impose None=emp.

    Save, Restore and OSCtxSw are explicit conditional platform/environment
    call boundaries. Their declared same-call/source/spatial effects must be
    realized by the linked environment on the very same heap execution. No
    theorem here manufactures that realization, assumes eventual return, or
    claims preservation for arbitrary kernel clients. The ordinary Scheduler
    C body is checked separately against these disclosed callee interfaces. *)
Definition os_sched_fields_capsules (environment : TaskStackCallEnvironment)
  (local : Armv7aContinuation -> Assertion) (state : UCOS2_Verify_State) : Assertion :=
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      state.(TskState) local) state.(TskState).(parkedTaskStacks).

Definition os_sched_fields_save_input (environment : TaskStackCallEnvironment)
  (critical : CriticalRegionResources) local sg call mask state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask **
   UCOS2_fields_inv sg state ** os_sched_fields_capsules environment local state).

Definition os_sched_fields_restore_input environment critical local sg call saved acquired released : Assertion :=
  coq_prop (task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) &&
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call ** UCOS2_fields_inv sg released **
  os_sched_fields_capsules environment local released).

Lemma os_sched_fields_save_input_closed_world :
  forall environment critical local sg call mask state,
  os_sched_fields_save_input environment critical local sg call mask state **
    unmap_table_rep sg --||--
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    kernel_program_fields_inv local sg (task_stack_call_active_key call) call mask state.
Proof.
  intros; unfold os_sched_fields_save_input, os_sched_fields_capsules,
    kernel_continuation_call_closed, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

Lemma os_sched_fields_restore_input_masked_world : forall environment critical local sg call saved acquired state,
  os_sched_fields_restore_input environment critical local sg call saved acquired state **
    unmap_table_rep sg --||--
  kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_fields_inv
    local critical sg
    (task_stack_call_active_key call) call saved acquired state.
Proof.
  intros; unfold os_sched_fields_restore_input, os_sched_fields_capsules,
    kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_fields_inv_split_unmap; split; entailer!.
Qed.

Definition os_sched_fields_pre environment local resources sg original mask before : Assertion :=
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    resources local sg
    (task_stack_call_active_key original) original mask before.

Definition os_sched_fields_call_pre environment local resources
  sg call mask state : Assertion :=
  coq_prop (os_sched_call_cut sg call state) &&
  os_sched_fields_pre environment local resources sg call mask state.

Definition os_sched_fields_switch_pre environment critical local resources
  sg call saved acquired entry : Assertion :=
  coq_prop (os_sched_requests_switch entry = true /\
    os_sched_current_storage_binding sg call entry /\
    entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None) &&
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    resources local critical sg
    (task_stack_call_active_key call) call saved acquired (os_sched_prefix_state entry).

Definition os_sched_fields_body_post environment critical local resources
  sg call saved acquired entry : Assertion :=
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical
      sg entry call returned current) &&
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      resources local critical sg
      (task_stack_call_active_key returned) returned saved acquired current.

Definition os_sched_fields_save_history_output environment critical local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (os_sched_continuation_save_effect environment critical sg
        original mask saved before returned acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      os_sched_call_cut sg returned acquired) &&
    os_sched_fields_restore_input environment critical local
      sg returned saved acquired acquired.

Definition os_sched_fields_restore_history_output environment critical local
  sg original saved released : Assertion :=
  EX returned current,
    coq_prop (os_sched_continuation_restore_effect environment critical sg original released returned current /\
      task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current)) &&
    os_sched_fields_save_input environment critical local sg
      returned (armv7a_irq_fiq_mask saved) current.

Definition os_sched_fields_history_return_post environment critical local resources
  sg original mask before : Assertion :=
  EX returned current,
    coq_prop (os_sched_continuation_call_history environment critical sg original mask before returned current /\
      task_tcb_init_stack_same_call returned original /\
      (kernel_call_task_source original before -> kernel_call_task_source returned current)) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      resources local sg
      (task_stack_call_active_key returned) returned mask current.

Lemma os_sched_fields_body_restore_input : forall environment critical local
  sg call saved acquired entry,
  os_sched_fields_body_post environment critical local kernel_program_fields_inv
    sg call saved acquired entry |--
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical
      sg entry call returned current /\ UCOS2_state_inv sg current) &&
    (os_sched_fields_restore_input environment critical local sg
       returned saved acquired current ** unmap_table_rep sg).
Proof.
  intros; unfold os_sched_fields_body_post; Intros returned current.
  Exists returned current.
  sep_apply_l_atomic (proj2 (os_sched_fields_restore_input_masked_world
    environment critical local sg returned saved acquired current)).
  unfold os_sched_fields_restore_input, UCOS2_fields_inv; entailer!.
Qed.

Lemma os_sched_fields_restore_history_output_return : forall environment critical local sg
  original scheduled resumed mask saved before entry released,
  os_sched_continuation_save_effect environment critical sg original mask saved before scheduled entry ->
  task_tcb_init_stack_same_call scheduled original ->
  (kernel_call_task_source original before -> kernel_call_task_source scheduled entry) ->
  (os_sched_requests_switch entry = true -> os_sched_current_storage_binding sg scheduled entry) ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled resumed released ->
  UCOS2_state_inv sg released -> interrupt_saved_value mask saved ->
  os_sched_fields_restore_history_output environment critical local sg resumed saved released **
    unmap_table_rep sg |--
  os_sched_fields_history_return_post environment critical local kernel_program_fields_inv
    sg original mask before.
Proof.
  intros environment critical local sg original scheduled resumed mask saved before entry released
    Hsave Hscheduled Hentry_source Hcut Hbody Hvalid Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hresumed.
  unfold os_sched_fields_restore_history_output; Intros returned current.
  assert (Hrestore : os_sched_continuation_restore_effect environment critical sg resumed released returned current)
    by tauto.
  assert (Hreturned : task_tcb_init_stack_same_call returned resumed) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved resumed released current) by tauto.
  assert (Hhistory : os_sched_continuation_call_history environment critical sg original mask before returned current).
  { exists scheduled, entry, resumed, released, saved; repeat split; assumption. }
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { eapply os_sched_continuation_call_history_same_call; exact Hhistory. }
  assert (Hfinal_source : kernel_call_task_source original before -> kernel_call_task_source returned current).
  { intro Hinitial.
    pose proof (os_sched_continuation_c_return_source _ _ _ _ _ _ _ Hcut Hbody
      (Hentry_source Hinitial)) as Hreleased.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned resumed current Hreturned)).
    apply Hsource; exact Hreleased. }
  sep_apply_l_atomic (proj1 (os_sched_fields_save_input_closed_world
    environment critical local sg returned (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold os_sched_fields_history_return_post; Exists returned current; entailer!.
Qed.

(** Exact complement of the same ordinary C scheduler stores.
    Flag fields remain owned once in the untouched module residual. *)
Definition os_sched_fields_remaining_task_storage_sched sg state : Assertion :=
  flag_fields_configured_rep sg state.(FlagState) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg state.

Definition os_sched_fields_work_frame (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) : Assertion :=
  task_public_storage_without_prio_tbl sg entry.(TskState) **
  store_parked_stacks entry.(TskState).(parkedTaskStacks) **
  flag_fields_configured_rep sg entry.(FlagState) **
  UCOS2_selected_rep sg entry (fun m => match m with
    | TaskModule | SchedModule | InterruptModule | FlagModule => false | _ => true end) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0).

Definition os_sched_fields_work_cells (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (high pointer counter : Z) : Assertion :=
  sg.(g_OSIntNesting) # UChar |-> os_sched_ints entry **
  sg.(g_OSLockNesting) # UChar |-> os_sched_locks entry **
  sched_new_rep sg (os_sched_group entry) (os_sched_rows entry) high **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (os_sched_table sg entry) **
  sg.(g_OSPrioCur) # UChar |-> os_sched_current entry **
  sg.(g_OSTCBHighRdy) # Ptr |-> pointer **
  sg.(g_OSCtxSwCtr) # UInt |-> counter ** os_sched_fields_work_frame sg entry.

Lemma os_sched_fields_work_cells_entry_equiv : forall sg entry,
  UCOS2_fields_raw_rep sg entry ** unmap_table_rep sg --||--
  os_sched_fields_work_cells sg entry (os_sched_old_high entry)
    (os_sched_old_pointer sg entry) (os_sched_counter entry).
Proof.
  intros; unfold os_sched_fields_work_cells, os_sched_fields_work_frame,
    os_sched_ints, os_sched_locks, os_sched_group, os_sched_rows,
    os_sched_old_high, os_sched_old_pointer, os_sched_current, os_sched_counter,
    os_sched_table, UCOS2_fields_raw_rep, UCOS2_raw_rep_missing_flag,
    UCOS2_raw_rep_missing_module, UCOS2_selected_rep,
    task_shared_rep, sched_raw_rep,
    sched_new_rep, sched_physical_rep, task_public_storage,
    task_public_storage_without_prio_tbl, store_prio_tbl.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold task_shared_rep, sched_raw_rep, sched_physical_rep, task_public_storage,
    task_public_storage_without_prio_tbl, store_prio_tbl.
  rewrite sched_rows_array_equiv.
  split.
  - unfold interrupt_inv, store_int_state; entailer!.
  - pose proof (interrupt_inv_merge_counters sg entry.(IntrState)) as Hmerge.
    unfold store_int_state in Hmerge.
    sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma os_sched_fields_prefix_merge_inv : forall sg entry,
  UCOS2_state_inv sg entry ->
  (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) ->
  task_public_storage sg entry.(TskState) ** os_sched_prefix_rep sg entry **
  os_sched_fields_remaining_task_storage_sched sg entry |--
    UCOS2_fields_inv sg (replace_SchedS (os_sched_ready_checkpoint entry) entry).
Proof.
  intros sg entry Hvalid Hnonempty.
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  assert (Hregistered : task_current_prio_registered entry.(TskState)).
  { unfold task_in_range in Htasks; tauto. }
  pose proof (proj1 (os_sched_prefix_rep_eq_checkpoint sg entry Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty)) as Hphysical.
  unfold os_sched_fields_remaining_task_storage_sched.
  pose proof (UCOS2_fields_inv_merge_updated_task_storage_sched_flag sg entry
    (replace_SchedS (os_sched_ready_checkpoint entry) entry)
    (os_sched_ready_checkpoint_preserves_validity sg entry Hvalid) eq_refl) as Hmerge.
  sep_apply_l_atomic Hphysical.
  cbn [replace_SchedS TskState SchedState FlagState] in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

