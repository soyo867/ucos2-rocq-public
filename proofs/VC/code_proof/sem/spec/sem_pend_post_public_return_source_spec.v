Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cleanup_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_post_wake_source_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations Monad MonadNotation.
Import KernelHeapObservation KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Reassemble the real resumed cells with the observation of the SAME
    wait. The live switch consumer below supplies this observation from
    its concrete C prefix and switch, and the saved mask from its actual
    second Save. *)
Lemma sem_pend_resume_stack_phase_output : forall environment critical sg original call mask initial observed
  eid timeout waiting current node saved,
  sem_pend_wait_at (Some environment) critical sg original mask initial observed eid timeout waiting call current ->
  interrupt_saved_value mask saved ->
  sem_pend_resume_stack_resources environment critical sg call saved current eid
    original.(os_sched_call_stack).(stackLeaseSlot) node |--
  sem_pend_phase_save_output (SemPendWaitPhase original mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform) (Some environment)
    critical sg call mask saved current ** unmap_table_rep sg.
Proof.
  intros environment critical sg original call mask initial observed eid timeout waiting current node saved Hwait Hsaved.
  sep_apply_l_atomic (sem_pend_resume_stack_merge environment critical sg call saved current eid
    original.(os_sched_call_stack).(stackLeaseSlot) node).
  Intros.
  assert (Hselected : sem_pend_wait_selected_at (Some environment) critical sg original mask initial observed
    eid timeout waiting call current) by (split; [exact Hwait|exists node; assumption]).
  rewrite <- task_tcb_init_stack_restore_input_masked_world.
  unfold task_tcb_init_stack_restore_input, sem_pend_phase_save_output,
    sem_pend_optional_stack_resources, task_tcb_init_stack_capsules.
  Exists call current.
  unfold sem_pend_stack_save_observation, kernel_stack_call_same_call;
    cbn [sem_pend_save_phase_observation]; entailer!; discriminate.
Qed.

(** Extend the original wait by the concrete C prefix and this SAME
    foreign task switch. Its physical frame producer returns the original
    SemPend invocation, executes the second Save and immediately supplies
    all result branches, cleanup and the public postcondition. The two
    source observations exposed upstream are conclusions, not premises. *)
Lemma sem_pend_live_switch_public_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port) environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg scheduler_entry node context old_sp cpsr registers lr prefix suffix first old_words publication
  original suspended original_saved entry eid waiting perr before (frame : Assertion)
  public_call mask initial observed pevent timeout wait_start selector_heap X,
  let state := os_sched_prefix_state scheduler_entry in
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot initial eid observed ->
  sem_pend_context_error (event_slot_type_value initial.(EventState) eid)
    initial.(IntrState).(intNesting) initial.(IntrState).(lockNesting) = None ->
  interrupt_saved_value mask original_saved ->
  safeExec (LastSeen initial)
    (bind (atomic_cmd (sem_pend_runtime_program environment.(task_stack_call_external) environment.(task_stack_call_platform)
      (Some environment) critical sg public_call pevent timeout)) sem_query_observe_error) X ->
  sem_pend_wait_at (Some environment) critical sg public_call mask initial observed eid timeout
    wait_start original scheduler_entry ->
  os_sched_source_switch_prefix_execution sg selector_heap before ->
  os_sched_source_live_save_input sg state node context old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended -> armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr) = 192 ->
  state.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some waiting ->
  sem_pend_wait_continuation eid original.(os_sched_call_stack).(stackLeaseGeneration) waiting ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state original.(os_sched_call_stack) suspended.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  event_object_layout_prop sg eid ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg context focus state **
   (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token original_saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
    critical_region_inside critical sg original.(os_sched_call_invocation) entry ** unmap_table_rep sg **
    (perr # UChar |->_ ** frame))) before ->
  let saved := armv7a_task_save_image context old_sp cpsr registers lr fragments in
  let hooked := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments original.(os_sched_call_stack) hooked in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured heap,
      armv7a_task_capture_transition task_abi context saved stored captured ->
      kernel_heap_execution [] captured heap ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg hooked hooked ->
      task_invocation_active hooked.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
      exists installed selected,
        sched_install_heap_fragment sg heap installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (forall restored cursor restore_written middle final_cursor returned_heap next_registers final_registers acquired after,
          armv7a_task_restore_transition task_abi context selected installed restored ->
          cursor.(kernel_restore_r0) = original_saved ->
          cursor.(kernel_restore_current_cpsr) = selected.(armv7a_continuation_cpsr) ->
          next_registers.(kernel_save_return_word) = None -> valid_os_cpu_sr next_registers.(kernel_save_cpsr) ->
          armv7a_irq_fiq_mask next_registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask original_saved ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor returned_heap ->
          armv7a_save_suffix_transition save (kernel_save_read_cpsr next_registers) current returned_heap
            final_registers acquired after ->
          os_sched_source_switch_execution environment.(task_stack_call_external) environment.(task_stack_call_platform)
            environment.(task_stack_call_port) environment.(task_stack_call_continuations) task_abi sg state
            context old_sp cpsr registers lr saved original.(os_sched_call_stack) selected before restored /\
          kernel_call_task_source (armv7a_continuation_resumed_call selected original) current /\
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor returned_heap /\
          kernel_call_save_uninterrupted_execution arch next_registers current returned_heap final_registers acquired after /\
          acquired = current /\
          kernel_stack_call_same_call (armv7a_continuation_resumed_call selected original) original /\
          final_registers.(kernel_save_r0) = next_registers.(kernel_save_cpsr) /\
          exists returned resumed result_node cleaning clean_node branch_heap cleaned,
              sem_pend_resume_branch_fragment sg resumed eid public_call.(os_sched_call_stack).(stackLeaseSlot) result_node after branch_heap /\
              sem_pend_cleanup_fragment sg perr
                (encode_os_err_code (sem_pend_resume_error (encode_pend_status result_node.(statPend)))) branch_heap cleaned /\
              sem_pend_checkpoint_result (Some environment) critical sg public_call pevent timeout initial
                (encode_os_err_code (sem_pend_resume_error (encode_pend_status result_node.(statPend))))
                (event_pend_cleanup_state sg false cleaning public_call.(os_sched_call_stack).(stackLeaseSlot) clean_node) /\
              kernel_stack_call_same_call returned public_call /\ interrupt_saved_value mask final_registers.(kernel_save_r0) /\
              (task_tcb_init_stack_restore_input environment critical sg returned final_registers.(kernel_save_r0) resumed
                (event_pend_cleanup_state sg false cleaning public_call.(os_sched_call_stack).(stackLeaseSlot) clean_node) **
                unmap_table_rep sg ** perr # UChar |->
                  encode_os_err_code (sem_pend_resume_error (encode_pend_status result_node.(statPend))) ** frame) cleaned /\
              (forall final_start final_written final_middle final_exit final_heap,
                final_start.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
                armv7a_irq_fiq_mask final_start.(kernel_restore_current_cpsr) = 192 ->
                armv7a_restore_prefix_transition restore final_start cleaned final_written final_middle ->
                armv7a_restore_suffix_transition restore final_written final_middle final_exit final_heap ->
                kernel_call_restore_uninterrupted_execution arch final_start cleaned final_exit final_heap /\
                (sem_pend_stack_call_post environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) (Some environment) critical sg public_call mask
                  pevent timeout perr initial X ** frame) final_heap))).

Proof.
  intros environment critical arch task_abi restore save sg scheduler_entry node context old_sp cpsr registers lr
    prefix suffix first old_words publication original suspended original_saved entry eid waiting perr before frame
    public_call mask initial observed pevent timeout wait_start selector_heap X state abi focus fragments
    Hnonnull Haddress_event Heid Hslot Hordered Horiginal_saved Hexec Hwait_history Hprefix
    Hinput Horigin Hbinding Hcall Hslice Hmask Hwaiting Hwait Hactive Hpointer Hparked Hselected Hlayout Hpre.
  intros saved hooked current.
  destruct (sem_pend_live_switch_pending_return_source environment critical arch task_abi restore save
    sg state node context old_sp cpsr registers lr prefix suffix first old_words publication
    original suspended original_saved entry eid waiting perr before frame Hinput Horigin Hbinding Hcall Hslice Hmask
    Hwaiting Hwait Hactive Hpointer Hparked Hselected Hlayout Hpre)
    as [written [stored [Hwrites [Hload [Hstore Hselect]]]]].
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured heap Hcapture Hhook_heap Hhook.
  destruct (Hselect captured heap Hcapture Hhook_heap Hhook)
    as [Hactive_after [installed [selected [Hinstall [Hreads Hreturn]]]]].
  split; [exact Hactive_after|]. exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  intros restored cursor restore_written middle final_cursor returned_heap next_registers final_registers acquired after
    Hrestore Hr0 Hcursor Hreg Hvalid Hnextmask Hrestore_prefix Hrestore_suffix Hsave.
  destruct (Hreturn restored cursor restore_written middle final_cursor returned_heap next_registers final_registers
    acquired after Hrestore Hr0 Hcursor Hreg Hvalid Hnextmask Hrestore_prefix Hrestore_suffix Hsave)
    as (Hswitch & Htask & Hrestore_run & Hsave_run & Hacquired & Hsame & Hvalue & Hresources & Hcleanup).
  split; [exact Hswitch|]. split; [exact Htask|]. split; [exact Hrestore_run|]. split; [exact Hsave_run|].
  split; [exact Hacquired|]. split; [exact Hsame|]. split; [exact Hvalue|].
  assert (Hcurrent_wait : sem_pend_wait_at (Some environment) critical sg public_call mask initial observed
    eid timeout wait_start original current).
  { exact (sem_pend_wait_phase_switch_source environment critical sg public_call mask initial observed eid timeout
      wait_start original scheduler_entry task_abi context old_sp cpsr registers lr saved original.(os_sched_call_stack)
      selected selector_heap before restored Hwait_history Hprefix Hswitch). }
  assert (Hreturned_wait : sem_pend_wait_at (Some environment) critical sg public_call mask initial observed
    eid timeout wait_start (armv7a_continuation_resumed_call selected original) current).
  { destruct Hcurrent_wait as [owned [Henv [Hinitial_same [Hinitial Hpath]]]].
    exists owned; split; [exact Henv|]. split.
    - unfold kernel_stack_call_same_call in *; intuition congruence.
    - split; assumption. }
  assert (Hsaved : interrupt_saved_value mask final_registers.(kernel_save_r0)).
  { rewrite Hvalue; split; [exact Hvalid|]. rewrite Hnextmask; exact (proj2 Horiginal_saved). }
  assert (Hlease : original.(os_sched_call_stack) = public_call.(os_sched_call_stack)).
  { destruct Hwait_history as [owned [Henv [Hsame_initial Hrest]]]; exact (proj2 (proj2 Hsame_initial)). }
  assert (Hslot_same : original.(os_sched_call_stack).(stackLeaseSlot) = public_call.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite Hlease; reflexivity).
  assert (Hacquired_current : acquired = current) by exact Hacquired.
  subst acquired.
  fold current in Hresources.
  rewrite Hslot_same in Hresources.
  change ((sem_pend_resume_stack_resources environment critical sg
    (armv7a_continuation_resumed_call selected original) final_registers.(kernel_save_r0) current eid
    public_call.(os_sched_call_stack).(stackLeaseSlot) waiting ** (perr # UChar |->_ ** frame)) after) in Hresources.
  eapply (sem_pend_saved_wait_return_source environment critical arch restore sg public_call mask initial observed
    eid pevent timeout wait_start (armv7a_continuation_resumed_call selected original) current
    final_registers.(kernel_save_r0) perr frame after X Hnonnull Haddress_event Heid Hslot Hlayout Hordered Hexec).
  match type of Hresources with ?P after => match goal with |- ?Q after => assert (Hpack : P |-- Q) end end.
  { sep_apply_l_atomic (sem_pend_resume_stack_phase_output environment critical sg public_call
      (armv7a_continuation_resumed_call selected original) mask initial observed eid timeout wait_start current waiting
      final_registers.(kernel_save_r0) Hreturned_wait Hsaved); entailer!. }
  exact (Hpack after Hresources).
Qed.
