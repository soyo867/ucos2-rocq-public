Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_pending_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A different, currently executing creator may call OS_Sched while the
    focused invocation remains parked. Keep that invocation's descriptor
    through the actual local Save, all three no-switch C branches and
    Restore. The ready-list premise follows from the creator's source
    stage, not CPU authority or an added public API premise.

    The two final spatial assertions are alternative views of ONE heap,
    connected by consequence, not two separated copies of the stack map.
    The focused view feeds a later resumption; the source-return view feeds
    Create's existing success continuation. Intervening IRQs and switches
    have separate source obligations and are not excluded globally. *)
Lemma task_create_nonswitch_sched_preserves_pending_call :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call state focus payload mask registers before
    final_registers acquired saved_heap (frame : Assertion),
  task_create_call_stage call state -> state.(SchedState).(isRunning) = true ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks environment.(task_stack_call_continuations)
     state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\ acquired = state /\
  task_stack_live_coverage (os_sched_prefix_state state).(TskState) (task_stack_call_active_key call) /\
  (os_sched_prefix_state state).(TskState).(parkedTaskStacks)
    (armv7a_call_focus_key focus) = Some payload /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (kernel_call_execution_owned environment.(task_stack_call_external)
         environment.(task_stack_call_platform) call mask **
       kernel_program_inv sg (os_sched_prefix_state state) **
       armv7a_task_call_stacks environment.(task_stack_call_continuations)
         (os_sched_prefix_state state).(TskState) focus
         (os_sched_prefix_state state).(TskState).(parkedTaskStacks) ** frame) after /\
      (os_sched_source_return_post environment critical sg call mask
        (os_sched_prefix_state state) ** frame) after).
Proof.
  intros environment critical arch save restore sg call state focus payload mask registers before
    final_registers acquired saved_heap frame Hstage Hrunning Hcoverage Hfocus Hreturn Hvalid Hmask
    Hnoswitch Hpre Hsave.
  assert (Hnonempty : os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []).
  { intros Henabled.
    destruct Hstage as [Horigin Hstage].
    destruct call.(os_sched_call_origin) as [|slot generation] eqn:Horigin_call.
    - unfold task_create_call_origin in Horigin; congruence.
    - destruct Hstage as [_ [_ [_ Hready]]].
      destruct (Hready Henabled) as [node [[Hlookup [Hcurrent [Hpriority [Hin Heffective]]]] Hgen]].
      intros Hempty; rewrite Hempty in Hin; contradiction. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid|reflexivity]).
  match type of Hpre with ?P before => assert (Hsave_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_program_inv sg state **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)) end.
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired saved_heap _ Hsaved
    (Hsave_input before Hpre) Hsave) as [Hstate [Hmemory [Hlr [Hr0 Hmasked]]]].
  split.
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Hstate|]. split; [exact Hcoverage|]. split; [exact Hfocus|].
  assert (Hsaved_mask : armv7a_irq_fiq_mask final_registers.(kernel_save_r0) = mask)
    by (rewrite Hr0; exact Hmask).
  match type of Hmasked with ?P saved_heap => assert (Hprefix_input : P |--
    UCOS2_inv sg state ** unmap_table_rep sg **
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
     os_sched_context_resources environment.(task_stack_call_external) call **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_source_nonswitch_prefix_resources sg state _ saved_heap Hnoswitch Hnonempty
    (Hprefix_input saved_heap Hmasked)) as [prefix_heap [Hprefix Hafter_prefix]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hcursor Hcursor_mask Hrestore_prefix Hrestore_suffix.
  match type of Hafter_prefix with ?P prefix_heap => assert (Hrestore_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_program_inv sg (os_sched_prefix_state state) **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       (os_sched_prefix_state state).(TskState) focus
       (os_sched_prefix_state state).(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_inv_split_unmap.
    change (os_sched_prefix_state state).(TskState) with state.(TskState); entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call
    final_registers.(kernel_save_r0) state cursor prefix_heap written middle final_cursor after _
    Hcursor Hcursor_mask (Hrestore_input prefix_heap Hafter_prefix) Hrestore_prefix Hrestore_suffix)
    as [Hrun [Hreturn_word [Hmemory_return Hreturned]]].
  rewrite Hsaved_mask in Hreturned.
  match type of Hreturned with ?P after => assert (Hfocused :
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) call mask **
     kernel_program_inv sg (os_sched_prefix_state state) **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       (os_sched_prefix_state state).(TskState) focus
       (os_sched_prefix_state state).(TskState).(parkedTaskStacks) ** frame) after)
    by (match goal with |- ?Q after => assert (Horder : P |-- Q) by entailer! end;
        exact (Horder after Hreturned)) end.
  split; [exact Hrun|]. split; [exact Hfocused|].
  assert (Hhistory : kernel_call_restore_history environment critical sg call
    (os_sched_prefix_state state) call (os_sched_prefix_state state))
    by (eapply KernelCallRestoreUninterrupted; eassumption).
  match type of Hfocused with ?P after => match goal with |- ?Q after =>
    assert (Hforget : P |-- Q) end end.
  { unfold os_sched_source_return_post; Exists call (os_sched_prefix_state state).
    rewrite kernel_program_inv_split_unmap; unfold kernel_stack_inv.
    sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ environment.(task_stack_call_continuations)
      (os_sched_prefix_state state).(TskState) focus
      (os_sched_prefix_state state).(TskState).(parkedTaskStacks)); entailer!. }
  exact (Hforget after Hfocused).
Qed.

(** Connect the producer at the actual publication cut to the complete
    no-IRQ/no-switch return suffix. The child's initial stack publication
    and the earlier waiting invocation's preserved descriptor travel on
    the same physical heap throughout both Restore calls and the Save.
    This supplies the source-return assertion already consumed by the
    Create success proof while retaining the stronger pending-call view. *)
Lemma task_create_publication_pending_nonswitch_return :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg publication state call focus payload saved acquired before (frame : Assertion),
  let args := task_create_stack_publication_args publication in
  let published := task_create_stack_publication_state sg publication state in
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_create_call_stage call state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg args state
     publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_call_stacks environment.(task_stack_call_continuations)
     state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame)) before ->
  exists publication_heap,
    task_tcb_init_publication_tail_fragment sg args.(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before publication_heap /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    (forall tcb_cursor tcb_written tcb_middle tcb_final returned_heap,
      tcb_cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask tcb_cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore tcb_cursor publication_heap tcb_written tcb_middle ->
      armv7a_restore_suffix_transition restore tcb_written tcb_middle tcb_final returned_heap ->
      kernel_call_restore_uninterrupted_execution arch tcb_cursor publication_heap tcb_final returned_heap /\
      (forall registers final_registers sched_acquired saved_heap,
        published.(SchedState).(isRunning) = true ->
        registers.(kernel_save_return_word) = None ->
        valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
        os_sched_requests_switch published = false ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) published returned_heap
          final_registers sched_acquired saved_heap ->
        kernel_call_save_uninterrupted_execution arch registers published returned_heap
          final_registers sched_acquired saved_heap /\ sched_acquired = published /\
        task_stack_live_coverage (os_sched_prefix_state published).(TskState)
          (task_stack_call_active_key call) /\
        (os_sched_prefix_state published).(TskState).(parkedTaskStacks)
          (armv7a_call_focus_key focus) = Some payload /\
        exists prefix_heap,
          os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
          (forall cursor written middle final_cursor after,
            cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
            armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
            armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
            armv7a_restore_suffix_transition restore written middle final_cursor after ->
            kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
            (kernel_call_execution_owned environment.(task_stack_call_external)
               environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask saved) **
             kernel_program_inv sg (os_sched_prefix_state published) **
             armv7a_task_call_stacks environment.(task_stack_call_continuations)
               (os_sched_prefix_state published).(TskState) focus
               (os_sched_prefix_state published).(TskState).(parkedTaskStacks) ** frame) after /\
            (os_sched_source_return_post environment critical sg call (armv7a_irq_fiq_mask saved)
              (os_sched_prefix_state published) ** frame) after))).
Proof.
  intros environment critical arch save restore sg publication state call focus payload saved acquired
    before frame args published Hvalid Hinput Hstage Hcoverage Hfocus Hpriority Hpointer Hpre.
  destruct (task_create_tcb_publication_preserves_pending_call environment critical arch restore sg
    publication state call focus payload saved acquired before frame Hvalid Hinput Hstage Hcoverage
    Hfocus Hpriority Hpointer Hpre)
    as [publication_heap [Hstores [Hstep [Hstage_published [Hcovered [Hretained [Hmasked Htail]]]]]]].
  fold published in Hstep, Hstage_published, Hcovered, Hretained, Hmasked, Htail.
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|].
  intros tcb_cursor tcb_written tcb_middle tcb_final returned_heap Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail tcb_cursor tcb_written tcb_middle tcb_final returned_heap Hr0 Hmask Hprefix Hsuffix)
    as [Hrestore_run Hreturned].
  split; [exact Hrestore_run|].
  intros registers final_registers sched_acquired saved_heap Hrunning Hreturn Hcpsr Hsaved_mask
    Hnoswitch Hsave.
  exact (task_create_nonswitch_sched_preserves_pending_call environment critical arch save restore
    sg call published focus payload (armv7a_irq_fiq_mask saved) registers returned_heap
    final_registers sched_acquired saved_heap frame Hstage_published Hrunning Hcovered Hretained
    Hreturn Hcpsr Hsaved_mask Hnoswitch Hreturned Hsave).
Qed.
