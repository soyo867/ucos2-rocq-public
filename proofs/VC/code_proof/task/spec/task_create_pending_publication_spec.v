Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The running creator and the earlier pending caller are different
    source roles. Reuse the actual TCB publication stores with coverage
    exempting the running creator, retaining the pending caller's exact
    map entry. The earlier built-in handler consumer used [active=None];
    that cannot be silently used while a different task is executing.

    The same published heap flows through the creator's final Restore.
    This is its uninterrupted return branch; interrupting paths must
    supply their own source composition. No global registry is narrowed,
    and no weak C-facing callee postcondition is upgraded by this lemma. *)
Lemma task_create_tcb_publication_preserves_pending_call :
  forall environment critical arch
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
    task_create_call_stage call published /\
    task_stack_live_coverage published.(TskState) (task_stack_call_active_key call) /\
    published.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload /\
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment call ** kernel_program_inv sg published **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       published.(TskState) focus published.(TskState).(parkedTaskStacks) ** frame) publication_heap /\
    (forall cursor written middle final_cursor returned_heap,
      cursor.(kernel_restore_r0) = saved ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor publication_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor returned_heap ->
      kernel_call_restore_uninterrupted_execution arch cursor publication_heap final_cursor returned_heap /\
      (kernel_call_execution_owned environment.(task_stack_call_external)
         environment.(task_stack_call_platform) call (armv7a_irq_fiq_mask saved) **
       kernel_program_inv sg published **
       armv7a_task_call_stacks environment.(task_stack_call_continuations)
         published.(TskState) focus published.(TskState).(parkedTaskStacks) ** frame) returned_heap).
Proof.
  intros environment critical arch restore sg publication state call focus payload saved acquired
    before frame args published Hvalid Hinput Hstage Hcoverage Hfocus Hpriority Hpointer Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    task_tcb_init_publication_tail_storage sg args state
      publication.(stack_publication_slot) publication.(stack_publication_image) **
    (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       state.(TskState) focus state.(TskState).(parkedTaskStacks) **
     (critical_region_masked environment.(task_stack_call_platform) critical sg
        call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
      task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame))) by entailer! end.
  destruct (task_tcb_init_publication_tail_store_execution sg args
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid (proj1 (proj2 (proj2 Hinput)))
    Hpriority Hpointer (Hopen before Hpre)) as [publication_heap [Hstores Hafter]].
  pose proof (task_create_publication_call_stack_merge _ _ _
    environment.(task_stack_call_continuations) sg publication state focus
    (task_stack_call_active_key call) payload Hvalid Hinput Hcoverage Hfocus) as Hmerge.
  cbv zeta in Hmerge; fold args published in Hmerge.
  pose proof (task_create_publication_preserves_call_stage sg publication state call Hvalid Hinput Hstage)
    as Hstage_after; fold published in Hstage_after.
  match type of Hafter with ?P publication_heap => assert (Hclose : P |--
    coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg state published /\
      task_stack_live_coverage published.(TskState) (task_stack_call_active_key call) /\
      published.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment call ** kernel_program_inv sg published **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       published.(TskState) focus published.(TskState).(parkedTaskStacks) ** frame)) end.
  { sepcon_assoc_change; sep_apply_l_atomic Hmerge; Intros.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hclose publication_heap Hafter) as [[Hstep [Hcovered Hretained]] Hmasked].
  exists publication_heap; split; [exact Hstores|]. split; [exact Hstep|].
  split; [exact Hstage_after|]. split; [exact Hcovered|]. split; [exact Hretained|].
  split; [exact Hmasked|].
  intros cursor written middle final_cursor returned_heap Hr0 Hmask Hprefix Hsuffix.
  match type of Hmasked with ?P publication_heap => assert (Hrestore_input : P |--
    critical_region_masked environment.(task_stack_call_platform) critical sg
      call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources environment.(task_stack_call_external) call **
    (kernel_program_inv sg published **
     armv7a_task_call_stacks environment.(task_stack_call_continuations)
       published.(TskState) focus published.(TskState).(parkedTaskStacks) ** frame))
    by (unfold task_tcb_init_stack_context; entailer!) end.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg call saved acquired
    cursor publication_heap written middle final_cursor returned_heap _ Hr0 Hmask
    (Hrestore_input publication_heap Hmasked) Hprefix Hsuffix) as [Hsource [Hlr [Hmemory Hreturned]]].
  split; [exact Hsource|].
  match type of Hreturned with ?P returned_heap => match goal with |- ?Q returned_heap =>
    assert (Hreturn : P |-- Q) by entailer! end end.
  exact (Hreturn returned_heap Hreturned).
Qed.
