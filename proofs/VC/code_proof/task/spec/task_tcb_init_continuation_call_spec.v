Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same physical parked map carries each saved program point's local
    owner. None is the existing initial-frame case and has no saved local.
    No field or resource law is added to TaskStackCallEnvironment. *)
Definition task_tcb_init_continuation_capsules environment saved_local state : Assertion :=
  store_parked_continuations
    (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
      state.(TskState) (task_create_continuation_local saved_local))
    state.(TskState).(parkedTaskStacks).

(** Reservation, private detach and rollback retain both maps. This rule
    only reindexes their existing resources; it cannot recover forgotten
    local owners or transport an arbitrary interfering state change. *)
Lemma task_tcb_init_continuation_capsules_used_map_eq :
  forall environment saved_local before after,
  before.(TskState).(inUsedTaskStates) = after.(TskState).(inUsedTaskStates) ->
  before.(TskState).(parkedTaskStacks) = after.(TskState).(parkedTaskStacks) ->
  task_tcb_init_continuation_capsules environment saved_local before |--
  task_tcb_init_continuation_capsules environment saved_local after.
Proof.
  intros environment saved_local before after Hused Hparked.
  unfold task_tcb_init_continuation_capsules; rewrite <- Hparked.
  apply kernel_saved_continuation_map_used_map_eq; exact Hused.
Qed.

(** Source-facing posts describe the actual returning endpoint. They are
    not installed as universal CPU postconditions. A returning producer
    must supply this endpoint's entire continuation map on its real heap. *)
Definition task_tcb_init_continuation_save_post environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg original returned mask saved before acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(task_stack_call_external) returned ** UCOS2_inv sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).

Definition task_tcb_init_continuation_restore_post environment critical saved_local
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients)
      sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      released false returned.(os_sched_call_origin) current /\
      returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
      UCOS2_state_inv sg current /\
      task_stack_live_coverage current.(TskState) (task_stack_call_active_key returned)) &&
    (kernel_call_execution_owned environment.(task_stack_call_external)
       environment.(task_stack_call_platform) returned mask **
     critical_region_outside critical sg returned.(os_sched_call_invocation) current **
     task_tcb_init_continuation_capsules environment saved_local current).

(** Concrete MSR/BX execution keeps the supplied map and local resources.
    The reflexive source interval is justified by this uninterrupted branch
    alone, not by the shape of the public Restore interface. *)
Lemma task_tcb_init_continuation_uninterrupted_restore_post :
  forall environment critical saved_local arch
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call saved entry released cursor before written_cursor middle final_cursor after (frame : Assertion),
  UCOS2_state_inv sg released ->
  task_stack_live_coverage released.(TskState) (task_stack_call_active_key call) ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources environment.(task_stack_call_external) call ** UCOS2_inv sg released **
   task_tcb_init_continuation_capsules environment saved_local released ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written_cursor middle ->
  armv7a_restore_suffix_transition restore written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (task_tcb_init_continuation_restore_post environment critical saved_local sg call
     (armv7a_irq_fiq_mask saved) released ** frame) after.
Proof.
  intros environment critical saved_local arch restore sg call saved entry released
    cursor before written_cursor middle final_cursor after frame Hvalid Hcoverage Hr0 Hmask Hbefore Hprefix Hsuffix.
  match type of Hbefore with ?P before =>
    assert (Horder : P |--
      critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved entry **
      os_sched_context_resources environment.(task_stack_call_external) call **
      (UCOS2_inv sg released ** task_tcb_init_continuation_capsules environment saved_local released ** frame))
  end.
  { entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch restore sg call saved entry cursor before written_cursor
    middle final_cursor after _ Hr0 Hmask (Horder before Hbefore) Hprefix Hsuffix)
    as [Hrun [Hreturn [Hmemory Hafter]]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None call.(os_sched_call_origin)
    released false call.(os_sched_call_origin) released) by constructor.
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_continuation_restore_post environment critical saved_local
      sg call (armv7a_irq_fiq_mask saved) released ** frame)
  end.
  { unfold task_tcb_init_continuation_restore_post; Exists call released.
    unfold critical_region_outside; rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running; unfold UCOS2_inv; entailer!. }
  exact (Hpost after Hafter).
Qed.

(** Actual MRS/CPSID/DSB/BX with the same supplied frame. This branch
    does not erase interrupt execution. An interrupted return still needs
    its own registered producer of the source-facing post above. *)
Lemma task_tcb_init_continuation_uninterrupted_save_post :
  forall environment critical saved_local arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg call mask state registers before final_registers acquired after (frame : Assertion),
  UCOS2_state_inv sg state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask **
   critical_region_outside critical sg call.(os_sched_call_invocation) state **
   task_tcb_init_continuation_capsules environment saved_local state ** frame) before ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (task_tcb_init_continuation_save_post environment critical saved_local sg call mask
     final_registers.(kernel_save_r0) state ** frame) after.
Proof.
  intros environment critical saved_local arch suffix sg call mask state registers before
    final_registers acquired after frame Hvalid Hcoverage Hreturn Hcpsr Hmask Hbefore Hrun.
  match type of Hbefore with ?P before =>
    assert (Hopen : P |--
      kernel_call_execution_owned environment.(task_stack_call_external)
        environment.(task_stack_call_platform) call
        (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
      (UCOS2_inv sg state ** task_tcb_init_continuation_capsules environment saved_local state ** frame))
  end.
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask.
    unfold critical_region_outside; rewrite critical_region_outside_without_running_rep.
    rewrite <- UCOS2_raw_rep_split_running; unfold UCOS2_inv; entailer!. }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hcpsr|reflexivity]. }
  assert (Hsource : kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun). }
  destruct (armv7a_save_suffix_preserves_source_heap environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch suffix sg call (kernel_save_read_cpsr registers)
    state before final_registers acquired after _ Hsaved (Hopen before Hbefore) Hrun)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  split; [exact Hsource|]. subst acquired.
  assert (Hcall : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call call mask final_registers.(kernel_save_r0) state state).
  { split; [constructor|]. repeat (split; [reflexivity|]).
    rewrite Hr0; split; [exact Hcpsr|exact Hmask]. }
  match type of Hafter with ?P after =>
    assert (Hpost : P |-- task_tcb_init_continuation_save_post environment critical saved_local
      sg call mask final_registers.(kernel_save_r0) state ** frame)
  end.
  { unfold task_tcb_init_continuation_save_post; Exists call state; entailer!. }
  exact (Hpost after Hafter).
Qed.
