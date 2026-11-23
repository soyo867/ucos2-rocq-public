Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_sched_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_fields_continuation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual masked suffix transports the already owned continuation
    world.  The current call, active key, local family, parked map and frame
    are unchanged.  This proves no statement about an interruptible prefix
    and does not construct a source trace or its indexed call receipts. *)
Lemma sem_pend_fields_save_suffix_resources :
  forall environment local critical arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg returned registers acquired before final_registers final_state after (frame : Assertion),
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  (sem_pend_fields_closed environment local sg returned
     (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) acquired ** frame) before ->
  armv7a_save_suffix_transition suffix registers acquired before final_registers final_state after ->
  final_state = acquired /\ after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  (sem_pend_fields_masked environment local critical sg returned
     final_registers.(kernel_save_r0) final_state final_state ** frame) after.
Proof.
  intros environment local critical arch suffix sg returned registers acquired before
    final_registers final_state after frame Hsaved Hpre Hrun.
  assert (Hopen : sem_pend_fields_closed environment local sg returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) acquired ** frame |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) returned
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
    (kernel_continuation_inv environment.(task_stack_call_continuations)
      kernel_program_fields_inv local sg (task_stack_call_active_key returned) acquired ** frame)).
  { unfold sem_pend_fields_closed, kernel_continuation_call_closed; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ suffix sg returned registers
    acquired before final_registers final_state after _ Hsaved (Hopen before Hpre) Hrun)
    as [Hstate [Hmemory [Hreturn [Hvalue Hpost]]]].
  subst final_state; split; [reflexivity|]. split; [exact Hmemory|].
  split; [exact Hreturn|]. split; [exact Hvalue|].
  match type of Hpost with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold sem_pend_fields_masked, kernel_continuation_call_masked; entailer!. }
  exact (Hclose after Hpost).
Qed.

(** The input is the actual selected take: handler authority, selected
    fragments/dormant capsule, and the fields world at acquired.  Restore
    creates the resumed running authority; only its real Save suffix creates
    masked ownership.  The descriptor/cursor/register premises identify a
    resumed Save, not a new initial entry.  The caller keeps its source and
    receipt beside this resource composition. *)
Lemma sem_pend_fields_irq_restored_save_resources :
  forall environment local critical arch
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg handler selected original acquired registers heap restored
    final_registers final_state after (frame : Assertion),
  selected.(armv7a_continuation_call) = Some original ->
  selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  armv7a_continuation_restore_reads selected heap ->
  (interrupt_platform_running environment.(task_stack_call_platform)
     handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
   os_int_exit_context_resources environment.(task_stack_call_port) handler **
   task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
     selected.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation environment.(task_stack_call_continuations) selected **
   (kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_fields_inv
      local sg (task_stack_call_active_key (armv7a_continuation_resumed_call selected original))
      acquired ** frame)) heap ->
  armv7a_restore_transition environment.(task_stack_call_continuations) handler selected heap restored ->
  armv7a_save_suffix_transition suffix registers acquired restored final_registers final_state after ->
  final_state = acquired /\ after.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
  final_registers.(kernel_save_return_word) = Some selected.(armv7a_continuation_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  (sem_pend_fields_masked environment local critical sg
     (armv7a_continuation_resumed_call selected original)
     final_registers.(kernel_save_r0) final_state final_state **
   (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) after.
Proof.
  intros environment local critical arch suffix sg handler selected original acquired registers
    heap restored final_registers final_state after frame Hcall Hcursor Hcpsr Hr0 Hlr
    Hsaved Hreads Hpre Hrestore Hsuffix.
  destruct (armv7a_restore_call_resources _ _ _ environment.(task_stack_call_continuations)
    handler selected original _ heap restored Hcall Hreads Hpre Hrestore)
    as [Hmemory Hrestored].
  match type of Hrestored with ?P restored => assert (Hclose : P |--
    sem_pend_fields_closed environment local sg (armv7a_continuation_resumed_call selected original)
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) acquired **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold sem_pend_fields_closed, kernel_continuation_call_closed; rewrite Hcpsr; entailer!. }
  destruct (sem_pend_fields_save_suffix_resources environment local critical arch suffix sg
    (armv7a_continuation_resumed_call selected original) registers acquired restored
    final_registers final_state after _ Hsaved (Hclose restored Hrestored) Hsuffix)
    as [Hstate [Hmemory' [Hreturn [Hvalue Hpost]]]].
  split; [exact Hstate|]. split; [rewrite Hmemory'; exact Hmemory|].
  split; [rewrite <- Hlr; exact Hreturn|]. split; assumption.
Qed.

(** This producer starts before the real Task install loads/stores and
    selects the continuation once.  Its returned function consumes the same
    actual Task restore and Save suffix.  The origin fact connects the
    producer's selected live-coverage key to this returning invocation; no
    active Some key is relabelled None.  Initial-entry descriptors remain
    admitted by the underlying install producer and are not called a return
    of this old Save. *)
Lemma sem_pend_fields_task_installed_save_resources :
  forall environment local critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (suffix : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing hooked incoming resumed before (frame : Assertion),
  let resource := kernel_saved_continuation_entry environment.(task_stack_call_continuations)
    hooked.(TskState) local in
  let acquired := os_sched_install_context context outgoing incoming hooked in
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_fields_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed selected,
    sched_install_heap_fragment sg before installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_binding selected /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at acquired incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage acquired.(TskState) (Some (task_stack_key incoming)) /\
    (forall original registers restored final_registers final_state after,
      selected.(armv7a_continuation_call) = Some original ->
      original.(os_sched_call_origin) = RunningInvocation incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
      selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_task_restore_transition task_abi context selected installed restored ->
      armv7a_save_suffix_transition suffix registers acquired restored final_registers final_state after ->
      armv7a_task_restored_source environment.(task_stack_call_external) selected /\
      final_state = acquired /\ after.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      final_registers.(kernel_save_return_word) = Some selected.(armv7a_continuation_lr) /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
      (sem_pend_fields_masked environment local critical sg
         (armv7a_continuation_resumed_call selected original)
         final_registers.(kernel_save_r0) final_state final_state **
       (local selected ** frame)) after).
Proof.
  intros environment local critical arch task_abi suffix sg context outgoing hooked incoming resumed
    before frame resource acquired Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (kernel_saved_continuation_fields_install_source _ _ _
    environment.(task_stack_call_continuations) task_abi sg context outgoing hooked incoming resumed
    local before frame Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hbinding [Hlease [Hfragments
      [Hcurrent [Hcovered Hrestore]]]]]]]]].
  fold acquired in Hcurrent, Hcovered, Hrestore.
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hbinding|]. split; [exact Hlease|]. split; [exact Hfragments|].
  split; [exact Hcurrent|]. split; [exact Hcovered|].
  intros original registers restored final_registers final_state after Hcall Horigin Hcursor
    Hcpsr Hr0 Hlr Hsaved_value Hactual Hsuffix.
  destruct (Hrestore restored Hactual) as [Hmemory [Hsource Howned]].
  unfold armv7a_task_restored_execution in Howned; rewrite Hcall in Howned.
  assert (Hactive : task_stack_call_active_key (armv7a_continuation_resumed_call selected original) =
    Some (task_stack_key incoming)).
  { unfold task_stack_call_active_key, armv7a_continuation_resumed_call.
    cbn [os_sched_call_origin]; rewrite Horigin; reflexivity. }
  match type of Howned with ?P restored => assert (Hclose : P |--
    sem_pend_fields_closed environment local sg (armv7a_continuation_resumed_call selected original)
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) acquired ** (local selected ** frame)) end.
  { unfold sem_pend_fields_closed, kernel_continuation_call_closed, kernel_continuation_inv.
    rewrite Hcpsr, Hactive; entailer!. }
  destruct (sem_pend_fields_save_suffix_resources environment local critical arch suffix sg
    (armv7a_continuation_resumed_call selected original) registers acquired restored
    final_registers final_state after _ Hsaved_value (Hclose restored Howned) Hsuffix)
    as [Hstate [Hmemory' [Hreturn [Hvalue Hpost]]]].
  split; [exact Hsource|]. split; [exact Hstate|].
  split; [rewrite Hmemory'; exact Hmemory|].
  split; [rewrite <- Hlr; exact Hreturn|]. split; assumption.
Qed.
