Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_wake_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_return_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The original TaskCreate invocation has reached its successful
    OS_Sched call. At this CURRENT selector cut that saved invocation
    is selected again. Its exact entry must have been established by
    [kernel_sched_save_capture_source] and transported through the actual
    intervening execution; a generic Some entry cannot be strengthened
    into it. No separate previous Save/inside pair is assumed below.

    The existing physical producer performs the outgoing stores/capture
    and exact original install/TaskRestore. The shared source tail then
    consumes the later real OS_CPU_SR_Restore call, with its own LR, and
    supplies the same Scheduler return post that TaskCreate's successful
    TCB-return consumer uses. Child resources are accounted for by the
    current kernel world, without promising survival across arbitrary
    earlier interference; disjoint caller storage stays in [frame].

    This is the present selected-call / no-write-hook / uninterrupted
    final-Restore source family. It does not select an empty application
    hook, prove arbitrary foreign execution or eventual selection, or
    treat an initializer's arbitrary interrupted PC as a Scheduler return. *)
Lemma task_create_saved_sched_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg state node context old_sp cpsr values lr prefix suffix first old_words publication
  original saved acquired descriptor focus call_entry region args task_return lower old_frame upper
  before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments original.(os_sched_call_stack) updated in
  let returned := kernel_selected_call descriptor current in
  os_sched_source_live_save_input sg state node context old_sp cpsr values lr
    prefix suffix first old_words focus publication ->
  state.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
     context 192 ** kernel_program_inv sg state **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        descriptor.(armv7a_continuation_call) = Some original /\
        (forall restored,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          forall cursor restore_written middle final_cursor after,
          cursor.(kernel_restore_r0) = saved ->
          armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
          armv7a_restore_prefix_transition restore cursor restored restore_written middle ->
          armv7a_restore_suffix_transition restore restore_written middle final_cursor after ->
          kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
          final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
          (os_sched_stack_return_post environment kernel_program_inv sg original
             (armv7a_irq_fiq_mask saved) call_entry ** frame) after /\
          (task_create_stack_post environment critical sg region args task_return lower old_frame upper
             original (armv7a_irq_fiq_mask saved) 0 ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg state node context old_sp cpsr values lr prefix suffix
    first old_words publication original saved acquired descriptor focus call_entry region args task_return
    lower old_frame upper before frame abi fragments outgoing updated current returned
    Hinput Hselected Hparked Hcoverage Hpre.
  pose proof Hinput as [Hcurrent [Hnode Hinput_rest]].
  match type of Hpre with ?P before => assert (Hobserve : P |--
    coq_prop (armv7a_continuation_binding descriptor) && TT) end.
  { sep_apply_l_atomic (kernel_saved_sched_call_take_resources _ _ _ abi critical sg original saved acquired
      descriptor state.(TskState) focus state.(TskState).(parkedTaskStacks)
      descriptor.(armv7a_continuation_fragments) Hparked).
    unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec; [|contradiction].
    Intros; entailer!; intros ? ?; exact I. }
  pose proof (proj1 (Hobserve before Hpre)) as Hbinding.
  assert (Hcovered_updated : task_stack_live_coverage updated.(TskState)
    (Some (task_stack_key context.(os_sched_call_stack)))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    eapply task_stack_save_sp_preserves_coverage; eassumption. }
  assert (Hcovered_current : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks updated.(TskState)
        (task_stack_park_fragments updated.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) fragments))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active updated.(TskState) context.(os_sched_call_stack) fragments Hcovered_updated)). }
  destruct (kernel_saved_sched_call_live_switch_source _ _ _ abi critical task_abi sg state node context
    old_sp cpsr values lr prefix suffix first old_words publication original saved acquired descriptor focus
    before frame Hinput Hselected Hparked Hpre)
    as [written [stored [Hwrites [Hload [Hstore Hcontinue]]]]].
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook Hhook_source.
  destruct (Hcontinue captured hooked Hcapture Hhook Hhook_source)
    as [installed [Hinstall [Hreads [Hcall [Hsource Hrestore]]]]].
  fold current returned in Hsource, Hrestore.
  assert (Hsource_returned : kernel_call_task_source returned current) by exact Hsource.
  assert (Hlease : descriptor.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hsame : kernel_stack_call_same_call returned original).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold kernel_stack_call_same_call, armv7a_continuation_resumed_call; cbn; auto. }
  assert (Hactive : task_stack_call_active_key original = Some (task_stack_key original.(os_sched_call_stack))).
  { assert (Horigin : returned.(os_sched_call_origin) = RunningInvocation
      returned.(os_sched_call_stack).(stackLeaseSlot) returned.(os_sched_call_stack).(stackLeaseGeneration))
      by exact (proj1 Hsource).
    rewrite (proj1 (proj2 Hsame)), (proj2 (proj2 Hsame)) in Horigin.
    unfold task_stack_call_active_key; rewrite Horigin; reflexivity. }
  exists installed; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hcall|].
  intros restored Htask_restore cursor restore_written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Hrestore restored Htask_restore) as [Hresume [Hpc [Hcpsr [Hmemory Howned]]]].
  assert (Howned_current :
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       returned.(os_sched_call_invocation) returned.(os_sched_call_origin) saved acquired **
     os_sched_context_resources environment.(task_stack_call_external) returned **
     kernel_program_inv sg current **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
     frame) restored) by exact Howned.
  match type of Howned_current with ?P restored => assert (Hmasked : P |--
    kernel_stack_call_masked abi kernel_program_inv critical sg (task_stack_call_active_key original)
      returned saved acquired current ** frame) end.
  { sep_apply_l_atomic (armv7a_task_call_stacks_forget _ _ _ abi current.(TskState) focus
      current.(TskState).(parkedTaskStacks)).
    unfold kernel_stack_call_masked, kernel_stack_inv; rewrite Hactive; entailer!. }
  destruct (kernel_saved_sched_call_return_source environment kernel_program_inv critical arch restore
    sg original returned call_entry saved acquired current cursor restored restore_written middle final_cursor after
    frame Hsame Hsource_returned Hr0 Hmask (Hmasked restored Howned_current) Hprefix Hsuffix)
    as [Hrun [Hlr [Hclosed Hpost]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hpost|].
  match type of Hpost with ?P after => match goal with |- ?Q after => assert (Hpublic : P |-- Q) end end.
  { sep_apply_l_atomic (os_sched_stack_return_post_returns_create environment critical sg original original
      (armv7a_irq_fiq_mask saved) call_entry region args task_return lower old_frame upper
      ltac:(unfold task_tcb_init_stack_same_call; auto)); entailer!. }
  exact (Hpublic after Hpost).
Qed.
