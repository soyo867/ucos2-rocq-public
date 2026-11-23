Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected original call's real Scheduler local is consumed by
    install/TaskRestore and its own C Restore. The resulting TaskCreate
    public post preserves every OTHER local, including arbitrary IRQ cuts
    and initial None entries. A source trace must supply this actual
    selector cut; neither eventual selection nor a future post is assumed. *)
Lemma task_create_saved_continuation_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg context outgoing hooked original saved acquired saved_local resumed before
  region args task_return lower old_frame upper (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_at environment.(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired
    (task_create_continuation_local saved_local) in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding environment.(task_stack_call_external)
    context outgoing hooked original.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
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
        (task_create_continuation_post environment critical saved_local sg region args task_return
          lower old_frame upper original (armv7a_irq_fiq_mask saved) 0 ** frame) after)).
Proof.
  intros environment critical arch task_abi restore sg context outgoing hooked original saved acquired
    saved_local resumed before region args task_return lower old_frame upper frame abi local resource current
    Hsaved Hdestination Haddress Hcoverage Hpre.
  destruct (kernel_saved_sched_continuation_return_source _ _ _ abi critical arch task_abi restore
    sg context outgoing hooked original saved acquired (task_create_continuation_local saved_local)
    resumed before frame Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  fold current local in Hrestore.
  assert (Hcoverage_current : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  assert (Habsent : current.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None).
  { apply task_stack_take_lookup. }
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hcall [Hsource Htail]].
  fold returned in Hsource, Htail.
  assert (Hsame : task_tcb_init_stack_same_call returned original).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold armv7a_continuation_resumed_call, task_tcb_init_stack_same_call; cbn; auto. }
  assert (Hcoverage_returned : task_stack_live_coverage current.(TskState)
    (task_stack_call_active_key returned)).
  { destruct Hsame as [Hi [Ho Hs]].
    pose proof (proj1 Hsource) as Horigin.
    unfold task_stack_call_active_key; rewrite Horigin, Hs; exact Hcoverage_current. }
  split; [exact Hcall|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  split; [exact Hrun|]. split; [exact Hlr|].
  match type of Howned with ?P after => assert (Hclose : P |--
    kernel_continuation_call_closed abi kernel_program_inv (task_create_continuation_local saved_local)
      sg (task_stack_call_active_key returned) returned (armv7a_irq_fiq_mask saved) current ** frame) end.
  { unfold local.
    sep_apply_l_atomic (kernel_saved_continuation_map_unfocus_absent _ _ _ abi critical sg hooked.(TskState)
      current.(TskState) original saved acquired (task_create_continuation_local saved_local)
      current.(TskState).(parkedTaskStacks) Habsent).
    unfold kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
  pose proof (Hclose after Howned) as Hclosed.
  match type of Hclosed with ?P after => match goal with |- ?Q after => assert (Hpost : P |-- Q) end end.
  { unfold abi; sepcon_assoc_change.
    sep_apply_l_atomic (task_create_continuation_closed_returns_success environment critical saved_local sg
      original returned (armv7a_irq_fiq_mask saved) current region args task_return lower old_frame upper Hsame).
    entailer!. }
  exact (Hpost after Hclosed).
Qed.
