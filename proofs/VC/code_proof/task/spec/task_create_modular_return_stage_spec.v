Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_return_stage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The registered install action and the returned execution source name
    the SAME post-hook/installed edge.  The cache/destination establish
    readiness, and the take establishes absence.  Neither fact is an
    arbitrary ClientFrame preservation requirement.  The final resource
    consumer below supplies this action from its executed install. *)
Lemma task_create_install_client_return_stage :
  forall external sg context outgoing incoming resumed hooked current returned,
  UCOS2_state_inv sg hooked ->
  hooked.(SchedState).(isRunning) = true ->
  kernel_client_step (os_sched_install_client external context outgoing incoming resumed)
    sg hooked current ->
  returned.(os_sched_call_stack) = incoming ->
  kernel_call_task_source returned current ->
  task_create_call_stage returned current /\ current.(IntrState) = hooked.(IntrState).
Proof.
  intros external sg context outgoing incoming resumed hooked current returned
    Hvalid Hrunning [Hsaved [Hdestination [Hhigh ->]]] Hstack Hsource.
  split; [|reflexivity].
  eapply task_create_installed_call_stage; try eassumption.
  intros _; exact Hhigh.
Qed.

(** Actual saved-call selection followed by its C Restore.  [acquired] is
    the original call's actual switching checkpoint; [selecting] is the
    later selector that really installs this saved call.  Both guards are
    observations of those executed C branches, not future-return claims.

    The supported no-kernel-write hook family has the literal post-hook
    endpoint [hooked] below.  This does not claim that arbitrary hooks have
    the same endpoint.  The current map, destination and save-local owner
    are consumed by the already proved modular return.  Its final call,
    stage and interrupt nesting use one exact returned/current pair.

    No partial Suspend/Pend cut is required to be ready.  No normal-stage
    law is added to a platform ABI or to every registered client action. *)
Lemma task_create_modular_selected_return_stage :
  forall environment critical saved_local arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg context outgoing selecting sp source_tasks original saved acquired resumed before (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let hooked := os_sched_save_current_sp (os_sched_prefix_state selecting)
    context.(os_sched_call_stack).(stackLeaseSlot) sp in
  let local := kernel_sched_saved_local_at environment.(task_stack_call_platform)
    critical sg source_tasks original saved acquired (task_create_continuation_local saved_local) in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  os_sched_requests_switch acquired = true ->
  os_sched_requests_switch selecting = true ->
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  hooked.(SchedState).(isRunning) = true ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
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
      task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        task_create_call_stage returned current /\
        current.(IntrState).(intNesting) = acquired.(IntrState).(intNesting) /\
        (os_sched_continuation_pre environment saved_local kernel_program_inv sg
          returned (armv7a_irq_fiq_mask saved) current ** frame) after /\
        (os_sched_continuation_return_post environment saved_local kernel_program_inv sg
          original (armv7a_irq_fiq_mask saved) acquired ** frame) after)).
Proof.
  intros environment critical saved_local arch task_abi restore sg context outgoing selecting sp source_tasks
    original saved acquired resumed before frame abi hooked local resource current
    Horiginal_switch Hselected_switch Hactive Hrunning Hhigh Hsaved Hdestination Haddress Hcoverage Hpre.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P before =>
      assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hpre)). }
  destruct (os_sched_modular_saved_call_return
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    environment.(task_stack_call_port) critical arch abi task_abi restore
    sg context outgoing hooked source_tasks original saved acquired
    (task_create_continuation_local saved_local) resumed before frame
    Hactive Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease Hfinish]]]]].
  fold current local resource in Hfinish.
  destruct (os_sched_install_client_resources environment.(task_stack_call_external)
    sg context outgoing hooked original.(os_sched_call_stack) resumed resource
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)
    before installed selected.(armv7a_continuation_sp)
    Hsaved Hdestination Hhigh Haddress Hpre Hinstall)
    as [Hinstall_step [Hselected_current [Harch_restore Hinstalled]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Hrestore returned.
  destruct (Hfinish restored Hrestore) as [Hcall [Hi [Ho [Hs [Hsource Htail]]]]].
  fold returned in Hi, Ho, Hs, Hsource, Htail.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by exact (conj Hi (conj Ho Hs)).
  destruct (task_create_install_client_return_stage environment.(task_stack_call_external) sg
    context outgoing original.(os_sched_call_stack) resumed hooked current returned
    Hvalid Hrunning Hinstall_step Hs Hsource) as [Hstage Hinterrupt].
  assert (Hnesting : current.(IntrState).(intNesting) = acquired.(IntrState).(intNesting)).
  { pose proof (proj1 (proj1 (os_sched_requests_switch_iff acquired) Horiginal_switch)) as Horiginal_enabled.
    pose proof (proj1 (proj1 (os_sched_requests_switch_iff selecting) Hselected_switch)) as Hselected_enabled.
    pose proof (proj1 (proj1 (os_sched_selection_enabled_iff acquired) Horiginal_enabled)) as Horiginal_zero.
    pose proof (proj1 (proj1 (os_sched_selection_enabled_iff selecting) Hselected_enabled)) as Hselected_zero.
    rewrite Hinterrupt.
    change (selecting.(IntrState).(intNesting) = acquired.(IntrState).(intNesting)).
    rewrite Horiginal_zero, Hselected_zero; reflexivity. }
  split; [exact Hcall|]. split; [exact Hsame|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  split; [exact Hrun|]. split; [exact Hstage|]. split; [exact Hnesting|].
  assert (Hclosed :
    (os_sched_continuation_pre environment saved_local kernel_program_inv sg
      returned (armv7a_irq_fiq_mask saved) current ** frame) after).
  { unfold os_sched_continuation_pre.
    pose proof (proj1 Hsource) as Horigin.
    unfold task_stack_call_active_key; rewrite Horigin, Hs; exact Howned. }
  split; [exact Hclosed|].
  assert (Hpost : os_sched_continuation_pre environment saved_local kernel_program_inv sg
      returned (armv7a_irq_fiq_mask saved) current ** frame |--
    os_sched_continuation_return_post environment saved_local kernel_program_inv sg
      original (armv7a_irq_fiq_mask saved) acquired ** frame).
  { unfold os_sched_continuation_pre, os_sched_continuation_return_post.
    assert (Htransport : kernel_call_task_source original acquired ->
      kernel_call_task_source returned current) by (intros _; exact Hsource).
    Exists returned current; entailer!. }
  exact (Hpost after Hclosed).
Qed.
