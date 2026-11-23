Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
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
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_saved_continuation_return_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A saved local retains the registration fact from its actual save cut.
    At a later selector the already executed source chain separately supplies
    the current registration. Only that pure observation changes here: the
    descriptor, live-SP index, physical owner, Save token and inside resource
    remain the same. Other keys retain their original local predicates.
    No inactive historical entry is required to become active, and a descriptor
    or address alone is never used to infer current registration. *)
Lemma kernel_saved_continuation_entry_current_registration :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    critical sg source_tasks current_tasks tasks original saved acquired other key payload,
  task_invocation_active current_tasks original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  kernel_saved_continuation_entry abi tasks
    (kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other)
    key payload |--
  kernel_saved_continuation_entry abi tasks
    (kernel_sched_saved_local_at platform critical sg current_tasks original saved acquired other)
    key payload.
Proof.
  intros external platform port abi critical sg source_tasks current_tasks tasks original
    saved acquired other key payload Hactive.
  unfold kernel_saved_continuation_entry; Intros descriptor; Exists descriptor.
  unfold kernel_sched_saved_local_at.
  destruct task_stack_key_eq_dec; [unfold kernel_sched_saved_local; entailer!|entailer!].
Qed.

(** The same pointwise conversion applies to the existing map. It neither
    removes a parked entry nor discards the owners of other continuations. *)
Lemma kernel_saved_continuation_map_current_registration :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    critical sg source_tasks current_tasks tasks original saved acquired other stacks,
  task_invocation_active current_tasks original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other)) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_at platform critical sg current_tasks original saved acquired other)) stacks.
Proof.
  intros external platform port abi critical sg source_tasks current_tasks tasks original
    saved acquired other stacks Hactive.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; apply kernel_saved_continuation_entry_current_registration; exact Hactive.
Qed.

(** Actual park/take, install, TaskRestore and the subsequent C Restore now
    consume the local from its historical save cut. The current-active premise
    is an observation to be established by the intervening concrete source
    chain; it is not an external law or a promise that this call will return.
    The whole chain need not be forced into a registry-only trace: physical
    deposit and take have their own checked source edges.

    This theorem starts at the actual selector cut. Its body invokes the
    existing physical return consumer and reaches the unchanged current
    TaskCreate public post, preserving all remaining saved locals. *)
Lemma task_create_saved_continuation_history_return_source : forall environment critical arch
  (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations))
  (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
    environment.(task_stack_call_platform) critical arch)
  sg context outgoing hooked source_tasks original saved acquired saved_local resumed before
  region args task_return lower old_frame upper (frame : Assertion),
  let abi := environment.(task_stack_call_continuations) in
  let local := kernel_sched_saved_local_at environment.(task_stack_call_platform)
    critical sg source_tasks original saved acquired
    (task_create_continuation_local saved_local) in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
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
  intros environment critical arch task_abi restore sg context outgoing hooked source_tasks original saved acquired
    saved_local resumed before region args task_return lower old_frame upper frame abi local resource current
    Hactive Hsaved Hdestination Haddress Hcoverage Hpre.
  set (current_local := kernel_sched_saved_local_at environment.(task_stack_call_platform)
    critical sg hooked.(TskState) original saved acquired (task_create_continuation_local saved_local)).
  set (current_resource := kernel_saved_continuation_entry abi hooked.(TskState) current_local).
  assert (Hentry : forall key payload, resource key payload |-- current_resource key payload).
  { intros key payload; unfold resource, local, current_resource, current_local.
    apply kernel_saved_continuation_entry_current_registration; exact Hactive. }
  assert (Hmap : store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) |--
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks)).
  { unfold resource, local, current_resource, current_local.
    apply kernel_saved_continuation_map_current_registration; exact Hactive. }
  match type of Hpre with ?P before => assert (Hconvert : P |--
    UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    current_resource (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) end.
  { sep_apply_l_atomic (Hentry (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
    sep_apply_l_atomic Hmap; entailer!. }
  exact (task_create_saved_continuation_return_source environment critical arch task_abi restore
    sg context outgoing hooked original saved acquired saved_local resumed before
    region args task_return lower old_frame upper frame
    Hsaved Hdestination Haddress Hcoverage (Hconvert before Hpre)).
Qed.
