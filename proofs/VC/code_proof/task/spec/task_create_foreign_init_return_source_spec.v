Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_interleaving_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_private_irq_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_switch_capture_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_pending_suffix_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A foreign task's ACTUAL later switch returns to an IRQ-suspended
    StackInit command boundary. The partial child frame stays in the same
    separating frame through sixteen foreign stack stores, its TCB-SP
    store, capture, selected empty hook, original install and restore.
    Only then does the existing finite initializer continue. The input is
    the current foreign selector checkpoint produced by the registered
    source chain, not a future original-return resource or postcondition.
    [original] anchors the initializer history; [pending] is the actual
    IRQ-cut call, whose fragments may have changed at earlier IRQ cuts. *)
Lemma task_create_stack_init_foreign_capture_return_source :
  forall schedule environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg args region lower upper initial_name task_return original pending initial_state released
    suspended state node foreign old_sp cpsr registers lr save_prefix save_suffix first old_words publication
    prefix suffix handler_region handler_fragments before (frame : Assertion),
  task_tcb_init_stack_same_call pending original ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial_state ->
  task_create_stack_init_entry_preserved sg args original initial_state released ->
  task_tcb_init_stack_source_preserved original initial_state released ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  Forall (fun word => 0 <= word < 4294967296) suffix ->
  UCOS2_state_inv sg released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released state ->
  pending.(os_sched_call_origin) = RunningInvocation
    pending.(os_sched_call_stack).(stackLeaseSlot) pending.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some pending ->
  armv7a_task_frame_slice suspended ->
  foreign.(os_sched_call_stack).(stackLeaseSlot) <> pending.(os_sched_call_stack).(stackLeaseSlot) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  os_sched_source_live_save_input sg state node foreign old_sp cpsr registers lr
    save_prefix save_suffix first old_words
    (armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr)) publication ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) environment.(task_stack_call_continuations) sg foreign
     (armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr)) state **
   unmap_table_rep sg ** task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
   task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  let fragments := save_prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ save_suffix in
  let foreign_saved := armv7a_task_save_image foreign old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state foreign.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg foreign.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg foreign.(os_sched_call_stack).(stackLeaseSlot))
      foreign_saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi foreign foreign_saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      os_sched_destination_binding environment.(task_stack_call_external) foreign fragments updated
        pending.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
      exists installed selected,
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg pending.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
        selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
        selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
        (forall restored,
          armv7a_task_restore_transition task_abi foreign selected installed restored ->
          task_create_stack_init_irq_continuation schedule environment critical sg args region handler_region
            handler_fragments task_return lower upper initial_name original
            (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) initial_state
            (armv7a_continuation_resumed_call selected pending)
            (os_sched_install_context foreign fragments pending.(os_sched_call_stack) updated)
            prefix suffix restored frame)).
Proof.
  intros schedule environment critical arch task_abi save restore sg args region lower upper initial_name
    task_return original pending initial_state released suspended state node foreign old_sp cpsr registers lr save_prefix
    save_suffix first old_words publication prefix suffix handler_region handler_fragments before frame
    Hpending Hlayout Hentry Hentry_before Hordinary Hwords Hranges Hreleased Hhistory Horigin Hbinding Hcall Hslice
    Hdifferent Hpointer Hinput Hpre fragments foreign_saved updated.
  set (buffer := task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix).
  set (retained := buffer ** task_stack_fragments_rep handler_region handler_fragments ** frame).
  pose proof (proj1 Hpending) as Hinvocation.
  assert (Hpending_history : task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) released state)
    by (rewrite Hinvocation; exact Hhistory).
  pose proof Hinput as Hgeometry.
  destruct Hgeometry as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments
    [Hregion [Hbounds [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges_foreign [Hmask [Hsp32
      [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  match type of Hpre with ?P before => assert (Hcapture_pre : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) environment.(task_stack_call_continuations) sg foreign
      (armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr)) state **
    unmap_table_rep sg ** retained) by (unfold retained, buffer; entailer!) end.
  destruct (task_tcb_init_switch_capture_source environment task_abi sg pending suspended released state node
    foreign old_sp cpsr registers lr save_prefix save_suffix first old_words publication retained before
    Hpending_history Hinput (Hcapture_pre before Hpre))
    as [written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  fold fragments foreign_saved updated in Hstore, Hcapture.
  assert (Hlease : suspended.(armv7a_continuation_stack) = pending.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hpointer_after : task_saved_pointer_at updated suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [original_node [Hlookup [Hg Hpointer]]].
    exists original_node; split; [|auto].
    unfold updated, os_sched_save_current_sp; rewrite Hnode.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    assert (Heq : (suspended.(armv7a_continuation_stack).(stackLeaseSlot) =?
      foreign.(os_sched_call_stack).(stackLeaseSlot)) = false) by
      (apply Z.eqb_neq; rewrite Hlease; congruence).
    rewrite Heq; exact Hlookup. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step Hdestination.
  assert (Hhook_eq : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hsave_source [Hhistory_after Hcaptured_owned]].
  destruct (task_tcb_init_pending_call_suffix_source environment critical arch task_abi save restore
    sg pending released foreign fragments updated suspended captured retained
    Hhistory_after Horigin Hbinding Hcall Hslice Hpointer_after (Haddress _) Hdestination Hcaptured_owned)
    as [installed [selected [Hinstall [Hreads [Hselected_sp [Hselected_cpsr [Hregisters Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hselected_sp|]. split; [exact Hselected_cpsr|]. split; [exact Hregisters|].
  intros restored Hrestore.
  destruct (Hreturn restored Hrestore)
    as [Hsame [Hready [Hstage [Hreturned_history [Hreturned_source [Howned Hsuffixes]]]]]].
  set (returned := armv7a_continuation_resumed_call selected pending).
  set (current := os_sched_install_context foreign fragments pending.(os_sched_call_stack) updated).
  rewrite Hinvocation in Hreturned_history.
  assert (Hsame_original : task_tcb_init_stack_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]]; destruct Hpending as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call, returned; repeat split; congruence. }
  assert (Hsource_next : task_tcb_init_stack_source_preserved original initial_state current).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact Hordinary|].
    eapply task_create_stack_same_call_source_preserved; [exact Hpending|exact (Hreturned_source Hreleased)]. }
  assert (Hentry_next : task_create_stack_init_entry_preserved sg args original initial_state current).
  { intros name Hinitial.
    eapply task_tcb_init_call_preserves_entry; [exact (Hentry_before name Hinitial)|exact Hreturned_history]. }
  match type of Howned with ?P restored => assert (Hnext : P |--
    task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
    task_tcb_init_stack_save_input environment critical sg returned
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current ** unmap_table_rep sg **
    task_stack_fragments_rep handler_region handler_fragments ** frame)
    by (unfold retained, buffer; entailer!) end.
  eapply task_create_stack_init_irq_continuation_source.
  - exact Hlayout.
  - exact Hentry.
  - exact Hsame_original.
  - exact Hentry_next.
  - exact Hsource_next.
  - exact Hwords.
  - exact Hranges.
  - exact (Hnext restored Howned).
Qed.

(** The same physical foreign return, now carrying the partially
    initialized private TCB and its allocation history. This directly
    consumes the existing pending restore producer before any Save/Restore
    suffix: execution resumes inside the C field/hook interval, so a
    second MRS/MSR/BX is neither inserted nor assumed. *)
Lemma task_tcb_init_private_foreign_capture_return_source :
  forall schedule environment critical arch
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg args initial_name original pending initial_state detached released slot free_image commands image
    suspended state node foreign old_sp cpsr registers lr save_prefix save_suffix first old_words publication
    handler_region handler_fragments before (frame : Assertion),
  task_tcb_init_stack_same_call pending original ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached released ->
  task_tcb_init_stack_source_preserved original initial_state released ->
  Forall (task_tcb_init_private_command_valid sg) commands ->
  fold_left task_tcb_init_private_command_image commands image =
    task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile) (task_tcb_init_stack_call_args args initial_name) free_image ->
  UCOS2_state_inv sg released ->
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released state ->
  pending.(os_sched_call_origin) = RunningInvocation
    pending.(os_sched_call_stack).(stackLeaseSlot) pending.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_continuation_binding suspended -> suspended.(armv7a_continuation_call) = Some pending ->
  armv7a_task_frame_slice suspended ->
  foreign.(os_sched_call_stack).(stackLeaseSlot) <> pending.(os_sched_call_stack).(stackLeaseSlot) ->
  task_saved_pointer_at state suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
  os_sched_source_live_save_input sg state node foreign old_sp cpsr registers lr
    save_prefix save_suffix first old_words
    (armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr)) publication ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) environment.(task_stack_call_continuations) sg foreign
     (armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr)) state **
   unmap_table_rep sg ** task_slot_storage_rep sg slot image **
   task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  let fragments := save_prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ save_suffix in
  let foreign_saved := armv7a_task_save_image foreign old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state foreign.(os_sched_call_stack).(stackLeaseSlot)
    foreign_saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg foreign.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg foreign.(os_sched_call_stack).(stackLeaseSlot))
      foreign_saved.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi foreign foreign_saved stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      os_sched_destination_binding environment.(task_stack_call_external) foreign fragments updated
        pending.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) ->
      exists installed selected,
        sched_install_heap_fragment sg hooked installed
          (task_slot_addr sg pending.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
        selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
        selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
        (forall restored,
          armv7a_task_restore_transition task_abi foreign selected installed restored ->
          task_tcb_init_private_irq_continuation schedule environment critical sg args initial_name
            handler_region handler_fragments original (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr))
            initial_state detached slot free_image (armv7a_continuation_resumed_call selected pending)
            (os_sched_install_context foreign fragments pending.(os_sched_call_stack) updated)
            commands image restored frame)).
Proof.
  intros schedule environment critical arch task_abi save restore sg args initial_name original pending initial_state
    detached released slot free_image commands image suspended state node foreign old_sp cpsr registers lr
    save_prefix save_suffix first old_words publication handler_region handler_fragments before frame
    Hpending Hprevious Hordinary Hcommands Himage Hreleased Hhistory Horigin Hbinding Hcall Hslice
    Hdifferent Hpointer Hinput Hpre fragments foreign_saved updated.
  set (buffer := task_slot_storage_rep sg slot image).
  set (retained := buffer ** task_stack_fragments_rep handler_region handler_fragments ** frame).
  pose proof (proj1 Hpending) as Hinvocation.
  assert (Hpending_history : task_tcb_init_call_preserved sg pending.(os_sched_call_invocation) released state)
    by (rewrite Hinvocation; exact Hhistory).
  pose proof Hinput as Hgeometry.
  destruct Hgeometry as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments
    [Hregion [Hbounds [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges_foreign [Hmask [Hsp32
      [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  match type of Hpre with ?P before => assert (Hcapture_pre : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) environment.(task_stack_call_continuations) sg foreign
      (armv7a_call_focus pending suspended.(armv7a_continuation_pc) suspended.(armv7a_continuation_lr)) state **
    unmap_table_rep sg ** retained) by (unfold retained, buffer; entailer!) end.
  destruct (task_tcb_init_switch_capture_source environment task_abi sg pending suspended released state node
    foreign old_sp cpsr registers lr save_prefix save_suffix first old_words publication retained before
    Hpending_history Hinput (Hcapture_pre before Hpre))
    as [written [stored [Hwrites [Hload [Hstore Hcapture]]]]].
  fold fragments foreign_saved updated in Hstore, Hcapture.
  assert (Hlease : suspended.(armv7a_continuation_stack) = pending.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hpointer_after : task_saved_pointer_at updated suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp)).
  { destruct Hpointer as [original_node [Hlookup [Hg Hpointer]]].
    exists original_node; split; [|auto].
    unfold updated, os_sched_save_current_sp; rewrite Hnode.
    cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
    assert (Heq : (suspended.(armv7a_continuation_stack).(stackLeaseSlot) =?
      foreign.(os_sched_call_stack).(stackLeaseSlot)) = false) by
      (apply Z.eqb_neq; rewrite Hlease; congruence).
    rewrite Heq; exact Hlookup. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcaptured Hhook_heap Hhook_step Hdestination.
  assert (Hhook_eq : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook_heap|].
    split; [constructor|]; split; reflexivity. }
  subst hooked.
  destruct (Hcapture captured Hcaptured) as [Hsave_source [Hhistory_after Hcaptured_owned]].
  destruct (task_tcb_init_pending_call_suffix_source environment critical arch task_abi save restore
    sg pending released foreign fragments updated suspended captured retained
    Hhistory_after Horigin Hbinding Hcall Hslice Hpointer_after (Haddress _) Hdestination Hcaptured_owned)
    as [installed [selected [Hinstall [Hreads [Hselected_sp [Hselected_cpsr [Hregisters Hreturn]]]]]]].
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hselected_sp|]. split; [exact Hselected_cpsr|]. split; [exact Hregisters|].
  intros restored Hrestore.
  destruct (Hreturn restored Hrestore)
    as [Hsame [Hready [Hstage [Hreturned_history [Hreturned_source [Howned Hsuffixes]]]]]].
  set (returned := armv7a_continuation_resumed_call selected pending).
  set (current := os_sched_install_context foreign fragments pending.(os_sched_call_stack) updated).
  rewrite Hinvocation in Hreturned_history.
  assert (Hsame_original : task_tcb_init_stack_same_call returned original).
  { destruct Hsame as [Hi [Ho Hs]]; destruct Hpending as [Hi' [Ho' Hs']].
    unfold task_tcb_init_stack_same_call, returned; repeat split; congruence. }
  assert (Hsource_next : task_tcb_init_stack_source_preserved original initial_state current).
  { eapply task_tcb_init_stack_source_preserved_trans; [exact Hordinary|].
    eapply task_create_stack_same_call_source_preserved; [exact Hpending|exact (Hreturned_source Hreleased)]. }
  assert (Hhistory_next : task_tcb_init_call_preserved sg original.(os_sched_call_invocation) detached current).
  { eapply task_tcb_init_call_preserved_trans; eassumption. }
  match type of Howned with ?P restored => assert (Hnext : P |--
    task_slot_storage_rep sg slot image **
    task_tcb_init_stack_save_input environment critical sg returned
      (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) current ** unmap_table_rep sg **
    task_stack_fragments_rep handler_region handler_fragments ** frame)
    by (unfold retained, buffer; entailer!) end.
  eapply task_tcb_init_private_irq_continuation_source.
  - exact Hsame_original.
  - exact Hhistory_next.
  - exact Hsource_next.
  - exact Hcommands.
  - exact Himage.
  - exact (Hnext restored Howned).
Qed.
