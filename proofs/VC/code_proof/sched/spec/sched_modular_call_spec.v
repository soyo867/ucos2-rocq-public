Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual no-switch C call: the existing platform Save contract,
    all three non-switch C branches, and the existing platform Restore
    contract act on the SAME owned world. The arbitrary local map is not
    forgotten between these calls. No source instruction is reproved here.

    This is the uninterrupted platform-return family. The actual branch
    observation is not a public exclusion of scheduling or interrupts;
    the theorem alone does not establish the whole OS_Sched contract. The
    readiness premise refers only to this current selection cut, never
    to every future acquisition or an eventual return. *)
Lemma os_sched_modular_nonswitch_continuation_call :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (save : Armv7aSaveSuffixABI external platform critical arch)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    local sg active call mask state registers before
    final_registers acquired saved_heap (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (kernel_continuation_call_closed abi kernel_program_inv local sg active
    call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  acquired = state /\
  kernel_call_save_uninterrupted_execution arch registers state before
    final_registers acquired saved_heap /\
  exists prefix_heap,
    os_sched_source_nonswitch_prefix_execution sg saved_heap prefix_heap /\
    (forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = final_registers.(kernel_save_r0) ->
      armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      (kernel_continuation_call_closed abi kernel_program_inv local sg active
        call mask (os_sched_prefix_state state) ** frame) after).
Proof.
  intros external platform port critical arch abi save restore local sg active call mask state
    registers before final_registers acquired saved_heap frame Hreturn Hvalid Hmask
    Hnoswitch Hnonempty Hpre Hsave.
  destruct (kernel_continuation_call_uninterrupted_save external platform port critical arch
    abi save kernel_program_inv local sg active call state mask registers before
    final_registers acquired saved_heap frame Hreturn Hvalid Hmask Hpre Hsave)
    as [Hstate [Hr0 [Hsave_run Hmasked]]].
  split; [exact Hstate|]. split; [exact Hsave_run|]. subst acquired.
  destruct (os_sched_modular_prefix_continuation_resources external platform port abi local
    critical sg active call final_registers.(kernel_save_r0) state state saved_heap frame
    Hnonempty Hmasked) as [prefix_heap [Hprefix [_ Hafter_prefix]]].
  unfold os_sched_modular_prefix_execution in Hprefix; rewrite Hnoswitch in Hprefix.
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hrestore_r0 Hrestore_mask Hprefix_run Hsuffix_run.
  destruct (kernel_continuation_call_uninterrupted_restore external platform port critical arch
    abi restore kernel_program_inv local sg active call final_registers.(kernel_save_r0)
    state (os_sched_prefix_state state) cursor prefix_heap written middle final_cursor after frame
    Hrestore_r0 Hrestore_mask Hafter_prefix Hprefix_run Hsuffix_run)
    as [Hrestore_run [Hword Hclosed]].
  rewrite Hr0, Hmask in Hclosed.
  split; assumption.
Qed.

(** The active key is absent before OSCtxSw parks it. Specialising only
    that key therefore changes no currently owned entry. In particular,
    this rule does not discard or recreate arbitrary saved locals. *)
Lemma kernel_saved_continuation_map_focus_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  critical sg source_tasks tasks call saved acquired other stacks,
  stacks (task_stack_key call.(os_sched_call_stack)) = None ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks other) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (kernel_sched_saved_local_at platform critical sg source_tasks call saved acquired other)) stacks.
Proof.
  intros external platform port abi critical sg source_tasks tasks call saved acquired other stacks Hnone.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  assert (Hkey : task_stack_key descriptor.(armv7a_continuation_stack) = key) by tauto.
  assert (Hdifferent : task_stack_key descriptor.(armv7a_continuation_stack) <>
    task_stack_key call.(os_sched_call_stack)).
  { intro Heq; rewrite Hkey in Heq; rewrite Heq, Hnone in Hlookup; discriminate. }
  Exists descriptor; unfold kernel_sched_saved_local_at.
  destruct task_stack_key_eq_dec; [contradiction|entailer!].
Qed.

(** The switching C branch reaches its actual masked prefix endpoint,
    then the already proved OSCtxSw save producer performs its physical
    save and TCB-SP store. The actual Save token/inside pair is moved into
    the new descriptor's local; every old entry keeps its previous local.

    Frame geometry and register observations below are the existing
    physical save interface. They describe this executed save, not all
    future resumes. No ready condition is imposed on the outgoing task:
    a blocking SemPend may have removed it from the ready list. The
    selected destination and a later return remain separate source cuts. *)
Lemma os_sched_modular_switch_capture :
  forall external platform port critical
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg state node call saved acquired other old_sp cpsr registers lr prefix suffix first old_words
    before (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  let local := kernel_sched_saved_local_at platform critical sg checkpoint.(TskState)
    call saved acquired other in
  os_sched_requests_switch state = true ->
  state.(SchedState).(readyList) <> [] ->
  kernel_call_task_source call state ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_continuation_call_masked abi kernel_program_inv other critical sg
    (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state ** frame) before ->
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg before prefix_heap /\
    sched_high_ready_consistency checkpoint.(TskState) checkpoint.(SchedState) /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call descriptor stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
      (UCOS2_inv sg updated **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       kernel_saved_continuation_entry abi updated.(TskState) local
         (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       store_parked_continuations (kernel_saved_continuation_entry abi updated.(TskState) local)
         updated.(TskState).(parkedTaskStacks) **
       armv7a_task_switch_control task_abi call ** (unmap_table_rep sg ** frame)) captured).
Proof.
  intros external platform port critical abi task_abi sg state node call saved acquired other old_sp cpsr
    registers lr prefix suffix first old_words before frame checkpoint fragments descriptor updated local
    Hswitch Hnonempty Hsource Hnode Hid Hgeneration Habsent Hfragments Hlength Hcpsr Hlr Hranges Hmask
    Hsprange Hsp Haddress Hpre.
  destruct (os_sched_modular_prefix_continuation_resources external platform port abi other critical sg
    (Some (task_stack_key call.(os_sched_call_stack))) call saved acquired state before frame
    (fun _ => Hnonempty) Hpre) as [prefix_heap [Hprefix [Hhigh Hmasked]]].
  unfold os_sched_modular_prefix_execution in Hprefix; rewrite Hswitch in Hprefix.
  specialize (Hhigh Hswitch); fold checkpoint in Hhigh, Hmasked.
  assert (Hsource_checkpoint : kernel_call_task_source call checkpoint).
  { apply os_sched_prefix_preserves_task_source; exact Hsource. }
  pose proof (proj1 (kernel_call_task_source_current_at call checkpoint Hsource_checkpoint)) as Hcurrent.
  assert (Hcoverage : task_stack_live_coverage checkpoint.(TskState)
    (Some (task_stack_key call.(os_sched_call_stack)))).
  { match type of Hmasked with ?P prefix_heap => assert (Hobserve : P |--
      coq_prop (task_stack_live_coverage checkpoint.(TskState)
        (Some (task_stack_key call.(os_sched_call_stack)))) && TT) end.
    { unfold kernel_continuation_call_masked, kernel_continuation_inv;
        entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve prefix_heap Hmasked)). }
  assert (Hlocal : interrupt_platform_saved platform
      (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) acquired |-- local descriptor).
  { unfold local; rewrite kernel_sched_saved_local_at_selected by reflexivity.
    exact (kernel_sched_saved_image_local_resources platform critical sg checkpoint call saved acquired
      old_sp cpsr registers lr fragments Hsource_checkpoint Hmask). }
  assert (Hmap : store_parked_continuations
      (kernel_saved_continuation_entry abi checkpoint.(TskState) other)
      checkpoint.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
      checkpoint.(TskState).(parkedTaskStacks)).
  { unfold local; apply kernel_saved_continuation_map_focus_absent; exact Habsent. }
  match type of Hmasked with ?P prefix_heap => assert (Hsave_input : P |--
    kernel_call_execution_owned external platform call 192 ** UCOS2_inv sg checkpoint **
    store_parked_continuations (kernel_saved_continuation_entry abi checkpoint.(TskState) local)
      checkpoint.(TskState).(parkedTaskStacks) ** local descriptor ** (unmap_table_rep sg ** frame)) end.
  { unfold kernel_continuation_call_masked, kernel_continuation_inv, critical_region_masked,
      kernel_call_execution_owned; rewrite kernel_program_inv_split_unmap.
    Intros.
    sep_apply_l_atomic Hmap; sep_apply_l_atomic Hlocal; entailer!. }
  destruct (kernel_task_save_continuation_resources external platform port abi task_abi sg checkpoint node call
    old_sp cpsr registers lr prefix suffix first old_words local (unmap_table_rep sg ** frame) prefix_heap
    Hcurrent Hnode Hid Hgeneration Habsent Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hmask
    Hsprange Hsp Haddress (Hsave_input prefix_heap Hmasked))
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  exists prefix_heap, written, stored.
  exact (conj Hprefix (conj Hhigh (conj Hwrites (conj Hload (conj Hstore (conj Hcovered Hcapture)))))).
Qed.

(** Ordinary return is consumed at the actual selector cut for the saved
    original call. Its current registration is a source-history fact;
    older entries need not remain active. The existing install/TaskRestore
    and final C Restore proofs consume this call's saved local. Once the
    selected key has been taken, all remaining entries use the ORIGINAL
    local policy again, with no reconstruction of any other resource.

    This is a resource endpoint, not a liveness theorem or a premise that
    an arbitrary context switch returns. It is shared by C clients; their
    own pure task-stage or wait-history consequences are kept separately. *)
Lemma os_sched_modular_saved_call_return :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    (restore : Armv7aRestoreResourceABI external platform critical arch)
    sg context outgoing hooked source_tasks original saved acquired other resumed before
    (frame : Assertion),
  let local := kernel_sched_saved_local_at platform critical sg source_tasks original saved acquired other in
  let resource := kernel_saved_continuation_entry abi hooked.(TskState) local in
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  task_invocation_active hooked.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack) resumed ->
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
      returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack) /\
      kernel_call_task_source returned current /\
      (forall cursor written middle final_cursor after,
        cursor.(kernel_restore_r0) = saved ->
        armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
        armv7a_restore_prefix_transition restore cursor restored written middle ->
        armv7a_restore_suffix_transition restore written middle final_cursor after ->
        kernel_call_restore_uninterrupted_execution arch cursor restored final_cursor after /\
        final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
        after.(ConAssertion.s_mem) = restored.(ConAssertion.s_mem) /\
        (kernel_continuation_call_closed abi kernel_program_inv other sg
           (Some (task_stack_key original.(os_sched_call_stack))) returned
           (armv7a_irq_fiq_mask saved) current ** frame) after)).
Proof.
  intros external platform port critical arch abi task_abi restore sg context outgoing hooked source_tasks
    original saved acquired other resumed before frame local resource current
    Hactive Hsaved Hdestination Haddress Hcoverage Hpre.
  set (current_local := kernel_sched_saved_local_at platform critical sg hooked.(TskState)
    original saved acquired other).
  set (current_resource := kernel_saved_continuation_entry abi hooked.(TskState) current_local).
  assert (Hentry : forall key payload, resource key payload |-- current_resource key payload).
  { intros key payload; unfold resource, current_resource, kernel_saved_continuation_entry.
    Intros descriptor; Exists descriptor.
    unfold local, current_local, kernel_sched_saved_local_at.
    destruct task_stack_key_eq_dec; [unfold kernel_sched_saved_local; entailer!|entailer!]. }
  assert (Hmap : store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) |--
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks)).
  { unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
    intros key payload Hlookup; apply Hentry. }
  match type of Hpre with ?P before => assert (Hconvert : P |--
    UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
    current_resource (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
    store_parked_continuations current_resource hooked.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) end.
  { sep_apply_l_atomic (Hentry (task_stack_key context.(os_sched_call_stack))
      (context.(os_sched_call_stack).(stackLeaseRegion), outgoing)).
    sep_apply_l_atomic Hmap; entailer!. }
  destruct (kernel_saved_sched_continuation_return_source external platform port abi critical arch
    task_abi restore sg context outgoing hooked original saved acquired other resumed before frame
    Hsaved Hdestination Haddress Hcoverage (Hconvert before Hpre))
    as [installed [selected [Hinstall [Hreads [Hlease Hrestore]]]]].
  fold current current_local in Hrestore.
  assert (Hcovered : task_stack_live_coverage current.(TskState)
    (Some (task_stack_key original.(os_sched_call_stack)))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      original.(os_sched_call_stack)
      (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  assert (Habsent : current.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None) by apply task_stack_take_lookup.
  assert (Hunfocus : store_parked_continuations
      (kernel_saved_continuation_entry abi current.(TskState) current_local)
      current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) other)
      current.(TskState).(parkedTaskStacks)).
  { unfold current_local; apply kernel_saved_continuation_map_unfocus_absent; exact Habsent. }
  exists installed, selected; split; [exact Hinstall|]. split; [exact Hreads|]. split; [exact Hlease|].
  intros restored Htask_restore returned.
  destruct (Hrestore restored Htask_restore) as [Hcall [Hsource Htail]].
  fold returned in Hsource, Htail.
  assert (Hsame : returned.(os_sched_call_invocation) = original.(os_sched_call_invocation) /\
      returned.(os_sched_call_origin) = original.(os_sched_call_origin) /\
      returned.(os_sched_call_stack) = original.(os_sched_call_stack)).
  { unfold returned, kernel_selected_call; rewrite Hcall.
    unfold armv7a_continuation_resumed_call; cbn; auto. }
  split; [exact Hcall|]. destruct Hsame as [Hi [Ho Hs]].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|]. split; [exact Hsource|].
  intros cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix.
  destruct (Htail cursor written middle final_cursor after Hr0 Hmask Hprefix Hsuffix)
    as [Hrun [Hlr [Hmemory Howned]]].
  split; [exact Hrun|]. split; [exact Hlr|]. split; [exact Hmemory|].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic Hunfocus.
    unfold kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
  exact (Hclose after Howned).
Qed.
