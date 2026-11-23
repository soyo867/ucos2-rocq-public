Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_tcb_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_pending_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The active creator's next Save and switch retain a DIFFERENT pending
    invocation's focus. Its key differs from the active key because the
    former is present and the latter absent in the same map; no extra
    public exclusion is imposed. Actual stack stores, TCB-SP update,
    capture, configured hook, destination selection and restore reuse the
    general source producer. A selected foreign task keeps the pending
    entry; selecting the focused task transfers its descriptor to the
    restored execution. Neither case is silently called a return of the
    active creator. The saved interrupt token remains its separate frame. *)
Lemma task_create_pending_sched_switch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg call mask state focus payload registers before final_registers acquired saved_heap
    old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  task_create_call_stage call state -> state.(SchedState).(isRunning) = true ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  os_sched_requests_switch state = true ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    call.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened state.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks environment.(task_stack_call_continuations)
     state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  let abi := environment.(task_stack_call_continuations) in
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    suspended.(armv7a_continuation_sp) in
  let retained := unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state ** frame) in
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      suspended.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi call suspended stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
      exists incoming resumed installed selected current,
        os_sched_destination_binding environment.(task_stack_call_external) call fragments updated incoming resumed /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
        (task_stack_key incoming <> armv7a_call_focus_key focus ->
          (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
            (armv7a_call_focus_key focus) = Some payload) /\
        (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
          os_sched_source_switch_execution environment.(task_stack_call_external)
            environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg
            checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
          armv7a_task_restored_source environment.(task_stack_call_external) selected /\
          (os_sched_source_selected_post environment.(task_stack_call_external)
            environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
            sg focus incoming selected current (os_sched_install_context call fragments incoming updated) **
           retained) restored)).
Proof.
  intros environment critical arch save task_abi initial sg call mask state focus payload registers before
    final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame
    Hstage Hrunning Hcoverage Hfocus Hswitch Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range
    Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave
    abi checkpoint fragments suspended updated retained.
  assert (Hvalid : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { rewrite kernel_program_inv_split_unmap; unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hpre)). }
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid_sr|reflexivity]).
  match type of Hpre with ?P before => assert (Hsave_input : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_program_inv sg state ** armv7a_task_call_stacks abi
      state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)) end.
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired saved_heap _ Hsaved
    (Hsave_input before Hpre) Hsave) as [Hstate [Hmemory [Hlr_return [Hr0 Hmasked]]]].
  split.
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave). }
  split; [exact Hstate|].
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)) as Henabled.
  destruct (task_create_call_stage_selection_ready call state Hstage Hrunning Henabled)
    as [Horigin [Habsent [node [Hready Hgeneration]]]].
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hin Heffective]]]].
  assert (Hdifferent : task_stack_key call.(os_sched_call_stack) <> armv7a_call_focus_key focus)
    by (intro Heq; rewrite Heq in Habsent; congruence).
  assert (Hnonempty : state.(SchedState).(readyList) <> [])
    by (intro Hnil; rewrite Hnil in Hin; contradiction).
  match type of Hmasked with ?P saved_heap => assert (Hprefix_input : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg call focus state ** unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
       (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) state ** frame)) end.
  { unfold os_sched_source_switch_pre, kernel_call_execution_owned, critical_region_masked.
    rewrite kernel_program_inv_split_unmap.
    unfold task_stack_call_active_key in Hcoverage; rewrite Horigin in Hcoverage; entailer!. }
  destruct (os_sched_source_switch_prefix_resources _ _ _ abi sg state call focus _ saved_heap
    Hswitch Hnonempty (Hprefix_input saved_heap Hmasked)) as [prefix_heap [Hprefix [Hhigh Hprefix_owned]]].
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid)))) as Hactive.
    destruct Hactive as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
    eapply task_create_active_links_node_id; [exact Hlinks| |exact Hnode].
    apply Hdomain; eauto. }
  assert (Hcheckpoint_current : checkpoint.(SchedState).(curTaskID) =
    Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch;
      exact Hcurrent. }
  assert (Hcheckpoint_nonempty : checkpoint.(SchedState).(readyList) <> []).
  { unfold checkpoint, os_sched_prefix_state, os_sched_ready_checkpoint; rewrite Henabled, Hswitch;
      exact Hnonempty. }
  assert (Hinput : os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input.
    repeat first [assumption | reflexivity | split | intro | contradiction]. }
  match type of Hprefix_owned with ?P prefix_heap => assert (Horder : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg call focus checkpoint ** retained)
    by (unfold retained; entailer!) end.
  destruct (os_sched_source_live_switch_destination_resources _ _ _ abi task_abi initial sg checkpoint
    node call old_sp cpsr values lr prefix suffix first old_words focus publication retained prefix_heap
    Hinput (Horder prefix_heap Hprefix_owned))
    as [written [stored [Hwrites [Hload [Hstore Hselected]]]]].
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current [Hsource [Hdestination [Hselected_fragments
      [Hinstall [Hreads [Hpending Hrestore]]]]]]]]]]].
  exists incoming, resumed, installed, selected, current.
  split; [exact Hdestination|]. split; [exact Hselected_fragments|]. split; [exact Hinstall|].
  split; [exact Hreads|]. split; [|exact Hrestore].
  intros Hforeign; apply Hpending; [|exact Hforeign].
  unfold updated, os_sched_save_current_sp.
  change (checkpoint.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node)
    in Hnode.
  rewrite Hnode; exact Hfocus.
Qed.

(** Consume the real publication producer, then its returning Restore and
    the creator's next Save/switch. This is the switched counterpart of
    task_create_publication_pending_nonswitch_return. The live caller's
    ready facts and the pending descriptor are produced at publication;
    only the actual stack/register cut and platform transitions are supplied
    at their execution points. A foreign selected task is a new execution
    owner, not a fabricated completion of either pending invocation. *)
Lemma task_create_publication_pending_switch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (restore : Armv7aRestoreResourceABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
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
      (forall registers final_registers sched_acquired saved_heap
        old_sp cpsr values lr prefix suffix first old_words caller_publication,
        published.(SchedState).(isRunning) = true -> os_sched_requests_switch published = true ->
        registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
        armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask saved ->
        call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
        valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
        task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
          call.(os_sched_call_fragments) ->
        task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
        task_publication_happened published.(TskState) caller_publication
          call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
        List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
        Forall (fun value => 0 <= value < 4294967296) values ->
        armv7a_irq_fiq_mask cpsr = 192 -> 0 <= old_sp - 64 < 4294967296 ->
        old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
        (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
        armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) published returned_heap
          final_registers sched_acquired saved_heap ->
        let abi := environment.(task_stack_call_continuations) in
        let checkpoint := os_sched_prefix_state published in
        let fragments := prefix ++ [(first, first + 16,
          map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
        let suspended := armv7a_task_save_image call old_sp cpsr values lr fragments in
        let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
          suspended.(armv7a_continuation_sp) in
        let retained := unmap_table_rep sg **
          (interrupt_platform_saved environment.(task_stack_call_platform)
             (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
           critical_region_inside critical sg call.(os_sched_call_invocation) published ** frame) in
        kernel_call_save_uninterrupted_execution arch registers published returned_heap
          final_registers sched_acquired saved_heap /\ sched_acquired = published /\
        exists prefix_heap written stored,
          os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
          kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
          pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
          kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
            suspended.(armv7a_continuation_sp)) written stored /\
          (forall captured hooked,
            armv7a_task_capture_transition task_abi call suspended stored captured ->
            kernel_heap_execution [] captured hooked ->
            kernel_client_step environment.(task_stack_call_external).(os_sched_hook_action) sg updated updated ->
            exists incoming resumed installed selected current,
              os_sched_destination_binding environment.(task_stack_call_external) call fragments updated incoming resumed /\
              selected.(armv7a_continuation_fragments) = resumed /\
              sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
                selected.(armv7a_continuation_sp) /\
              armv7a_continuation_restore_reads selected installed /\
              (task_stack_key incoming <> armv7a_call_focus_key focus ->
                (os_sched_install_context call fragments incoming updated).(TskState).(parkedTaskStacks)
                  (armv7a_call_focus_key focus) = Some payload) /\
              (forall restored, armv7a_task_restore_transition task_abi call selected installed restored ->
                os_sched_source_switch_execution environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi task_abi sg
                  checkpoint call old_sp cpsr values lr suspended incoming selected prefix_heap restored /\
                armv7a_task_restored_source environment.(task_stack_call_external) selected /\
                (os_sched_source_selected_post environment.(task_stack_call_external)
                  environment.(task_stack_call_platform) environment.(task_stack_call_port) abi
                  sg focus incoming selected current (os_sched_install_context call fragments incoming updated) **
                 retained) restored)))).
Proof.
  intros environment critical arch save restore task_abi initial sg publication state call focus payload
    saved acquired before frame args published Hvalid Hinput Hstage Hcoverage Hfocus Hpriority Hpointer Hpre.
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
  intros registers final_registers sched_acquired saved_heap old_sp cpsr values lr prefix suffix first
    old_words caller_publication Hrunning Hswitch Hreturn Hcpsr Hsaved_mask Hfragments Hregion Hgeometry
    Hsp_range Hpublication Hlength Hcpsr_range Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hsave.
  exact (task_create_pending_sched_switch_source environment critical arch save task_abi initial sg call
    (armv7a_irq_fiq_mask saved) published focus payload registers returned_heap final_registers sched_acquired
    saved_heap old_sp cpsr values lr prefix suffix first old_words caller_publication frame Hstage_published
    Hrunning Hcovered Hretained Hswitch Hreturn Hcpsr Hsaved_mask Hfragments Hregion Hgeometry Hsp_range
    Hpublication Hlength Hcpsr_range Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hreturned Hsave).
Qed.
