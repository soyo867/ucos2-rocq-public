Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** One actual Scheduler save, with its own local Restore resources.
    The descriptor is the image written by OSCtxSw: PC and LR are its
    real return LR, and the saved CPSR remains masked. Stack bytes stay
    in the existing physical stack owner; no second stack is allocated.
    This predicate must be produced before the ordinary non-focused
    entry hides the descriptor identity. *)
Definition kernel_saved_sched_call {external platform port}
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor : Assertion :=
  coq_prop (descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
    call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
      call.(os_sched_call_stack).(stackLeaseGeneration)) &&
  (armv7a_dormant_continuation abi descriptor **
   interrupt_platform_saved platform (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
   critical_region_inside critical sg call.(os_sched_call_invocation) acquired).

(** A local exact-entry view of the existing map. The distinguished
    outgoing descriptor owns its Save/inside pair; all other entries,
    including an earlier pending caller, keep the existing focused view.
    Generic map park/take transports this predicate without forgetting
    the association. This is a proof-side resource view, not a new global
    state field, authority, or assumption on a public function. *)
Definition kernel_saved_sched_call_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor
  tasks focus key payload : Assertion :=
  if task_stack_key_eq_dec key (task_stack_key call.(os_sched_call_stack)) then
    coq_prop (armv7a_continuation_binding descriptor /\
      task_stack_key descriptor.(armv7a_continuation_stack) = key /\
      (descriptor.(armv7a_continuation_stack).(stackLeaseRegion),
        descriptor.(armv7a_continuation_fragments)) = payload /\
      armv7a_task_frame_slice descriptor /\
      task_stack_live_sp tasks key descriptor.(armv7a_continuation_sp) /\
      task_invocation_active tasks call.(os_sched_call_invocation) call.(os_sched_call_origin)) &&
    kernel_saved_sched_call abi critical sg call saved acquired descriptor
  else armv7a_task_call_stack_entry abi tasks focus key payload.

Lemma kernel_saved_sched_call_map_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor tasks focus stacks,
  stacks (task_stack_key call.(os_sched_call_stack)) = None ->
  armv7a_task_call_stacks abi tasks focus stacks |--
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus) stacks.
Proof.
  intros external platform port abi critical sg call saved acquired descriptor tasks focus stacks Hnone.
  unfold armv7a_task_call_stacks, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros key payload Hlookup.
  unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec as [Heq|Hne].
  - subst key; rewrite Hnone in Hlookup; discriminate.
  - reflexivity.
Qed.

(** The token is generated by the real OS_CPU_SR_Save suffix, then
    carried through the C selector, sixteen stack writes, TCB-SP write,
    and capture. The older pending owner remains in [focus]/[frame].
    None of the output resources is an input premise. *)
Lemma kernel_sched_save_capture_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (save : Armv7aSaveSuffixABI external platform critical arch)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg state call node mask focus old_sp cpsr values lr prefix suffix first old_words publication
  registers final_registers acquired before saved_heap (frame : Assertion),
  let checkpoint := os_sched_prefix_state state in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let descriptor := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp checkpoint call.(os_sched_call_stack).(stackLeaseSlot)
    descriptor.(armv7a_continuation_sp) in
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  os_sched_source_live_save_input sg checkpoint node call old_sp cpsr values lr
    prefix suffix first old_words focus publication ->
  task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  kernel_call_task_source call state ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_call_execution_owned external platform call mask ** kernel_program_inv sg state **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired saved_heap /\
  acquired = state /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call descriptor stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call descriptor.(armv7a_continuation_sp) fragments /\
      (UCOS2_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state descriptor
         updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
         (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       store_parked_continuations
         (kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state descriptor
           updated.(TskState) focus) updated.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi call ** unmap_table_rep sg ** frame)) captured).
Proof.
  intros external platform port abi critical arch save task_abi sg state call node mask focus old_sp cpsr values lr
    prefix suffix first old_words publication registers final_registers acquired before saved_heap frame
    checkpoint fragments descriptor updated Hswitch Hnonempty Hinput Hcovered Hcall_source Hreturn Hvalid_sr Hmask Hpre Hsave.
  destruct Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hready [Hfocus [Hfragments
    [Hregion [Hgeometry [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges [Hcpsr_mask [Hsp32 [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  assert (Hobserved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid_sr|reflexivity]).
  match type of Hpre with ?P before => assert (Horder : P |--
    kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_program_inv sg state **
     armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame)) end.
  { change (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) with
      (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)); rewrite Hmask; entailer!. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch save sg call
    (kernel_save_read_cpsr registers) state before final_registers acquired saved_heap _ Hobserved
    (Horder before Hpre) Hsave) as [Hacquired [Hmemory [Hpc [Hr0 Hmasked]]]].
  split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hacquired|]. subst acquired.
    set (retained := interrupt_platform_saved platform
      (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) state ** frame).
    match type of Hmasked with ?P saved_heap => assert (Hprefix_input : P |--
      os_sched_source_switch_pre external platform port abi sg call focus state ** unmap_table_rep sg ** retained) end.
    { unfold os_sched_source_switch_pre, critical_region_masked, kernel_call_execution_owned, retained.
      rewrite kernel_program_inv_split_unmap; entailer!. }
    destruct (os_sched_source_switch_prefix_resources external platform port abi sg state call focus retained saved_heap
      Hswitch Hnonempty (Hprefix_input saved_heap Hmasked)) as [prefix_heap [Hprefix [Hprefix_high Hprefix_owned]]].
    fold checkpoint in Hprefix_owned.
    match type of Hprefix_owned with ?P prefix_heap => assert (Hwrite_input : P |--
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) call.(os_sched_call_fragments) **
      UCOS2_inv sg checkpoint **
      armv7a_task_call_stacks abi checkpoint.(TskState) focus checkpoint.(TskState).(parkedTaskStacks) **
      (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** unmap_table_rep sg ** retained)) end.
    { unfold os_sched_source_switch_pre, kernel_call_execution_owned, os_sched_context_resources; entailer!. }
    destruct (armv7a_task_save_global_resources external platform port abi sg checkpoint node call old_sp cpsr values lr
      prefix suffix first old_words focus _ prefix_heap Hcurrent Hnode Hid Hgen Hnone Hcovered Hfragments Hlength
      Hcpsr Hlr Hranges Hsp32 Hsp (Haddress _) (Hwrite_input prefix_heap Hprefix_owned))
      as [written [stored [Hwrites [Hload [Hstore [Hbinding [Hslice [Hlive [Hcoverage [Hreads Hstored]]]]]]]]]].
    fold fragments descriptor updated in Hstore, Hbinding, Hslice, Hlive, Hcoverage, Hreads, Hstored.
    exists prefix_heap, written, stored; split; [exact Hprefix|]. split; [exact Hwrites|].
    split; [exact Hload|]. split; [exact Hstore|]. split; [exact Hcoverage|].
    intros captured Hcapture.
    match type of Hstored with ?P stored => assert (Hcapture_input : P |--
      interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
      external.(os_sched_arch_running) call **
      (UCOS2_inv sg updated **
       armv7a_task_call_stacks abi updated.(TskState) focus updated.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
         descriptor.(armv7a_continuation_fragments) ** unmap_table_rep sg ** retained)) end.
    { entailer!. }
    assert (Hdescriptor_mask : armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192).
    { unfold descriptor, armv7a_task_save_image; cbn [armv7a_continuation_cpsr].
      rewrite armv7a_task_saved_cpsr_mask; exact Hcpsr_mask. }
    destruct (armv7a_task_capture_resources _ _ _ abi task_abi call descriptor _ stored captured
      eq_refl Hreads Hdescriptor_mask (Hcapture_input stored Hstored) Hcapture)
      as [Hcaptured_memory [Hsource Hcaptured]].
    split; [exact Hcaptured_memory|]. split; [exact Hsource|].
    assert (Habsent_updated : updated.(TskState).(parkedTaskStacks)
      (task_stack_key call.(os_sched_call_stack)) = None).
    { unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Hnone. }
    assert (Hactive_updated : task_invocation_active updated.(TskState)
      call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    { unfold updated, os_sched_save_current_sp; rewrite Hnode.
      apply glob_task_set_usedtask_preserves_invocation_active with (old := node).
      - exact Hnode.
      - reflexivity.
      - exact (proj1 (proj2 Hcall_source)). }
    pose proof (proj1 Hcall_source) as Horigin.
    assert (Hsaved_entry : armv7a_dormant_continuation abi descriptor **
      interrupt_platform_saved platform
        (save_token final_registers.(kernel_save_r0) call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) state |--
      kernel_saved_sched_call_entry abi critical sg call final_registers.(kernel_save_r0) state descriptor
        updated.(TskState) focus (task_stack_key call.(os_sched_call_stack))
        (call.(os_sched_call_stack).(stackLeaseRegion), fragments)).
    { unfold kernel_saved_sched_call_entry.
      destruct task_stack_key_eq_dec; [|contradiction].
      unfold kernel_saved_sched_call; entailer!; try assumption; reflexivity. }
    match type of Hcaptured with ?P captured => match goal with |- ?Q captured => assert (Hclose : P |-- Q) end end.
    { sep_apply_l_atomic (kernel_saved_sched_call_map_absent external platform port abi critical sg call
        final_registers.(kernel_save_r0) state descriptor updated.(TskState) focus
        updated.(TskState).(parkedTaskStacks) Habsent_updated).
      sep_apply_r_atomic Hsaved_entry; unfold retained; entailer!. }
    exact (Hclose captured Hcaptured).
Qed.

Lemma kernel_saved_sched_call_map_without_saved : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor tasks focus stacks,
  stacks (task_stack_key call.(os_sched_call_stack)) = None ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus) stacks |--
  armv7a_task_call_stacks abi tasks focus stacks.
Proof.
  intros external platform port abi critical sg call saved acquired descriptor tasks focus stacks Hnone.
  unfold armv7a_task_call_stacks, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros key payload Hlookup.
  unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec as [Heq|Hne].
  - subst key; rewrite Hnone in Hlookup; discriminate.
  - reflexivity.
Qed.

(** The outgoing exact entry is parked while a DIFFERENT already pending
    entry is taken. Its token and descriptor remain together in the same
    resource map. The selected entry retains the older focus; no map or
    dormant capability is duplicated. Physical installation uses exactly
    this generic park/take rule through the existing resource parameter. *)
Lemma kernel_saved_sched_call_park_take_other : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor
  tasks focus stacks fragments incoming resumed,
  stacks (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_key incoming <> task_stack_key call.(os_sched_call_stack) ->
  stacks (task_stack_key incoming) = Some (incoming.(stackLeaseRegion), resumed) ->
  kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus
    (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
  armv7a_task_call_stacks abi tasks focus stacks |--
  armv7a_task_call_stack_entry abi tasks focus (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus)
    (task_stack_take (task_stack_park_fragments stacks call.(os_sched_call_stack) fragments) incoming).
Proof.
  intros external platform port abi critical sg call saved acquired descriptor tasks focus stacks fragments
    incoming resumed Hnone Hother Hlookup.
  sep_apply_l_atomic (kernel_saved_sched_call_map_absent external platform port abi critical sg call saved acquired
    descriptor tasks focus stacks Hnone).
  sep_apply_l_atomic (store_parked_continuations_switch
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus)
    stacks call.(os_sched_call_stack) incoming fragments resumed Hnone
    ltac:(rewrite task_stack_park_fragments_lookup_other; assumption)).
  unfold kernel_saved_sched_call_entry at 1; destruct task_stack_key_eq_dec; [contradiction|reflexivity].
Qed.

(** Taking that exact entry later recovers its original invocation and
    own Restore resources. This theorem proves only ownership transfer;
    a real wake/selector producer must establish that it is selected. *)
Lemma kernel_saved_sched_call_take_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor
  tasks focus stacks fragments,
  stacks (task_stack_key call.(os_sched_call_stack)) = Some (call.(os_sched_call_stack).(stackLeaseRegion), fragments) ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus) stacks |--
  kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus
    (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
  armv7a_task_call_stacks abi tasks focus (task_stack_take stacks call.(os_sched_call_stack)).
Proof.
  intros external platform port abi critical sg call saved acquired descriptor tasks focus stacks fragments Hlookup.
  sep_apply_l_atomic (store_parked_continuations_take
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus)
    stacks call.(os_sched_call_stack) fragments Hlookup).
  sep_apply_l_atomic (kernel_saved_sched_call_map_without_saved external platform port abi critical sg call saved
    acquired descriptor tasks focus (task_stack_take stacks call.(os_sched_call_stack))
    (task_stack_take_lookup stacks call.(os_sched_call_stack))).
  entailer!.
Qed.

(** Consume the exact dormant descriptor while retaining its OWN saved
    mask and critical-region resources. The actual task restore resumes
    the OSCtxSw return PC, which equals the LR saved by OSCtxSw. This is
    a masked C continuation, BEFORE the later OS_CPU_SR_Restore call.
    That later call has its own BL/LR source binding; its LR cannot be
    equated with this descriptor's LR. No Scheduler/API return is claimed.
    Every kernel/map/private owner stays in [frame] on the same heap. *)
Lemma kernel_saved_sched_call_resume_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg call saved acquired descriptor outgoing before resumed (frame : Assertion),
  armv7a_continuation_restore_reads descriptor before ->
  (armv7a_task_switch_control task_abi outgoing **
   task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
     descriptor.(armv7a_continuation_fragments) **
   kernel_saved_sched_call abi critical sg call saved acquired descriptor ** frame) before ->
  armv7a_task_restore_transition task_abi outgoing descriptor before resumed ->
  external.(os_sched_arch_resume_source) call (armv7a_continuation_resumed_call descriptor call) /\
  descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
  armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
  resumed.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved acquired **
   os_sched_context_resources external (armv7a_continuation_resumed_call descriptor call) ** frame) resumed.
Proof.
  intros external platform port abi critical task_abi sg call saved acquired descriptor outgoing
    before resumed frame Hreads Hpre Htask_restore.
  assert (Hcall : descriptor.(armv7a_continuation_call) = Some call /\
      descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
      armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192).
  { match type of Hpre with ?P before => assert (Hobserve : P |-- coq_prop
      (descriptor.(armv7a_continuation_call) = Some call /\
       descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
       armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192) && TT) end.
    { unfold kernel_saved_sched_call; entailer!; try tauto; intros ? ?; exact I. }
    exact (proj1 (Hobserve before Hpre)). }
  destruct Hcall as [Hcall [Hpc Hmask]].
  match type of Hpre with ?P before => assert (Hinput : P |--
    armv7a_task_switch_control task_abi outgoing **
    task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion)
      descriptor.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi descriptor **
    (interrupt_platform_saved platform (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) acquired ** frame)) end.
  { unfold kernel_saved_sched_call, armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  destruct (armv7a_task_restore_resources _ _ _ abi task_abi outgoing descriptor _ before resumed
    Hreads (Hinput before Hpre) Htask_restore) as [Hresume_memory [Hsource Hresumed]].
  unfold armv7a_task_restored_source in Hsource; rewrite Hcall in Hsource.
  match type of Hresumed with ?P resumed => assert (Hlocal : P |--
    critical_region_masked platform critical sg call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
    os_sched_context_resources external (armv7a_continuation_resumed_call descriptor call) ** frame) end.
  { unfold armv7a_task_restored_execution; rewrite Hcall, Hmask.
    unfold kernel_call_execution_owned, critical_region_masked, armv7a_continuation_resumed_call;
      cbn [os_sched_call_invocation os_sched_call_origin]; entailer!. }
  exact (conj Hsource (conj Hpc (conj Hmask (conj Hresume_memory (Hlocal resumed Hresumed))))).
Qed.

(** At an actual later selector cut, consume the registered exact entry.
    [destination] is the CURRENT source selector binding, not an eventual
    readiness promise. A previously blocked task still needs a real wake
    producer before this cut can be reached. Generic physical install
    parks the outgoing entry and takes the saved entry; taking this key
    leaves precisely the old focused map. Registration comes from the
    saved source entry, while current-task identity comes from the actual
    OSTCBCur installation. Both are needed for the Some normalization.
    The final task restore recovers a masked C continuation. The later
    C call/BL into OS_CPU_SR_Restore remains a separate source boundary;
    neither local OS_Sched nor an enclosing API is declared returned. *)
Lemma kernel_saved_sched_call_install_resume_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg context outgoing hooked call saved acquired descriptor resumed focus before (frame : Assertion),
  let resource := kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor hooked.(TskState) focus in
  let current := os_sched_install_context context outgoing call.(os_sched_call_stack) hooked in
  let returned := kernel_selected_call descriptor current in
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked call.(os_sched_call_stack) resumed ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   resource (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   store_parked_continuations resource hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) before ->
  exists installed,
    sched_install_heap_fragment sg before installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      descriptor.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads descriptor installed /\
    descriptor.(armv7a_continuation_call) = Some call /\
    kernel_call_task_source returned current /\
    (forall restored,
      armv7a_task_restore_transition task_abi context descriptor installed restored ->
      external.(os_sched_arch_resume_source) call returned /\
      descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
      armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
         returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
       kernel_program_inv sg current **
       armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi critical task_abi sg context outgoing hooked call saved acquired
    descriptor resumed focus before frame resource current returned Hsaved Hdestination Haddress Hbefore.
  destruct (os_sched_install_continuation_map_resources external sg context outgoing hooked call.(os_sched_call_stack)
    resumed resource _ before Hsaved Hdestination Haddress Hbefore)
    as [installed [sp [Hrun [[Hcurrent Harch] Hinstalled]]]].
  fold current in Hcurrent, Hinstalled.
  assert (Hexpose : UCOS2_inv sg current **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) resumed **
      resource (task_stack_key call.(os_sched_call_stack)) (call.(os_sched_call_stack).(stackLeaseRegion), resumed) **
      store_parked_continuations resource current.(TskState).(parkedTaskStacks) **
      (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame) |--
    coq_prop (armv7a_continuation_binding descriptor /\ armv7a_task_frame_slice descriptor /\
      task_stack_live_sp hooked.(TskState) (task_stack_key call.(os_sched_call_stack)) descriptor.(armv7a_continuation_sp) /\
      descriptor.(armv7a_continuation_call) = Some call /\
      descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack) /\
      descriptor.(armv7a_continuation_fragments) = resumed /\
      call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
        call.(os_sched_call_stack).(stackLeaseGeneration) /\
      task_invocation_active hooked.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin)) &&
    (UCOS2_inv sg current **
     task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion) descriptor.(armv7a_continuation_fragments) **
     kernel_saved_sched_call abi critical sg call saved acquired descriptor **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
     (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame))).
  { unfold resource at 1; unfold kernel_saved_sched_call_entry at 1.
    destruct task_stack_key_eq_dec as [Heq|Hne]; [|contradiction].
    unfold kernel_saved_sched_call at 1; Intros.
    assert (Hbound : armv7a_continuation_binding descriptor) by tauto.
    assert (Hsome : descriptor.(armv7a_continuation_call) = Some call) by tauto.
    assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
    { pose proof (proj2 Hbound) as Hstack; rewrite Hsome in Hstack; symmetry; exact Hstack. }
    assert (Hpayload : (descriptor.(armv7a_continuation_stack).(stackLeaseRegion),
      descriptor.(armv7a_continuation_fragments)) = (call.(os_sched_call_stack).(stackLeaseRegion), resumed)) by tauto.
    assert (Hfragments : descriptor.(armv7a_continuation_fragments) = resumed)
      by exact (f_equal snd Hpayload).
    assert (Habsent : current.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None).
    { unfold current, os_sched_install_context; apply task_stack_take_lookup. }
    unfold resource.
    sep_apply_l_atomic (kernel_saved_sched_call_map_without_saved external platform port abi critical sg call saved
      acquired descriptor hooked.(TskState) focus current.(TskState).(parkedTaskStacks) Habsent).
    change (armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks)) with
      (armv7a_task_call_stacks abi hooked.(TskState) focus current.(TskState).(parkedTaskStacks)).
    unfold kernel_saved_sched_call; rewrite Hlease, Hfragments; entailer!; tauto. }
  destruct (Hexpose installed Hinstalled) as
    [[Hbinding [Hslice [Hlive [Hsome [Hlease [Hfragments [Horigin Hactive]]]]]]] Howned].
  destruct Hdestination as [Hhigh [[node [Hnode [Hgen [Hprio Hrestore_source]]]] Hrest]].
  assert (Hnode_sp : node.(tcbStkPtr) = descriptor.(armv7a_continuation_sp)) by (apply Hlive; assumption).
  assert (Hload : pointer_load (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) node.(tcbStkPtr) installed).
  { eapply task_stack_framed_live_sp_load with (state := current); [exact Hnode|exact Haddress|].
    match type of Howned with ?P installed => assert (Horder : P |-- UCOS2_inv sg current **
      (task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion) descriptor.(armv7a_continuation_fragments) **
       kernel_saved_sched_call abi critical sg call saved acquired descriptor **
       armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hsp : sp = descriptor.(armv7a_continuation_sp)).
  { rewrite <- Hnode_sp; eapply pointer_load_deterministic; [exact (proj2 Hrun)|exact Hload]. }
  rewrite Hsp in Hrun.
  assert (Hreads : armv7a_continuation_restore_reads descriptor installed).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Howned with ?P installed => assert (Horder : P |--
      task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion) descriptor.(armv7a_continuation_fragments) **
      (UCOS2_inv sg current ** kernel_saved_sched_call abi critical sg call saved acquired descriptor **
       armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
       (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame))) by entailer! end.
    exact (Horder installed Howned). }
  assert (Hreturned : returned = armv7a_continuation_resumed_call descriptor call).
  { unfold returned, kernel_selected_call; rewrite Hsome; reflexivity. }
  assert (Hsource : kernel_call_task_source returned current).
  { rewrite Hreturned; unfold kernel_call_task_source, armv7a_continuation_resumed_call;
      cbn [os_sched_call_origin os_sched_call_stack os_sched_call_invocation]; rewrite Hlease.
    split; [exact Horigin|]. split; [exact Hactive|].
    unfold task_execution_current; rewrite Horigin; exact (proj1 Hcurrent). }
  exists installed; split; [exact Hrun|]. split; [exact Hreads|]. split; [exact Hsome|]. split; [exact Hsource|].
  intros restored Htask_restore.
  match type of Howned with ?P installed => assert (Hrestore_input : P |--
    armv7a_task_switch_control task_abi context **
    task_stack_fragments_rep descriptor.(armv7a_continuation_stack).(stackLeaseRegion) descriptor.(armv7a_continuation_fragments) **
    kernel_saved_sched_call abi critical sg call saved acquired descriptor **
    (kernel_program_inv sg current **
     armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) ** frame)) end.
  { rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (kernel_saved_sched_call_resume_resources external platform port abi critical task_abi sg call saved
    acquired descriptor context installed restored _ Hreads
    (Hrestore_input installed Howned) Htask_restore)
    as [Hresume [Hpc [Hmask [Hmemory Hafter]]]].
  rewrite Hreturned; split; [exact Hresume|]. split; [exact Hpc|].
  split; [exact Hmask|]. split; [exact Hmemory|].
  cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin].
  match type of Hafter with ?P restored => match goal with |- ?Q restored => assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose restored Hafter).
Qed.
