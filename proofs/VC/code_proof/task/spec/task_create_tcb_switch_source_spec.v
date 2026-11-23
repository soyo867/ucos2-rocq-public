Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_stack_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** TCBInit's source return supplies the current owned world. The next
    actual MRS/CPSID/DSB/BX retains that exact state and exposes it instead
    of hiding it in the historical weak Save postcondition. This local
    suffix makes no claim about an IRQ between its MRS and CPSID. *)
Lemma task_create_tcb_return_sched_masked_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    sg original returned mask state registers before
    final_registers acquired after (frame : Assertion),
  task_tcb_init_stack_same_call returned original ->
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    sg (task_stack_call_active_key returned) returned mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  task_tcb_init_stack_same_call returned original /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
    critical sg (task_stack_call_active_key returned) returned final_registers.(kernel_save_r0)
    acquired acquired ** frame) after.
Proof.
  intros environment critical arch save sg original returned mask state registers before
    final_registers acquired after frame Hsame Hreturn Hvalid Hmask Hpre Hsave.
  assert (Hobserved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hvalid|reflexivity]).
  assert (Hinput : (kernel_stack_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    sg (task_stack_call_active_key returned) returned
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) state ** frame) before).
  { cbn [kernel_save_read_cpsr kernel_save_cpsr]; rewrite Hmask; exact Hpre. }
  match type of Hinput with ?P before => assert (Hopen : P |--
    kernel_call_execution_owned environment.(task_stack_call_external)
      environment.(task_stack_call_platform) returned
      (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr)) **
    (kernel_stack_inv environment.(task_stack_call_continuations) kernel_program_inv sg
      (task_stack_call_active_key returned) state ** frame))
    by (unfold kernel_stack_call_closed; entailer!) end.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg returned
    (kernel_save_read_cpsr registers) state before final_registers acquired after _
    Hobserved (Hopen before Hinput) Hsave) as [Hstate [Hmemory [Hlr [Hr0 Hpost]]]].
  assert (Hmasked : (kernel_stack_call_masked environment.(task_stack_call_continuations)
    kernel_program_inv critical sg (task_stack_call_active_key returned) returned
    final_registers.(kernel_save_r0) acquired acquired ** frame) after).
  { rewrite Hstate; unfold kernel_stack_call_masked.
    match type of Hpost with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose after Hpost). }
  split; [exact Hsame|]. split.
  - unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - exact (conj Hstate (conj Hr0 Hmasked)).
Qed.

(** The caller stage, together with the C branch guards, establishes the
    live ready caller and the absent pending-call key. CPU authority and
    stack coverage do not establish these facts. *)
Lemma task_create_call_stage_selection_ready : forall call state,
  task_create_call_stage call state -> state.(SchedState).(isRunning) = true ->
  os_sched_selection_enabled state = true ->
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) /\
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None /\
  exists node,
    sched_current_ready_at state.(TskState) state.(SchedState)
      call.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration).
Proof.
  intros call state [Horigin Hstage] Hrunning Henabled.
  destruct call.(os_sched_call_origin) as [|slot generation] eqn:Hcall.
  - unfold task_create_call_origin in Horigin; congruence.
  - destruct Hstage as [Hslot [Hgeneration [Habsent Hready]]].
    subst slot generation. split; [reflexivity|]. split; [exact Habsent|].
    apply Hready; exact Henabled.
Qed.

(** The true C switch branch begins from the current masked source world.
    The actual priority/cache reads and writes produce the switch cut and
    high-ready consistency from its source-established nonempty ready list.
    The original Save token and inside handle
    remain a separate retained owner, to be rejoined only on return of
    that invocation; they never duplicate its running authority. *)
Lemma task_create_sched_masked_switch_prefix_source :
  forall environment critical sg call saved acquired state lr before (frame : Assertion),
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  state.(SchedState).(readyList) <> [] ->
  os_sched_requests_switch state = true ->
  (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
    critical sg (task_stack_call_active_key call) call saved acquired state ** frame) before ->
  exists after,
    os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
      (os_sched_prefix_state state).(SchedState) /\
    state.(SchedState).(readyList) <> [] /\
    (os_sched_source_switch_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) sg call (armv7a_call_focus call lr lr)
      (os_sched_prefix_state state) ** unmap_table_rep sg **
     (interrupt_platform_saved environment.(task_stack_call_platform)
        (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
      critical_region_inside critical sg call.(os_sched_call_invocation) acquired ** frame)) after.
Proof.
  intros environment critical sg call saved acquired state lr before frame
    Horigin Habsent Hnonempty Hswitch Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations) sg call (armv7a_call_focus call lr lr) state **
    unmap_table_rep sg **
    (interrupt_platform_saved environment.(task_stack_call_platform)
      (save_token saved call.(os_sched_call_invocation) call.(os_sched_call_origin)) **
     critical_region_inside critical sg call.(os_sched_call_invocation) acquired ** frame)) end.
  { unfold kernel_stack_call_masked.
    sep_apply_l_atomic (kernel_stack_inv_focus_call _ _ _ environment.(task_stack_call_continuations)
      kernel_program_inv sg (task_stack_call_active_key call) state
      (armv7a_call_focus call lr lr) Habsent).
    unfold os_sched_source_switch_pre, kernel_call_execution_owned, critical_region_masked,
      task_stack_call_active_key; rewrite Horigin, kernel_program_inv_split_unmap; entailer!. }
  destruct (os_sched_source_switch_prefix_resources _ _ _ environment.(task_stack_call_continuations)
    sg state call (armv7a_call_focus call lr lr) _ before Hswitch Hnonempty (Hopen before Hpre))
    as [after [Hprefix [Hhigh Hpost]]].
  exists after; exact (conj Hprefix (conj Hhigh (conj Hnonempty Hpost))).
Qed.

Lemma task_create_active_links_node_id : forall tasks previous ids tid node,
  task_active_links tasks previous ids -> In tid ids -> tasks tid = Some node -> node.(taskID) = tid.
Proof.
  intros tasks previous ids; revert previous.
  induction ids as [|head tail IH]; intros previous tid node Hlinks Hin Hnode; [contradiction|].
  destruct Hlinks as [first [Hfirst [Hid [Hprev [Hnext Htail]]]]].
  destruct Hin as [Heq|Hin].
  - subst tid; assert (Hsame : node = first) by congruence; rewrite Hsame; exact Hid.
  - eapply IH; eassumption.
Qed.

(** The registered ordinary entry and the conditional source fact retained
    by the canonical TaskCreate cuts supply the CURRENT live caller.
    Consume the actual scheduler-call world, then execute its next Save,
    C selector, OSCtxSw save and destination. No current-ready condition
    is needed. Nonempty readiness and the taken-key absence remain local
    source facts (for example, publication followed by no intervening IRQ),
    not future safety assumptions in the public Require. The stack geometry
    and register values describe this concrete source cut.

    The selected post may belong to an initial or a foreign task. It is
    deliberately not called a return of the original TaskCreate. The
    retained saved-mask/inside resources accompany its pending call. *)
Lemma task_create_tcb_return_sched_switch_source :
  forall environment critical arch
    (save : Armv7aSaveSuffixABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) critical arch)
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    (initial : Armv7aInitialEntryABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg args name original entry call mask state registers before final_registers acquired saved_heap
    old_sp cpsr values lr prefix suffix first old_words publication (frame : Assertion),
  task_create_source_entry sg args name original entry ->
  entry.(SchedState).(isRunning) = true ->
  task_tcb_init_stack_same_call call original ->
  task_tcb_init_stack_source_preserved original entry state ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  state.(SchedState).(readyList) <> [] ->
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
  (os_sched_stack_pre environment kernel_program_inv sg call mask state ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired saved_heap ->
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus call lr lr in
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
  task_tcb_init_stack_same_call call original /\
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
        task_invocation_active (os_sched_install_context call fragments incoming updated).(TskState)
          original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
        selected.(armv7a_continuation_fragments) = resumed /\
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg incoming.(stackLeaseSlot))
          selected.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads selected installed /\
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
  intros environment critical arch save task_abi initial sg args name original entry call mask state registers before
    final_registers acquired saved_heap old_sp cpsr values lr prefix suffix first old_words publication frame
    Hentry Hentry_running Hsame Htransport Habsent Hnonempty Hswitch Hreturn Hvalid_sr Hmask Hfragments Hregion Hgeometry Hsp_range
    Hpublication Hlength Hcpsr Hlr Hranges Hswitch_mask Hsp32 Hsp Haddress Hpre Hsave
    abi focus checkpoint fragments suspended updated retained.
  assert (Hordinary : kernel_call_task_source call state).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff call original state Hsame)).
    apply Htransport; eapply task_create_source_entry_running_source; eassumption. }
  destruct Hordinary as [Horigin [Hactive Hcurrent]].
  pose proof (proj2 (proj2 Hactive)) as Hlive.
  rewrite Horigin in Hlive, Hcurrent.
  destruct Hlive as [node [Hnode Hgeneration]].
  destruct (task_create_tcb_return_sched_masked_source environment critical arch save sg original
    call mask state registers before final_registers acquired saved_heap frame
    Hsame Hreturn Hvalid_sr Hmask Hpre Hsave) as [_ [Hrun [Hstate [Hr0 Hmasked]]]].
  split; [exact Hsame|]. split; [exact Hrun|]. split; [exact Hstate|]. subst acquired.
  destruct (task_create_sched_masked_switch_prefix_source environment critical sg call
    final_registers.(kernel_save_r0) state state lr saved_heap frame Horigin Habsent Hnonempty Hswitch Hmasked)
    as [prefix_heap [Hprefix [Hhigh [_ Hprefix_owned]]]].
  assert (Hvalid_state : UCOS2_state_inv sg state).
  { match type of Hpre with ?P before => assert (Hexpose : P |-- coq_prop (UCOS2_state_inv sg state) && TT) end.
    { unfold os_sched_stack_pre, kernel_stack_call_closed, kernel_stack_inv; rewrite kernel_program_inv_split_unmap.
      unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hexpose before Hpre)). }
  pose proof (proj1 (proj1 (os_sched_requests_switch_iff state) Hswitch)) as Henabled.
  assert (Hid : node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { pose proof (proj1 (proj2 (proj1 (proj2 Hvalid_state)))) as Hactive_nodes.
    destruct Hactive_nodes as [Hnodup [Hhead [Hcount [Hdomain Hlinks]]]].
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
  { unfold os_sched_source_live_save_input, focus.
    repeat first [assumption | reflexivity | split | intro]. }
  assert (Hactive_updated : task_invocation_active updated.(TskState)
    original.(os_sched_call_invocation) original.(os_sched_call_origin)).
  { unfold updated, os_sched_save_current_sp, checkpoint, os_sched_prefix_state.
    cbn [replace_SchedS TskState]; rewrite Hnode.
    cbn [replace_TskS TskState].
    eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hnode|reflexivity|].
    rewrite <- (proj1 Hsame), <- (proj1 (proj2 Hsame)); exact Hactive. }
  match type of Hprefix_owned with ?P prefix_heap => assert (Horder : P |--
    os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
      environment.(task_stack_call_port) abi sg call focus checkpoint ** retained) by
      (unfold retained; entailer!) end.
  destruct (os_sched_source_live_switch_destination_resources _ _ _ abi task_abi initial sg checkpoint
    node call old_sp cpsr values lr prefix suffix first old_words focus publication retained prefix_heap
    Hinput (Horder prefix_heap Hprefix_owned))
    as [written [stored [Hwrites [Hload [Hstore Hselected]]]]].
  exists prefix_heap, written, stored.
  split; [exact Hprefix|]. split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook_heap Hhook_step.
  destruct (Hselected captured hooked Hcapture Hhook_heap Hhook_step)
    as [incoming [resumed [installed [selected [current [Hsource [Hdestination [Hfragments_selected
      [Hinstall [Hreads [Hpending Hrestore]]]]]]]]]]].
  exists incoming, resumed, installed, selected, current.
  exact (conj Hdestination (conj Hactive_updated
    (conj Hfragments_selected (conj Hinstall (conj Hreads Hrestore))))).
Qed.
