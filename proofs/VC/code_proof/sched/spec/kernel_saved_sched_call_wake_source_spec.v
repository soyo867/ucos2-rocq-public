Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_selected_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_profile_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_pending_stack_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_wake_selection_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reindex the existing exact-entry view after a concrete TCB update.
    The two premises are proved for the actual wake/SP writes below.
    Descriptor identity, its own Save/inside pair, and the older focus
    remain owned on the same heap; no second continuation map is added. *)
Lemma kernel_saved_sched_call_map_reindex : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor
  before after focus stacks,
  (forall key payload node, stacks key = Some payload ->
    after.(inUsedTaskStates) (fst key) = Some node -> node.(taskGeneration) = snd key ->
    exists old, before.(inUsedTaskStates) (fst key) = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)) ->
  (task_invocation_active before call.(os_sched_call_invocation) call.(os_sched_call_origin) ->
    task_invocation_active after call.(os_sched_call_invocation) call.(os_sched_call_origin)) ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor before focus) stacks |--
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor after focus) stacks.
Proof.
  intros external platform port abi critical sg call saved acquired descriptor before after focus stacks
    Htransport Hactive.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_sched_call_entry.
  destruct task_stack_key_eq_dec as [Hkey|Hkey].
  - Intros.
    assert (Hsp : task_stack_live_sp before key descriptor.(armv7a_continuation_sp)) by tauto.
    assert (Hnext : task_stack_live_sp after key descriptor.(armv7a_continuation_sp)).
    { intros node Hnode Hgen.
      destruct (Htransport key payload node Hlookup Hnode Hgen) as [old [Hold [Hg Hv]]].
      rewrite <- Hv; apply Hsp; [exact Hold|congruence]. }
    assert (Hregistered : task_invocation_active after call.(os_sched_call_invocation) call.(os_sched_call_origin))
      by (apply Hactive; tauto).
    entailer!; tauto.
  - unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec;
      [|unfold armv7a_task_stack_entry]; Intros parked.
    all: assert (Hsp : task_stack_live_sp before key parked.(armv7a_continuation_sp)) by tauto.
    all: assert (Hnext : task_stack_live_sp after key parked.(armv7a_continuation_sp)).
    all: try (intros node Hnode Hgen;
      destruct (Htransport key payload node Hlookup Hnode Hgen) as [old [Hold [Hg Hv]]];
      rewrite <- Hv; apply Hsp; [exact Hold|congruence]).
    all: Exists parked; entailer!.
Qed.

(** Observe the actual selected descriptor without weakening its owner.
    Its registration supplies the matching live generation, and the
    dormant owner supplies the architecture restore relation. *)
Lemma kernel_saved_sched_call_destination : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg state context outgoing call saved acquired descriptor focus,
  UCOS2_state_inv sg state ->
  state.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  sched_high_ready_consistency state.(TskState) state.(SchedState) -> state.(SchedState).(readyList) <> [] ->
  state.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor state.(TskState) focus)
    state.(TskState).(parkedTaskStacks) |--
  coq_prop (os_sched_destination_binding external context outgoing state call.(os_sched_call_stack)
    descriptor.(armv7a_continuation_fragments)) && TT.
Proof.
  intros external platform port abi critical task_abi sg state context outgoing call saved acquired descriptor focus
    Hvalid Hselected Hhigh Hnonempty Hnone Hparked.
  assert (Hother : task_stack_key call.(os_sched_call_stack) <> task_stack_key context.(os_sched_call_stack))
    by (intro Heq; rewrite Heq, Hnone in Hparked; discriminate).
  assert (Hlookup : (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) (task_stack_key call.(os_sched_call_stack)) =
      Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { rewrite task_stack_park_fragments_lookup_other by exact Hother; exact Hparked. }
  sep_apply_l_atomic (kernel_saved_sched_call_take_resources external platform port abi critical sg call saved
    acquired descriptor state.(TskState) focus state.(TskState).(parkedTaskStacks)
    descriptor.(armv7a_continuation_fragments) Hparked).
  unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec; [|contradiction].
  unfold kernel_saved_sched_call; Intros.
  assert (Hbinding : armv7a_continuation_binding descriptor) by tauto.
  assert (Hcall : descriptor.(armv7a_continuation_call) = Some call) by tauto.
  assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Horigin : call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration)) by tauto.
  assert (Hactive : task_invocation_active state.(TskState) call.(os_sched_call_invocation)
    call.(os_sched_call_origin)) by tauto.
  destruct Hactive as [_ [_ Hlive_origin]]; rewrite Horigin in Hlive_origin.
  destruct Hlive_origin as [node [Hnode Hgen]].
  assert (Hsp : node.(tcbStkPtr) = descriptor.(armv7a_continuation_sp)).
  { assert (Hpointer : task_stack_live_sp state.(TskState) (task_stack_key call.(os_sched_call_stack))
      descriptor.(armv7a_continuation_sp)) by tauto; apply Hpointer; assumption. }
  assert (Hpriority : state.(SchedState).(highRdyPrio) = Some node.(curPrio)).
  { destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    unfold sched_high_ready_consistency in Hhigh; rewrite Hlist in Hhigh.
    destruct Hhigh as [Hhead [found [Hfound Hprio]]].
    assert (head = call.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst head.
    assert (found = node) by congruence; subst found; exact Hprio. }
  assert (Hlive : task_stack_live_binding state.(TskState) call.(os_sched_call_stack)).
  { assert (Hconsistent : parked_stacks_consistent state.(TskState) state.(TskState).(parkedTaskStacks))
      by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
    destruct (Hconsistent _ _ _ _ Hparked) as [Hr [Hf [Hp Hmatch]]].
    exists node; split; [exact Hnode|apply Hmatch; assumption]. }
  sep_apply_l_atomic (armv7a_task_dormant_restore_source external platform port abi task_abi descriptor); Intros.
  assert (Hsource : external.(os_sched_arch_restore_source) call.(os_sched_call_stack)
    node.(tcbStkPtr) descriptor.(armv7a_continuation_fragments)).
  { rewrite Hsp, <- Hlease; assumption. }
  assert (Hdestination : os_sched_destination_binding external context outgoing state call.(os_sched_call_stack)
    descriptor.(armv7a_continuation_fragments)).
  { unfold os_sched_destination_binding; split; [exact Hselected|].
    split; [exists node; tauto|]. split; assumption. }
  entailer!; intros ? ?; exact I.
Qed.

(** Writing the CURRENT task's SP cannot overwrite a parked generation's
    saved SP: that current key is absent from this very map. Its other
    task fields and invocation registrations survive the actual update. *)
Lemma kernel_saved_sched_call_map_save_sp : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor
  tasks node sp outgoing focus stacks,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  stacks (task_stack_key outgoing) = None ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor tasks focus) stacks |--
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor
      (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)) focus) stacks.
Proof.
  intros external platform port abi critical sg call saved acquired descriptor tasks node sp outgoing focus stacks
    Hnode Hgeneration Hnone.
  apply kernel_saved_sched_call_map_reindex.
  - intros [slot generation] payload updated Hlookup Hupdated Hgen; cbn in Hgen.
    cbn [fst glob_task_set_usedtask inUsedTaskStates] in Hupdated.
    destruct (Z.eqb slot outgoing.(stackLeaseSlot)) eqn:Hslot.
    + apply Z.eqb_eq in Hslot; subst slot; injection Hupdated as Hupdated; subst updated.
      change (node.(taskGeneration) = generation) in Hgen.
      assert (Hkey : (outgoing.(stackLeaseSlot), generation) = task_stack_key outgoing)
        by (unfold task_stack_key; f_equal; congruence).
      rewrite Hkey, Hnone in Hlookup; discriminate.
    + exists updated; auto.
  - intros Hactive; eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hnode|reflexivity|exact Hactive].
Qed.

(** Reuse the physical sixteen stores and raw TCB-SP write with an
    arbitrary frame. The caller below supplies its exact saved-call map
    in that frame, then uses the concrete SP reindex above. *)
Lemma kernel_sched_save_frame_source : forall sg state node call old_sp cpsr values lr
  prefix suffix first old_words (frame : Assertion) before,
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) call.(os_sched_call_fragments) **
   UCOS2_inv sg state ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image call old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    armv7a_continuation_binding outgoing /\ armv7a_task_frame_slice outgoing /\
    task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack)) outgoing.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads outgoing stored /\
    (UCOS2_inv sg updated ** task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments ** frame) stored.
Proof.
  intros sg state node call old_sp cpsr values lr prefix suffix first old_words frame before
    Hcurrent Hnode Hid Hgen Hnone Hfragments Hlength Hcpsr Hlr Hranges Hsprange Hsp Haddress Hbefore.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix).
  set (outgoing := armv7a_task_save_image call old_sp cpsr values lr fragments).
  set (updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp)).
  match type of Hbefore with ?P before => assert (Horder : P |--
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) ** (UCOS2_inv sg state ** frame)) end.
  { rewrite Hfragments; entailer!. }
  destruct (armv7a_task_save_fragment_execution call old_sp cpsr values lr prefix suffix first old_words
    _ before Hlength Hcpsr Hlr Hranges Hsp (Horder before Hbefore))
    as [written [Hwrites [Hwritten [Hreads Hslice]]]].
  fold fragments outgoing in Hwritten, Hreads, Hslice.
  assert (Hload : pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written).
  { match type of Hwritten with ?P written => assert (Hcell : P |--
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** TT) end.
    { unfold UCOS2_inv, UCOS2_raw_rep, sched_raw_rep, sched_physical_rep;
        rewrite Hcurrent; cbn [encode_task_link]; entailer!; intros ? ?; exact I. }
    eapply framed_pointer_store_load; exact (Hcell written Hwritten). }
  match type of Hwritten with ?P written => assert (Hopen : P |-- coq_prop (UCOS2_state_inv sg state) &&
    (UCOS2_raw_rep sg state **
     (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments ** frame))) end.
  { unfold UCOS2_inv, outgoing, armv7a_task_save_image; cbn; entailer!. }
  destruct (Hopen written Hwritten) as [Hvalid [owned [rest [Hjoin [Hraw Hrest]]]]].
  destruct (armv7a_irq_store_live_sp_raw_post sg state call.(os_sched_call_stack).(stackLeaseSlot) node
    outgoing.(armv7a_continuation_sp) owned Hnode Haddress Hsprange Hraw)
    as [changed [Hstore Hchanged]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hstore Hjoin) as [stored [Hrun Hjoined]].
  assert (Hvalid_after : UCOS2_state_inv sg updated).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    exact (os_sched_save_live_sp_preserves_validity sg state node outgoing.(armv7a_continuation_sp)
      call.(os_sched_call_stack) Hvalid Hnode Hid Hgen Hnone). }
  assert (Hstored : (UCOS2_inv sg updated **
    (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments ** frame)) stored).
  { exists changed, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
  assert (Hbinding : armv7a_continuation_binding outgoing)
    by (apply armv7a_task_save_image_binding; exact Hlength).
  assert (Hlive : task_stack_live_sp updated.(TskState) (task_stack_key call.(os_sched_call_stack))
      outgoing.(armv7a_continuation_sp)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    intros other Hother Hothergen;
      cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates task_stack_key fst] in Hother.
    rewrite Z.eqb_refl in Hother; injection Hother as Hother; subst other; reflexivity. }
  assert (Hstored_reads : armv7a_continuation_restore_reads outgoing stored).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    match type of Hstored with ?P stored => assert (Hfocus : P |--
      task_stack_fragments_rep outgoing.(armv7a_continuation_stack).(stackLeaseRegion)
        outgoing.(armv7a_continuation_fragments) ** (UCOS2_inv sg updated ** frame)) end.
    { unfold outgoing, armv7a_task_save_image; cbn; entailer!. }
    exact (Hfocus stored Hstored). }
  exists written, stored.
  refine (conj Hwrites (conj Hload (conj Hrun (conj Hbinding
    (conj Hslice (conj Hlive (conj Hstored_reads _))))))).
  match type of Hstored with ?P stored => match goal with |- ?Q stored =>
    assert (Hclose : P |-- Q) by entailer! end end.
  exact (Hclose stored Hstored).
Qed.

(** The real OS_EventTaskRdy return inside OSSemPost. All TCB updates
    here preserve generation and saved SP. Registration preservation is
    derived from that same update, while local Save/inside resources are
    framed. No assumption about which task will be selected is needed. *)
Lemma kernel_saved_sched_call_wake_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg call saved acquired descriptor
  entry eid event tid old priority focus active,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) active ->
  let after := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid **
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
    entry.(TskState).(parkedTaskStacks) |--
  coq_prop (sem_post_wake_result sg eid entry after priority /\ task_stack_live_coverage after.(TskState) active) &&
  (kernel_program_inv sg after **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor after.(TskState) focus)
     after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi critical sg call saved acquired descriptor entry eid event tid old priority
    focus active Hvalid Hlookup Htype Hentry Hcoverage after.
  pose proof Hentry as [_ [_ [_ [_ [_ [Hhead Hold]]]]]].
  assert (Hkind : event_type_to_pend_type event.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct event.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid event tid tail PendSem 0 PendOK Hvalid Hlookup Hkind Hlist)
    as [found [Hfound [Hstep Hrest]]].
  assert (found = old) by congruence; subst found.
  assert (Hnodes : forall slot node, after.(TskState).(inUsedTaskStates) slot = Some node ->
    exists previous, entry.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = node.(taskGeneration) /\ previous.(tcbStkPtr) = node.(tcbStkPtr)).
  { intros slot node Hnode.
    change ((if Z.eqb slot tid then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) slot) = Some node) in Hnode.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hnode as Hnode; subst node.
      exists old; repeat split; assumption || reflexivity.
    - exists node; repeat split; assumption || reflexivity. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active).
  { eapply task_stack_live_coverage_used_map_frame with (before := entry.(TskState));
      [|reflexivity|exact Hcoverage].
    intros slot node Hnode; destruct (Hnodes slot node Hnode) as [previous [Hp [Hg Hsp]]].
    exists previous; auto. }
  assert (Htransport : store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor after.(TskState) focus)
      after.(TskState).(parkedTaskStacks)).
  { change after.(TskState).(parkedTaskStacks) with entry.(TskState).(parkedTaskStacks).
    apply kernel_saved_sched_call_map_reindex.
    - intros key payload node Hpayload Hnode Hgen; apply Hnodes; exact Hnode.
    - intros Hactive; eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hold|reflexivity|exact Hactive]. }
  sep_apply_l_atomic (sem_post_wake_merge_full sg entry eid event tid old priority
    Hvalid Hlookup Htype Hentry); Intros returned.
  assert (Hresult : sem_post_wake_result sg eid entry returned priority) by tauto.
  unfold sem_post_wake_result in Hresult; rewrite Hstep in Hresult.
  injection Hresult as Hpriority Hreturned; subst returned.
  sep_apply_l_atomic Htransport.
  rewrite kernel_program_inv_split_unmap; unfold sem_post_wake_result, after; entailer!.
Qed.

(** The existing raw selector and counter-store producers already admit
    an arbitrary frame. Keep that parameter here so an exact saved-call
    map is never projected down to the weaker existential map. *)
Lemma kernel_sched_switch_prefix_frame_source : forall sg state (frame : Assertion) before,
  os_sched_requests_switch state = true -> state.(SchedState).(readyList) <> [] ->
  (UCOS2_inv sg state ** unmap_table_rep sg ** frame) before ->
  exists after, os_sched_source_switch_prefix_execution sg before after /\
    sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
      (os_sched_prefix_state state).(SchedState) /\
    (UCOS2_inv sg (os_sched_prefix_state state) ** unmap_table_rep sg ** frame) after.
Proof.
  intros sg state frame before Hswitch Hnonempty Hpre.
  destruct (proj1 (os_sched_requests_switch_iff state) Hswitch) as [Hselection Hdifferent].
  destruct (proj1 (os_sched_selection_enabled_iff state) Hselection) as [Hints Hlocks].
  assert (Hopen : UCOS2_inv sg state ** unmap_table_rep sg ** frame |--
    coq_prop (UCOS2_state_inv sg state) && (UCOS2_raw_rep sg state ** unmap_table_rep sg ** frame))
    by (unfold UCOS2_inv; entailer!).
  destruct (Hopen before Hpre) as [Hvalid Hraw].
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hregistered : task_current_prio_registered state.(TskState)).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks; unfold task_in_range in Htasks; tauto. }
  assert (Hguards : uchar_load sg.(g_OSIntNesting) 0 before /\ uchar_load sg.(g_OSLockNesting) 0 before).
  { match type of Hraw with ?P before => assert (Hi : P |-- sg.(g_OSIntNesting) # UChar |-> 0 ** TT) end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; rewrite Hints; entailer!; intros ? ?; exact I. }
    match type of Hraw with ?P before => assert (Hl : P |-- sg.(g_OSLockNesting) # UChar |-> 0 ** TT) end.
    { unfold UCOS2_raw_rep, interrupt_inv, store_int_state; rewrite Hlocks; entailer!; intros ? ?; exact I. }
    split; eapply framed_uchar_store_load; [exact (Hi before Hraw)|exact (Hl before Hraw)]. }
  destruct (os_int_exit_selection_raw_frame_post sg state frame before Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty Hraw)
    as [selected [Hselect [Hhighread [Hcurrentread Hselected]]]].
  destruct Hselected as [selected_owned [rest [Hjoin
    [[raw [unmap [Hselected_join [Hselected_raw Hunmap]]]] Hrest]]]].
  destruct (os_sched_profile_global_raw_post sg (os_int_exit_selection_state state) raw Hselected_raw)
    as [counted [Hcounter Hcounted]].
  destruct (os_sched_profile_global_fragment_frame sg raw counted unmap selected_owned Hcounter Hselected_join)
    as [counted_owned [Hcounter_owned Hcounted_join]].
  destruct (os_sched_profile_global_fragment_frame sg selected_owned counted_owned rest selected Hcounter_owned Hjoin)
    as [after [Hcounter_whole Hafter_join]].
  assert (Hstate : os_sched_profile_global_state (os_int_exit_selection_state state) = os_sched_prefix_state state).
  { unfold os_sched_profile_global_state, os_int_exit_selection_state, os_sched_prefix_state,
      os_sched_ready_checkpoint; rewrite Hselection, Hswitch; reflexivity. }
  assert (Hvalid_after : UCOS2_state_inv sg (os_sched_prefix_state state))
    by (apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid).
  exists after; split.
  - split; [exact (proj1 Hguards)|]. split; [exact (proj2 Hguards)|].
    exists selected, (sched_selected_priority state.(TskState) state.(SchedState)),
      (sched_priority_byte state.(SchedState).(curSchedPrio)).
    exact (conj Hselect (conj Hhighread (conj Hcurrentread (conj Hdifferent Hcounter_whole)))).
  - split.
    + apply os_sched_ready_checkpoint_high_consistency with (sg := sg);
        [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hselection].
    + exists counted_owned, rest; split; [exact Hafter_join|]. split; [|exact Hrest].
      exists counted, unmap; split; [exact Hcounted_join|]. split; [|exact Hunmap].
      split; [exact Hvalid_after|rewrite <- Hstate; exact Hcounted].
Qed.

(** Consume a CURRENT selector cut, not an eventual destination promise.
    The next lemma supplies that cut from EventTaskRdy and real Save/
    Restore executions. An explicit no-write hook path remains a
    condition: App_TaskSwHook has no selected empty-source binding.
    The endpoint is the saved task's masked OSCtxSw continuation; its
    later OS_CPU_SR_Restore has a distinct C-call return LR. *)
Lemma kernel_saved_sched_call_live_switch_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg state node context old_sp cpsr values lr prefix suffix first old_words publication
  call saved acquired descriptor focus before (frame : Assertion),
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp state context.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments call.(os_sched_call_stack) updated in
  let returned := kernel_selected_call descriptor current in
  os_sched_source_live_save_input sg state node context old_sp cpsr values lr
    prefix suffix first old_words focus publication ->
  state.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  (kernel_call_execution_owned external platform context 192 ** kernel_program_inv sg state **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor state.(TskState) focus)
     state.(TskState).(parkedTaskStacks) ** frame) before ->
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        descriptor.(armv7a_continuation_call) = Some call /\ kernel_call_task_source returned current /\
        (forall restored,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          external.(os_sched_arch_resume_source) call returned /\
          descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
          armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
          restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
          (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
             returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
           kernel_program_inv sg current **
           armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) ** frame) restored)).
Proof.
  intros external platform port abi critical task_abi sg state node context old_sp cpsr values lr prefix suffix
    first old_words publication call saved acquired descriptor focus before frame fragments outgoing updated current returned
    Hinput Hselected Hparked Hbefore.
  destruct Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments
    [Hregion [Hgeometry [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges [Hmask [Hsp32 [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  assert (Hother : task_stack_key context.(os_sched_call_stack) <> task_stack_key call.(os_sched_call_stack)).
  { intro Heq; rewrite <- Heq, Hnone in Hparked; discriminate. }
  set (retained := store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) 192 **
     external.(os_sched_arch_running) context ** unmap_table_rep sg ** frame)).
  match type of Hbefore with ?P before => assert (Horder : P |--
    task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) context.(os_sched_call_fragments) **
    UCOS2_inv sg state ** retained) end.
  { unfold retained, kernel_call_execution_owned, os_sched_context_resources;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (kernel_sched_save_frame_source sg state node context old_sp cpsr values lr prefix suffix first old_words
    retained before Hcurrent Hnode Hid Hgen Hnone Hfragments Hlength Hcpsr Hlr Hranges Hsp32 Hsp (Haddress _)
    (Horder before Hbefore))
    as [written [stored [Hwrites [Hload [Hstore [Hbinding [Hslice [Hlive [Hreads Hstored]]]]]]]]].
  fold fragments outgoing updated in Hstore, Hbinding, Hslice, Hlive, Hreads, Hstored.
  assert (Htransport : store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor state.(TskState) focus)
      state.(TskState).(parkedTaskStacks) |--
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor updated.(TskState) focus)
      updated.(TskState).(parkedTaskStacks)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode.
    apply kernel_saved_sched_call_map_save_sp; assumption. }
  assert (Hmask_out : armv7a_irq_fiq_mask outgoing.(armv7a_continuation_cpsr) = 192).
  { unfold outgoing, armv7a_task_save_image; cbn [armv7a_continuation_cpsr].
    rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  assert (Hsaved : os_sched_saved_stack_binding context fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hhigh_after : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
    destruct (Z.eqb head context.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst head; assert (high = node) by congruence; subst high.
      exists (task_set_saved_sp node outgoing.(armv7a_continuation_sp)); split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - exists high; split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  assert (Hparked_after : updated.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Hparked. }
  assert (Hselected_after : updated.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Hselected. }
  assert (Hnonempty_after : updated.(SchedState).(readyList) <> []).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Hnonempty. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured hooked Hcapture Hhook Hhook_source.
  assert (Heq : hooked = captured).
  { eapply kernel_heap_execution_deterministic; [exact Hhook|]. split; [constructor|]; split; reflexivity. }
  subst hooked.
  match type of Hstored with ?P stored => assert (Hcapture_input : P |--
    interrupt_platform_running platform context.(os_sched_call_invocation) context.(os_sched_call_origin) 192 **
    external.(os_sched_arch_running) context **
    (UCOS2_inv sg updated ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) fragments **
     store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor updated.(TskState) focus)
       updated.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) end.
  { unfold retained; sep_apply_l_atomic Htransport; entailer!. }
  destruct (armv7a_task_capture_resources external platform port abi task_abi context outgoing _ stored captured
    eq_refl Hreads Hmask_out (Hcapture_input stored Hstored) Hcapture) as [Hmemory [Hsource Hcaptured]].
  assert (Hentry : armv7a_dormant_continuation abi outgoing |--
    kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor updated.(TskState) focus
      (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), fragments)).
  { unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec; [contradiction|].
    unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec as [Heq|Hneq].
    - Exists outgoing.
      assert (Hfocused : armv7a_continuation_focus_binding focus outgoing).
      { rewrite (Hfocus Heq); unfold armv7a_continuation_focus_binding, armv7a_call_focus,
          outgoing, armv7a_task_save_image; cbn; repeat split; reflexivity. }
      entailer!.
    - unfold armv7a_task_stack_entry; Exists outgoing.
      unfold armv7a_task_continuation_resource; cbn [outgoing armv7a_task_save_image armv7a_continuation_call]; entailer!. }
  assert (Hdestination : os_sched_destination_binding external context fragments updated call.(os_sched_call_stack)
    descriptor.(armv7a_continuation_fragments)).
  { match type of Hcaptured with ?P captured => assert (Hobserve : P |-- coq_prop
      (os_sched_destination_binding external context fragments updated call.(os_sched_call_stack)
        descriptor.(armv7a_continuation_fragments)) && TT) end.
    { unfold UCOS2_inv; Intros.
      sep_apply_l_atomic (kernel_saved_sched_call_destination external platform port abi critical task_abi sg updated
        context fragments call saved acquired descriptor focus ltac:(assumption) Hselected_after Hhigh_after
        Hnonempty_after (proj2 (proj2 (proj2 (proj2 Hsaved)))) Hparked_after).
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured)). }
  match type of Hcaptured with ?P captured => assert (Hinstall : P |--
    UCOS2_inv sg updated ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) fragments **
    kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor updated.(TskState) focus
      (task_stack_key context.(os_sched_call_stack)) (context.(os_sched_call_stack).(stackLeaseRegion), fragments) **
    store_parked_continuations
      (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor updated.(TskState) focus)
      updated.(TskState).(parkedTaskStacks) **
    (armv7a_task_switch_control task_abi context ** unmap_table_rep sg ** frame)) end.
  { sep_apply_l_atomic Hentry; entailer!. }
  exact (kernel_saved_sched_call_install_resume_source external platform port abi critical task_abi sg context fragments
    updated call saved acquired descriptor descriptor.(armv7a_continuation_fragments) focus captured frame
    Hsaved Hdestination (Haddress _) (Hinstall captured Hcaptured)).
Qed.

(** The real EventTaskRdy post is merged before the current poster exits
    its critical section. Both uninterrupted Restore/Save executions
    carry the exact saved entry as an arbitrary, unchanged heap frame.
    The selector still computes its destination from the woken state. *)
Lemma kernel_saved_sched_call_wake_sched_prefix : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  (save : Armv7aSaveSuffixABI external platform critical arch)
  sg entry eid event tid old priority context poster_saved call saved acquired descriptor focus
  before (frame : Assertion) cursor written middle final_cursor released
  registers final_registers next_acquired saved_heap,
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  os_sched_requests_switch checkpoint = true -> checkpoint.(SchedState).(readyList) <> [] ->
  (critical_region_masked platform critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) poster_saved entry ** os_sched_context_resources external context **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
     entry.(TskState).(parkedTaskStacks) ** frame) before ->
  cursor.(kernel_restore_r0) = poster_saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask poster_saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers next_acquired saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers next_acquired saved_heap /\
  next_acquired = checkpoint /\
  exists prefix_heap,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    sched_high_ready_consistency selected.(TskState) selected.(SchedState) /\
    (kernel_call_execution_owned external platform context 192 ** kernel_program_inv sg selected **
     store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor selected.(TskState) focus)
       selected.(TskState).(parkedTaskStacks) **
     (interrupt_platform_saved platform
        (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
      critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint ** frame)) prefix_heap.
Proof.
  intros external platform port abi critical arch restore save sg entry eid event tid old priority context poster_saved
    call saved acquired descriptor focus before frame cursor written middle final_cursor released registers final_registers
    next_acquired saved_heap checkpoint selected Hvalid Hlookup Htype Hentry Hcoverage Hswitch Hnonempty Hpre
    Hr0 Hmask Hprefix Hsuffix Hreturn Hcpsr Hnextmask Hsave.
  match type of Hpre with ?P before => assert (Hmerge : P |--
    critical_region_masked platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) poster_saved entry ** os_sched_context_resources external context **
    (kernel_program_inv sg checkpoint **
     store_parked_continuations
       (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor checkpoint.(TskState) focus)
       checkpoint.(TskState).(parkedTaskStacks) ** frame)) end.
  { pose proof (kernel_saved_sched_call_wake_merge external platform port abi critical sg call saved acquired
      descriptor entry eid event tid old priority focus (Some (task_stack_key context.(os_sched_call_stack)))
      Hvalid Hlookup Htype Hentry Hcoverage) as Hwake.
    cbv zeta in Hwake; sep_apply_l_atomic Hwake; Intros; entailer!. }
  destruct (armv7a_restore_uninterrupted_transports_owned_execution _ _ _ _ restore sg context poster_saved entry
    cursor before written middle final_cursor released _ Hr0 Hmask (Hmerge before Hpre) Hprefix Hsuffix)
    as [Hrestore [Hlr [Hmemory Hreleased]]].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)) by (split; [exact Hcpsr|reflexivity]).
  rewrite <- Hnextmask in Hreleased.
  destruct (armv7a_save_suffix_preserves_source_heap _ _ _ _ save sg context
    (kernel_save_read_cpsr registers) checkpoint released final_registers next_acquired saved_heap _
    Hsaved Hreleased Hsave) as [Hstate [Hmemory_after [Hreturned [Hvalue Hsaved_owned]]]].
  split; [exact Hrestore|]. split.
  - unfold kernel_call_save_uninterrupted_execution; econstructor.
    + constructor; [exact Hreturn|reflexivity].
    + exact (armv7a_save_suffix_source _ _ _ _ save _ _ _ _ _ _ Hsave).
  - split; [exact Hstate|]. subst next_acquired.
    set (retained := kernel_call_execution_owned external platform context 192 **
      store_parked_continuations
        (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor checkpoint.(TskState) focus)
        checkpoint.(TskState).(parkedTaskStacks) **
      (interrupt_platform_saved platform
         (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
       critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint ** frame)).
    match type of Hsaved_owned with ?P saved_heap => assert (Horder : P |--
      UCOS2_inv sg checkpoint ** unmap_table_rep sg ** retained) end.
    { unfold retained, critical_region_masked, kernel_call_execution_owned;
        rewrite kernel_program_inv_split_unmap; entailer!. }
    destruct (kernel_sched_switch_prefix_frame_source sg checkpoint retained saved_heap Hswitch Hnonempty
      (Horder saved_heap Hsaved_owned)) as [prefix_heap [Hrun [Hhigh Hafter]]].
    exists prefix_heap; split; [exact Hrun|]. split; [exact Hhigh|].
    match type of Hafter with ?P prefix_heap => assert (Hclose : P |--
      kernel_call_execution_owned external platform context 192 ** kernel_program_inv sg selected **
      store_parked_continuations
        (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor selected.(TskState) focus)
        selected.(TskState).(parkedTaskStacks) **
      (interrupt_platform_saved platform
         (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
       critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint ** frame)) end.
    { unfold retained; rewrite kernel_program_inv_split_unmap.
      change selected.(TskState) with checkpoint.(TskState); entailer!. }
    exact (Hclose prefix_heap Hafter).
Qed.

(** A concrete returning source family. EventTaskRdy wakes THIS saved
    invocation's task; its actual priority precedes every currently ready
    task and the current poster is ready with scheduling enabled. These
    present-state facts imply the physical selector destination below.
    No premise assumes an eventual selection or an eventual return.

    Non-highest/suspended paths still retain their exact entry by
    [kernel_saved_sched_call_wake_merge]. This family takes the explicit
    no-write TaskSwHook branch, not an unconfigured empty-hook claim.
    It ends at TaskRestore's masked OSCtxSw continuation, owning this
    invocation's original Save/inside pair and the poster's new pair in
    its frame. A later OS_CPU_SR_Restore is a separate C-call join. *)
Lemma kernel_saved_sched_call_wake_resume_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical arch
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  (save : Armv7aSaveSuffixABI external platform critical arch)
  sg entry eid event tid old priority context node poster_saved call saved acquired descriptor focus
  old_sp cpsr values lr prefix suffix first old_words publication
  before (frame : Assertion) cursor restore_written middle final_cursor released
  registers final_registers next_acquired saved_heap,
  let checkpoint := event_wake_state sg entry eid event tid old PendSem 0 PendOK in
  let selected := os_sched_prefix_state checkpoint in
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: values ++ [lr; lr]))] ++ suffix in
  let outgoing := armv7a_task_save_image context old_sp cpsr values lr fragments in
  let updated := os_sched_save_current_sp selected context.(os_sched_call_stack).(stackLeaseSlot)
    outgoing.(armv7a_continuation_sp) in
  let current := os_sched_install_context context fragments call.(os_sched_call_stack) updated in
  let returned := kernel_selected_call descriptor current in
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid event -> event.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid event tid old ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  task_status_is_suspended
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)) = false ->
  (forall slot ready, In slot entry.(SchedState).(readyList) ->
    entry.(TskState).(inUsedTaskStates) slot = Some ready -> old.(curPrio) < ready.(curPrio)) ->
  sched_current_ready_at entry.(TskState) entry.(SchedState) context.(os_sched_call_stack).(stackLeaseSlot) node ->
  entry.(IntrState).(intNesting) = 0 -> entry.(IntrState).(lockNesting) = 0 ->
  tid = call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) =
    Some (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  node.(taskID) = context.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None ->
  (task_stack_key context.(os_sched_call_stack) = armv7a_call_focus_key focus ->
    focus = armv7a_call_focus context lr lr) ->
  context.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  valid_task_stack_region context.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    context.(os_sched_call_fragments) ->
  task_stack_saved_pointer_in_range context.(os_sched_call_stack).(stackLeaseRegion) (old_sp - 64) ->
  task_publication_happened entry.(TskState) publication
    context.(os_sched_call_stack).(stackLeaseSlot) context.(os_sched_call_stack).(stackLeaseGeneration) ->
  List.length values = 13%nat -> 0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) values -> armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = context.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (forall slot, tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  (critical_region_masked platform critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) poster_saved entry ** os_sched_context_resources external context **
   event_task_rdy_post sg entry.(TskState) eid event tid old 0 1 0
     (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
     (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
   sem_post_wake_frame sg entry eid tid **
   store_parked_continuations
     (kernel_saved_sched_call_entry abi critical sg call saved acquired descriptor entry.(TskState) focus)
     entry.(TskState).(parkedTaskStacks) ** frame) before ->
  cursor.(kernel_restore_r0) = poster_saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  armv7a_restore_prefix_transition restore cursor before restore_written middle ->
  armv7a_restore_suffix_transition restore restore_written middle final_cursor released ->
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = armv7a_irq_fiq_mask poster_saved ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) checkpoint released
    final_registers next_acquired saved_heap ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor released /\
  kernel_call_save_uninterrupted_execution arch registers checkpoint released final_registers next_acquired saved_heap /\
  next_acquired = checkpoint /\
  exists prefix_heap written stored,
    os_sched_source_switch_prefix_execution sg saved_heap prefix_heap /\
    selected.(SchedState).(highRdyTid) = Some tid /\
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr values lr) prefix_heap written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg context.(os_sched_call_stack).(stackLeaseSlot))
      outgoing.(armv7a_continuation_sp)) written stored /\
    (forall captured hooked,
      armv7a_task_capture_transition task_abi context outgoing stored captured ->
      kernel_heap_execution [] captured hooked ->
      kernel_client_step external.(os_sched_hook_action) sg updated updated ->
      exists installed,
        sched_install_heap_fragment sg hooked installed (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
          descriptor.(armv7a_continuation_sp) /\
        armv7a_continuation_restore_reads descriptor installed /\
        descriptor.(armv7a_continuation_call) = Some call /\ kernel_call_task_source returned current /\
        (forall restored,
          armv7a_task_restore_transition task_abi context descriptor installed restored ->
          external.(os_sched_arch_resume_source) call returned /\
          descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) /\
          armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
          restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
          (critical_region_masked platform critical sg returned.(os_sched_call_invocation)
             returned.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
           kernel_program_inv sg current **
           armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
           (interrupt_platform_saved platform
              (save_token final_registers.(kernel_save_r0) context.(os_sched_call_invocation) context.(os_sched_call_origin)) **
            critical_region_inside critical sg context.(os_sched_call_invocation) checkpoint ** frame)) restored)).
Proof.
  intros external platform port abi critical arch task_abi restore save sg entry eid event tid old priority
    context node poster_saved call saved acquired descriptor focus old_sp cpsr values lr prefix suffix first old_words
    publication before frame cursor restore_written middle final_cursor released registers final_registers next_acquired
    saved_heap checkpoint selected fragments outgoing updated current returned Hvalid Hlookup Htype Hentry Hcoverage
    Hunsuspended Hhighest Hcurrent Hnest Hlock Htid Hparked Hid Hgeneration Hnone Hfocus Hfragments Hregion
    Hgeometry Hsp_range Hpublication Hlength Hcpsr Hlr Hranges Hsaved_mask Hsp32 Hsp Haddress Hpre
    Hr0 Hmask Hrestore_prefix Hrestore_suffix Hreturn Hregisters_cpsr Hnextmask Hsave.
  destruct (sem_post_wake_selects_highest_waiter sg entry eid event tid old
    context.(os_sched_call_stack).(stackLeaseSlot) node Hvalid Hlookup Htype Hentry
    Hunsuspended Hhighest Hcurrent Hnest Hlock) as [Hready [Hwoken [Hswitch [Hselected Hpriority]]]].
  fold checkpoint selected in Hready, Hwoken, Hswitch, Hselected, Hpriority.
  assert (Hnonempty : checkpoint.(SchedState).(readyList) <> []) by (rewrite Hready; discriminate).
  destruct (kernel_saved_sched_call_wake_sched_prefix external platform port abi critical arch restore save
    sg entry eid event tid old priority context poster_saved call saved acquired descriptor focus before frame
    cursor restore_written middle final_cursor released registers final_registers next_acquired saved_heap
    Hvalid Hlookup Htype Hentry Hcoverage Hswitch Hnonempty Hpre Hr0 Hmask Hrestore_prefix Hrestore_suffix
    Hreturn Hregisters_cpsr Hnextmask Hsave)
    as [Hrestore_run [Hsave_run [Hacquired [prefix_heap [Hprefix_run [Hhigh Hprefix_heap]]]]]].
  fold checkpoint selected in Hacquired, Hhigh, Hprefix_heap.
  pose proof Hcurrent as [Hnode [Hcurrent_id [Hcurrent_priority [Hcurrent_ready Hcurrent_stat]]]].
  pose proof Hentry as [_ [_ [_ [_ [_ [Hwait_head Hold]]]]]].
  assert (Hdifferent : context.(os_sched_call_stack).(stackLeaseSlot) <> tid).
  { pose proof (Hhighest _ node Hcurrent_ready Hnode).
    intro Heq; rewrite Heq in Hnode; assert (node = old) by congruence.
    subst node; lia. }
  assert (Hnode_after : selected.(TskState).(inUsedTaskStates)
    context.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { change ((if Z.eqb context.(os_sched_call_stack).(stackLeaseSlot) tid
      then Some (task_event_wake_single old PendSem 0 PendOK)
      else entry.(TskState).(inUsedTaskStates) context.(os_sched_call_stack).(stackLeaseSlot)) = Some node).
    assert (Heq : Z.eqb context.(os_sched_call_stack).(stackLeaseSlot) tid = false)
      by (apply Z.eqb_neq; exact Hdifferent).
    rewrite Heq; exact Hnode. }
  assert (Hcurrent_after : selected.(SchedState).(curTaskID) =
    Some context.(os_sched_call_stack).(stackLeaseSlot)).
  { unfold selected, os_sched_prefix_state; cbn [replace_SchedS SchedState].
    unfold os_sched_ready_checkpoint.
    destruct (os_sched_selection_enabled checkpoint); destruct (os_sched_requests_switch checkpoint);
      cbn [sched_increment_switch_counter sched_refresh_high curTaskID].
    all: change ((sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
      (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).(curTaskID) =
      Some context.(os_sched_call_stack).(stackLeaseSlot)).
    all: unfold sched_wake_by_status; rewrite Hunsuspended; exact Hcurrent_id. }
  assert (Hready_after : selected.(SchedState).(readyList) = checkpoint.(SchedState).(readyList)).
  { unfold selected, os_sched_prefix_state; cbn [replace_SchedS SchedState].
    unfold os_sched_ready_checkpoint.
    destruct (os_sched_selection_enabled checkpoint); destruct (os_sched_requests_switch checkpoint); reflexivity. }
  assert (Hinput : os_sched_source_live_save_input sg selected node context old_sp cpsr values lr
    prefix suffix first old_words focus publication).
  { unfold os_sched_source_live_save_input.
    split; [exact Hcurrent_after|]. split; [exact Hnode_after|].
    split; [exact Hid|]. split; [exact Hgeneration|]. split; [exact Hnone|].
    split; [exact Hhigh|]. split; [rewrite Hready_after; exact Hnonempty|].
    split; [exact Hfocus|]. split; [exact Hfragments|]. split; [exact Hregion|].
    split; [exact Hgeometry|]. split; [exact Hsp_range|]. split; [exact Hpublication|].
    split; [exact Hlength|]. split; [exact Hcpsr|]. split; [exact Hlr|].
    split; [exact Hranges|]. split; [exact Hsaved_mask|]. split; [exact Hsp32|].
    split; [exact Hsp|exact Haddress]. }
  assert (Hselected_call : selected.(SchedState).(highRdyTid) = Some call.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite <- Htid; exact Hselected).
  destruct (kernel_saved_sched_call_live_switch_source external platform port abi critical task_abi
    sg selected node context old_sp cpsr values lr prefix suffix first old_words publication
    call saved acquired descriptor focus prefix_heap _ Hinput Hselected_call Hparked Hprefix_heap)
    as [written [stored [Hwrites [Hload [Hstore Hcontinuation]]]]].
  split; [exact Hrestore_run|]. split; [exact Hsave_run|]. split; [exact Hacquired|].
  exists prefix_heap, written, stored; split; [exact Hprefix_run|]. split; [exact Hselected|].
  split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|exact Hcontinuation].
Qed.
