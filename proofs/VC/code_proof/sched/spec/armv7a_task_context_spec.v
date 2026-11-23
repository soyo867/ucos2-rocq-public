Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only execution authority, not another stack owner. The Some branch
    resumes the actual saved invocation; first entry has no old caller.
    Neither branch means that the original OS_Sched invocation returned. *)
Definition armv7a_task_restored_execution external platform port
  (abi : Armv7aContinuationABI external platform port) saved : Assertion :=
  match saved.(armv7a_continuation_call) with
  | Some call => kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call saved call)
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr))
  | None => armv7a_initial_execution abi saved **
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments)
  end.

Definition armv7a_task_restored_source external saved : Prop :=
  match saved.(armv7a_continuation_call) with
  | Some call => external.(os_sched_arch_resume_source) call
      (armv7a_continuation_resumed_call saved call)
  | None => True
  end.

(** APPROVED external ARMv7-A/GNU non-VFP task-switch refinement.
    This is a parameterized port contract, NOT a proof of assembly/BSP.

    OSCtxSw enters in SVC with both IRQ/FIQ masked. Its sixteen physical
    stores and the TCB-SP store are proved separately from the C/ordinary
    memory projection. Capture is the execution-authority cut after those
    stores and before the hook: it consumes the original running authority
    and returns switch control plus a dormant continuation. Restore consumes
    switch control and the selected continuation at the actual LDM/MSR/LDM
    source event. No IRQ context or handler-stack owner is fabricated.

    The dormant family is shared with IRQ saves so an IRQ-created frame can
    later be restored by OSCtxSw and vice versa. No kernel state, ready bit,
    object lifetime, current TCB, whole-map invariant or future-call safety
    is granted by these fields. Such facts remain proved kernel obligations.
    The predicates below are execution resources, not ghost C addresses. *)
Record Armv7aTaskContextABI external platform port
  (abi : Armv7aContinuationABI external platform port) : Type := {
  armv7a_task_switch_control : OsSchedCallContext -> Assertion;
  armv7a_task_capture_transition :
    OsSchedCallContext -> Armv7aContinuation -> model -> model -> Prop;
  armv7a_task_restore_transition :
    OsSchedCallContext -> Armv7aContinuation -> model -> model -> Prop;
  armv7a_task_capture_resources : forall call saved (frame : Assertion) before after,
    saved.(armv7a_continuation_call) = Some call ->
    armv7a_continuation_restore_reads saved before ->
    armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = 192 ->
    (interrupt_platform_running platform call.(os_sched_call_invocation)
       call.(os_sched_call_origin) 192 ** external.(os_sched_arch_running) call ** frame) before ->
    armv7a_task_capture_transition call saved before after ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
    external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp)
      saved.(armv7a_continuation_fragments) /\
    (armv7a_task_switch_control call ** armv7a_dormant_continuation abi saved ** frame) after;
  armv7a_task_dormant_restore_source : forall saved,
    armv7a_dormant_continuation abi saved |--
    coq_prop (external.(os_sched_arch_restore_source) saved.(armv7a_continuation_stack)
      saved.(armv7a_continuation_sp) saved.(armv7a_continuation_fragments)) &&
    armv7a_dormant_continuation abi saved;
  armv7a_task_restore_resources : forall outgoing saved (frame : Assertion) before after,
    armv7a_continuation_restore_reads saved before ->
    (armv7a_task_switch_control outgoing **
     task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
       saved.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi saved ** frame) before ->
    armv7a_task_restore_transition outgoing saved before after ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
    armv7a_task_restored_source external saved /\
    (armv7a_task_restored_execution external platform port abi saved ** frame) after
}.

Arguments armv7a_task_switch_control {external platform port abi} _ _.
Arguments armv7a_task_capture_transition {external platform port abi} _ _ _ _ _.
Arguments armv7a_task_restore_transition {external platform port abi} _ _ _ _ _.

Lemma armv7a_task_saved_cpsr_mask : forall cpsr lr,
  armv7a_irq_fiq_mask (armv7a_task_saved_cpsr cpsr lr) = armv7a_irq_fiq_mask cpsr.
Proof.
  intros; unfold armv7a_task_saved_cpsr, armv7a_irq_fiq_mask.
  destruct (Z.eqb (Z.land lr 1) 0); [reflexivity|].
  rewrite Z.land_lor_distr_l; change (Z.lor (Z.land cpsr 192) 0 = Z.land cpsr 192).
  apply Z.lor_0_r.
Qed.

(** This bridges the pre-existing opaque restore relation only from its
    real continuation owner (or the approved initialized-frame instance),
    never from a task ID, a live TCB, or an arbitrary sixteen-word array. *)
Lemma armv7a_task_continuation_restore_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi) saved,
  armv7a_task_continuation_resource abi saved |--
  coq_prop (external.(os_sched_arch_restore_source) saved.(armv7a_continuation_stack)
    saved.(armv7a_continuation_sp) saved.(armv7a_continuation_fragments)) &&
  armv7a_task_continuation_resource abi saved.
Proof.
  intros; unfold armv7a_task_continuation_resource.
  destruct saved.(armv7a_continuation_call).
  - apply (armv7a_task_dormant_restore_source _ _ _ abi task_abi).
  - Intros; pose proof (armv7a_initial_restore_source _ _ _ abi initial saved H); entailer!.
Qed.

(** Eliminate the opaque architecture premise at a real selected-entry cut.
    High-pointer/priority, generation and park lookup are still required
    source/kernel facts. The exact SP is obtained from the strong entry. *)
Lemma os_sched_destination_from_stack_entry : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  context outgoing hooked incoming resumed node,
  hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) ->
  hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) ->
  task_stack_live_binding hooked.(TskState) incoming ->
  (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) (task_stack_key incoming) =
      Some (incoming.(stackLeaseRegion), resumed) ->
  armv7a_task_stack_entry abi hooked.(TskState) (task_stack_key incoming)
    (incoming.(stackLeaseRegion), resumed) |--
  coq_prop (os_sched_destination_binding external context outgoing hooked incoming resumed) &&
  armv7a_task_stack_entry abi hooked.(TskState) (task_stack_key incoming)
    (incoming.(stackLeaseRegion), resumed).
Proof.
  intros external platform port abi task_abi initial context outgoing hooked incoming resumed node
    Hhigh Hnode Hgen Hprio Hlive Hparked.
  unfold armv7a_task_stack_entry; Intros saved.
  assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
  assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
    saved.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
  assert (Hlease : saved.(armv7a_continuation_stack) = incoming).
  { unfold task_stack_key in Hkey; destruct saved.(armv7a_continuation_stack), incoming;
      cbn in *; congruence. }
  assert (Hfragments : saved.(armv7a_continuation_fragments) = resumed) by congruence.
  assert (Hsp : node.(tcbStkPtr) = saved.(armv7a_continuation_sp)).
  { assert (Hsaved_sp : task_stack_live_sp hooked.(TskState)
      (task_stack_key incoming) saved.(armv7a_continuation_sp)) by tauto.
    apply Hsaved_sp; assumption. }
  sep_apply_l_atomic (armv7a_task_continuation_restore_source external platform port abi task_abi initial saved).
  Intros.
  assert (Harch : external.(os_sched_arch_restore_source) incoming node.(tcbStkPtr) resumed).
  { rewrite Hsp, <- Hlease, <- Hfragments; assumption. }
  assert (Hdestination : os_sched_destination_binding external context outgoing hooked incoming resumed).
  { unfold os_sched_destination_binding; split; [exact Hhigh|].
    split; [exists node; tauto|].
    split; assumption. }
  Exists saved; entailer!.
Qed.

(** Actual live-current save producer followed by the task-level authority
    cut. The preceding stores are not postulated by the ABI. A real capture
    event is still required; this theorem does not assert that an external
    port transition occurs, terminates, or returns to the original caller. *)
Lemma armv7a_task_live_save_and_capture :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (task_abi : Armv7aTaskContextABI external platform port abi)
    sg tasks node call old_sp cpsr registers lr prefix suffix first old_words (frame : Assertion) before,
  tasks.(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  tasks.(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  task_stack_live_coverage tasks (Some (task_stack_key call.(os_sched_call_stack))) ->
  call.(os_sched_call_fragments) = prefix ++ [(first, first + 16, old_words)] ++ suffix ->
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  armv7a_irq_fiq_mask cpsr = 192 ->
  0 <= old_sp - 64 < 4294967296 ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  (kernel_call_execution_owned external platform call 192 ** task_public_storage sg tasks **
   armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) **
   sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    task_stack_live_coverage updated (Some (task_stack_key call.(os_sched_call_stack))) /\
    (forall captured, armv7a_task_capture_transition task_abi call saved stored captured ->
      captured.(ConAssertion.s_mem) = stored.(ConAssertion.s_mem) /\
      external.(os_sched_arch_save_source) call saved.(armv7a_continuation_sp) fragments /\
      (armv7a_task_switch_control task_abi call **
       task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       task_public_storage sg updated **
       armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
       armv7a_task_stack_entry abi updated (task_stack_key call.(os_sched_call_stack))
         (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame) captured).
Proof.
  intros external platform port abi task_abi sg tasks node call old_sp cpsr registers lr prefix suffix first
    old_words frame before Hnode Hgen Hnone Hcoverage Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsprange
    Hsp Haddress Hbefore.
  cbv zeta.
  set (fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix).
  set (saved := armv7a_task_save_image call old_sp cpsr registers lr fragments).
  set (updated := glob_task_set_usedtask tasks call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  match type of Hbefore with ?P before =>
    assert (Horder : P |-- task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
      call.(os_sched_call_fragments) ** task_public_storage sg tasks **
      armv7a_task_stack_continuations abi tasks tasks.(parkedTaskStacks) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) **
      (interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
       external.(os_sched_arch_running) call ** frame))
  end.
  { unfold kernel_call_execution_owned, os_sched_context_resources; entailer!. }
  destruct (task_stack_live_save_source external platform port abi sg tasks node call old_sp cpsr registers
    lr prefix suffix first old_words _ before Hnode Hgen Hnone Hcoverage Hfragments Hlength Hcpsr Hlr
    Hranges Hsprange Hsp Haddress (Horder before Hbefore))
    as [written [stored [Hstores [Hload [Hstore [Hbinding [Hslice [Hlive [Hcovered [Hreads Hstored]]]]]]]]]].
  fold fragments saved updated in Hstored, Hbinding, Hslice, Hlive, Hreads, Hstore, Hcovered.
  exists written, stored; fold fragments saved updated.
  split; [exact Hstores|]. split; [exact Hload|]. split; [exact Hstore|].
  split; [exact Hcovered|]. intros captured Hcapture.
  match type of Hstored with ?P stored =>
    assert (Hcapture_input : P |--
      interrupt_platform_running platform call.(os_sched_call_invocation) call.(os_sched_call_origin) 192 **
      external.(os_sched_arch_running) call **
      (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
       task_public_storage sg updated ** armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
       sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame))
  end.
  { unfold saved, armv7a_task_save_image; cbn; entailer!. }
  assert (Hsaved_mask : armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = 192).
  { unfold saved, armv7a_task_save_image; cbn; rewrite armv7a_task_saved_cpsr_mask; exact Hmask. }
  destruct (armv7a_task_capture_resources _ _ _ abi task_abi call saved _ stored captured
    eq_refl Hreads Hsaved_mask (Hcapture_input stored Hstored) Hcapture)
    as [Hmemory [Hsource Hcaptured]].
  split; [exact Hmemory|]. split; [exact Hsource|].
  match type of Hcaptured with ?P captured =>
    assert (Hclose : P |-- armv7a_task_switch_control task_abi call **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) fragments **
      task_public_storage sg updated ** armv7a_task_stack_continuations abi updated updated.(parkedTaskStacks) **
      armv7a_task_stack_entry abi updated (task_stack_key call.(os_sched_call_stack))
        (call.(os_sched_call_stack).(stackLeaseRegion), fragments) **
      sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ** frame)
  end.
  { assert (Hentry : armv7a_dormant_continuation abi saved |--
      armv7a_task_stack_entry abi updated (task_stack_key call.(os_sched_call_stack))
        (call.(os_sched_call_stack).(stackLeaseRegion), fragments)).
    { change (armv7a_task_continuation_resource abi saved |--
        armv7a_task_stack_entry abi updated (task_stack_key saved.(armv7a_continuation_stack))
          (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
      apply armv7a_task_stack_entry_resources; assumption. }
    sep_apply_l_atomic Hentry; entailer!. }
  exact (Hclose captured Hcaptured).
Qed.

(** Consume the real selected SP/read frame and the ENTIRE successor map
    produced by installation. Control is consumed exactly once. The world
    is retained through the masked final LDM; this is not an IRQ frame rule
    across an arbitrary open scheduler interval. *)
Lemma armv7a_task_restore_after_install : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg context outgoing hooked incoming resumed node (frame : Assertion) heap,
  os_sched_saved_stack_binding context outgoing hooked ->
  hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) ->
  hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = incoming.(stackLeaseGeneration) ->
  hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) ->
  task_stack_live_binding hooked.(TskState) incoming ->
  (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) (task_stack_key incoming) =
      Some (incoming.(stackLeaseRegion), resumed) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr = task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_stack_entry abi hooked.(TskState) (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_stack_continuations abi hooked.(TskState) hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) heap ->
  exists installed selected,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = incoming /\
    task_current_at (os_sched_install_context context outgoing incoming hooked)
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage (os_sched_install_context context outgoing incoming hooked).(TskState)
      (Some (task_stack_key incoming)) /\
    (forall restored, armv7a_task_restore_transition task_abi context selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected **
       UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
       armv7a_task_stack_continuations abi (os_sched_install_context context outgoing incoming hooked).(TskState)
         (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) ** frame) restored).
Proof.
  intros external platform port abi task_abi initial sg context outgoing hooked incoming resumed node frame heap
    Hsaved Hhigh Hnode Hgen Hprio Hlive Hparked Haddress Hcoverage Hbefore.
  assert (Hnone : hooked.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None).
  { unfold os_sched_saved_stack_binding in Hsaved; tauto. }
  assert (Hdestination : os_sched_destination_binding external context outgoing hooked incoming resumed).
  { match type of Hbefore with ?P heap =>
      assert (Hobserve : P |--
        coq_prop (os_sched_destination_binding external context outgoing hooked incoming resumed) && TT)
    end.
    { unfold armv7a_task_stack_continuations.
      sep_apply_l_atomic (store_parked_continuations_switch (armv7a_task_stack_entry abi hooked.(TskState))
        hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) incoming outgoing resumed Hnone Hparked).
      sep_apply_l_atomic (os_sched_destination_from_stack_entry external platform port abi task_abi initial
        context outgoing hooked incoming resumed node Hhigh Hnode Hgen Hprio Hlive Hparked).
      entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hbefore)). }
  destruct (os_sched_install_take_covered_continuation external platform port abi sg context outgoing hooked
    incoming resumed _ heap Hsaved Hdestination Haddress Hcoverage Hbefore)
    as [installed [selected [Hrun [Hreads [Hlease [Hfragments [Hcurrent [Hcovered Hinstalled]]]]]]]].
  exists installed, selected; split; [exact Hrun|]. split; [exact Hlease|].
  split; [exact Hcurrent|]. split; [exact Hcovered|]. intros restored Hrestore.
  match type of Hinstalled with ?P installed =>
    assert (Hinput : P |-- armv7a_task_switch_control task_abi context **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
      (UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
       armv7a_task_stack_continuations abi (os_sched_install_context context outgoing incoming hooked).(TskState)
         (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) ** frame))
  end.
  { entailer!. }
  destruct (armv7a_task_restore_resources _ _ _ abi task_abi context selected _ installed restored
    Hreads (Hinput installed Hinstalled) Hrestore) as [Hmemory [Hsource Hrestored]].
  split; [exact Hmemory|]. split; [exact Hsource|].
  match type of Hrestored with ?P restored =>
    assert (Hclose : P |-- armv7a_task_restored_execution external platform port abi selected **
      UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
      armv7a_task_stack_continuations abi (os_sched_install_context context outgoing incoming hooked).(TskState)
        (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) ** frame)
  end.
  { entailer!. }
  exact (Hclose restored Hrestored).
Qed.
