Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The incoming lease is obtained from the SAME ready head and covered
    parked map used by the actual high-cache loads. It is not a future
    destination supplied by a public caller. Parking the outgoing entry
    first also handles selection of that same slot/generation. Coverage
    supplies presence; consistency separately supplies the live binding.
    Neither pure fact supplies bytes or CPU authority. *)
Lemma os_sched_covered_high_destination : forall sg context outgoing hooked,
  UCOS2_state_inv sg hooked ->
  os_sched_saved_stack_binding context outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  exists incoming resumed node,
    hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
    hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
    task_stack_live_binding hooked.(TskState) incoming /\
    (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) outgoing) (task_stack_key incoming) =
        Some (incoming.(stackLeaseRegion), resumed) /\
    In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
    is_effectively_ready node.(stat) node.(dly) = true.
Proof.
  intros sg context outgoing hooked Hvalid Hsaved Hhigh Hnonempty Hcoverage.
  pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid)))) ) as Hready.
  assert (Hconsistent : parked_stacks_consistent hooked.(TskState) hooked.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  pose proof (os_sched_park_saved_context_preserves_consistency context outgoing hooked
    Hconsistent Hsaved) as Hparked.
  pose proof (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack)
    outgoing Hcoverage) as Hcovered.
  destruct hooked.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
  unfold sched_high_ready_consistency in Hhigh; rewrite Hlist in Hhigh.
  destruct Hhigh as [Hhigh [node [Hnode Hpriority]]].
  assert (Hin : In slot hooked.(SchedState).(readyList)) by (rewrite Hlist; left; reflexivity).
  destruct (Hready slot (or_introl eq_refl)) as [ready_node [Hready_node [Hrange Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  destruct (Hcovered slot node Hnode) as [Hnone|[region [fragments Hlookup]]]; [discriminate|].
  change ((task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
    context.(os_sched_call_stack) outgoing) (slot, node.(taskGeneration)) =
    Some (region, fragments)) in Hlookup.
  destruct (Hparked slot node.(taskGeneration) region fragments Hlookup)
    as [Hregion [Hgeometry [Hhistory Hbinding]]].
  exists {| stackLeaseRegion := region; stackLeaseSlot := slot;
    stackLeaseGeneration := node.(taskGeneration) |}, fragments, node.
  cbn [stackLeaseSlot stackLeaseGeneration stackLeaseRegion task_stack_key].
  split; [exact Hhigh|]. split; [exact Hnode|]. split; [reflexivity|].
  split; [exact Hpriority|]. split.
  - exists node; split; [exact Hnode|]. apply Hbinding; [exact Hnode|reflexivity].
  - exact (conj Hlookup (conj (or_introl eq_refl) Heffective)).
Qed.

(** Post-hook source consumer: choose the actual high-ready destination,
    obtain its saved SP and architecture source from its owned strong
    entry, execute the cache stores/SP load, and consume that entry on the
    actual restore event. A changed hook must establish its real high-cache
    checkpoint; no unchanged-hook or future-return law is assumed here. *)
Lemma armv7a_task_restore_selected_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  (initial : Armv7aInitialEntryABI external platform port abi)
  sg context outgoing hooked focus (frame : Assertion) heap,
  os_sched_saved_stack_binding context outgoing hooked ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  (forall slot node, hooked.(TskState).(inUsedTaskStates) slot = Some node ->
    tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked ** task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) heap ->
  exists incoming installed selected node,
    sched_install_heap_fragment sg heap installed (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_stack) = incoming /\
    (task_stack_key incoming = armv7a_call_focus_key focus ->
      armv7a_continuation_focus_binding focus selected) /\
    sched_current_ready_at (os_sched_install_context context outgoing incoming hooked).(TskState)
      (os_sched_install_context context outgoing incoming hooked).(SchedState)
      incoming.(stackLeaseSlot) node /\
    node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage (os_sched_install_context context outgoing incoming hooked).(TskState)
      (Some (task_stack_key incoming)) /\
    (forall payload,
      hooked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
      task_stack_key incoming <> armv7a_call_focus_key focus ->
      (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks)
        (armv7a_call_focus_key focus) = Some payload) /\
    (forall restored, armv7a_task_restore_transition task_abi context selected installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      armv7a_task_restored_source external selected /\
      (armv7a_task_restored_execution external platform port abi selected **
       UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
       armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
         focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
       frame) restored /\
      (task_stack_key incoming = armv7a_call_focus_key focus ->
       (kernel_call_execution_owned external platform
          (armv7a_continuation_resumed_call selected focus.(armv7a_focus_call))
          (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) **
        UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
        armv7a_task_call_stacks abi (os_sched_install_context context outgoing incoming hooked).(TskState)
          focus (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
        frame) restored)).
Proof.
  intros external platform port abi task_abi initial sg context outgoing hooked focus frame heap
    Hsaved Hhigh Hnonempty Haddress Hcoverage Hbefore.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hbefore with ?P heap =>
      assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT)
    end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hbefore)). }
  destruct (os_sched_covered_high_destination sg context outgoing hooked
    Hvalid Hsaved Hhigh Hnonempty Hcoverage)
    as [incoming [resumed [node [Hselected [Hnode [Hgeneration [Hpriority [Hlive
      [Hparked [Hin Heffective]]]]]]]]]].
  destruct (armv7a_task_restore_call_map external platform port abi task_abi initial
    sg context outgoing hooked incoming resumed node focus frame heap Hsaved Hselected Hnode
    Hgeneration Hpriority Hlive Hparked (Haddress _ _ Hnode) Hcoverage Hbefore)
    as [installed [selected [Hrun [Hlease [Hfocus [Hcurrent [Hcovered [Hother Hrestore]]]]]]]].
  exists incoming, installed, selected, node.
  split; [exact Hrun|]. split; [exact Hlease|]. split; [exact Hfocus|]. split.
  - unfold sched_current_ready_at.
    change (hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
      hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
      hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In incoming.(stackLeaseSlot) hooked.(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    tauto.
  - exact (conj Hgeneration (conj Hcovered (conj Hother Hrestore))).
Qed.
