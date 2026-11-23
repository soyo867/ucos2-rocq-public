Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The ordinary OSCtxSw restore of a genuinely pending call. The actual
    selector/post-hook producer supplies [destination]; the original saved
    SP has been transported along that same source state trace. Real
    install stores and SP/frame loads then recover ALL original registers,
    not only the PC/LR focus. Both outgoing/incoming aliasing and a foreign
    outgoing caller are handled by the existing park/take producer.

    This is the returning-destination branch, not a promise that the
    scheduler always selects this task. It preserves the shared
    selected_post interface used by other consumers and exposes the exact
    current world and authority of the original invocation. *)
Lemma task_create_sched_restore_pending_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  (task_abi : Armv7aTaskContextABI external platform port abi)
  sg context outgoing hooked original suspended (frame : Assertion) heap,
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  armv7a_continuation_binding suspended ->
  suspended.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice suspended ->
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked original.(os_sched_call_stack)
    suspended.(armv7a_continuation_fragments) ->
  sched_high_ready_consistency hooked.(TskState) hooked.(SchedState) ->
  hooked.(SchedState).(readyList) <> [] ->
  task_saved_pointer_at hooked suspended.(armv7a_continuation_stack)
    suspended.(armv7a_continuation_sp) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_call_stack_entry abi hooked.(TskState) focus (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_call_stacks abi hooked.(TskState) focus hooked.(TskState).(parkedTaskStacks) **
   (armv7a_task_switch_control task_abi context ** frame)) heap ->
  let current := os_sched_install_context context outgoing original.(os_sched_call_stack) hooked in
  exists installed selected node,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected installed /\
    armv7a_continuation_focus_binding focus selected /\
    selected.(armv7a_continuation_stack) = original.(os_sched_call_stack) /\
    selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_cpsr) = suspended.(armv7a_continuation_cpsr) /\
    selected.(armv7a_continuation_registers) = suspended.(armv7a_continuation_registers) /\
    task_stack_live_coverage current.(TskState) (Some (task_stack_key original.(os_sched_call_stack))) /\
    (forall after, armv7a_task_restore_transition task_abi context selected installed after ->
      after.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      external.(os_sched_arch_resume_source) original (armv7a_continuation_resumed_call selected original) /\
      (os_sched_source_selected_post external platform port abi sg focus original.(os_sched_call_stack)
         selected node current ** frame) after /\
      (kernel_call_execution_owned external platform (armv7a_continuation_resumed_call selected original)
         (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) **
       UCOS2_inv sg current ** armv7a_task_call_stacks abi current.(TskState) focus
         current.(TskState).(parkedTaskStacks) ** frame) after).
Proof.
  intros external platform port abi task_abi sg context outgoing hooked original suspended frame heap
    focus Hbinding Hcall Hslice Hsaved Hdestination Hhigh Hnonempty Hpointer Haddress Hcoverage Hpre current.
  assert (Horiginal_lease : suspended.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  destruct Hpointer as [node [Hnode [Hgen Hsp]]]; rewrite Horiginal_lease in Hnode, Hgen.
  assert (Hvalid : UCOS2_state_inv sg hooked).
  { match type of Hpre with ?P heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg hooked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve heap Hpre)). }
  assert (Hhigh_id : hooked.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot))
    by exact (proj1 Hdestination).
  assert (Hready : sched_current_ready_at current.(TskState) current.(SchedState)
    original.(os_sched_call_stack).(stackLeaseSlot) node).
  { pose proof (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid))))) as Hready.
    destruct hooked.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
    unfold sched_high_ready_consistency in Hhigh; rewrite Hlist in Hhigh.
    destruct Hhigh as [Hhead [head [Hhead_node Hpriority]]].
    assert (Hslot : slot = original.(os_sched_call_stack).(stackLeaseSlot)) by congruence; subst slot.
    assert (Hhead_eq : head = node) by congruence; subst head.
    destruct (Hready _ (or_introl eq_refl)) as [ready_node [Hready_node [_ Heffective]]].
    assert (Hnode_eq : ready_node = node) by congruence; subst ready_node.
    unfold sched_current_ready_at.
    change (hooked.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
      hooked.(SchedState).(highRdyTid) = Some original.(os_sched_call_stack).(stackLeaseSlot) /\
      hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      In original.(os_sched_call_stack).(stackLeaseSlot) hooked.(SchedState).(readyList) /\
      is_effectively_ready node.(stat) node.(dly) = true).
    rewrite Hlist; repeat split; try assumption; left; reflexivity. }
  destruct (os_sched_install_take_call_continuation external platform port abi sg context outgoing hooked
    original.(os_sched_call_stack) suspended.(armv7a_continuation_fragments) focus _ heap
    Hsaved Hdestination Haddress Hcoverage Hpre)
    as [installed [selected [Hinstall [Hreads [Hlease [Hfragments [Hfocus [Hcurrent [Hcovered Hinstalled]]]]]]]]].
  specialize (Hfocus eq_refl).
  assert (Hselected_sp : selected.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp)).
  { assert (Hload : pointer_load (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      node.(tcbStkPtr) installed).
    { eapply task_stack_framed_live_sp_load with (state := current).
      - exact Hnode.
      - exact Haddress.
      - match type of Hinstalled with ?P installed => assert (Horder : P |-- UCOS2_inv sg current **
          (armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) **
           task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
             selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
           (armv7a_task_switch_control task_abi context ** frame))) by entailer! end.
        exact (Horder installed Hinstalled). }
    rewrite Hsp in Hload; eapply pointer_load_deterministic; [exact (proj2 Hinstall)|exact Hload]. }
  assert (Hframe : exists rest : Assertion,
    (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) ** rest) installed).
  { eexists.
    match type of Hinstalled with ?P installed => assert (Horder : P |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_inv sg current ** armv7a_task_call_stacks abi current.(TskState) focus
         current.(TskState).(parkedTaskStacks) ** armv7a_task_continuation_resource abi selected **
       (armv7a_task_switch_control task_abi context ** frame))) by entailer! end.
    exact (Horder installed Hinstalled). }
  destruct Hframe as [rest Hframe].
  destruct (armv7a_same_frame_registers suspended selected rest installed Hbinding Hslice
    ltac:(congruence) Hfragments Hselected_sp Hreads Hframe) as [Hcpsr Hregisters].
  exists installed, selected, node; split; [exact Hinstall|]. split; [exact Hreads|].
  split; [exact Hfocus|]. split; [exact Hlease|]. split; [exact Hselected_sp|].
  split; [exact Hcpsr|]. split; [exact Hregisters|]. split; [exact Hcovered|].
  intros after Hrestore.
  match type of Hinstalled with ?P installed => assert (Hrestore_input : P |--
    armv7a_task_switch_control task_abi context **
    task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
      selected.(armv7a_continuation_fragments) ** armv7a_task_continuation_resource abi selected **
    (UCOS2_inv sg current ** armv7a_task_call_stacks abi current.(TskState) focus
      current.(TskState).(parkedTaskStacks) ** frame)) by entailer! end.
  destruct (armv7a_task_restore_resources _ _ _ abi task_abi context selected _ installed after
    Hreads (Hrestore_input installed Hinstalled) Hrestore) as [Hmemory [Hsource Hafter]].
  assert (Hselected_call : selected.(armv7a_continuation_call) = Some original) by exact (proj1 Hfocus).
  unfold armv7a_task_restored_source in Hsource; rewrite Hselected_call in Hsource.
  split; [exact Hmemory|]. split; [exact Hsource|]. split.
  - match type of Hafter with ?P after => assert (Hclose : P |--
      os_sched_source_selected_post external platform port abi sg focus original.(os_sched_call_stack)
        selected node current ** frame) end.
    { unfold os_sched_source_selected_post; entailer!. }
    exact (Hclose after Hafter).
  - unfold armv7a_task_restored_execution in Hafter; rewrite Hselected_call, Hcpsr in Hafter.
    match type of Hafter with ?P after => assert (Horder : P |--
      kernel_call_execution_owned external platform (armv7a_continuation_resumed_call selected original)
        (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) **
      UCOS2_inv sg current ** armv7a_task_call_stacks abi current.(TskState) focus
        current.(TskState).(parkedTaskStacks) ** frame) by entailer! end.
    exact (Horder after Hafter).
Qed.
