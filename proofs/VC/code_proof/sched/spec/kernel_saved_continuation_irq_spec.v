Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_save_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_irq_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** First-level IRQ on a live task: the approved save event consumes the
    interrupted execution, then the real nesting/SP stores park its bytes.
    The already owned local cut is retained through that SAME save and is
    deposited with the descriptor in the existing continuation map.

    The saved PC and mask are observations of the IRQ event. In particular
    they need not satisfy Scheduler's PC=LR or mask=192 properties. The
    handler's own execution resources remain outside the saved entry, and
    no current/forever-active invocation claim is inferred from its tag. *)
Lemma kernel_irq_save_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler descriptor publication
  (local : Armv7aContinuation -> Assertion) (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice descriptor ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
   (UCOS2_inv sg entry **
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) ** local descriptor ** frame)) before ->
  armv7a_save_transition abi handler descriptor before saved_heap ->
  exists final,
    descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes descriptor)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_inv sg parked **
     store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
       parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler descriptor publication local frame before saved_heap
    call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hcoverage Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler descriptor before saved_heap Hsave)
    as [Hsource [Hcall [Hbinding [Hmask [Hpc [Hsavedsp Hfragments]]]]]].
  destruct (armv7a_save_transition_resources _ _ _ abi handler descriptor call _ before saved_heap
    Hcall eq_refl Hbinding Hmask Hpc Hsavedsp Hfragments Hpre Hsave) as [Hwrites Hsaved].
  pose proof Hbinding as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask entry.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node descriptor.(armv7a_continuation_sp)))
    (task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      descriptor.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hmap : parked.(TskState).(parkedTaskStacks) =
    task_stack_park_fragments entry.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      descriptor.(armv7a_continuation_fragments)) by (rewrite Htasks; reflexivity).
  assert (Hlive : task_stack_live_sp parked.(TskState) (task_stack_key call.(os_sched_call_stack))
    descriptor.(armv7a_continuation_sp)).
  { intros current Hlookup Hcurrentgen; rewrite Htasks in Hlookup.
    cbn [task_stack_key fst glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask] in Hlookup.
    rewrite Z.eqb_refl in Hlookup; injection Hlookup as Hlookup; subst current; reflexivity. }
  assert (Hreindex :
    store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
      entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
      entry.(TskState).(parkedTaskStacks)).
  { rewrite Htasks.
    exact (kernel_saved_continuation_map_save_sp external platform port abi entry.(TskState) node
      descriptor.(armv7a_continuation_sp) call.(os_sched_call_stack) local
      entry.(TskState).(parkedTaskStacks) Hnode Hgen Hnone). }
  assert (Hentry : armv7a_dormant_continuation abi descriptor ** local descriptor |--
    kernel_saved_continuation_entry abi parked.(TskState) local
      (task_stack_key call.(os_sched_call_stack))
      (call.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { unfold kernel_saved_continuation_entry; Exists descriptor.
    unfold armv7a_task_continuation_resource; rewrite Hcall, <- Hstack; entailer!. }
  assert (Hattach : armv7a_dormant_continuation abi descriptor ** local descriptor **
      store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
        entry.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
      parked.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic Hreindex; sep_apply_l_atomic Hentry; rewrite Hmap.
    apply store_parked_continuations_park; exact Hnone. }
  match type of Hsaved with ?P saved_heap => assert (Hsplit : P |--
    (UCOS2_inv sg entry **
      task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
        descriptor.(armv7a_continuation_fragments)) **
    (armv7a_dormant_continuation abi descriptor ** local descriptor **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) **
     interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)) end.
  { change (call.(os_sched_call_stack) = descriptor.(armv7a_continuation_stack)) in Hstack.
    rewrite Hstack; entailer!. }
  destruct (Hsplit saved_heap Hsaved) as [owned [rest [Hjoin [Howned Hrest]]]].
  destruct (armv7a_irq_live_entry_parks_stack sg entry node descriptor.(armv7a_continuation_sp)
    call descriptor.(armv7a_continuation_fragments) publication owned Hrunning Hnesting Hcurrent Hnode
    Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Howned)
    as [written [Hrun Hwritten]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [final [Hwhole Hfinal]].
  assert (Hclose : UCOS2_inv sg parked **
    (armv7a_dormant_continuation abi descriptor ** local descriptor **
     store_parked_continuations (kernel_saved_continuation_entry abi entry.(TskState) local)
       entry.(TskState).(parkedTaskStacks) **
     interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame) |--
    UCOS2_inv sg parked **
    store_parked_continuations (kernel_saved_continuation_entry abi parked.(TskState) local)
      parked.(TskState).(parkedTaskStacks) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)).
  { sepcon_assoc_change; sep_apply_l_atomic Hattach; entailer!. }
  exists final; split; [exact Hcall|]. split; [exact Hpc|]. split; [exact Hmask|].
  split; [exact Hwrites|]. split; [exact Hwhole|].
  split; [eapply armv7a_irq_live_parked_stack_coverage; eassumption|].
  apply (Hclose final); exists written, rest; split; [exact Hfinal|]; split; assumption.
Qed.
