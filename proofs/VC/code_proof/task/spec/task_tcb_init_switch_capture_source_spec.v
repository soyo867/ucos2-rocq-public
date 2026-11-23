Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_save_global_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_switch_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_registered_return_source_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapObservation KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Produce the registry's capture view from the real sixteen stores,
    OSTCBCur read, TCB saved-SP write and existing authority exchange.
    The input is the actual selector checkpoint with its source geometry.
    No selected original task or future restore is required. The observer
    may be the saving caller or an already pending foreign invocation. *)
Lemma task_tcb_init_switch_capture_source :
  forall environment
    (task_abi : Armv7aTaskContextABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    sg original suspended released state node call old_sp cpsr registers lr prefix suffix
    first old_words publication (frame : Assertion) before,
  let abi := environment.(task_stack_call_continuations) in
  let focus := armv7a_call_focus original suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released state ->
  os_sched_source_live_save_input sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus publication ->
  (os_sched_source_switch_pre environment.(task_stack_call_external) environment.(task_stack_call_platform)
     environment.(task_stack_call_port) abi sg call focus state ** unmap_table_rep sg ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]))] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  let updated := os_sched_save_current_sp state call.(os_sched_call_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_sp) in
  exists written stored,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before written /\
    pointer_load sg.(g_OSTCBCur) (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) written /\
    kernel_heap_execution (pointer_store_writes (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
      saved.(armv7a_continuation_sp)) written stored /\
    (forall captured,
      armv7a_task_capture_transition task_abi call saved stored captured ->
      environment.(task_stack_call_external).(os_sched_arch_save_source)
        call saved.(armv7a_continuation_sp) fragments /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released updated /\
      (task_tcb_init_switch_capture environment task_abi sg original suspended call fragments updated ** frame) captured).
Proof.
  intros environment task_abi sg original suspended released state node call old_sp cpsr registers lr
    prefix suffix first old_words publication frame before abi focus Hhistory Hinput Hpre fragments saved updated.
  destruct Hinput as [Hcurrent [Hnode [Hid [Hgen [Hnone [Hhigh [Hnonempty [Hfocus [Hfragments
    [Hregion [Hgeometry [Hsp_range [Hpublication [Hlength [Hcpsr [Hlr [Hranges [Hmask [Hsp32
      [Hsp Haddress]]]]]]]]]]]]]]]]]]]].
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (kernel_call_execution_owned environment.(task_stack_call_external) environment.(task_stack_call_platform)
       call 192 ** UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
       state.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame)))
    by (unfold os_sched_source_switch_pre; entailer!) end.
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (armv7a_task_save_global_call _ _ _ abi task_abi sg state node call old_sp cpsr registers lr
    prefix suffix first old_words focus (unmap_table_rep sg ** frame) before Hcurrent Hnode Hid Hgen Hnone
    Hcoverage Hfocus Hfragments Hlength Hcpsr Hlr Hranges Hmask Hsp32 Hsp (Haddress _) Howned)
    as [written [stored [Hwrites [Hload [Hstore [Hcovered Hcapture]]]]]].
  fold fragments saved updated in Hstore, Hcovered, Hcapture.
  assert (Hsaved : os_sched_saved_stack_binding call fragments updated).
  { apply task_create_saved_context_binding with (node := node) (publication := publication); try assumption.
    unfold fragments; apply armv7a_task_frame_update_preserves_fragment_bounds with (old_words := old_words).
    rewrite <- Hfragments; exact Hgeometry. }
  assert (Hhigh_after : sched_high_ready_consistency updated.(TskState) updated.(SchedState)).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState SchedState].
    unfold sched_high_ready_consistency in *.
    destruct state.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
    destruct Hhigh as [Hhigh [high [Hlookup Hpriority]]]; split; [exact Hhigh|].
    destruct (Z.eqb head call.(os_sched_call_stack).(stackLeaseSlot)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst head; assert (high = node) by congruence; subst high.
      exists (task_set_saved_sp node saved.(armv7a_continuation_sp)); split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - exists high; split; [|exact Hpriority].
      cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Heq; exact Hlookup. }
  assert (Hnonempty_after : updated.(SchedState).(readyList) <> []).
  { unfold updated, os_sched_save_current_sp; rewrite Hnode; exact Hnonempty. }
  exists written, stored; split; [exact Hwrites|]. split; [exact Hload|]. split; [exact Hstore|].
  intros captured Hcaptured.
  destruct (Hcapture captured Hcaptured) as [Hmemory [Hsource Hcaptured_owned]].
  assert (Hvalid : UCOS2_state_inv sg updated).
  { match type of Hcaptured_owned with ?P captured =>
      assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg updated) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve captured Hcaptured_owned)). }
  split; [exact Hsource|]. split.
  - intros Hreleased.
    destruct (Hhistory Hreleased) as [_ [Hframe [Hactive Hname]]].
    split; [exact Hvalid|].
    unfold updated, os_sched_save_current_sp; rewrite Hnode; cbn [replace_TskS TskState NameState].
    split; [exact Hframe|]. split; [|exact Hname].
    intros origin Hlive; eapply task_set_saved_sp_preserves_invocation_active;
      [exact Hnode|apply Hactive; exact Hlive].
  - match type of Hcaptured_owned with ?P captured => match goal with |- ?Q captured =>
      assert (Hclose : P |-- Q) end end.
    { unfold task_tcb_init_switch_capture; fold abi focus; entailer!. }
    exact (Hclose captured Hcaptured_owned).
Qed.
