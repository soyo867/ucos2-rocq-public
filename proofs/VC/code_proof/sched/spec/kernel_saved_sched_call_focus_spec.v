Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_sched_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Expose the distinguished invocation's own Save/inside pair while
    retaining its exact descriptor in the SAME focused map. Taking and
    reinserting one continuation does not allocate or duplicate stack
    bytes: the existing parked-map spatial resources are retained on the
    same heap. This view does not require a kernel-world premise. Registration, the
    live TCB/SP binding and saved mask all come from the exact entry.
    This conservative view is consumed by real foreign wait/return code. *)
Lemma kernel_saved_sched_call_focus_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired descriptor state,
  let focus := armv7a_call_focus original descriptor.(armv7a_continuation_pc)
    descriptor.(armv7a_continuation_lr) in
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
    state.(TskState).(parkedTaskStacks) |--
  coq_prop (armv7a_continuation_binding descriptor /\
    descriptor.(armv7a_continuation_call) = Some original /\
    armv7a_task_frame_slice descriptor /\ armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 /\
    original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) /\
    task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) /\
    task_saved_pointer_at state descriptor.(armv7a_continuation_stack) descriptor.(armv7a_continuation_sp)) &&
  (armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
   interrupt_platform_saved platform
     (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
   critical_region_inside critical sg original.(os_sched_call_invocation) acquired).
Proof.
  intros external platform port abi critical sg original saved acquired descriptor state focus Hlookup.
  sep_apply_l_atomic (kernel_saved_sched_call_take_resources external platform port abi critical sg original
    saved acquired descriptor state.(TskState) focus state.(TskState).(parkedTaskStacks)
    descriptor.(armv7a_continuation_fragments) Hlookup).
  unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec; [|contradiction].
  unfold kernel_saved_sched_call; Intros.
  assert (Hbinding : armv7a_continuation_binding descriptor) by tauto.
  assert (Hcall : descriptor.(armv7a_continuation_call) = Some original) by tauto.
  assert (Hlease : descriptor.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hslice : armv7a_task_frame_slice descriptor) by tauto.
  assert (Hsp : task_stack_live_sp state.(TskState) (task_stack_key original.(os_sched_call_stack))
    descriptor.(armv7a_continuation_sp)) by tauto.
  assert (Hactive : task_invocation_active state.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin)) by tauto.
  assert (Horigin : original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration)) by tauto.
  assert (Hpointer : task_saved_pointer_at state descriptor.(armv7a_continuation_stack)
    descriptor.(armv7a_continuation_sp)).
  { pose proof (proj2 (proj2 Hactive)) as Hlive; rewrite Horigin in Hlive.
    destruct Hlive as [node [Hnode Hgen]]. rewrite Hlease.
    exists node; split; [exact Hnode|]. split; [exact Hgen|]. apply Hsp; assumption. }
  assert (Hentry : armv7a_dormant_continuation abi descriptor |--
    armv7a_task_call_stack_entry abi state.(TskState) focus
      (task_stack_key original.(os_sched_call_stack))
      (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec; [|contradiction].
    Exists descriptor; unfold armv7a_continuation_focus_binding, focus, armv7a_call_focus;
      cbn [armv7a_focus_call armv7a_focus_pc armv7a_focus_lr]; entailer!; congruence. }
  sep_apply_l_atomic Hentry.
  unfold armv7a_task_call_stacks.
  sep_apply_l_atomic (store_parked_continuations_park (armv7a_task_call_stack_entry abi state.(TskState) focus)
    (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack))
    original.(os_sched_call_stack) descriptor.(armv7a_continuation_fragments)
    (task_stack_take_lookup _ _)).
  assert (Hmap : task_stack_park_fragments
    (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack))
    original.(os_sched_call_stack) descriptor.(armv7a_continuation_fragments) = state.(TskState).(parkedTaskStacks)).
  { extensionality key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct task_stack_key_eq_dec; [subst key; symmetry; exact Hlookup|reflexivity]. }
  rewrite Hmap; entailer!; tauto.
Qed.

(** Reassemble the original saved entry after a focused-map client trace.
    The trace transports registration, the payload and the actual TCB SP;
    the original Save/inside pair stays in its disjoint frame. The focus
    identifies call/PC/LR, while reading the SAME owned sixteen-word frame
    identifies CPSR and all registers. No execution permission is created
    from a pure descriptor, and the physical parked map is returned intact.
    The TaskCreate focused return consumer uses this view before the real
    selector/install/TaskRestore producer. *)
Lemma kernel_saved_sched_call_merge_focus_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) critical sg original saved acquired descriptor state,
  let focus := armv7a_call_focus original descriptor.(armv7a_continuation_pc)
    descriptor.(armv7a_continuation_lr) in
  armv7a_continuation_binding descriptor ->
  descriptor.(armv7a_continuation_call) = Some original ->
  armv7a_task_frame_slice descriptor ->
  descriptor.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_lr) ->
  armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = 192 ->
  original.(os_sched_call_origin) = RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_invocation_active state.(TskState) original.(os_sched_call_invocation) original.(os_sched_call_origin) ->
  task_saved_pointer_at state descriptor.(armv7a_continuation_stack) descriptor.(armv7a_continuation_sp) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) =
    Some (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments)) ->
  kernel_program_inv sg state **
  armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
  interrupt_platform_saved platform
    (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
  critical_region_inside critical sg original.(os_sched_call_invocation) acquired |--
  kernel_program_inv sg state ** store_parked_continuations
    (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
    state.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi critical sg original saved acquired descriptor state focus
    Hbinding Hcall Hslice Hpc Hmask Horigin Hactive Hpointer Hlookup.
  assert (Hlease : descriptor.(armv7a_continuation_stack) = original.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Hkey : task_stack_key original.(os_sched_call_stack) = armv7a_call_focus_key focus)
    by reflexivity.
  match goal with |- ?P |-- _ => assert (Htake : P |-- EX selected,
    coq_prop (UCOS2_state_inv sg state /\ armv7a_continuation_binding selected /\
      armv7a_continuation_focus_binding focus selected /\
      selected.(armv7a_continuation_stack) = descriptor.(armv7a_continuation_stack) /\
      selected.(armv7a_continuation_fragments) = descriptor.(armv7a_continuation_fragments) /\
      armv7a_task_frame_slice selected /\
      task_stack_live_sp state.(TskState) (task_stack_key original.(os_sched_call_stack))
        selected.(armv7a_continuation_sp)) &&
    (task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) **
     (armv7a_dormant_continuation abi selected **
      store_parked_stacks (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)) **
      armv7a_task_stack_continuations abi state.(TskState)
        (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)) **
      UCOS2_raw_rep_missing_parked_stacks sg state ** unmap_table_rep sg **
      interrupt_platform_saved platform
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired))) end.
  { rewrite kernel_program_inv_split_unmap, UCOS2_inv_split_parked_stacks; Intros.
    sep_apply_l_atomic (armv7a_task_call_stacks_take external platform port abi state.(TskState)
      focus state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)
      descriptor.(armv7a_continuation_fragments) Hlookup Hkey).
    Intros selected.
    assert (Hselected_lease : selected.(armv7a_continuation_stack) = original.(os_sched_call_stack)) by tauto.
    assert (Hfragments : selected.(armv7a_continuation_fragments) = descriptor.(armv7a_continuation_fragments)) by tauto.
    Exists selected; rewrite Hselected_lease, Hlease, Hfragments; entailer!; tauto. }
  intros heap Hpre.
  destruct (Htake heap Hpre) as [selected
    [[Hvalid [Hselected_binding [Hfocused [Hselected_lease [Hfragments [Hselected_slice Hlive]]]]]] Howned]].
  assert (Hsp : selected.(armv7a_continuation_sp) = descriptor.(armv7a_continuation_sp)).
  { destruct Hpointer as [node [Hnode [Hgen Hsp]]].
    rewrite Hlease in Hnode, Hgen.
    pose proof (Hlive node Hnode Hgen); congruence. }
  assert (Hreads : armv7a_continuation_restore_reads selected heap).
  { eapply armv7a_task_frame_slice_restore_reads; eassumption. }
  destruct (armv7a_same_frame_registers descriptor selected _ heap Hbinding Hslice
    Hselected_lease Hfragments Hsp Hreads Howned) as [Hcpsr Hregisters].
  assert (Hselected_call : selected.(armv7a_continuation_call) = descriptor.(armv7a_continuation_call)).
  { unfold armv7a_continuation_focus_binding, focus, armv7a_call_focus in Hfocused;
      cbn in Hfocused; rewrite Hcall; exact (proj1 Hfocused). }
  assert (Hselected_pc : selected.(armv7a_continuation_pc) = descriptor.(armv7a_continuation_pc)).
  { unfold armv7a_continuation_focus_binding, focus, armv7a_call_focus in Hfocused; cbn in Hfocused; tauto. }
  assert (Hselected_lr : selected.(armv7a_continuation_lr) = descriptor.(armv7a_continuation_lr)).
  { unfold armv7a_continuation_focus_binding, focus, armv7a_call_focus in Hfocused; cbn in Hfocused; tauto. }
  assert (Hequal : selected = descriptor).
  { destruct selected, descriptor; cbn in Hselected_call, Hselected_lease, Hfragments,
      Hsp, Hcpsr, Hregisters, Hselected_pc, Hselected_lr; congruence. }
  subst selected.
  assert (Hnone : task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)
    (armv7a_call_focus_key focus) = None) by apply task_stack_take_lookup.
  assert (Hentry : armv7a_dormant_continuation abi descriptor **
      interrupt_platform_saved platform
        (save_token saved original.(os_sched_call_invocation) original.(os_sched_call_origin)) **
      critical_region_inside critical sg original.(os_sched_call_invocation) acquired |--
    kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus
      (task_stack_key original.(os_sched_call_stack))
      (original.(os_sched_call_stack).(stackLeaseRegion), descriptor.(armv7a_continuation_fragments))).
  { unfold kernel_saved_sched_call_entry; destruct task_stack_key_eq_dec; [|contradiction].
    unfold kernel_saved_sched_call; rewrite Hlease; entailer!. }
  assert (Hmap : task_stack_park_fragments
    (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack))
    original.(os_sched_call_stack) descriptor.(armv7a_continuation_fragments) = state.(TskState).(parkedTaskStacks)).
  { extensionality key; unfold task_stack_park_fragments, task_stack_take, field_update.
    destruct task_stack_key_eq_dec; [subst key; symmetry; exact Hlookup|reflexivity]. }
  match type of Howned with ?P heap => match goal with |- ?Q heap => assert (Hmerge : P |-- Q) end end.
  { sep_apply_l_atomic (armv7a_task_call_stacks_absent external platform port abi state.(TskState) focus
      (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)) Hnone).
    sep_apply_l_atomic (kernel_saved_sched_call_map_absent external platform port abi critical sg original
      saved acquired descriptor state.(TskState) focus
      (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack)) Hnone).
    sep_apply_l_atomic Hentry.
    sep_apply_l_atomic (store_parked_continuations_park
      (kernel_saved_sched_call_entry abi critical sg original saved acquired descriptor state.(TskState) focus)
      (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack))
      original.(os_sched_call_stack) descriptor.(armv7a_continuation_fragments) Hnone).
    rewrite Hlease.
    sep_apply_l_atomic (store_parked_stacks_park_fragments
      (task_stack_take state.(TskState).(parkedTaskStacks) original.(os_sched_call_stack))
      original.(os_sched_call_stack) descriptor.(armv7a_continuation_fragments) Hnone).
    rewrite Hmap, kernel_program_inv_split_unmap, UCOS2_inv_split_parked_stacks; entailer!. }
  exact (Hmerge heap Howned).
Qed.
