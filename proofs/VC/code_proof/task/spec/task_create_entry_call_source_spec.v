Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_context_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_lease_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_modular_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Consume the packet already established by register_entry,
    selected_initial_entry, or sequential_entry. Normalization keeps its
    source stage and available running-stack key at this SAME entry state.
    These observations are not declared invariant of intermediate calls.
    The old public pre is unchanged.

    The returned two pure facts are exactly the inputs of the existing
    [task_create_first_save_current_source]. Thus that actual Save-post
    consumer can be used without a caller-supplied current assumption.
    Boot continues through its independent existing entry/Save consumer. *)
Lemma task_create_source_entry_normalized_pre :
  forall environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial slot generation,
  task_create_source_entry sg args name original initial ->
  original.(os_sched_call_origin) = RunningInvocation slot generation ->
  task_create_continuation_pre environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial |--
  EX normalized,
    coq_prop (os_sched_execution_view normalized = os_sched_execution_view original /\
      task_stack_call_active_key normalized = task_stack_call_active_key original /\
      task_create_stack_entry sg args name normalized initial /\
      kernel_call_task_source normalized initial /\
      task_create_source_entry sg args name normalized initial /\
      kernel_call_stack_available normalized initial) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name normalized mask initial.
Proof.
  intros environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial slot generation Hentry Horigin.
  assert (Hcurrent : task_execution_current original.(os_sched_call_origin) initial).
  { pose proof (proj1 (proj2 Hentry)) as Hcall.
    unfold task_create_call_origin in Hcall; rewrite Horigin in Hcall.
    unfold task_execution_current; rewrite Horigin; exact (proj1 (proj2 Hcall)). }
  sep_apply_l_atomic (task_create_continuation_pre_normalize_lease
    environment critical saved_local sg region args task_return lower old_frame upper
    name original mask initial slot generation Horigin).
  Intros normalized.
  assert (Hview : os_sched_execution_view normalized = os_sched_execution_view original)
    by tauto.
  assert (Hsource : kernel_call_task_source normalized initial) by tauto.
  pose proof (f_equal os_execution_invocation Hview) as Hi.
  pose proof (f_equal os_execution_origin Hview) as Ho.
  change (normalized.(os_sched_call_invocation) = original.(os_sched_call_invocation)) in Hi.
  change (normalized.(os_sched_call_origin) = original.(os_sched_call_origin)) in Ho.
  assert (Hnormalized_entry : task_create_stack_entry sg args name normalized initial).
  { unfold task_create_stack_entry; rewrite Hi, Ho; exact (proj1 Hentry). }
  assert (Hnormalized_stage : task_create_call_stage normalized initial).
  { destruct (proj2 Hentry) as [Hcall Hstage].
    unfold task_create_call_stage; rewrite Ho; split; [exact Hcall|].
    rewrite Horigin; rewrite Horigin in Hstage.
    destruct Hstage as [Horiginal_slot [Horiginal_generation [Habsent Hready]]].
    assert (Hnormalized_slot : normalized.(os_sched_call_stack).(stackLeaseSlot) = slot)
      by tauto.
    assert (Hnormalized_generation : normalized.(os_sched_call_stack).(stackLeaseGeneration) = generation)
      by tauto.
    split; [symmetry; exact Hnormalized_slot|].
    split; [symmetry; exact Hnormalized_generation|]. split; [|exact Hready].
    unfold task_stack_key in *.
    rewrite Hnormalized_slot, Hnormalized_generation.
    rewrite <- Horiginal_slot, <- Horiginal_generation in Habsent; exact Habsent. }
  assert (Hnormalized_source_entry : task_create_source_entry sg args name normalized initial)
    by (split; assumption).
  assert (Havailable : kernel_call_stack_available normalized initial).
  { pose proof (proj2 Hnormalized_stage) as Hstage.
    rewrite Ho, Horigin in Hstage.
    destruct Hstage as [Hslot [Hgeneration [Habsent Hready]]].
    unfold kernel_call_stack_available; rewrite Ho, Horigin.
    unfold task_stack_key in Habsent.
    rewrite <- Hslot, <- Hgeneration in Habsent; exact Habsent. }
  Exists normalized; entailer!.
Qed.

(** One concrete producer-to-consumer path: the existing selected initial
    entry uses the actual installed current/node and restored execution
    owner, registers the call, then normalizes its redundant lease fields.
    The same generic map and real caller buffer are retained. This does
    not claim that an arbitrary weak public pre supplies the source packet. *)
Lemma task_create_selected_initial_normalized_pre :
  forall environment
    (entry : Armv7aInitialCallABI environment.(task_stack_call_external)
      environment.(task_stack_call_platform) environment.(task_stack_call_port)
      environment.(task_stack_call_continuations))
    critical saved_local sg args name selected node state
    region task_return lower old_frame upper,
  state.(SchedState).(isRunning) = true ->
  armv7a_initial_frame_binding selected ->
  task_stack_fragments_in_range selected.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) 0
    selected.(armv7a_continuation_fragments) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key selected.(armv7a_continuation_stack)) = None ->
  sched_current_ready_at state.(TskState) state.(SchedState)
    selected.(armv7a_continuation_stack).(stackLeaseSlot) node ->
  node.(taskGeneration) = selected.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  armv7a_task_restored_execution environment.(task_stack_call_external)
    environment.(task_stack_call_platform) environment.(task_stack_call_port)
    environment.(task_stack_call_continuations) selected **
  kernel_continuation_inv environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg
    (Some (task_stack_key selected.(armv7a_continuation_stack))) state **
  task_stack_storage region (lower ++ old_frame ++ upper) |--
  let call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments) in
  let registered := armv7a_initial_call_registered selected state in
  EX normalized,
    coq_prop (os_sched_execution_view normalized = os_sched_execution_view call /\
      task_stack_call_active_key normalized = task_stack_call_active_key call /\
      task_create_stack_entry sg args name normalized registered /\
      kernel_call_task_source normalized registered /\
      task_create_source_entry sg args name normalized registered /\
      kernel_call_stack_available normalized registered) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name normalized
      (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered.
Proof.
  intros environment entry critical saved_local sg args name selected node state
    region task_return lower old_frame upper Hrunning Hbinding Hfragments Habsent
    Hready Hgeneration Hname Hbuffer.
  cbv zeta.
  set (call := armv7a_initial_call selected state.(TskState).(taskLifecycle).(taskNextInvocation)
    selected.(armv7a_continuation_fragments)).
  set (registered := armv7a_initial_call_registered selected state).
  pose proof (task_create_continuation_selected_initial_entry_pre environment entry critical
    saved_local sg args name selected node state region task_return lower old_frame upper
    Hrunning Hbinding Hfragments Habsent Hready Hgeneration Hname Hbuffer) as Hentry.
  cbv zeta in Hentry; fold call registered in Hentry.
  eapply derivable1_trans; [exact Hentry|].
  Intros.
  apply (task_create_source_entry_normalized_pre environment critical saved_local
    sg region args task_return lower old_frame upper name call
    (armv7a_irq_fiq_mask selected.(armv7a_continuation_cpsr)) registered
    selected.(armv7a_continuation_stack).(stackLeaseSlot)
    selected.(armv7a_continuation_stack).(stackLeaseGeneration)).
  - assumption.
  - reflexivity.
Qed.

(** The actual successful OS_TCBInit post, not a future-return premise,
    is consumed at TaskCreate's completed TCB call. [Hinitial] is produced
    above; [Hprefix] is the source-preserved fact already carried by the
    canonical first Save, priority reservation, Restore and StackInit
    assertions (which_implies_6/7/8). Their same-call indices select this
    precise TCB call. Its post supplies the remaining source transport.

    [Haddress] is the existing named-C-field/selected-port layout bridge,
    kept separate from current identity. No new platform guarantee is
    assumed. The conclusion provides the Scheduler's current-storage
    component, not its destination, taken-key, readiness, or total return.
    The actual OSRunning guard still controls whether OS_Sched is called. *)
Lemma task_create_tcb_success_sched_storage :
  forall environment critical saved_local sg region args task_return lower upper name
    original initial tcb_call mask tcb_initial,
  kernel_call_task_source original initial ->
  task_tcb_init_stack_same_call tcb_call original ->
  task_tcb_init_stack_source_preserved original initial tcb_initial ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper name original.(os_sched_call_invocation) original.(os_sched_call_origin)
    mask tcb_initial tcb_call 0 ** unmap_table_rep sg |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current /\
      os_sched_current_storage_binding sg returned current) &&
    os_sched_continuation_pre environment saved_local kernel_program_inv sg returned mask current.
Proof.
  intros environment critical saved_local sg region args task_return lower upper name
    original initial tcb_call mask tcb_initial Hinitial Hsame Hprefix Haddress.
  assert (Htcb : kernel_call_task_source tcb_call tcb_initial).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff tcb_call original tcb_initial Hsame)).
    apply Hprefix; exact Hinitial. }
  sep_apply_l_atomic (task_create_modular_tcb_success_sched_input
    environment critical saved_local sg region args task_return lower upper name
    original.(os_sched_call_invocation) original.(os_sched_call_origin)
    tcb_call mask tcb_initial Htcb).
  Intros returned current.
  assert (Hreturned : task_tcb_init_stack_same_call returned tcb_call) by tauto.
  assert (Hsource : kernel_call_task_source returned current) by tauto.
  assert (Hsame_original : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hobserve :
    os_sched_continuation_pre environment saved_local kernel_program_inv sg returned mask current |--
    coq_prop (UCOS2_state_inv sg current) &&
    os_sched_continuation_pre environment saved_local kernel_program_inv sg returned mask current).
  { unfold os_sched_continuation_pre, kernel_continuation_call_closed,
      kernel_continuation_inv, kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg current) by assumption.
  destruct (kernel_call_task_source_current_at returned current Hsource)
    as [Hcurrent [node [Hnode Hgeneration]]].
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  destruct Htasks as [Hpool [Hclosure Hrest]].
  assert (Hrange : task_slot_in_range sg returned.(os_sched_call_stack).(stackLeaseSlot)).
  { apply (proj2 (proj1 Hpool returned.(os_sched_call_stack).(stackLeaseSlot))).
    left; exists node; exact Hnode. }
  destruct Hclosure as [Hnodup [Hhead [Hcount [Hmembership Hlinks]]]].
  assert (Hin : In returned.(os_sched_call_stack).(stackLeaseSlot)
    current.(TskState).(taskLifecycle).(taskActiveOrder)).
  { apply (proj2 (Hmembership _)); exists node; exact Hnode. }
  assert (Hlookup_id : forall ids previous,
    task_active_links current.(TskState).(inUsedTaskStates) previous ids ->
    In returned.(os_sched_call_stack).(stackLeaseSlot) ids ->
    node.(taskID) = returned.(os_sched_call_stack).(stackLeaseSlot)).
  { intro ids; induction ids as [|head tail IH]; intros previous Hactive Hin';
      [contradiction|].
    destruct Hactive as [first [Hfirst [Hid [_ [_ Htail]]]]].
    destruct Hin' as [Heq|Hin'].
    - rewrite Heq in Hfirst, Hid.
      assert (Hfirst_eq : first = node) by congruence.
      rewrite Hfirst_eq in Hid; exact Hid.
    - exact (IH (Some head) Htail Hin'). }
  assert (Hbinding : os_sched_current_storage_binding sg returned current).
  { unfold os_sched_current_storage_binding; cbv zeta.
    split; [exact (proj1 Hsource)|]. split; [exact Hcurrent|].
    split; [exact Hrange|]. split.
    - rewrite (proj2 (proj2 Hsame_original)); exact Haddress.
    - left; exists node; split; [exact Hnode|].
      split; [exact (Hlookup_id _ None Hlinks Hin)|exact Hgeneration]. }
  Exists returned current; entailer!.
Qed.
