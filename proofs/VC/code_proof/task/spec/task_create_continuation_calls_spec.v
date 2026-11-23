Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The caller carries one descriptor-indexed resource family through its
    actual callees. It is not a state-preservation assumption. Unrelated
    parked entries retain their existing local owners at every boundary. *)
Definition task_create_continuation_without_running environment critical saved_local
  sg call mask state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
     environment.(task_stack_call_platform) call mask **
   critical_region_outside_without_running critical sg call.(os_sched_call_invocation) state **
   task_tcb_init_continuation_capsules environment saved_local state).

Definition task_create_continuation_init_input environment critical saved_local sg region args
  task_return lower old_frame upper call mask before : Assertion :=
  task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
  task_tcb_init_continuation_save_input environment critical saved_local sg call mask before.

(** This endpoint owns the current map and the initialized caller buffer.
    The pure entry/source observations concern the actual completed call;
    they do not assert that a later acquisition or return will occur. *)
Definition task_create_continuation_init_output environment critical saved_local sg region args
  task_return lower upper call mask before returned_sp : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      task_create_stack_init_entry_preserved sg args call before current /\
      task_tcb_init_stack_source_preserved call before current) &&
    (task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
       args.(createEntry) args.(createArgument) task_return (task_create_options args)
       lower upper returned_sp **
     task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current).

Lemma task_create_continuation_tcb_result_codes :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result,
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result |--
  coq_prop (result = 0 \/ result = 66) &&
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_continuation_call_post; Intros released.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name invocation origin initial result released) by assumption.
  assert (Hcodes : result = 0 \/ result = 66) by (inversion Hresult; auto).
  Exists released; entailer!.
Qed.

Lemma task_create_continuation_save_output_entry :
  forall environment critical saved_local sg args initial_name original mask saved before,
  task_create_stack_entry sg args initial_name original before ->
  task_tcb_init_continuation_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_create_stack_entry sg args initial_name original acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired) &&
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      returned saved acquired acquired.
Proof.
  intros environment critical saved_local sg args initial_name original mask saved before Hentry.
  unfold task_tcb_init_continuation_save_output; Intros returned acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    before acquired) by tauto.
  pose proof (task_create_stack_entry_after_call sg args initial_name original
    before acquired Hentry Hhistory) as Hacquired.
  pose proof (proj1 Hentry) as Hbefore.
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired) by tauto.
  Exists returned acquired.
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_stack_context; entailer!.
Qed.

(** The actual sixteen selected StackInit stores leave this callable world
    in their separation frame. An interrupted StackInit needs the separate
    IRQ source producer; no such trace is inferred from this local branch. *)
Lemma task_create_continuation_init_uninterrupted_output :
  forall environment critical saved_local sg region args task_return lower old_frame upper
    call mask state (frame : Assertion) before,
  (task_create_continuation_init_input environment critical saved_local sg region args task_return
     lower old_frame upper call mask state ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_init_no_vfp_writes args.(createStackTop)
      args.(createEntry) args.(createArgument) task_return) before after /\
    (task_create_continuation_init_output environment critical saved_local sg region args task_return
       lower upper call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** frame) after.
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper call mask state
    frame before Hbefore.
  assert (Horder : task_create_continuation_init_input environment critical saved_local sg region args
      task_return lower old_frame upper call mask state ** frame |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** frame)).
  { unfold task_create_continuation_init_input; entailer!. }
  destruct (task_stack_init_no_vfp_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower old_frame upper _ before (Horder before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  match type of Hafter with ?P after =>
    assert (Hpack : P |-- task_create_continuation_init_output environment critical saved_local sg
      region args task_return lower upper call mask state
      (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** frame)
  end.
  { unfold task_create_continuation_init_output; Exists call state.
    assert (Hentry : task_create_stack_init_entry_preserved sg args call state state)
      by (unfold task_create_stack_init_entry_preserved; auto).
    assert (Hsource : task_tcb_init_stack_source_preserved call state state)
      by apply task_tcb_init_stack_source_preserved_refl.
    unfold task_tcb_init_stack_same_call; entailer!. }
  exact (Hpack after Hafter).
Qed.

(** The post-store priority cell supplies the actual reservation update.
    Reservation changes neither the used-task/SP map nor parked payloads;
    reindexing preserves every existing descriptor and its local owner. *)
Lemma task_create_continuation_reservation_resources :
  forall environment saved_local sg args initial_name call acquired,
  task_create_stack_entry sg args initial_name call acquired ->
  task_priority_in_range sg args.(createPriority) ->
  acquired.(TskState).(prioTbl) args.(createPriority) = PTFree ->
  (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 1 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(createPriority) **
    UCOS2_raw_rep_missing_priority_table sg acquired **
    task_tcb_init_continuation_capsules environment saved_local acquired |--
  let reserved := replace_TskS (task_reserve acquired.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)) acquired in
  coq_prop (task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) reserved /\
    (forall observer, task_create_call_stage observer acquired ->
      task_create_call_stage observer reserved)) &&
  (UCOS2_inv sg reserved ** task_tcb_init_continuation_capsules environment saved_local reserved).
Proof.
  intros environment saved_local sg args initial_name call acquired
    [Hvalid [Hactive [Hempty Hname]]] Hpriority Hfree.
  cbv zeta.
  assert (Hguard : task_reserve_guard sg acquired.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)).
  { unfold task_reserve_guard; unfold task_invocation_active in Hactive; tauto. }
  pose proof (UCOS2_task_reserve_preserves_validity sg acquired args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) Hvalid Hguard) as Hpost.
  assert (Hentry : task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)
    (replace_TskS (task_reserve acquired.(TskState) args.(createPriority)
      call.(os_sched_call_invocation) call.(os_sched_call_origin)) acquired)).
  { unfold task_tcb_init_entry, task_tcb_init_pending.
    assert (Hprio : (task_tcb_init_stack_call_args args initial_name).(initPrio) = args.(createPriority)).
    { unfold task_tcb_init_stack_call_args, task_create_tcb_args; destruct args.(createExtension); reflexivity. }
    rewrite Hprio; split; [exact Hpost|]; split; [exact Hpriority|]; split; [exact Hactive|]; split.
    - cbn; destruct (Z.eq_dec args.(createPriority) args.(createPriority)); [reflexivity|contradiction].
    - exact Hname. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local acquired |--
    task_tcb_init_continuation_capsules environment saved_local
      (replace_TskS (task_reserve acquired.(TskState) args.(createPriority)
        call.(os_sched_call_invocation) call.(os_sched_call_origin)) acquired)).
  { unfold task_tcb_init_continuation_capsules; cbn [replace_TskS TskState].
    apply kernel_saved_continuation_map_used_map_eq; reflexivity. }
  sep_apply_l_atomic (UCOS2_inv_merge_reserved_priority sg acquired args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) Hvalid Hguard).
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

Lemma task_create_continuation_init_output_tcb_pre :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    original mask before returned_sp,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_create_continuation_init_output environment critical saved_local sg region args task_return
    lower upper original mask before returned_sp |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      returned_sp = task_stack_init_sp TaskStackNoVFP args.(createStackTop) /\
      task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) current /\
      task_tcb_init_stack_source_preserved original before current) &&
    task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
      lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
      mask current returned.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name original
    mask before returned_sp Hlayout Hentry.
  unfold task_create_continuation_init_output; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hpreserved : task_create_stack_init_entry_preserved sg args original before current) by tauto.
  pose proof (Hpreserved initial_name Hentry) as Hcurrent.
  sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args task_return
    lower upper returned_sp Hlayout).
  Intros; Exists returned current.
  unfold task_tcb_init_continuation_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre,
    task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned.
  destruct Hsame as [Hinvocation [Horigin Hstack]]; rewrite Hinvocation, Horigin; entailer!; tauto.
Qed.

(** TCBInit supplies both its actual publication history and its returned
    current world. No released map is retained through the final Restore. *)
Lemma task_create_continuation_tcb_success_source :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial,
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 0 |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original initial current) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial.
  unfold task_tcb_init_continuation_call_post; Intros released.
  assert (Hreleased : UCOS2_state_inv sg released) by tauto.
  assert (Hbefore : task_tcb_init_stack_source_preserved original initial released) by tauto.
  unfold task_tcb_init_continuation_call_return_post; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original)
    by (unfold task_tcb_init_stack_same_call; tauto).
  assert (Hrestore : task_tcb_init_stack_source_preserved original released current)
    by (unfold task_tcb_init_stack_return_preserved in *; tauto).
  pose proof (task_tcb_init_stack_source_preserved_trans original initial released current
    Hbefore Hrestore) as Hsource.
  Exists returned current.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_stack_buffer_result.
  destruct (Z.eq_dec 0 66); [discriminate|]. entailer!.
Qed.

(** A failed creation keeps the initialized buffer and the actual returned
    map. Only the lifecycle result is indexed by the released snapshot. *)
Lemma task_create_continuation_no_free_reacquire :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    original mask initial,
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
    mask initial original 66 |--
  EX released returned current,
    coq_prop (task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released /\
      task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      task_tcb_init_stack_return_preserved original released current) &&
    (task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current **
     task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper)).
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    original mask initial.
  unfold task_tcb_init_continuation_call_post; Intros released.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released)
    by assumption.
  assert (Hraw : task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released).
  { inversion Hresult; subst; assumption. }
  unfold task_tcb_init_continuation_call_return_post; Intros returned current.
  Exists released returned current.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_stack_same_call, task_tcb_init_stack_buffer_result.
  destruct (Z.eq_dec 66 66); [|contradiction].
  Intros; unfold task_tcb_init_stack_same_call in *; entailer!; tauto.
Qed.

Lemma task_create_continuation_save_output_no_free :
  forall environment critical saved_local sg args original checkpoint_call mask saved
    initial released checkpoint,
  task_tcb_init_stack_same_call checkpoint_call original ->
  task_tcb_init_call_result sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial 66 released ->
  UCOS2_state_inv sg checkpoint ->
  task_tcb_init_stack_return_preserved original released checkpoint ->
  task_tcb_init_continuation_save_output environment critical saved_local sg
    checkpoint_call mask saved checkpoint |--
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_return_preserved original released acquired /\
      task_rollback_guard acquired.(TskState) args.(initPrio) original.(os_sched_call_invocation) /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).
Proof.
  intros environment critical saved_local sg args original checkpoint_call mask saved initial released
    checkpoint Hsame Hresult Hcheckpoint Hprevious.
  pose proof Hsame as [Hinvocation [Horigin Hstack]].
  unfold task_tcb_init_continuation_save_output; Intros returned acquired.
  assert (Hlast : task_tcb_init_call_preserved sg checkpoint_call.(os_sched_call_invocation)
    checkpoint acquired) by tauto.
  rewrite Hinvocation in Hlast.
  destruct (Hlast Hcheckpoint) as [Hvalid [Hframe [Hactive Hname]]].
  assert (Hcheckpoint_source : task_tcb_init_stack_source_preserved checkpoint_call checkpoint acquired) by tauto.
  pose proof (task_create_stack_same_call_source_preserved _ _ _ _ Hsame Hcheckpoint_source) as Hordinary.
  assert (Hpreserved : task_tcb_init_stack_return_preserved original released acquired).
  { destruct Hprevious as [Hprevious_frame [Hprevious_active Hprevious_source]].
    split.
    - unfold task_creation_frame in *; congruence.
    - split; [intro Hlive; apply Hactive, Hprevious_active; exact Hlive|].
      eapply task_tcb_init_stack_source_preserved_trans; eassumption. }
  destruct (task_tcb_init_call_no_free_pending_agreement sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial released Hresult) as [_ [entry [Hentry [Hinv Hempty]]]].
  assert (Hguard : task_rollback_guard acquired.(TskState) args.(initPrio) original.(os_sched_call_invocation)).
  { exists entry; split; [|auto].
    eapply task_creation_frame_lookup; [exact (proj1 Hpreserved)|exact Hentry|exact Hinv]. }
  assert (Hreturned : task_tcb_init_stack_same_call returned checkpoint_call) by tauto.
  destruct Hreturned as [Hreturned_invocation [Hreturned_origin Hreturned_stack]].
  Exists returned acquired.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_context, UCOS2_inv.
  rewrite Hreturned_invocation, Hreturned_origin, Hinvocation, Horigin; entailer!; congruence.
Qed.

(** The real post-store NULL cell reconstructs the rollback world. This
    protected operation leaves every existing continuation/local pair in
    place; the following Restore must still produce its actual endpoint. *)
Lemma task_create_continuation_no_free_rollback_resources :
  forall environment (critical : CriticalRegionResources) saved_local sg args invocation origin
    initial released acquired,
  task_tcb_init_entry sg args invocation origin initial ->
  task_tcb_init_call_result sg args invocation origin initial 66 released ->
  UCOS2_state_inv sg acquired ->
  task_creation_frame invocation released.(TskState) acquired.(TskState) ->
  (task_invocation_active released.(TskState) invocation origin ->
    task_invocation_active acquired.(TskState) invocation origin) ->
  (sg.(g_OSTCBPrioTbl) + args.(initPrio) * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(initPrio) **
    UCOS2_raw_rep_missing_priority_table sg acquired **
    task_tcb_init_continuation_capsules environment saved_local acquired |--
  coq_prop (task_invocation_active
    (task_rollback_reservation acquired.(TskState) args.(initPrio)) invocation origin /\
    (forall observer, task_create_call_stage observer acquired ->
      task_create_call_stage observer
        (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired))) &&
  (UCOS2_inv sg
     (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired) **
   task_tcb_init_continuation_capsules environment saved_local
     (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired)).
Proof.
  intros environment critical saved_local sg args invocation origin initial released acquired
    Hentry Hresult Hvalid Hframe Hresume.
  assert (Hreleased : task_tcb_init_entry sg args invocation origin released).
  { inversion Hresult; subst; eapply task_tcb_init_call_preserves_entry; eassumption. }
  assert (Hactive : task_invocation_active acquired.(TskState) invocation origin).
  { apply Hresume; exact (proj1 (proj2 (proj2 Hreleased))). }
  destruct (task_tcb_init_call_no_free_pending_agreement sg args invocation origin
    initial released Hresult) as [_ [entry [Hlookup [Hinv Hempty]]]].
  assert (Hguard : task_rollback_guard acquired.(TskState) args.(initPrio) invocation).
  { exists entry; split; [|auto]. eapply task_creation_frame_lookup; eassumption. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local acquired |--
    task_tcb_init_continuation_capsules environment saved_local
      (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired)).
  { unfold task_tcb_init_continuation_capsules; cbn [replace_TskS TskState].
    apply kernel_saved_continuation_map_used_map_eq; reflexivity. }
  sep_apply_l_atomic (UCOS2_inv_merge_rollback_priority sg acquired args.(initPrio)
    invocation Hvalid Hguard).
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.
