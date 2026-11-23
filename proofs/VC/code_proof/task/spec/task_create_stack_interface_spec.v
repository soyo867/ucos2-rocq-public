Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This invocation has not started another allocation. This is its actual
    entry-stage ownership fact, not readiness or future stack coverage. *)
Definition task_create_stack_no_reservation (state : UCOS2_Verify_State) (invocation : nat) : Prop :=
  forall priority entry,
    state.(TskState).(taskLifecycle).(taskReservations) priority = Some entry ->
    entry.(creationInvocation) <> invocation.

Definition task_create_stack_entry sg args initial_name call state : Prop :=
  UCOS2_state_inv sg state /\
  task_invocation_active state.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin) /\
  task_create_stack_no_reservation state call.(os_sched_call_invocation) /\
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args initial_name) state.

Definition task_create_stack_arguments (args : TaskCreateArgs) (entry argument top priority : addr) : Prop :=
  args.(createExtension) = TaskCreateBasic /\ args.(createEntry) = entry /\
  args.(createArgument) = argument /\ args.(createStackTop) = top /\ args.(createPriority) = priority.

Definition task_create_stack_old_image (lower old_frame upper : list (option Z)) :=
  lower ++ old_frame ++ upper.

Definition task_create_stack_global_addresses (sg : StableGlobVars)
  (nesting priorities running : addr) : Prop :=
  sg.(g_OSIntNesting) = nesting /\ sg.(g_OSTCBPrioTbl) = priorities /\ sg.(g_OSRunning) = running.

Definition task_create_stack_nesting state := state.(IntrState).(intNesting).
Definition task_create_stack_running state : Z :=
  if state.(SchedState).(isRunning) then 1 else 0.
Definition task_create_stack_priority sg args state :=
  prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) args.(createPriority)).
Definition task_create_stack_reserved args call state :=
  replace_TskS (task_reserve state.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)) state.

Lemma task_create_stack_reserve_preserves_call_source : forall args call state observer,
  kernel_call_task_source observer state ->
  kernel_call_task_source observer (task_create_stack_reserved args call state).
Proof.
  intros args call state observer [Horigin [Hactive Hcurrent]].
  split; [exact Horigin|]. split; [|exact Hcurrent].
  unfold task_invocation_active, task_invocation_origin_live in *.
  destruct observer.(os_sched_call_origin); exact Hactive.
Qed.

Lemma task_create_stack_same_call_source_preserved : forall returned original before after,
  task_tcb_init_stack_same_call returned original ->
  task_tcb_init_stack_source_preserved returned before after ->
  task_tcb_init_stack_source_preserved original before after.
Proof.
  intros returned original before after Hsame Hpreserved Hsource.
  apply (proj1 (task_tcb_init_stack_same_call_source_iff returned original after Hsame)).
  apply Hpreserved.
  apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original before Hsame)); exact Hsource.
Qed.
Definition task_create_stack_rolled_back args state :=
  replace_TskS (task_rollback_reservation state.(TskState) args.(createPriority)) state.
Definition task_create_stack_without_nesting sg state : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
  (interrupt_inv_no_int_nesting sg state.(IntrState) ** UCOS2_raw_rep_missing_interrupt sg state).

Definition task_create_stack_without_priority sg args state : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
  (store_prio_tbl_missing_i sg state.(TskState).(prioTbl) args.(createPriority) **
   UCOS2_raw_rep_missing_priority_table sg state).

Definition task_create_stack_without_running environment critical sg call mask state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
  (kernel_call_execution_owned environment.(task_stack_call_external)
    environment.(task_stack_call_platform) call mask **
  critical_region_outside_without_running critical sg call.(os_sched_call_invocation) state **
  task_tcb_init_stack_capsules environment state).

(** The result/release history is pure; this assertion wrapper keeps its
    indices together at the two source-level acquisition cuts. It does not
    own or produce any kernel cell. *)
Definition task_create_stack_no_free_history (critical : CriticalRegionResources) sg args initial_name original
  initial released current : Assertion :=
  coq_prop (task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial /\
    task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released /\
    UCOS2_state_inv sg current /\
    task_tcb_init_stack_return_preserved original released current) && emp.

Definition task_create_stack_buffer_domain region args task_return
  (lower old_frame upper : list (option Z)) : Prop :=
  task_create_stack_layout TaskStackNoVFP region args lower upper /\ Zlength old_frame = 16 /\
  0 <= args.(createEntry) < 4294967296 /\ 0 <= args.(createArgument) < 4294967296 /\
  0 <= task_return < 4294967296.

Definition task_create_stack_pre environment critical sg region args task_return lower old_frame upper
  initial_name call mask initial : Assertion :=
  coq_prop (task_create_stack_entry sg args initial_name call initial /\
    task_create_stack_buffer_domain region args task_return lower old_frame upper) &&
  (task_tcb_init_stack_save_input environment critical sg call mask initial **
   task_stack_storage region (lower ++ old_frame ++ upper) ** unmap_table_rep sg).

(** StackInit owns the caller's buffer and the actual open-call world.
    Its source contract returns a new checkpoint, never a frame claiming
    that the entry world/map survived an arbitrary interrupt unchanged. *)
Definition task_create_stack_init_input environment critical sg region args task_return
  lower old_frame upper call mask before : Assertion :=
  task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
  task_tcb_init_stack_save_input environment critical sg call mask before.

(** StackInit must preserve this invocation's actual next TCBInit entry,
    not replay a flat kernel-client history across IRQ stack save/take.
    [initial_name] is ghost caller data, not a StackInit C argument. This
    relation transports only an entry that already held for these creation
    arguments; the source producer must establish it, not the caller assume
    a future acquire or a desired public return. Current physical ownership
    and stack bytes remain separate components of the output below. *)
Definition task_create_stack_init_entry_preserved sg args call before after : Prop :=
  forall initial_name,
    task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
      call.(os_sched_call_invocation) call.(os_sched_call_origin) before ->
    task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
      call.(os_sched_call_invocation) call.(os_sched_call_origin) after.

Definition task_create_stack_init_output environment critical sg region args task_return
  lower upper call mask before returned_sp : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned call /\
      task_create_stack_init_entry_preserved sg args call before current /\
      task_tcb_init_stack_source_preserved call before current) &&
    (task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
       args.(createEntry) args.(createArgument) task_return (task_create_options args)
       lower upper returned_sp **
     task_tcb_init_stack_save_input environment critical sg returned mask current).

Definition task_create_stack_failure_buffer region args task_return lower old_frame upper
  (initialized : bool) : Assertion :=
  task_stack_storage region
    (if initialized then task_create_stack_image TaskStackNoVFP args task_return lower upper
     else lower ++ old_frame ++ upper).

(** This resource post does not promise that a newly created child is still
    alive or ready at return. Error paths retain their actual original or
    initialized buffer; successful publication transfers it to the kernel. *)
Definition task_create_stack_post environment critical sg region args task_return lower old_frame upper
  original mask result : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      (result = 0 \/ result = 40 \/ result = 42 \/ result = 60 \/ result = 66)) &&
    (task_tcb_init_stack_save_input environment critical sg returned mask current **
     unmap_table_rep sg **
     (if Z.eq_dec result 0 then emp else
       EX initialized, task_create_stack_failure_buffer region args task_return lower old_frame upper initialized)).

Lemma task_create_stack_tcb_result_codes :
  forall environment critical sg region args task_return lower upper initial_name
    invocation origin mask initial original result,
  task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
    invocation origin mask initial original result |--
  coq_prop (result = 0 \/ result = 66) &&
  task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
    invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_stack_call_post; Intros released.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name invocation origin initial result released) by assumption.
  assert (Hcodes : result = 0 \/ result = 66) by (inversion Hresult; auto).
  Exists released; entailer!.
Qed.

Lemma task_create_stack_entry_after_call :
  forall sg args initial_name call before after,
  task_create_stack_entry sg args initial_name call before ->
  task_tcb_init_call_preserved sg call.(os_sched_call_invocation) before after ->
  task_create_stack_entry sg args initial_name call after.
Proof.
intros sg args initial_name call before after [Hvalid [Hactive [Hempty Hname]]] Hpreserved.
  destruct (Hpreserved Hvalid) as [Hafter [Hframe [Hresume Hnames]]].
  split; [exact Hafter|]; split; [apply Hresume; exact Hactive|]; split.
  - intros priority entry Hentry Hequal.
    assert (Hreverse : task_creation_frame call.(os_sched_call_invocation) after.(TskState) before.(TskState)).
    { unfold task_creation_frame in *; symmetry; exact Hframe. }
    apply (Hempty priority entry).
    + eapply task_creation_frame_lookup; eassumption.
    + exact Hequal.
  - unfold task_tcb_init_name_valid in *; rewrite <- Hnames; exact Hname.
Qed.

Lemma task_create_stack_save_output_entry :
  forall environment critical sg args initial_name original mask saved before,
  task_create_stack_entry sg args initial_name original before ->
  task_tcb_init_stack_save_output environment critical sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_create_stack_entry sg args initial_name original acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired) &&
    task_tcb_init_stack_restore_input environment critical sg returned saved acquired acquired.
Proof.
intros environment critical sg args initial_name original mask saved before Hentry.
  unfold task_tcb_init_stack_save_output; Intros returned acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    before acquired) by tauto.
  pose proof (task_create_stack_entry_after_call sg args initial_name original
    before acquired Hentry Hhistory) as Hacquired.
  pose proof (proj1 Hentry) as Hbefore.
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired) by tauto.
  Exists returned acquired.
  unfold task_tcb_init_stack_restore_input, task_tcb_init_stack_context, task_tcb_init_stack_capsules; entailer!.
Qed.

Lemma task_create_stack_inv_split_nesting : forall sg state,
  UCOS2_inv sg state --||--
    (sg.(g_OSIntNesting) # UChar |-> task_create_stack_nesting state **
     task_create_stack_without_nesting sg state).
Proof.
  intros sg state; rewrite UCOS2_inv_split_interrupt.
  unfold task_create_stack_nesting, task_create_stack_without_nesting,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state; split; entailer!.
Qed.

Lemma task_create_stack_priority_zero_is_free : forall sg args state,
  UCOS2_state_inv sg state -> task_priority_in_range sg args.(createPriority) ->
  task_create_stack_priority sg args state = 0 ->
  state.(TskState).(prioTbl) args.(createPriority) = PTFree.
Proof.
  intros sg args state Hvalid Hpriority Hzero.
  pose proof (proj1 (proj1 Hvalid)) as Hstable.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Hvalid))))) as Hcross.
  unfold task_create_stack_priority in Hzero.
  destruct (state.(TskState).(prioTbl) args.(createPriority)) as [| |tid] eqn:Hslot;
    [reflexivity|discriminate|].
  exfalso.
  pose proof (proj1 (proj2 (proj1 Hcross)) args.(createPriority) Hpriority) as Hlive.
  rewrite Hslot in Hlive; destruct Hlive as [node Hnode].
  assert (Hrange : task_slot_in_range sg tid).
  { apply (proj2 (proj1 (proj1 Htasks) tid)); left; exists node; exact Hnode. }
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable) as Hbase.
  assert (Hin : In sg.(g_OSTCBTbl) (stable_global_addresses sg))
    by (unfold stable_global_addresses; simpl; tauto).
  specialize (Hbase Hin).
  unfold prio_tbl_entry_to_addr, task_slot_addr, tcb_configured_size, tcb_layout_size in Hzero.
  unfold task_slot_in_range in Hrange.
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled), sg.(osKernelConfig).(cfgTaskProfile); lia.
Qed.

(** This branch is genuinely the sixteen selected StackInit stores with no
    intervening IRQ. It establishes the new call interface by consuming the
    existing source producer. A general interrupted call still requires the
    actual handler heap registry; it is not inferred from this branch. *)
Lemma task_create_stack_init_uninterrupted_output :
  forall environment critical sg region args task_return lower old_frame upper call mask state
    (frame : Assertion) before,
  (task_create_stack_init_input environment critical sg region args task_return
     lower old_frame upper call mask state ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_init_no_vfp_writes args.(createStackTop)
      args.(createEntry) args.(createArgument) task_return) before after /\
    (task_create_stack_init_output environment critical sg region args task_return lower upper
       call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** frame) after.
Proof.
  intros environment critical sg region args task_return lower old_frame upper call mask state
    frame before Hbefore.
  assert (Horder : task_create_stack_init_input environment critical sg region args task_return
      lower old_frame upper call mask state ** frame |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_stack_save_input environment critical sg call mask state ** frame)).
  { unfold task_create_stack_init_input; entailer!. }
  destruct (task_stack_init_no_vfp_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower old_frame upper _ before (Horder before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  match type of Hafter with ?P after =>
    assert (Hpack : P |-- task_create_stack_init_output environment critical sg region args task_return
      lower upper call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** frame)
  end.
  { unfold task_create_stack_init_output; Exists call state.
    assert (Hentry : task_create_stack_init_entry_preserved sg args call state state)
      by (unfold task_create_stack_init_entry_preserved; auto).
    assert (Hsource : task_tcb_init_stack_source_preserved call state state)
      by apply task_tcb_init_stack_source_preserved_refl.
    unfold task_tcb_init_stack_same_call; entailer!. }
  exact (Hpack after Hafter).
Qed.

Lemma task_create_stack_reservation_resources :
  forall environment sg args initial_name call acquired,
  task_create_stack_entry sg args initial_name call acquired ->
  task_priority_in_range sg args.(createPriority) ->
  acquired.(TskState).(prioTbl) args.(createPriority) = PTFree ->
  (sg.(g_OSTCBPrioTbl) + args.(createPriority) * sizeof(PTR)) # Ptr |-> 1 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(createPriority) **
    UCOS2_raw_rep_missing_priority_table sg acquired **
    task_tcb_init_stack_capsules environment acquired |--
  let reserved := replace_TskS (task_reserve acquired.(TskState) args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin)) acquired in
  coq_prop (task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) reserved) &&
  (UCOS2_inv sg reserved ** task_tcb_init_stack_capsules environment reserved).
Proof.
  intros environment sg args initial_name call acquired [Hvalid [Hactive [Hempty Hname]]] Hpriority Hfree.
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
  sep_apply_l_atomic (UCOS2_inv_merge_reserved_priority sg acquired args.(createPriority)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) Hvalid Hguard).
  unfold task_tcb_init_stack_capsules; cbn [replace_TskS task_reserve]; entailer!.
Qed.

Lemma task_create_stack_init_output_tcb_pre :
  forall environment critical sg region args task_return lower upper initial_name
    original mask before returned_sp,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_create_stack_init_output environment critical sg region args task_return lower upper
    original mask before returned_sp |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      returned_sp = task_stack_init_sp TaskStackNoVFP args.(createStackTop) /\
      task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) current /\
      task_tcb_init_stack_source_preserved original before current) &&
    task_tcb_init_stack_call_pre environment critical sg region args task_return lower upper initial_name
      original.(os_sched_call_invocation) original.(os_sched_call_origin) mask current returned.
Proof.
  intros environment critical sg region args task_return lower upper initial_name original mask before
    returned_sp Hlayout Hentry.
  unfold task_create_stack_init_output; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hpreserved : task_create_stack_init_entry_preserved sg args original before current)
    by tauto.
  pose proof (Hpreserved initial_name Hentry) as Hcurrent.
  sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args task_return
    lower upper returned_sp Hlayout).
  Intros; Exists returned current.
  unfold task_tcb_init_stack_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre,
    task_tcb_init_stack_save_input, kernel_call_execution_owned.
  destruct Hsame as [Hinvocation [Horigin Hstack]]; rewrite Hinvocation, Horigin; entailer!; tauto.
Qed.

(** Consume TCBInit's proved conditional source post AND its actual final
    Restore source. The released validity is retained by the callee; no
    whole entry map or ready fact is transported across that return. *)
Lemma task_create_stack_tcb_success_source :
  forall environment critical sg region args task_return lower upper initial_name
    invocation origin original mask initial,
  task_tcb_init_stack_call_post environment critical sg region args task_return lower upper initial_name
    invocation origin mask initial original 0 |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original initial current) &&
    task_tcb_init_stack_save_input environment critical sg returned mask current.
Proof.
  intros environment critical sg region args task_return lower upper initial_name
    invocation origin original mask initial.
  unfold task_tcb_init_stack_call_post; Intros released.
  assert (Hreleased : UCOS2_state_inv sg released) by tauto.
  assert (Hbefore : task_tcb_init_stack_source_preserved original initial released) by tauto.
  unfold task_tcb_init_stack_call_return_post; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original)
    by (unfold task_tcb_init_stack_same_call; tauto).
  assert (Hrestore : task_tcb_init_stack_source_preserved original released current)
    by (unfold task_tcb_init_stack_return_preserved in *; tauto).
  pose proof (task_tcb_init_stack_source_preserved_trans original initial released current
    Hbefore Hrestore) as Hsource.
  Exists returned current.
  unfold task_tcb_init_stack_save_input, task_tcb_init_stack_buffer_result, task_tcb_init_stack_capsules.
  destruct (Z.eq_dec 0 66); [discriminate|]. entailer!.
Qed.

(** The basic caller's failed-create trace is empty in the selected original
    header. Its next external operation is Save. Consume the ACTUAL TCBInit
    return owners at that source cut; the no-free released snapshot supplies
    lifecycle history only. In particular, no released capsule map is kept. *)
Lemma task_create_stack_no_free_reacquire :
  forall environment critical sg region args task_return lower upper initial_name
    original mask initial,
  task_tcb_init_stack_call_post environment critical sg region args task_return
    lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
    mask initial original 66 |--
  EX released returned current,
    coq_prop (task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released /\
      task_tcb_init_stack_same_call returned original /\
      UCOS2_state_inv sg current /\
      task_tcb_init_stack_return_preserved original released current) &&
    (task_tcb_init_stack_save_input environment critical sg returned mask current **
     task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper)).
Proof.
  intros environment critical sg region args task_return lower upper initial_name original mask initial.
  unfold task_tcb_init_stack_call_post; Intros released.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released)
    by assumption.
  assert (Hraw : task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released).
  { inversion Hresult; subst; assumption. }
  unfold task_tcb_init_stack_call_return_post; Intros returned current.
  Exists released returned current.
  unfold task_tcb_init_stack_save_input, task_tcb_init_stack_same_call,
    task_tcb_init_stack_buffer_result; destruct (Z.eq_dec 66 66); [|contradiction].
  Intros; unfold task_tcb_init_stack_same_call in *; entailer!; tauto.
Qed.

(** Compose the already observed TCBInit creation frame with the actual
    next acquisition. The protected rollback guard is established here;
    a flat released-to-current source trace is unnecessary. *)
Lemma task_create_stack_save_output_no_free :
  forall environment critical sg args original checkpoint_call mask saved
    initial released checkpoint,
  task_tcb_init_stack_same_call checkpoint_call original ->
  task_tcb_init_call_result sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial 66 released ->
  UCOS2_state_inv sg checkpoint ->
  task_tcb_init_stack_return_preserved original released checkpoint ->
  task_tcb_init_stack_save_output environment critical sg checkpoint_call mask saved checkpoint |--
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_return_preserved original released acquired /\
      task_rollback_guard acquired.(TskState) args.(initPrio) original.(os_sched_call_invocation) /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned)) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg acquired **
     task_tcb_init_stack_capsules environment acquired).
Proof.
intros environment critical sg args original checkpoint_call mask saved initial released checkpoint
    Hsame Hresult Hcheckpoint Hprevious.
  pose proof Hsame as [Hinvocation [Horigin Hstack]].
  unfold task_tcb_init_stack_save_output; Intros returned acquired.
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
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_context, task_tcb_init_stack_capsules, UCOS2_inv.
  rewrite Hreturned_invocation, Hreturned_origin, Hinvocation, Horigin; entailer!; congruence.
Qed.

(** The actual post-store NULL cell, not the result code or guard by itself,
    reconstructs the rolled-back world. The parked map is unchanged by this
    particular protected table/lifecycle store and is reindexed accordingly;
    its subsequent Restore must still return an actual fresh world/map. *)
Lemma task_create_stack_no_free_rollback_resources :
  forall environment (critical : CriticalRegionResources) sg args invocation origin initial released acquired,
  task_tcb_init_entry sg args invocation origin initial ->
  task_tcb_init_call_result sg args invocation origin initial 66 released ->
  UCOS2_state_inv sg acquired ->
  task_creation_frame invocation released.(TskState) acquired.(TskState) ->
  (task_invocation_active released.(TskState) invocation origin ->
    task_invocation_active acquired.(TskState) invocation origin) ->
  (sg.(g_OSTCBPrioTbl) + args.(initPrio) * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) args.(initPrio) **
    UCOS2_raw_rep_missing_priority_table sg acquired **
    task_tcb_init_stack_capsules environment acquired |--
  coq_prop (task_invocation_active
    (task_rollback_reservation acquired.(TskState) args.(initPrio)) invocation origin) &&
  (UCOS2_inv sg
     (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired) **
   task_tcb_init_stack_capsules environment
     (replace_TskS (task_rollback_reservation acquired.(TskState) args.(initPrio)) acquired)).
Proof.
  intros environment critical sg args invocation origin initial released acquired Hentry Hresult
    Hvalid Hframe Hresume.
  assert (Hreleased : task_tcb_init_entry sg args invocation origin released).
  { inversion Hresult; subst; eapply task_tcb_init_call_preserves_entry; eassumption. }
  assert (Hactive : task_invocation_active acquired.(TskState) invocation origin).
  { apply Hresume; exact (proj1 (proj2 (proj2 Hreleased))). }
  destruct (task_tcb_init_call_no_free_pending_agreement sg args invocation origin
    initial released Hresult) as [_ [entry [Hlookup [Hinv Hempty]]]].
  assert (Hguard : task_rollback_guard acquired.(TskState) args.(initPrio) invocation).
  { exists entry; split; [|auto]. eapply task_creation_frame_lookup; eassumption. }
  sep_apply_l_atomic (UCOS2_inv_merge_rollback_priority sg acquired args.(initPrio)
    invocation Hvalid Hguard).
  unfold task_tcb_init_stack_capsules; cbn [replace_TskS task_rollback_reservation]; entailer!.
Qed.
