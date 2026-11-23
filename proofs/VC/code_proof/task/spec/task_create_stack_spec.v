Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_clear_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_return_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Caller composition for the selected descending ARMv7-A stack port.
    This descriptor binds actual storage and ptos; it does NOT recover the
    extent from OS_TCBInit's basic-API bottom/size fields.  The Ext clear
    call's bottom and size are bound separately, only where that call is
    used.  There is no extra executable validity or capacity branch. *)
Definition task_create_stack_region_binding (region : TaskStackRegion)
  (args : TaskCreateArgs) : Prop :=
  valid_task_stack_region region /\ region.(stackRegionGrowsDown) = true /\
  args.(createStackTop) = task_stack_region_top region.

Definition task_create_stack_layout (variant : TaskStackVFP)
  (region : TaskStackRegion) (args : TaskCreateArgs)
  (lower upper : list (option Z)) : Prop :=
  task_create_stack_region_binding region args /\
  task_stack_init_sp variant args.(createStackTop) =
    region.(stackRegionBase) + Zlength lower * sizeof(UINT) /\
  region.(stackRegionWords) =
    Zlength lower + task_stack_init_word_count variant + Zlength upper.

Definition task_create_stack_image (variant : TaskStackVFP)
  (args : TaskCreateArgs) (task_return : addr)
  (lower upper : list (option Z)) : list (option Z) :=
  lower ++ map (@Some Z)
    (task_stack_init_frame_words variant args.(createEntry) args.(createArgument)
      task_return (task_create_options args)) ++ upper.

Lemma task_create_stack_layout_geometry : forall variant region args lower upper,
  task_create_stack_layout variant region args lower upper ->
  task_stack_init_buffer_geometry variant region.(stackRegionBase)
    region.(stackRegionWords) args.(createStackTop) (Zlength lower).
Proof.
  intros variant region args lower upper [[Hvalid [Hdown Htop]] [Hsp Hsize]].
  destruct Hvalid as [Hwords [Hbase [Halign Hend]]].
  unfold task_stack_region_top in Htop; rewrite Hdown in Htop.
  unfold task_stack_region_end in Hend.
  pose proof (Zlength_nonneg lower) as Hlower.
  pose proof (Zlength_nonneg upper) as Hupper.
  unfold task_stack_init_buffer_geometry; rewrite sizeof_uint in *.
  repeat split; lia.
Qed.

Lemma task_create_stack_pointer_in_range : forall variant region args lower upper,
  task_create_stack_layout variant region args lower upper ->
  task_stack_saved_pointer_in_range region
    (task_stack_init_sp variant args.(createStackTop)).
Proof.
  intros variant region args lower upper [[Hvalid [Hdown Htop]] [Hsp Hsize]].
  destruct Hvalid as [Hwords [Hbase [Halign Hend]]].
  pose proof (Zlength_nonneg lower) as Hlower.
  pose proof (Zlength_nonneg upper) as Hupper.
  pose proof (task_stack_init_word_count_positive variant) as Hcount.
  unfold task_stack_saved_pointer_in_range, task_stack_region_end.
  split.
  - rewrite Hsp; rewrite sizeof_uint in *; lia.
  - rewrite Hsp, Z.add_mod, Z.mod_mul by (rewrite sizeof_uint; lia).
    rewrite Halign; reflexivity.
Qed.

Lemma task_create_stack_image_length : forall variant region args task_return lower upper,
  task_create_stack_layout variant region args lower upper ->
  Zlength (task_create_stack_image variant args task_return lower upper) =
    region.(stackRegionWords).
Proof.
  intros variant region args task_return lower upper [_ [_ Hsize]].
  unfold task_create_stack_image; rewrite !Zlength_app.
  assert (Hlength : Zlength (map (@Some Z)
    (task_stack_init_frame_words variant args.(createEntry) args.(createArgument)
      task_return (task_create_options args))) = task_stack_init_word_count variant).
  { rewrite Zlength_correct, map_length, <- Zlength_correct;
      apply task_stack_init_frame_words_length. }
  rewrite Hlength; lia.
Qed.

Lemma task_create_basic_zero_fields_nonempty_region : forall region args sp initial_name,
  task_create_stack_region_binding region args ->
  args.(createExtension) = TaskCreateBasic ->
  (task_create_tcb_args args sp initial_name).(initStkBottom) = 0 /\
  (task_create_tcb_args args sp initial_name).(initStkSize) = 0 /\
  0 < region.(stackRegionWords) /\ 0 < region.(stackRegionBase).
Proof.
  intros region args sp initial_name [[Hwords [Hbase Hrest]] Hbinding] Hbasic.
  destruct (task_create_tcb_args_basic_fields args sp initial_name Hbasic)
    as [Hbottom [_ [Hsize _]]].
  repeat split; tauto || lia.
Qed.

Lemma task_create_stack_storage_split_regions : forall variant region args lower old_frame upper,
  task_create_stack_layout variant region args lower upper ->
  Zlength old_frame = task_stack_init_word_count variant ->
  task_stack_storage region (lower ++ old_frame ++ upper) |--
  UIntArray.mixed_full region.(stackRegionBase) (Zlength lower) lower **
  UIntArray.mixed_full (task_stack_init_sp variant args.(createStackTop))
    (task_stack_init_word_count variant) old_frame **
  UIntArray.mixed_full (task_stack_init_aligned_top args.(createStackTop)) (Zlength upper) upper.
Proof.
  intros variant region args lower old_frame upper [_ [Hsp Hsize]] Hframe.
  assert (Htotal : region.(stackRegionWords) = Zlength lower + Zlength (old_frame ++ upper)).
  { rewrite Zlength_app; lia. }
  unfold task_stack_storage; rewrite Htotal.
  sep_apply_l_atomic (task_stack_array_split_app region.(stackRegionBase) lower (old_frame ++ upper)).
  rewrite <- Hsp.
  rewrite Zlength_app.
  sep_apply_l_atomic (task_stack_array_split_app
    (task_stack_init_sp variant args.(createStackTop)) old_frame upper).
  rewrite Hframe, task_stack_init_frame_upper_address; entailer!.
Qed.

Lemma task_create_stack_storage_init_pre :
  forall variant region args task_return lower old_frame upper,
  task_create_stack_layout variant region args lower upper ->
  Zlength old_frame = task_stack_init_word_count variant ->
  0 <= args.(createEntry) < 4294967296 ->
  0 <= args.(createArgument) < 4294967296 -> 0 <= task_return < 4294967296 ->
  task_stack_storage region (lower ++ old_frame ++ upper) |--
  task_stack_init_pre variant region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper.
Proof.
  intros variant region args task_return lower old_frame upper Hlayout Hframe Hentry Harg Hreturn.
  pose proof (task_create_stack_layout_geometry variant region args lower upper Hlayout) as Hgeometry.
  pose proof (proj2 (proj2 Hlayout)) as Hsize.
  unfold task_stack_init_pre.
  sep_apply_l_atomic (task_create_stack_storage_split_regions
    variant region args lower old_frame upper Hlayout Hframe).
  entailer!.
Qed.

(** Consumes the real StackInit postcondition; the old frame is absent.
    The lower/upper lists are its INPUT-state values.  In CreateExt that
    input may already have been cleared, so these are not necessarily the
    bytes at entry to OSTaskCreateExt. *)
Lemma task_create_stack_init_post_storage :
  forall variant region args task_return lower upper returned_sp,
  task_create_stack_layout variant region args lower upper ->
  task_stack_init_post variant region.(stackRegionBase) args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower upper returned_sp |--
  coq_prop (returned_sp = task_stack_init_sp variant args.(createStackTop) /\
    task_stack_saved_pointer_in_range region returned_sp) &&
  task_stack_storage region (task_create_stack_image variant args task_return lower upper).
Proof.
  intros variant region args task_return lower upper returned_sp Hlayout.
  pose proof (task_create_stack_pointer_in_range variant region args lower upper Hlayout) as Hrange.
  destruct Hlayout as [_ [Hsp Hsize]].
  eapply derivable1_trans.
  - apply task_stack_init_post_merge_buffer; exact Hsp.
  - unfold task_stack_storage, task_create_stack_image; rewrite Hsize; Intros.
    subst returned_sp.
    entailer!.
Qed.

(** Actual selected StackInit writes, consumed at its real creation-call
    boundary. The allocation generation has not yet been chosen by
    TCBInit; it is deliberately not guessed here. Later publication binds
    this CURRENT owned buffer to that actual allocation. *)
Lemma task_create_stack_init_store_execution :
  forall region args task_return lower old_frame upper (frame : Assertion) before,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  Zlength old_frame = 16 ->
  0 <= args.(createEntry) < 4294967296 ->
  0 <= args.(createArgument) < 4294967296 -> 0 <= task_return < 4294967296 ->
  (task_stack_storage region (lower ++ old_frame ++ upper) ** frame) before ->
  exists after,
    kernel_heap_execution
      (task_stack_init_no_vfp_writes args.(createStackTop) args.(createEntry)
        args.(createArgument) task_return) before after /\
    (task_stack_storage region
      (task_create_stack_image TaskStackNoVFP args task_return lower upper) ** frame) after.
Proof.
  intros region args task_return lower old_frame upper frame before
    Hlayout Hlength Hentry Hargument Hreturn Hbefore.
  assert (Hpre : task_stack_storage region (lower ++ old_frame ++ upper) ** frame |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return
      lower old_frame upper ** frame).
  { apply derivable1_sepcon_mono; [|reflexivity].
    apply task_create_stack_storage_init_pre; assumption. }
  destruct (task_stack_init_no_vfp_store_execution region.(stackRegionBase)
    region.(stackRegionWords) args.(createStackTop) args.(createEntry) args.(createArgument)
    task_return (task_create_options args) lower old_frame upper frame before
    (Hpre before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hpost : task_stack_init_post TaskStackNoVFP region.(stackRegionBase)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return
      (task_create_options args) lower upper (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) **
      frame |--
    task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) ** frame).
  { sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args task_return
      lower upper (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) Hlayout); entailer!. }
  exact (Hpost after Hafter).
Qed.

(** The optional clear call has its own source-order semantics.  These
    bridges merely retain its actual current image in the same caller
    region before StackInit writes the register frame. *)
Lemma task_create_extended_clear_arguments : forall region args id extension options,
  region.(stackRegionGrowsDown) = true ->
  args.(createExtension) = TaskCreateExtended id (task_stack_region_bottom region)
    region.(stackRegionWords) extension options ->
  task_create_stack_clear_args true args =
    Some (region.(stackRegionBase), region.(stackRegionWords), options).
Proof.
  intros region args id extension options Hdown Hargs.
  rewrite (task_create_stack_clear_extended args id (task_stack_region_bottom region)
    region.(stackRegionWords) extension options Hargs).
  unfold task_stack_region_bottom; rewrite Hdown; reflexivity.
Qed.

Lemma task_create_stack_clear_current_storage : forall region initial done,
  region.(stackRegionWords) = Zlength initial ->
  task_stack_clear_rep region.(stackRegionBase) initial done |--
  task_stack_storage region (task_stack_clear_words initial done).
Proof. intros; unfold task_stack_clear_rep, task_stack_storage; rewrite H; reflexivity. Qed.

Lemma task_create_stack_clear_complete_storage : forall region initial,
  region.(stackRegionWords) = Zlength initial ->
  task_stack_clear_rep region.(stackRegionBase) initial (Zlength initial) |--
  task_stack_storage region (repeat (Some 0) (List.length initial)).
Proof.
  intros; unfold task_stack_clear_rep, task_stack_storage.
  rewrite H, task_stack_clear_words_complete; reflexivity.
Qed.

Lemma task_create_stack_clear_returned_image : forall region initial options after,
  region.(stackRegionWords) = Zlength initial ->
  task_stack_clear_enabled options = true ->
  task_stack_clear_result options
    (task_stack_clear_initial region.(stackRegionBase) region.(stackRegionWords) initial) after ->
  after.(stackClearWords) = repeat (Some 0) (List.length initial).
Proof.
  intros region initial options after Hsize Henabled Hresult; rewrite Hsize in Hresult.
  exact (proj2 (proj2 (proj2 (task_stack_clear_result_complete options
    region.(stackRegionBase) initial after Henabled Hresult)))).
Qed.

Lemma task_create_cleared_stack_init_pre :
  forall variant region args task_return initial lower old_frame upper,
  task_create_stack_layout variant region args lower upper ->
  region.(stackRegionWords) = Zlength initial ->
  repeat (Some 0) (List.length initial) = lower ++ old_frame ++ upper ->
  Zlength old_frame = task_stack_init_word_count variant ->
  0 <= args.(createEntry) < 4294967296 ->
  0 <= args.(createArgument) < 4294967296 -> 0 <= task_return < 4294967296 ->
  task_stack_clear_rep region.(stackRegionBase) initial (Zlength initial) |--
  task_stack_init_pre variant region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper.
Proof.
  intros variant region args task_return initial lower old_frame upper
    Hlayout Hsize Hcleared Hframe Hentry Harg Hreturn.
  eapply derivable1_trans.
  - exact (task_create_stack_clear_complete_storage region initial Hsize).
  - rewrite Hcleared; apply task_create_stack_storage_init_pre; assumption.
Qed.

(** Allocation identity is taken from the existing reservation.  The
    generation is the one reserved by TCBInit's detach, not an application
    ID, a new counter, or a lease guessed after publication. *)
Lemma task_create_stack_commit_allocation_binding :
  forall region args invocation origin acquired current slot,
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  exists allocation,
    allocation.(privateSlot) = slot /\
    allocation.(privateGeneration) = acquired.(TskState).(taskLifecycle).(taskNextGeneration) /\
    task_stack_creation_binding current.(TskState) args.(initPrio) invocation origin
      (task_stack_lease_of_allocation region allocation).
Proof.
  intros region args invocation origin acquired current slot
    [entry [allocation [Hentry [Hinv [Horigin [Halloc [Hslot Hgen]]]]]]].
  exists allocation; split; [exact Hslot|]. split; [exact Hgen|].
  unfold task_stack_creation_binding; exists entry, allocation.
  repeat split; assumption || reflexivity.
Qed.

(** Resource handover AT THE PROTECTED COMMIT.  Its storage antecedent is
    actual current ownership at that point: this does not infer byte
    preservation from pure lifecycle-frame equalities.  The initialized
    buffer is consumed into the parked map, with its actual publication
    identity.  The existing map can retain older retired generations.
    An absent key is a resource-transfer premise, not a new C guard.
    There is intentionally no rule retaining the initial frame at Create's
    successful return, after the new task may have run.  The call protocol
    must still place this transfer before the first public link write and
    close the protected publication phase before Restore. *)
Lemma task_create_stack_protected_commit_map_resources :
  forall sg variant region args task_return lower upper initial_name
    invocation origin acquired current slot image lease stacks,
  task_create_stack_layout variant region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp variant args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  parked_stacks_consistent current.(TskState) stacks ->
  stacks (task_stack_key lease) = None ->
  task_stack_storage region (task_create_stack_image variant args task_return lower upper) **
    store_parked_stacks stacks |--
  coq_prop (parked_stacks_consistent
    (task_tcb_init_published_state sg actual invocation acquired current slot image).(TskState)
    (task_stack_park stacks lease (task_create_stack_image variant args task_return lower upper))) &&
    store_parked_stacks
      (task_stack_park stacks lease (task_create_stack_image variant args task_return lower upper)).
Proof.
  intros sg variant region args task_return lower upper initial_name
    invocation origin acquired current slot image lease stacks
    Hlayout Hregion actual Hcommit Hbinding Hconsistent Hnone.
  change (task_stack_storage region (task_create_stack_image variant args task_return lower upper) **
    store_parked_stacks stacks |--
    coq_prop (parked_stacks_consistent
      (task_commit current.(TskState) actual.(initPrio) invocation
        (task_tcb_init_commit_node actual acquired slot image))
      (task_stack_park stacks lease (task_create_stack_image variant args task_return lower upper))) &&
      store_parked_stacks
        (task_stack_park stacks lease (task_create_stack_image variant args task_return lower upper))).
  rewrite <- Hregion at 1.
  apply task_stack_commit_park_consistent_resources with (origin := origin).
  - exact Hconsistent.
  - exact Hnone.
  - exact Hbinding.
  - eapply task_tcb_init_commit_binding_identity; exact Hcommit.
  - rewrite Hregion; exact (proj1 (proj1 Hlayout)).
  - rewrite Hregion.
    change (task_stack_saved_pointer_in_range region actual.(initStkPtr)).
    destruct (task_create_tcb_args_common_fields args
      (task_stack_init_sp variant args.(createStackTop)) initial_name) as [_ [Hpointer _]].
    unfold actual; rewrite Hpointer.
    apply task_create_stack_pointer_in_range with (lower := lower) (upper := upper); exact Hlayout.
Qed.

(** Publication and buffer handover share one result state.  TCBInit's
    existing commit fixes the allocation, generation, public links and
    scheduler fields; this composition records the consumed stack buffer
    in that state's Task component without changing those effects. *)
Definition task_create_stack_published_state (sg : StableGlobVars)
  (args : TaskTCBInitArgs) (invocation : nat)
  (acquired current : UCOS2_Verify_State) (slot : TaskID) (image : TCBLayoutImage)
  (lease : TaskStackLease) (words : list (option Z)) : UCOS2_Verify_State :=
  let committed := task_tcb_init_published_state sg args invocation acquired current slot image in
  replace_TskS
    (glob_task_set_parked_stacks committed.(TskState)
      (task_stack_park current.(TskState).(parkedTaskStacks) lease words)) committed.

Lemma task_create_stack_published_state_parked_stacks :
  forall sg args invocation acquired current slot image lease words,
  (task_create_stack_published_state sg args invocation acquired current slot image lease words)
    .(TskState).(parkedTaskStacks) =
  task_stack_park current.(TskState).(parkedTaskStacks) lease words.
Proof. reflexivity. Qed.

Lemma task_create_stack_published_state_commit_frame :
  forall sg args invocation acquired current slot image lease words,
  let committed := task_tcb_init_published_state sg args invocation acquired current slot image in
  let after := task_create_stack_published_state sg args invocation acquired current slot image lease words in
  after.(TskState).(inUsedTaskStates) = committed.(TskState).(inUsedTaskStates) /\
  after.(TskState).(taskLifecycle) = committed.(TskState).(taskLifecycle) /\
  after.(SchedState) = committed.(SchedState) /\ after.(IntrState) = committed.(IntrState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_create_stack_published_state_consistent :
  forall sg args invocation acquired current slot image lease words,
  parked_stacks_consistent
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState)
    (task_stack_park current.(TskState).(parkedTaskStacks) lease words) ->
  let after := task_create_stack_published_state sg args invocation acquired current slot image lease words in
  parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks).
Proof.
  intros sg args invocation acquired current slot image lease words Hconsistent after.
  eapply parked_stacks_consistent_task_map_frame with
    (before := (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState)).
  - reflexivity.
  - intros observer observed_slot generation Hhistory; exact Hhistory.
  - exact Hconsistent.
Qed.

(** State-bound complete-buffer endpoint.  The creation binding and actual
    initialized bytes are unchanged from the map-level rule above.  The
    parked owner is now the map carried by the committed Task state, not a
    side parameter that can drift independently of that state. *)
Lemma task_create_stack_protected_commit_resources :
  forall sg variant region args task_return lower upper initial_name
    invocation origin acquired current slot image lease,
  task_create_stack_layout variant region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp variant args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  parked_stacks_consistent current.(TskState) current.(TskState).(parkedTaskStacks) ->
  current.(TskState).(parkedTaskStacks) (task_stack_key lease) = None ->
  let after := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image variant args task_return lower upper) in
  task_stack_storage region (task_create_stack_image variant args task_return lower upper) **
    store_parked_stacks current.(TskState).(parkedTaskStacks) |--
  coq_prop (parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks)) &&
    store_parked_stacks after.(TskState).(parkedTaskStacks).
Proof.
  intros sg variant region args task_return lower upper initial_name
    invocation origin acquired current slot image lease Hlayout Hregion actual
    Hcommit Hbinding Hconsistent Hnone after.
  eapply derivable1_trans.
  - exact (task_create_stack_protected_commit_map_resources sg variant region args task_return
      lower upper initial_name invocation origin acquired current slot image lease
      current.(TskState).(parkedTaskStacks) Hlayout Hregion Hcommit Hbinding Hconsistent Hnone).
  - Intros.
    assert (Hpost : parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks)).
    { apply task_create_stack_published_state_consistent; assumption. }
    entailer!.
Qed.

(** Failure 66 occurs after StackInit.  The spatial frame below is the
    initialized CURRENT image, held at the rollback store, not an equality
    used to manufacture a heap or to restore entry bytes.  Transport across
    TCBInit/trace/Save must satisfy their separate resource-frame contracts;
    critical_region_interval alone transports only its registered resources.
    Restore and the Basic-only trace call are not implementations here. *)
Lemma task_create_no_free_rollback_stack_resources :
  forall critical sg variant region args task_return lower upper initial_name
    invocation origin initial released acquired,
  let actual := task_create_tcb_args args
    (task_stack_init_sp variant args.(createStackTop)) initial_name in
  task_tcb_init_entry sg actual invocation origin initial ->
  task_tcb_init_result critical sg actual invocation origin initial 66 released ->
  critical_region_interval critical sg invocation released acquired ->
  (sg.(g_OSTCBPrioTbl) + actual.(initPrio) * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) actual.(initPrio) **
    UCOS2_raw_rep_missing_priority_table sg acquired **
    task_stack_storage region (task_create_stack_image variant args task_return lower upper) |--
  coq_prop (task_invocation_active
    (task_rollback_reservation acquired.(TskState) actual.(initPrio)) invocation origin) &&
  (UCOS2_inv sg
    (replace_TskS (task_rollback_reservation acquired.(TskState) actual.(initPrio)) acquired) **
   task_stack_storage region (task_create_stack_image variant args task_return lower upper)).
Proof.
  intros critical sg variant region args task_return lower upper initial_name
    invocation origin initial released acquired actual Hentry Hresult Hinterval.
  sep_apply_l_atomic (task_create_no_free_rollback_merge_inv critical sg actual invocation origin
    initial released acquired Hentry Hresult Hinterval).
  entailer!.
Qed.

(** These composition rules neither instantiate the ARM Hoare contract nor
    prove its allocation provenance, callback behavior, or Save/Restore.
    The publication endpoint records its parked-buffer map in the existing
    Task state.  Binding the actual linked VFP variant and establishing the
    complete call/context protocol remain explicit integration work. *)

Lemma task_create_initial_frame_binding :
  forall lease region args task_return lower upper,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  armv7a_initial_frame_binding (armv7a_initial_continuation lease
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower upper).
Proof.
  intros lease region args task_return lower upper Hlayout Hregion.
  destruct Hlayout as [[Hvalid Htop] [Hsp Hsize]].
  exists args.(createStackTop), args.(createEntry), args.(createArgument), task_return, lower, upper.
  cbn [armv7a_initial_continuation armv7a_continuation_stack armv7a_continuation_sp].
  rewrite Hregion; split; [reflexivity|].
  split; [exact Hvalid|]. split; [exact Hsp|exact Hsize].
Qed.

Lemma task_create_stack_published_initial_pointer :
  forall sg args task_return lower upper initial_name
    invocation origin acquired current slot image lease,
  let actual := task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  let after := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  exists node, after.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node /\
    node.(taskID) = lease.(stackLeaseSlot) /\
    node.(taskGeneration) = lease.(stackLeaseGeneration) /\
    node.(tcbStkPtr) = task_stack_init_sp TaskStackNoVFP args.(createStackTop).
Proof.
  intros sg args task_return lower upper initial_name invocation origin acquired current slot image
    lease actual Hcommit Hcreation after.
  pose proof (task_tcb_init_commit_binding_identity actual invocation origin acquired current slot image Hcommit)
    as Hidentity.
  destruct (task_stack_creation_binding_commit_identity current.(TskState) actual.(initPrio)
    invocation origin lease (task_tcb_init_commit_node actual acquired slot image) Hcreation Hidentity)
    as [Hslot Hgeneration].
  exists (task_set_links (task_tcb_init_commit_node actual acquired slot image)
    current.(TskState).(tcbListHead) None).
  split.
  - change ((task_commit current.(TskState) actual.(initPrio) invocation
      (task_tcb_init_commit_node actual acquired slot image)).(inUsedTaskStates) lease.(stackLeaseSlot) =
      Some (task_set_links (task_tcb_init_commit_node actual acquired slot image)
        current.(TskState).(tcbListHead) None)).
    rewrite <- Hslot; apply (proj1 (task_commit_publication_fields_eq _ _ _ _)).
  - split; [exact Hslot|]. split; [exact Hgeneration|].
    change (actual.(initStkPtr) = task_stack_init_sp TaskStackNoVFP args.(createStackTop)).
    exact (proj1 (proj2 (task_create_tcb_args_common_fields args
      (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name))).
Qed.

(** The absence of this key is derived from the actual private allocation
    and publication history, not added to a caller Require. Only the new
    initial descriptor is introduced; old entries are retained by the same
    map operation. Both the real byte buffer and its map owner are consumed.
    The None metadata is not a minted opaque suspended-call receipt. *)
Lemma task_create_stack_park_initial_continuation :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg region args task_return lower upper initial_name invocation origin acquired current slot image lease,
  UCOS2_state_inv sg current ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  let after := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    store_parked_stacks current.(TskState).(parkedTaskStacks) **
    armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) |--
  coq_prop (parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks)) &&
    (store_parked_stacks after.(TskState).(parkedTaskStacks) **
     armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease Hvalid Hlayout Hregion actual Hcommit Hcreation after.
  pose proof (task_tcb_init_commit_binding_identity actual invocation origin acquired current slot image Hcommit)
    as Hidentity.
  assert (Hconsistent : parked_stacks_consistent current.(TskState) current.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  destruct (task_stack_creation_binding_commit_identity current.(TskState) actual.(initPrio)
    invocation origin lease (task_tcb_init_commit_node actual acquired slot image)
    Hcreation Hidentity) as [Hslot Hgeneration].
  assert (Hfresh : current.(TskState).(parkedTaskStacks) (task_stack_key lease) = None).
  { unfold task_stack_key; rewrite <- Hslot, <- Hgeneration.
    eapply task_commit_stack_key_absent;
      [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  set (saved := armv7a_initial_continuation lease args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return lower upper).
  assert (Hinitial : armv7a_initial_frame_binding saved).
  { apply task_create_initial_frame_binding with (region := region); assumption. }
  assert (Hattachment : armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) |--
    armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
  { unfold armv7a_task_continuations.
    eapply derivable1_trans with (y :=
      armv7a_task_continuation_entry abi (task_stack_key lease)
        (lease.(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
      store_parked_continuations (armv7a_task_continuation_entry abi)
        current.(TskState).(parkedTaskStacks)).
    - unfold armv7a_task_continuation_entry; Exists saved.
      assert (Hbinding : armv7a_continuation_binding saved)
        by apply armv7a_initial_continuation_binding.
      unfold armv7a_task_continuation_resource; cbn [saved armv7a_initial_continuation
        armv7a_continuation_call armv7a_continuation_stack]; entailer!.
    - change (armv7a_task_continuation_entry abi (task_stack_key lease)
        (lease.(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
        store_parked_continuations (armv7a_task_continuation_entry abi)
          current.(TskState).(parkedTaskStacks) |--
        store_parked_continuations (armv7a_task_continuation_entry abi)
          (task_stack_park_fragments current.(TskState).(parkedTaskStacks) lease
            saved.(armv7a_continuation_fragments))).
      apply store_parked_continuations_park; exact Hfresh. }
  sep_apply_l_atomic Hattachment.
  pose proof (task_create_stack_protected_commit_resources sg TaskStackNoVFP region args
    task_return lower upper initial_name invocation origin acquired current slot image lease
    Hlayout Hregion Hcommit Hcreation Hconsistent Hfresh) as Hpark.
  cbv zeta in Hpark; sep_apply_l_atomic Hpark; entailer!.
Qed.
