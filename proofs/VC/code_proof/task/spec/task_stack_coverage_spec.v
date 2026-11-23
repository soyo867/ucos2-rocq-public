Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A concrete separation-logic slice, not an architecture law or future
    scheduler-safety assumption. The residual is the rest of the SAME
    fragments. A lease/SP bound alone cannot establish these sixteen
    initialized words. This also permits holes owned by real borrowers. *)
Definition armv7a_task_frame_slice (saved : Armv7aContinuation) : Prop :=
  exists residual : Assertion,
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) |--
    UIntArray.mixed_full saved.(armv7a_continuation_sp) 16
      (map (@Some Z) (armv7a_continuation_words saved)) ** residual.

Lemma armv7a_task_frame_slice_restore_reads : forall saved (frame : Assertion) heap,
  armv7a_continuation_binding saved -> armv7a_task_frame_slice saved ->
  (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) ** frame) heap ->
  armv7a_continuation_restore_reads saved heap.
Proof.
  intros saved frame heap Hbinding [residual Hslice] Hheap.
  split; [exact Hbinding|].
  assert (Hlength : Zlength (armv7a_continuation_words saved) = 16).
  { rewrite Zlength_correct, (armv7a_continuation_words_length saved Hbinding); reflexivity. }
  apply (armv7a_frame_array_reads (armv7a_continuation_words saved)
    saved.(armv7a_continuation_sp) (residual ** frame) heap).
  assert (Hsplit : task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** frame |--
    UIntArray.mixed_full saved.(armv7a_continuation_sp)
      (Zlength (armv7a_continuation_words saved))
      (map (@Some Z) (armv7a_continuation_words saved)) ** (residual ** frame)).
  { rewrite Hlength; sep_apply_l_atomic Hslice; entailer!. }
  exact (Hsplit heap Hheap).
Qed.

(** The source producer may use this after it has assembled the actual
    post-save image. No opaque receipt or ABI field supplies the image. *)
Lemma armv7a_task_frame_slice_from_image : forall saved lower upper,
  armv7a_continuation_binding saved ->
  saved.(armv7a_continuation_fragments) =
    task_stack_complete_fragments saved.(armv7a_continuation_stack).(stackLeaseRegion)
      (lower ++ map (@Some Z) (armv7a_continuation_words saved) ++ upper) ->
  saved.(armv7a_continuation_sp) =
    saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionBase) +
      Zlength lower * sizeof(UINT) ->
  saved.(armv7a_continuation_stack).(stackLeaseRegion).(stackRegionWords) =
    Zlength lower + 16 + Zlength upper ->
  armv7a_task_frame_slice saved.
Proof.
  intros saved lower upper Hbinding Hfragments Hsp Hsize.
  assert (Hlength : Zlength (map (@Some Z) (armv7a_continuation_words saved)) = 16).
  { rewrite Zlength_correct, map_length,
      (armv7a_continuation_words_length saved Hbinding); reflexivity. }
  exists (task_stack_storage_without_region
    saved.(armv7a_continuation_stack).(stackLeaseRegion) lower 16 upper).
  rewrite Hfragments, task_stack_fragments_rep_complete.
  sep_apply_l_atomic (task_stack_storage_split_region
    saved.(armv7a_continuation_stack).(stackLeaseRegion) lower
    (map (@Some Z) (armv7a_continuation_words saved)) upper
    ltac:(rewrite Hlength; exact Hsize)).
  rewrite Hlength, <- Hsp; reflexivity.
Qed.

Lemma armv7a_initial_frame_slice : forall saved,
  armv7a_initial_frame_binding saved -> armv7a_task_frame_slice saved.
Proof.
  intros saved [top [entry [argument [task_return [lower [upper [Heq [Hregion [Hsp Hsize]]]]]]]]].
  remember saved.(armv7a_continuation_stack) as lease eqn:Hlease.
  subst saved.
  eapply armv7a_task_frame_slice_from_image with (lower := lower) (upper := upper).
  - apply armv7a_initial_continuation_binding.
  - reflexivity.
  - exact Hsp.
  - exact Hsize.
Qed.

(** Conditional on matching generation: a retired descriptor at a reused
    TCB address does not constrain the new task's saved SP. *)
Definition task_stack_live_sp (tasks : Glob_TaskAbstractState)
  (key : TaskID * nat) (sp : Z) : Prop :=
  forall node, tasks.(inUsedTaskStates) (fst key) = Some node ->
    node.(taskGeneration) = snd key -> node.(tcbStkPtr) = sp.

Definition armv7a_task_stack_entry {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (tasks : Glob_TaskAbstractState) (key : TaskID * nat)
  (payload : TaskStackRegion * TaskStackFragments) : Assertion :=
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      task_stack_key saved.(armv7a_continuation_stack) = key /\
      (saved.(armv7a_continuation_stack).(stackLeaseRegion),
        saved.(armv7a_continuation_fragments)) = payload /\
      armv7a_task_frame_slice saved /\
      task_stack_live_sp tasks key saved.(armv7a_continuation_sp)) &&
    armv7a_task_continuation_resource abi saved.

Definition armv7a_task_stack_continuations {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  (tasks : Glob_TaskAbstractState) (stacks : TaskStackMap) : Assertion :=
  store_parked_continuations (armv7a_task_stack_entry abi tasks) stacks.

Lemma armv7a_task_stack_entry_forget : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks key payload,
  armv7a_task_stack_entry abi tasks key payload |--
  armv7a_task_continuation_entry abi key payload.
Proof.
  intros; unfold armv7a_task_stack_entry, armv7a_task_continuation_entry;
    Intros saved; Exists saved; entailer!.
Qed.

Lemma armv7a_task_stack_continuations_forget : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks,
  armv7a_task_stack_continuations abi tasks stacks |-- armv7a_task_continuations abi stacks.
Proof.
  intros; unfold armv7a_task_stack_continuations, armv7a_task_continuations,
    store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros; apply armv7a_task_stack_entry_forget.
Qed.

Lemma armv7a_task_stack_continuations_reindex : forall external platform port
  (abi : Armv7aContinuationABI external platform port) before after stacks,
  (forall key payload node, stacks key = Some payload ->
    after.(inUsedTaskStates) (fst key) = Some node -> node.(taskGeneration) = snd key ->
    exists old, before.(inUsedTaskStates) (fst key) = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)) ->
  armv7a_task_stack_continuations abi before stacks |--
  armv7a_task_stack_continuations abi after stacks.
Proof.
  intros external platform port abi before after stacks Htransport.
  unfold armv7a_task_stack_continuations, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros key payload Hlookup.
  unfold armv7a_task_stack_entry; Intros saved.
  assert (Hsp : task_stack_live_sp before key saved.(armv7a_continuation_sp)) by tauto.
  assert (Hafter : task_stack_live_sp after key saved.(armv7a_continuation_sp)).
  { intros node Hnode Hgen.
    destruct (Htransport key payload node Hlookup Hnode Hgen)
      as [old [Hold [Hg Hvalue]]].
    rewrite <- Hvalue; apply Hsp; [exact Hold|congruence]. }
  Exists saved; entailer!.
Qed.

Lemma armv7a_task_stack_continuations_used_map_eq : forall external platform port
  (abi : Armv7aContinuationABI external platform port) before after stacks,
  before.(inUsedTaskStates) = after.(inUsedTaskStates) ->
  armv7a_task_stack_continuations abi before stacks |--
  armv7a_task_stack_continuations abi after stacks.
Proof.
  intros; apply armv7a_task_stack_continuations_reindex.
  intros key payload node Hlookup Hnode Hgen; exists node; rewrite H; auto.
Qed.

Lemma armv7a_task_stack_continuations_take : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks lease fragments,
  stacks (task_stack_key lease) = Some (lease.(stackLeaseRegion), fragments) ->
  store_parked_stacks stacks ** armv7a_task_stack_continuations abi tasks stacks |--
  EX saved,
    coq_prop (armv7a_continuation_binding saved /\
      saved.(armv7a_continuation_stack) = lease /\
      saved.(armv7a_continuation_fragments) = fragments /\
      armv7a_task_frame_slice saved /\
      task_stack_live_sp tasks (task_stack_key lease) saved.(armv7a_continuation_sp)) &&
    (task_stack_fragments_rep lease.(stackLeaseRegion) fragments **
     armv7a_task_continuation_resource abi saved **
     store_parked_stacks (task_stack_take stacks lease) **
     armv7a_task_stack_continuations abi tasks (task_stack_take stacks lease)).
Proof.
  intros external platform port abi tasks stacks lease fragments Hlookup.
  sep_apply_l_atomic (store_parked_stacks_take_fragments stacks lease fragments Hlookup).
  unfold armv7a_task_stack_continuations.
  sep_apply_l_atomic (store_parked_continuations_take (armv7a_task_stack_entry abi tasks)
    stacks lease fragments Hlookup).
  unfold armv7a_task_stack_entry; Intros saved.
  assert (Hkey : task_stack_key saved.(armv7a_continuation_stack) = task_stack_key lease) by tauto.
  assert (Hpayload : (saved.(armv7a_continuation_stack).(stackLeaseRegion),
    saved.(armv7a_continuation_fragments)) = (lease.(stackLeaseRegion), fragments)) by tauto.
  assert (Hlease : saved.(armv7a_continuation_stack) = lease).
  { unfold task_stack_key in Hkey; destruct saved.(armv7a_continuation_stack), lease;
      cbn in *; congruence. }
  Exists saved; entailer!; congruence.
Qed.

(** Coverage is indexed by the existing live map and parked map. The
    optional active key is an execution cut, not a second mutable ledger.
    Its actual bytes/CPU authority remain outside the parked owner. *)
Definition task_stack_live_coverage (tasks : Glob_TaskAbstractState)
  (active : option (TaskID * nat)) : Prop :=
  forall slot node, tasks.(inUsedTaskStates) slot = Some node ->
    active = Some (slot, node.(taskGeneration)) \/
    exists region fragments,
      tasks.(parkedTaskStacks) (slot, node.(taskGeneration)) = Some (region, fragments).

Lemma task_boot_stack_coverage : forall sg name,
  task_stack_live_coverage (task_boot sg name) None.
Proof. intros sg name slot node Hnode; discriminate. Qed.

Lemma task_boot_empty_stack_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg name,
  emp |-- store_parked_stacks (task_boot sg name).(parkedTaskStacks) **
    armv7a_task_stack_continuations abi (task_boot sg name) (task_boot sg name).(parkedTaskStacks).
Proof.
  intros; unfold store_parked_stacks, armv7a_task_stack_continuations, store_parked_continuations.
  assert (Hempty : forall resource : (TaskID * nat) -> (TaskStackRegion * TaskStackFragments) -> Assertion,
    store_map resource (task_boot sg name).(parkedTaskStacks) --||-- emp).
  { intros; apply store_map_empty.
    - exists []; split.
      + intros key; split; [intros Hin; contradiction|intros [payload Hentry]; discriminate].
      + constructor.
    - intros key; left; reflexivity. }
  rewrite !Hempty; entailer!.
Qed.

(** Consumes the existing checked initializer's real storage post and the
    two cells supplied by OS_InitMisc. Empty coverage is established only
    before any task is published; later publication proves its extension. *)
Lemma init_tcb_list_establishes_stack_coverage : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg name,
  init_tcb_list_profile sg ->
  init_tcb_list_post sg name ** sg.(g_OSTaskCtr) # UChar |-> 0 **
    sg.(g_OSTaskRegNextAvailID) # UChar |-> 0 |--
  coq_prop (task_stack_live_coverage (task_boot sg name) None) &&
    (task_shared_rep sg (task_boot sg name) **
     armv7a_task_stack_continuations abi (task_boot sg name) (task_boot sg name).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg name Hprofile.
  sep_apply_l_atomic (init_tcb_list_post_to_task_boot sg name Hprofile).
  unfold task_shared_rep.
  pose proof (task_boot_stack_coverage sg name) as Hcoverage.
  entailer!; apply task_boot_empty_stack_resources.
Qed.

Lemma task_stack_live_coverage_used_map_frame : forall before after active,
  (forall slot node, after.(inUsedTaskStates) slot = Some node ->
    exists old, before.(inUsedTaskStates) slot = Some old /\
      node.(taskGeneration) = old.(taskGeneration)) ->
  after.(parkedTaskStacks) = before.(parkedTaskStacks) ->
  task_stack_live_coverage before active -> task_stack_live_coverage after active.
Proof.
  intros before after active Hnodes Hstacks Hcoverage slot node Hnode.
  destruct (Hnodes slot node Hnode) as [old [Hold Hgen]].
  rewrite Hgen, Hstacks; apply Hcoverage; exact Hold.
Qed.

Lemma task_stack_save_sp_preserves_coverage : forall tasks slot node sp active,
  tasks.(inUsedTaskStates) slot = Some node -> task_stack_live_coverage tasks active ->
  task_stack_live_coverage (glob_task_set_usedtask tasks slot (task_set_saved_sp node sp)) active.
Proof.
  intros tasks slot node sp active Hnode Hcoverage.
  eapply task_stack_live_coverage_used_map_frame with (before := tasks);
    [|reflexivity|exact Hcoverage].
  intros key updated Hupdated; cbn [glob_task_set_usedtask inUsedTaskStates] in Hupdated.
  destruct (Z.eqb key slot) eqn:Hkey.
  - apply Z.eqb_eq in Hkey; subst key; injection Hupdated as Hupdated; subst updated.
    exists node; auto.
  - exists updated; auto.
Qed.

Lemma task_stack_park_covers_active : forall tasks lease fragments,
  task_stack_live_coverage tasks (Some (task_stack_key lease)) ->
  task_stack_live_coverage
    (glob_task_set_parked_stacks tasks
      (task_stack_park_fragments tasks.(parkedTaskStacks) lease fragments)) None.
Proof.
  intros tasks lease fragments Hcoverage slot node Hnode.
  right; change (exists region words,
    task_stack_park_fragments tasks.(parkedTaskStacks) lease fragments
      (slot, node.(taskGeneration)) = Some (region, words)).
  destruct (task_stack_key_eq_dec (slot, node.(taskGeneration)) (task_stack_key lease)) as [Heq|Hneq].
  - rewrite Heq; eexists; eexists; apply task_stack_park_fragments_lookup.
  - rewrite task_stack_park_fragments_lookup_other by exact Hneq.
    destruct (Hcoverage slot node Hnode) as [Hactive|Hparked]; [congruence|exact Hparked].
Qed.

Lemma task_stack_take_covers_selected : forall tasks lease,
  task_stack_live_coverage tasks None ->
  task_stack_live_coverage
    (glob_task_set_parked_stacks tasks (task_stack_take tasks.(parkedTaskStacks) lease))
    (Some (task_stack_key lease)).
Proof.
  intros tasks lease Hcoverage slot node Hnode.
  destruct (task_stack_key_eq_dec (slot, node.(taskGeneration)) (task_stack_key lease)) as [Heq|Hneq].
  - left; congruence.
  - right; change (exists region words,
      task_stack_take tasks.(parkedTaskStacks) lease (slot, node.(taskGeneration)) = Some (region, words)).
    rewrite task_stack_take_lookup_other by exact Hneq.
    destruct (Hcoverage slot node Hnode) as [Hactive|Hparked]; [discriminate|exact Hparked].
Qed.

Lemma task_commit_stack_coverage : forall tasks priority invocation node lease words active,
  node.(taskID) = lease.(stackLeaseSlot) -> node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  task_stack_live_coverage tasks active ->
  task_stack_live_coverage
    (glob_task_set_parked_stacks (task_commit tasks priority invocation node)
      (task_stack_park tasks.(parkedTaskStacks) lease words)) active.
Proof.
  intros tasks priority invocation node lease words active Hid Hgen Hcoverage slot updated Hupdated.
  destruct (Z.eq_dec slot node.(taskID)) as [Heq|Hneq].
  - subst slot; pose proof (proj1 (task_commit_publication_fields_eq tasks priority invocation node)) as Hnew.
    change ((task_commit tasks priority invocation node).(inUsedTaskStates) node.(taskID) = Some updated)
      in Hupdated.
    rewrite Hnew in Hupdated; injection Hupdated as Hupdated; subst updated.
    right; exists lease.(stackLeaseRegion), (task_stack_complete_fragments lease.(stackLeaseRegion) words).
    change (task_stack_park tasks.(parkedTaskStacks) lease words (node.(taskID), node.(taskGeneration)) =
      Some (lease.(stackLeaseRegion), task_stack_complete_fragments lease.(stackLeaseRegion) words)).
    rewrite Hid, Hgen; apply task_stack_park_lookup.
  - destruct (task_commit_lookup_old_fields tasks priority invocation node slot updated Hneq Hupdated)
      as [old [Hold Hfields]].
    assert (Hupdated_gen : updated.(taskGeneration) = old.(taskGeneration)).
    { exact (f_equal taskGeneration Hfields). }
    destruct (Hcoverage slot old Hold) as [Hactive|[region [fragments Hparked]]].
    + left; rewrite Hupdated_gen; exact Hactive.
    + right; exists region, fragments.
      change (task_stack_park tasks.(parkedTaskStacks) lease words (slot, updated.(taskGeneration)) =
        Some (region, fragments)).
      rewrite task_stack_park_lookup_other.
      * rewrite Hupdated_gen; exact Hparked.
      * intro Heq; apply Hneq; rewrite Hid; exact (f_equal fst Heq).
Qed.

Lemma task_stack_ready_coverage : forall sg tasks sched active,
  sched_ready_in_range sg tasks sched -> task_stack_live_coverage tasks active ->
  forall slot, In slot sched.(readyList) -> exists node,
    tasks.(inUsedTaskStates) slot = Some node /\
    (active = Some (slot, node.(taskGeneration)) \/
     exists region fragments,
       tasks.(parkedTaskStacks) (slot, node.(taskGeneration)) = Some (region, fragments)).
Proof.
  intros sg tasks sched active [Hready Hrest] Hcoverage slot Hin.
  destruct (Hready slot Hin) as [node [Hnode Hproperties]].
  exists node; split; [exact Hnode|apply Hcoverage; exact Hnode].
Qed.

Lemma armv7a_task_stack_continuations_commit : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks priority invocation node stacks,
  stacks (node.(taskID), node.(taskGeneration)) = None ->
  armv7a_task_stack_continuations abi tasks stacks |--
  armv7a_task_stack_continuations abi (task_commit tasks priority invocation node) stacks.
Proof.
  intros external platform port abi tasks priority invocation node stacks Hfresh.
  apply armv7a_task_stack_continuations_reindex.
  intros [slot generation] payload updated Hlookup Hupdated Hgen.
  change ((task_commit tasks priority invocation node).(inUsedTaskStates) slot = Some updated) in Hupdated.
  change (updated.(taskGeneration) = generation) in Hgen.
  destruct (Z.eq_dec slot node.(taskID)) as [Heq|Hneq].
  - subst slot.
    pose proof (proj1 (task_commit_publication_fields_eq tasks priority invocation node)) as Hnew.
    rewrite Hnew in Hupdated; injection Hupdated as Hupdated; subst updated.
    change (node.(taskGeneration) = generation) in Hgen.
    rewrite <- Hgen, Hfresh in Hlookup; discriminate.
  - destruct (task_commit_lookup_old_fields tasks priority invocation node slot updated Hneq Hupdated)
      as [old [Hold Hfields]].
    exists old; split; [exact Hold|]; split.
    + symmetry; exact (f_equal taskGeneration Hfields).
    + symmetry; exact (f_equal tcbStkPtr Hfields).
Qed.

Lemma armv7a_task_stack_continuations_save_sp : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks node sp outgoing stacks,
  tasks.(inUsedTaskStates) outgoing.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = outgoing.(stackLeaseGeneration) ->
  stacks (task_stack_key outgoing) = None ->
  armv7a_task_stack_continuations abi tasks stacks |--
  armv7a_task_stack_continuations abi
    (glob_task_set_usedtask tasks outgoing.(stackLeaseSlot) (task_set_saved_sp node sp)) stacks.
Proof.
  intros external platform port abi tasks node sp outgoing stacks Hnode Hgeneration Hnone.
  apply armv7a_task_stack_continuations_reindex.
  intros [slot generation] payload updated Hlookup Hupdated Hgen; cbn in Hgen.
  cbn [fst glob_task_set_usedtask inUsedTaskStates] in Hupdated.
  destruct (Z.eqb slot outgoing.(stackLeaseSlot)) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; injection Hupdated as Hupdated; subst updated.
    change (node.(taskGeneration) = generation) in Hgen.
    assert (Hkey : (outgoing.(stackLeaseSlot), generation) = task_stack_key outgoing)
      by (unfold task_stack_key; f_equal; congruence).
    rewrite Hkey, Hnone in Hlookup; discriminate.
  - exists updated; auto.
Qed.

(** Strengthened producer at the SAME protected publication cut as
    task_create_stack_park_initial_continuation. It preserves every old
    capsule, reindexes only live-generation SP facts, and deposits the
    initialized buffer plus its concrete frame slice exactly once. *)
Lemma task_create_stack_park_covered_continuation :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg region args task_return lower upper initial_name invocation origin acquired current slot image lease,
  UCOS2_state_inv sg current ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  let after := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    store_parked_stacks current.(TskState).(parkedTaskStacks) **
    armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) |--
  coq_prop (parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks)) &&
    (store_parked_stacks after.(TskState).(parkedTaskStacks) **
     armv7a_task_stack_continuations abi after.(TskState) after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg region args task_return lower upper initial_name invocation origin
    acquired current slot image lease Hvalid Hlayout Hregion actual Hcommit Hcreation after.
  pose proof (task_tcb_init_commit_binding_identity actual invocation origin acquired current slot image Hcommit)
    as Hidentity.
  assert (Hconsistent : parked_stacks_consistent current.(TskState) current.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  destruct (task_stack_creation_binding_commit_identity current.(TskState) actual.(initPrio)
    invocation origin lease (task_tcb_init_commit_node actual acquired slot image) Hcreation Hidentity)
    as [Hslot Hgeneration].
  assert (Hfresh : current.(TskState).(parkedTaskStacks) (task_stack_key lease) = None).
  { unfold task_stack_key; rewrite <- Hslot, <- Hgeneration.
    eapply task_commit_stack_key_absent;
      [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  set (saved := armv7a_initial_continuation lease args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return lower upper).
  assert (Hinitial : armv7a_initial_frame_binding saved).
  { apply task_create_initial_frame_binding with (region := region); assumption. }
  assert (Hslice : armv7a_task_frame_slice saved) by (apply armv7a_initial_frame_slice; exact Hinitial).
  assert (Hsp : task_stack_live_sp after.(TskState) (task_stack_key lease)
    saved.(armv7a_continuation_sp)).
  { destruct (task_create_stack_published_initial_pointer sg args task_return lower upper initial_name
      invocation origin acquired current slot image lease Hcommit Hcreation)
      as [node [Hnode [Hid [Hgen Hpointer]]]].
    change (after.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node) in Hnode.
    intros updated Hupdated Hg; cbn [task_stack_key fst] in Hupdated.
    assert (updated = node) by congruence; subst updated; exact Hpointer. }
  assert (Hreindex : armv7a_task_stack_continuations abi current.(TskState)
      current.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi after.(TskState) current.(TskState).(parkedTaskStacks)).
  { change (armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) |--
      armv7a_task_stack_continuations abi
        (glob_task_set_parked_stacks
          (task_commit current.(TskState) actual.(initPrio) invocation
            (task_tcb_init_commit_node actual acquired slot image)) after.(TskState).(parkedTaskStacks))
        current.(TskState).(parkedTaskStacks)).
    assert (Hnewkey : current.(TskState).(parkedTaskStacks)
      ((task_tcb_init_commit_node actual acquired slot image).(taskID),
       (task_tcb_init_commit_node actual acquired slot image).(taskGeneration)) = None).
    { rewrite Hslot, Hgeneration; exact Hfresh. }
    pose proof (armv7a_task_stack_continuations_commit external platform port abi
      current.(TskState) actual.(initPrio) invocation (task_tcb_init_commit_node actual acquired slot image)
      current.(TskState).(parkedTaskStacks) Hnewkey) as Hcommit_caps.
    sep_apply_l_atomic Hcommit_caps.
    apply armv7a_task_stack_continuations_used_map_eq; reflexivity. }
  assert (Hattachment : armv7a_task_stack_continuations abi current.(TskState)
      current.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi after.(TskState) after.(TskState).(parkedTaskStacks)).
  { sep_apply_l_atomic Hreindex.
    unfold armv7a_task_stack_continuations.
    assert (Hnew_entry :
      store_parked_continuations (armv7a_task_stack_entry abi after.(TskState))
        current.(TskState).(parkedTaskStacks) |--
      armv7a_task_stack_entry abi after.(TskState) (task_stack_key lease)
        (lease.(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
      store_parked_continuations (armv7a_task_stack_entry abi after.(TskState))
        current.(TskState).(parkedTaskStacks)).
    { unfold armv7a_task_stack_entry; Exists saved.
      assert (Hbinding : armv7a_continuation_binding saved) by apply armv7a_initial_continuation_binding.
      unfold armv7a_task_continuation_resource; cbn [saved armv7a_initial_continuation
        armv7a_continuation_call armv7a_continuation_stack]; entailer!. }
    intros heap Hheap.
    exact (store_parked_continuations_park (armv7a_task_stack_entry abi after.(TskState))
      current.(TskState).(parkedTaskStacks) lease saved.(armv7a_continuation_fragments)
      Hfresh heap (Hnew_entry heap Hheap)). }
  sep_apply_l_atomic Hattachment.
  pose proof (task_create_stack_protected_commit_resources sg TaskStackNoVFP region args
    task_return lower upper initial_name invocation origin acquired current slot image lease
    Hlayout Hregion Hcommit Hcreation Hconsistent Hfresh) as Hpark.
  cbv zeta in Hpark; sep_apply_l_atomic Hpark; entailer!.
Qed.

Lemma task_create_publication_covered_stack_merge :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg publication current active,
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  task_stack_live_coverage current.(TskState) active ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_publication_storage sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image) **
  task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
  armv7a_task_stack_continuations abi current.(TskState) current.(TskState).(parkedTaskStacks) |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current after /\
    task_stack_live_coverage after.(TskState) active) &&
  (UCOS2_inv sg after **
   armv7a_task_stack_continuations abi after.(TskState) after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication current active Hvalid Hinput Hcoverage after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current after)
    by (split; [exact Hinput|reflexivity]).
  destruct Hinput as [Hlayout [Hregion [Hcommit [Hcreation [[flags Hflags] Hname]]]]].
  set (actual := task_create_stack_publication_args publication).
  set (committed := task_create_stack_publication_raw_state sg publication current).
  assert (Hidentity : task_commit_identity current.(TskState) actual.(initPrio)
    publication.(stack_publication_invocation)
    (task_tcb_init_commit_node actual publication.(stack_publication_acquired)
      publication.(stack_publication_slot) publication.(stack_publication_image))).
  { eapply task_tcb_init_commit_binding_identity; exact Hcommit. }
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity) as [Hslot Hgen].
  assert (Hcovered : task_stack_live_coverage after.(TskState) active).
  { apply task_commit_stack_coverage; assumption. }
  assert (Hmerge : task_create_publication_storage sg actual publication.(stack_publication_invocation)
      publication.(stack_publication_acquired) current publication.(stack_publication_slot)
      publication.(stack_publication_image) |-- UCOS2_inv sg committed).
  { exact (task_tcb_init_publication_storage_merge__publication_and_returns sg actual
      publication.(stack_publication_invocation) publication.(stack_publication_origin)
      publication.(stack_publication_acquired) current publication.(stack_publication_slot)
      publication.(stack_publication_image) flags Hvalid Hcommit Hflags Hname). }
  sep_apply_l_atomic Hmerge; rewrite UCOS2_inv_split_parked_stacks; Intros.
  assert (Hcommitted : UCOS2_state_inv sg committed) by assumption.
  assert (Hmap : committed.(TskState).(parkedTaskStacks) = current.(TskState).(parkedTaskStacks))
    by reflexivity.
  rewrite Hmap.
  pose proof (task_create_stack_park_covered_continuation external platform port abi sg
    publication.(stack_publication_region) publication.(stack_publication_args)
    publication.(stack_publication_return) publication.(stack_publication_lower)
    publication.(stack_publication_upper) publication.(stack_publication_name)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) current publication.(stack_publication_slot)
    publication.(stack_publication_image) publication.(stack_publication_lease)
    Hvalid Hlayout Hregion Hcommit Hcreation) as Hpark.
  cbv zeta in Hpark; fold (task_create_stack_publication_args publication) in Hpark.
  fold (task_create_stack_publication_words publication) in Hpark.
  fold (task_create_stack_publication_state sg publication current) in Hpark; fold after in Hpark.
  sep_apply_l_atomic Hpark; Intros.
  assert (Hconsistent : parked_stacks_consistent committed.(TskState) after.(TskState).(parkedTaskStacks))
    by assumption.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg committed
    after.(TskState).(parkedTaskStacks) Hcommitted Hconsistent).
  unfold after, task_create_stack_publication_state, task_create_stack_published_state;
    entailer!.
Qed.

Lemma task_stack_framed_live_sp_load : forall sg state slot node (frame : Assertion) heap,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  (UCOS2_inv sg state ** frame) heap ->
  pointer_load (task_slot_addr sg slot) node.(tcbStkPtr) heap.
Proof.
  intros sg state slot node frame heap Hnode Haddress
    [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  eapply pointer_load_frame; [|exact Hjoin].
  eapply armv7a_irq_raw_live_stack_pointer_load; eassumption.
Qed.

(** Actual task-level cache stores and TCB-SP load, instantiated with the
    stronger SAME-map entry. This is the first real consumer of its SP
    and sixteen-word slice. No weak-to-strong conversion, future safety
    premise, new platform law, or assumed stability across the hook is
    involved. The input is explicitly AFTER the real save/SP-write/hook.
    Root's source producer is responsible for that preceding segment. *)
Lemma os_sched_install_take_covered_continuation :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg context outgoing hooked incoming resumed (frame : Assertion) heap,
  os_sched_saved_stack_binding context outgoing hooked ->
  os_sched_destination_binding external context outgoing hooked incoming resumed ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  task_stack_live_coverage hooked.(TskState) (Some (task_stack_key context.(os_sched_call_stack))) ->
  (UCOS2_inv sg hooked **
   task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion) outgoing **
   armv7a_task_stack_entry abi hooked.(TskState) (task_stack_key context.(os_sched_call_stack))
     (context.(os_sched_call_stack).(stackLeaseRegion), outgoing) **
   armv7a_task_stack_continuations abi hooked.(TskState) hooked.(TskState).(parkedTaskStacks) **
   frame) heap ->
  exists final selected,
    sched_install_heap_fragment sg heap final (task_slot_addr sg incoming.(stackLeaseSlot))
      selected.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads selected final /\
    selected.(armv7a_continuation_stack) = incoming /\
    selected.(armv7a_continuation_fragments) = resumed /\
    task_current_at (os_sched_install_context context outgoing incoming hooked)
      incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) /\
    task_stack_live_coverage
      (os_sched_install_context context outgoing incoming hooked).(TskState)
      (Some (task_stack_key incoming)) /\
    (UCOS2_inv sg (os_sched_install_context context outgoing incoming hooked) **
     armv7a_task_stack_continuations abi
       (os_sched_install_context context outgoing incoming hooked).(TskState)
       (os_sched_install_context context outgoing incoming hooked).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
       selected.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi selected ** frame) final.
Proof.
  intros external platform port abi sg context outgoing hooked incoming resumed frame heap
    Hsaved Hdestination Haddress Hcoverage Hbefore.
  destruct (os_sched_install_continuation_map_resources external sg context outgoing hooked incoming
    resumed (armv7a_task_stack_entry abi hooked.(TskState)) frame heap
    Hsaved Hdestination Haddress Hbefore)
    as [final [sp [Hrun [[Hcurrent Hrestore] Hafter]]]].
  set (installed := os_sched_install_context context outgoing incoming hooked).
  assert (Hextract : UCOS2_inv sg installed **
      task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
      armv7a_task_stack_entry abi hooked.(TskState) (task_stack_key incoming)
        (incoming.(stackLeaseRegion), resumed) **
      store_parked_continuations (armv7a_task_stack_entry abi hooked.(TskState))
        installed.(TskState).(parkedTaskStacks) ** frame |--
    EX selected,
      coq_prop (armv7a_continuation_binding selected /\
        selected.(armv7a_continuation_stack) = incoming /\
        selected.(armv7a_continuation_fragments) = resumed /\
        armv7a_task_frame_slice selected /\
        task_stack_live_sp hooked.(TskState) (task_stack_key incoming)
          selected.(armv7a_continuation_sp)) &&
      (UCOS2_inv sg installed **
       armv7a_task_stack_continuations abi installed.(TskState) installed.(TskState).(parkedTaskStacks) **
       task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
         selected.(armv7a_continuation_fragments) **
       armv7a_task_continuation_resource abi selected ** frame)).
  { unfold armv7a_task_stack_entry; Intros selected.
    assert (Hkey : task_stack_key selected.(armv7a_continuation_stack) = task_stack_key incoming) by tauto.
    assert (Hpayload : (selected.(armv7a_continuation_stack).(stackLeaseRegion),
      selected.(armv7a_continuation_fragments)) = (incoming.(stackLeaseRegion), resumed)) by tauto.
    assert (Hlease : selected.(armv7a_continuation_stack) = incoming).
    { unfold task_stack_key in Hkey; destruct selected.(armv7a_continuation_stack), incoming;
        cbn in *; congruence. }
    assert (Hfragments : selected.(armv7a_continuation_fragments) = resumed) by congruence.
    Exists selected; unfold armv7a_task_stack_continuations.
    rewrite Hlease, Hfragments; entailer!. }
  destruct (Hextract final Hafter) as [selected
    [[Hbinding [Hlease [Hfragments [Hslice Hsp]]]] Hresources]].
  destruct Hdestination as [Hhigh [[node [Hnode [Hgeneration [Hprio Harch]]]] Hother]].
  assert (Hnode_sp : node.(tcbStkPtr) = selected.(armv7a_continuation_sp)).
  { apply Hsp; assumption. }
  assert (Hload : pointer_load (task_slot_addr sg incoming.(stackLeaseSlot)) node.(tcbStkPtr) final).
  { eapply task_stack_framed_live_sp_load with (state := installed).
    - exact Hnode.
    - exact Haddress.
    - assert (Horder : UCOS2_inv sg installed **
        armv7a_task_stack_continuations abi installed.(TskState) installed.(TskState).(parkedTaskStacks) **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) **
        armv7a_task_continuation_resource abi selected ** frame |--
        UCOS2_inv sg installed **
        (armv7a_task_stack_continuations abi installed.(TskState) installed.(TskState).(parkedTaskStacks) **
         task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
           selected.(armv7a_continuation_fragments) **
         armv7a_task_continuation_resource abi selected ** frame)) by entailer!.
      exact (Horder final Hresources). }
  assert (Hloaded_sp : sp = selected.(armv7a_continuation_sp)).
  { rewrite <- Hnode_sp; eapply pointer_load_deterministic; [exact (proj2 Hrun)|exact Hload]. }
  assert (Hreads : armv7a_continuation_restore_reads selected final).
  { eapply armv7a_task_frame_slice_restore_reads; [exact Hbinding|exact Hslice|].
    assert (Horder : UCOS2_inv sg installed **
        armv7a_task_stack_continuations abi installed.(TskState) installed.(TskState).(parkedTaskStacks) **
        task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
          selected.(armv7a_continuation_fragments) **
        armv7a_task_continuation_resource abi selected ** frame |--
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) **
      (UCOS2_inv sg installed **
       armv7a_task_stack_continuations abi installed.(TskState) installed.(TskState).(parkedTaskStacks) **
       armv7a_task_continuation_resource abi selected ** frame)) by entailer!.
    exact (Horder final Hresources). }
  assert (Hcovered : task_stack_live_coverage installed.(TskState) (Some (task_stack_key incoming))).
  { exact (task_stack_take_covers_selected
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks) context.(os_sched_call_stack) outgoing))
      incoming (task_stack_park_covers_active hooked.(TskState) context.(os_sched_call_stack) outgoing Hcoverage)). }
  exists final, selected; rewrite Hloaded_sp in Hrun.
  exact (conj Hrun (conj Hreads (conj Hlease (conj Hfragments
    (conj Hcurrent (conj Hcovered Hresources)))))).
Qed.
