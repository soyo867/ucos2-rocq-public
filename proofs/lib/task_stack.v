Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.task.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition task_stack_region_end (region : TaskStackRegion) : addr :=
  region.(stackRegionBase) + region.(stackRegionWords) * sizeof(UINT).

Definition task_stack_region_top (region : TaskStackRegion) : addr :=
  if region.(stackRegionGrowsDown)
  then region.(stackRegionBase) + (region.(stackRegionWords) - 1) * sizeof(UINT)
  else region.(stackRegionBase).

Definition task_stack_region_bottom (region : TaskStackRegion) : addr :=
  if region.(stackRegionGrowsDown) then region.(stackRegionBase)
  else region.(stackRegionBase) + (region.(stackRegionWords) - 1) * sizeof(UINT).

(** A nonempty creation-stack domain for the selected 32-bit OS_STK.
    This is a resource/ABI condition, not a new runtime error branch.  A
    zero-length OS_TaskStkClr still has its separate no-access contract.
    Integer bounds do not establish C allocation provenance. *)
Definition valid_task_stack_region (region : TaskStackRegion) : Prop :=
  0 < region.(stackRegionWords) <= 4294967295 /\
  0 < region.(stackRegionBase) /\
  region.(stackRegionBase) mod sizeof(UINT) = 0 /\
  task_stack_region_end region <= 4294967295.

Definition task_stack_saved_pointer_in_range (region : TaskStackRegion) (sp : addr) : Prop :=
  region.(stackRegionBase) <= sp < task_stack_region_end region /\
  sp mod sizeof(UINT) = 0.

Lemma task_stack_region_top_in_range : forall region,
  valid_task_stack_region region ->
  region.(stackRegionBase) <= task_stack_region_top region < task_stack_region_end region.
Proof.
  intros region [Hwords Hrest]; unfold task_stack_region_top, task_stack_region_end.
  destruct region.(stackRegionGrowsDown); simpl; lia.
Qed.

Lemma task_stack_region_down_top_successor : forall region,
  region.(stackRegionGrowsDown) = true ->
  task_stack_region_top region + sizeof(UINT) = task_stack_region_end region.
Proof.
  intros region Hdown; unfold task_stack_region_top, task_stack_region_end.
  rewrite Hdown; ring.
Qed.

(** The generation is the existing allocation generation, not an additional
    counter or an application task ID.  This descriptor is pure: it is NOT
    an unforgeable token, a permission, or a second global task ledger.
    Physical exclusivity comes only from the QCP array assertion below. *)
Record TaskStackLease : Type := {
  stackLeaseRegion : TaskStackRegion;
  stackLeaseSlot : TaskID;
  stackLeaseGeneration : nat
}.

Definition task_stack_lease_of_allocation (region : TaskStackRegion)
  (allocation : TaskPrivateAllocation) : TaskStackLease :=
  {| stackLeaseRegion := region;
     stackLeaseSlot := allocation.(privateSlot);
     stackLeaseGeneration := allocation.(privateGeneration) |}.

Definition task_stack_creation_binding (tasks : Glob_TaskAbstractState)
  (priority : Priority) (invocation : nat) (origin : TaskInvocationOrigin)
  (lease : TaskStackLease) : Prop :=
  exists entry allocation,
    tasks.(taskLifecycle).(taskReservations) priority = Some entry /\
    entry.(creationInvocation) = invocation /\ entry.(creationOrigin) = origin /\
    entry.(creationAllocation) = Some allocation /\
    allocation.(privateSlot) = lease.(stackLeaseSlot) /\
    allocation.(privateGeneration) = lease.(stackLeaseGeneration).

Definition task_stack_lease_matches_task (lease : TaskStackLease)
  (node : TaskAbstractState) : Prop :=
  node.(taskID) = lease.(stackLeaseSlot) /\
  node.(taskGeneration) = lease.(stackLeaseGeneration) /\
  task_stack_saved_pointer_in_range lease.(stackLeaseRegion) node.(tcbStkPtr).

Definition task_stack_live_binding (tasks : Glob_TaskAbstractState)
  (lease : TaskStackLease) : Prop :=
  exists node, tasks.(inUsedTaskStates) lease.(stackLeaseSlot) = Some node /\
    task_stack_lease_matches_task lease node.

Lemma task_stack_creation_binding_allocation : forall tasks priority entry allocation region,
  tasks.(taskLifecycle).(taskReservations) priority = Some entry ->
  entry.(creationAllocation) = Some allocation ->
  task_stack_creation_binding tasks priority entry.(creationInvocation) entry.(creationOrigin)
    (task_stack_lease_of_allocation region allocation).
Proof. intros; exists entry, allocation; repeat split; assumption || reflexivity. Qed.

Lemma task_stack_creation_binding_frame : forall before after priority invocation origin lease,
  task_creation_frame invocation before after ->
  task_stack_creation_binding before priority invocation origin lease ->
  task_stack_creation_binding after priority invocation origin lease.
Proof.
  intros before after priority invocation origin lease Hframe
    [entry [allocation [Hentry [Hinv [Horigin [Hallocation Hidentity]]]]]].
  exists entry, allocation; split.
  - eapply task_creation_frame_lookup; eassumption.
  - repeat split; tauto.
Qed.

Lemma task_stack_creation_binding_private_image :
  forall tasks priority entry allocation image region,
  task_stack_creation_binding
    (task_update_private_image tasks priority entry allocation image)
    priority entry.(creationInvocation) entry.(creationOrigin)
    (task_stack_lease_of_allocation region allocation).
Proof.
  intros; unfold task_stack_creation_binding.
  eexists; eexists; simpl; destruct (Z.eq_dec priority priority);
    [repeat split; reflexivity|contradiction].
Qed.

Lemma task_stack_lease_matches_task_frame : forall lease before after,
  after.(taskID) = before.(taskID) ->
  after.(taskGeneration) = before.(taskGeneration) ->
  after.(tcbStkPtr) = before.(tcbStkPtr) ->
  task_stack_lease_matches_task lease before -> task_stack_lease_matches_task lease after.
Proof. intros; unfold task_stack_lease_matches_task in *; rewrite H, H0, H1; assumption. Qed.

Lemma task_stack_live_binding_task_map_frame : forall before after lease,
  before.(inUsedTaskStates) = after.(inUsedTaskStates) ->
  task_stack_live_binding before lease -> task_stack_live_binding after lease.
Proof. intros; unfold task_stack_live_binding in *; rewrite <- H; assumption. Qed.

Lemma task_stack_live_binding_reused_generation : forall tasks lease node,
  tasks.(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
  node.(taskGeneration) <> lease.(stackLeaseGeneration) ->
  ~ task_stack_live_binding tasks lease.
Proof.
  intros tasks lease node Hnode Hdifferent [other [Hother [_ [Hgeneration _]]]].
  assert (other = node) by congruence; subst other; contradiction.
Qed.

Lemma task_stack_creation_binding_commit_identity : forall tasks priority invocation origin lease node,
  task_stack_creation_binding tasks priority invocation origin lease ->
  task_commit_identity tasks priority invocation node ->
  node.(taskID) = lease.(stackLeaseSlot) /\
  node.(taskGeneration) = lease.(stackLeaseGeneration).
Proof.
  intros tasks priority invocation origin lease node
    [entry [allocation [Hentry [Hinv [Horigin [Hallocation [Hslot Hgen]]]]]]]
    [entry' [allocation' [Hentry' [Hinv' [Hallocation' [Hslot' [Hgen' Hprio]]]]]]].
  assert (entry' = entry) by congruence; subst entry'.
  assert (allocation' = allocation) by congruence; subst allocation'.
  split; congruence.
Qed.

Lemma task_commit_establishes_stack_binding : forall tasks priority invocation lease node,
  task_stack_lease_matches_task lease node ->
  task_stack_live_binding (task_commit tasks priority invocation node) lease.
Proof.
  intros tasks priority invocation lease node [Hslot [Hgen Hsp]].
  exists (task_set_links node tasks.(tcbListHead) None); split.
  - cbn [task_commit inUsedTaskStates].
    destruct (Z.eq_dec lease.(stackLeaseSlot) node.(taskID)); [reflexivity|congruence].
  - exact (conj Hslot (conj Hgen Hsp)).
Qed.

(** This is the application's actual buffer, in address order.  No implicit
    zeroing, allocation, TCB ownership or saved execution token is hidden. *)
Definition task_stack_storage (region : TaskStackRegion) (words : list (option Z)) : Assertion :=
  UIntArray.mixed_full region.(stackRegionBase) region.(stackRegionWords) words.

Lemma task_stack_storage_length : forall region words,
  task_stack_storage region words |-- coq_prop (Zlength words = region.(stackRegionWords)).
Proof. intros; apply UIntArray.mixed_full_Zlength. Qed.

(** A direct specialization of QCP's array split, not another array model. *)
Lemma task_stack_array_split_app : forall base left right,
  UIntArray.mixed_full base (Zlength left + Zlength right) (left ++ right) |--
  UIntArray.mixed_full base (Zlength left) left **
  UIntArray.mixed_full (base + Zlength left * sizeof(UINT)) (Zlength right) right.
Proof.
  intros base left right.
  pose proof (Zlength_nonneg left) as Hleft.
  pose proof (Zlength_nonneg right) as Hright.
  eapply derivable1_trans.
  - apply (UIntArray.mixed_full_split_to_mixed_full base (Zlength left)
      (Zlength left + Zlength right) (left ++ right)); lia.
  - rewrite sublist_app_exact1.
    rewrite (sublist_split_app_r (Zlength left) (Zlength left + Zlength right)
      (Zlength left) left right eq_refl ltac:(lia)).
    replace (Zlength left - Zlength left) with 0 by lia.
    replace (Zlength left + Zlength right - Zlength left) with (Zlength right) by lia.
    rewrite sublist_self by reflexivity; reflexivity.
Qed.

(** The middle [count] words are genuinely absent from this ownership.
    Lower/upper retain their current values; no old middle image is stored
    here.  In particular, this is not mixed_full with None at loaned words:
    None still owns an undefined cell.  A Flag/Multi borrower must separately
    relate its typed representation to the actual middle array before a
    transfer or return can use these rules. *)
Definition task_stack_storage_without_region (region : TaskStackRegion)
  (lower : list (option Z)) (count : Z) (upper : list (option Z)) : Assertion :=
  UIntArray.mixed_full region.(stackRegionBase) (Zlength lower) lower **
  UIntArray.mixed_full
    (region.(stackRegionBase) + (Zlength lower + count) * sizeof(UINT)) (Zlength upper) upper.

Lemma task_stack_storage_split_region : forall region lower middle upper,
  region.(stackRegionWords) = Zlength lower + Zlength middle + Zlength upper ->
  task_stack_storage region (lower ++ middle ++ upper) |--
  UIntArray.mixed_full (region.(stackRegionBase) + Zlength lower * sizeof(UINT))
    (Zlength middle) middle **
  task_stack_storage_without_region region lower (Zlength middle) upper.
Proof.
  intros region lower middle upper Hsize.
  unfold task_stack_storage, task_stack_storage_without_region; rewrite Hsize.
  eapply derivable1_trans with (y :=
    UIntArray.mixed_full region.(stackRegionBase) (Zlength lower) lower **
    UIntArray.mixed_full (region.(stackRegionBase) + Zlength lower * sizeof(UINT))
      (Zlength middle + Zlength upper) (middle ++ upper)).
  - pose proof (task_stack_array_split_app region.(stackRegionBase) lower (middle ++ upper))
      as Hsplit.
    rewrite Zlength_app in Hsplit.
    replace (Zlength lower + Zlength middle + Zlength upper)
      with (Zlength lower + (Zlength middle + Zlength upper)) by lia.
    exact Hsplit.
  - eapply derivable1_trans with (y :=
      UIntArray.mixed_full region.(stackRegionBase) (Zlength lower) lower **
      (UIntArray.mixed_full (region.(stackRegionBase) + Zlength lower * sizeof(UINT))
         (Zlength middle) middle **
       UIntArray.mixed_full
         (region.(stackRegionBase) + (Zlength lower + Zlength middle) * sizeof(UINT))
         (Zlength upper) upper)).
    + apply derivable1_sepcon_mono; [apply derivable1_refl|].
      pose proof (task_stack_array_split_app
        (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) middle upper) as Hsplit.
      replace (region.(stackRegionBase) + Zlength lower * sizeof(UINT) +
        Zlength middle * sizeof(UINT)) with
        (region.(stackRegionBase) + (Zlength lower + Zlength middle) * sizeof(UINT))
        in Hsplit by ring.
      exact Hsplit.
    + entailer!.
Qed.

(** The returned middle may have changed arbitrarily within its original
    word count.  Both the unchanged and updated-image cases use this same
    rule because the residual does not retain ownership or values there. *)
Lemma task_stack_storage_merge_region : forall region lower middle upper count,
  region.(stackRegionWords) = Zlength lower + count + Zlength upper ->
  Zlength middle = count ->
  UIntArray.mixed_full (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) count middle **
  task_stack_storage_without_region region lower count upper |--
  task_stack_storage region (lower ++ middle ++ upper).
Proof.
  intros region lower middle upper count Hsize Hlength; subst count.
  pose proof (Zlength_nonneg lower) as Hlower.
  pose proof (Zlength_nonneg middle) as Hmiddle.
  pose proof (Zlength_nonneg upper) as Hupper.
  pose proof (UIntArray.mixed_full_merge_to_mixed_full
    (region.(stackRegionBase) + Zlength lower * sizeof(UINT))
    (Zlength middle) (Zlength middle + Zlength upper) middle upper ltac:(lia)) as Hmiddle_merge.
  replace (Zlength middle + Zlength upper - Zlength middle)
    with (Zlength upper) in Hmiddle_merge by lia.
  replace (region.(stackRegionBase) + Zlength lower * sizeof(UINT) +
    Zlength middle * sizeof(UINT)) with
    (region.(stackRegionBase) + (Zlength lower + Zlength middle) * sizeof(UINT))
    in Hmiddle_merge by ring.
  pose proof (UIntArray.mixed_full_merge_to_mixed_full region.(stackRegionBase)
    (Zlength lower) (Zlength lower + Zlength middle + Zlength upper)
    lower (middle ++ upper) ltac:(lia)) as Hwhole_merge.
  replace (Zlength lower + Zlength middle + Zlength upper - Zlength lower)
    with (Zlength middle + Zlength upper) in Hwhole_merge by lia.
  unfold task_stack_storage, task_stack_storage_without_region; rewrite Hsize.
  eapply derivable1_trans with (y :=
    UIntArray.mixed_full region.(stackRegionBase) (Zlength lower) lower **
    (UIntArray.mixed_full (region.(stackRegionBase) + Zlength lower * sizeof(UINT))
       (Zlength middle) middle **
     UIntArray.mixed_full
       (region.(stackRegionBase) + (Zlength lower + Zlength middle) * sizeof(UINT))
       (Zlength upper) upper)).
  - entailer!.
  - eapply derivable1_trans; [|exact Hwhole_merge].
    apply derivable1_sepcon_mono; [apply derivable1_refl|exact Hmiddle_merge].
Qed.

Lemma task_stack_storage_split_cell : forall region words index,
  0 <= index < region.(stackRegionWords) ->
  task_stack_storage region words |--
  UIntArray.mixedstoreA region.(stackRegionBase) index (Znth index words None) **
  UIntArray.mixed_missing_i region.(stackRegionBase) index 0 region.(stackRegionWords) words.
Proof. intros; apply UIntArray.mixed_full_split_to_mixed_missing_i; assumption. Qed.

Lemma task_stack_storage_merge_cell : forall region words index,
  0 <= index < region.(stackRegionWords) ->
  UIntArray.mixedstoreA region.(stackRegionBase) index (Znth index words None) **
  UIntArray.mixed_missing_i region.(stackRegionBase) index 0 region.(stackRegionWords) words |--
  task_stack_storage region words.
Proof.
  intros; unfold task_stack_storage; eapply derivable1_trans.
  - apply UIntArray.mixed_missing_i_merge_to_mixed_full; assumption.
  - rewrite replace_Znth_Znth; reflexivity.
Qed.

Lemma task_stack_storage_merge_updated_cell : forall region words index value,
  0 <= index < region.(stackRegionWords) ->
  UIntArray.mixedstoreA region.(stackRegionBase) index value **
  UIntArray.mixed_missing_i region.(stackRegionBase) index 0 region.(stackRegionWords) words |--
  task_stack_storage region (replace_Znth index value words).
Proof. intros; apply UIntArray.mixed_missing_i_merge_to_mixed_full; assumption. Qed.

Definition task_stack_live_resources (tasks : Glob_TaskAbstractState)
  (lease : TaskStackLease) (words : list (option Z)) : Assertion :=
  coq_prop (task_stack_live_binding tasks lease) && task_stack_storage lease.(stackLeaseRegion) words.

(** A resource assembly AT THE PROTECTED COMMIT, not a rule for holding the
    initial image through Restore.  The receiving Task/context protocol must
    consume these bytes before another task may execute.  No such global
    protocol or callable Save/Restore implementation is postulated here. *)
Lemma task_stack_commit_resources : forall tasks priority invocation origin lease node words,
  task_stack_creation_binding tasks priority invocation origin lease ->
  task_commit_identity tasks priority invocation node ->
  task_stack_saved_pointer_in_range lease.(stackLeaseRegion) node.(tcbStkPtr) ->
  task_stack_storage lease.(stackLeaseRegion) words |--
  task_stack_live_resources (task_commit tasks priority invocation node) lease words.
Proof.
  intros tasks priority invocation origin lease node words Hbinding Hidentity Hsp.
  destruct (task_stack_creation_binding_commit_identity tasks priority invocation origin lease node
    Hbinding Hidentity) as [Hslot Hgen].
  pose proof (task_commit_establishes_stack_binding tasks priority invocation lease node
    (conj Hslot (conj Hgen Hsp))) as Hlive.
  unfold task_stack_live_resources; entailer!.
Qed.

(** A fragment owns only its explicit interval.  The bounds are word
    offsets relative to the caller's actual buffer; QCP mixed_seg supplies
    the content-length and typed-cell obligations. *)
Definition task_stack_fragment_rep (region : TaskStackRegion)
  (fragment : TaskStackFragment) : Assertion :=
  let '((lo, hi), words) := fragment in
  UIntArray.mixed_seg region.(stackRegionBase) lo hi words.

Definition task_stack_fragments_rep (region : TaskStackRegion)
  (fragments : TaskStackFragments) : Assertion :=
  iter_sepcon (map (task_stack_fragment_rep region) fragments).

Definition task_stack_complete_fragments (region : TaskStackRegion)
  (words : list (option Z)) : TaskStackFragments :=
  [(0, region.(stackRegionWords), words)].

(** Ordered, disjoint, nonempty intervals inside the caller extent.
    This is not a claim that the fragments cover that extent.  Borrowed
    intervals must be owned by their actual Flag/Multi/call consumers. *)
Fixpoint task_stack_fragments_in_range (limit lower : Z)
  (fragments : TaskStackFragments) : Prop :=
  match fragments with
  | [] => True
  | ((lo, hi), _) :: rest =>
      lower <= lo /\ lo < hi <= limit /\
      task_stack_fragments_in_range limit hi rest
  end.

Lemma task_stack_complete_fragments_in_range : forall region words,
  valid_task_stack_region region ->
  task_stack_fragments_in_range region.(stackRegionWords) 0
    (task_stack_complete_fragments region words).
Proof.
  intros region words [Hwords Hrest].
  unfold task_stack_complete_fragments; simpl; repeat split; lia.
Qed.

Lemma task_stack_fragments_rep_complete : forall region words,
  task_stack_fragments_rep region (task_stack_complete_fragments region words) --||--
  task_stack_storage region words.
Proof.
  intros region words; unfold task_stack_fragments_rep, task_stack_complete_fragments.
  cbn [map]; split.
  - eapply derivable1_trans; [apply derivable1_iter_sepcon_l|].
    cbn [fold_left task_stack_fragment_rep].
    unfold task_stack_storage, UIntArray.mixed_full; entailer!.
  - eapply derivable1_trans; [|apply derivable1_iter_sepcon_r].
    cbn [fold_left task_stack_fragment_rep].
    unfold task_stack_storage, UIntArray.mixed_full; entailer!.
Qed.

Lemma task_stack_fragments_rep_app : forall region first second,
  task_stack_fragments_rep region (first ++ second) --||--
  task_stack_fragments_rep region first ** task_stack_fragments_rep region second.
Proof.
  intros; unfold task_stack_fragments_rep; rewrite map_app; split.
  - apply derivable1_sepcon_iter_sepcon2.
  - apply derivable1_sepcon_iter_sepcon1.
Qed.

(** The context protocol owns finite, parked stack fragments.
    Its key includes the EXISTING Task generation: an old
    retiring stack and a new task at the same TCB slot need not be the same
    allocation.  Values contain only the otherwise unavailable buffer
    descriptor and current bytes, not a duplicate Task state.  UCOS2_inv
    assembles the map stored directly in Glob_TaskAbstractState.  The
    platform/call protocol must keep its executing fragments outside this
    ownership; a TCB current-cache pointer alone does not identify that
    execution phase. *)
Definition task_stack_key (lease : TaskStackLease) : TaskID * nat :=
  (lease.(stackLeaseSlot), lease.(stackLeaseGeneration)).

Definition task_stack_key_eq_dec : forall a b : TaskID * nat, {a = b} + {a <> b}.
Proof. decide equality; [apply Nat.eq_dec|apply Z.eq_dec]. Defined.

Definition task_stack_map_entry (_key : TaskID * nat)
  (entry : TaskStackRegion * TaskStackFragments) : Assertion :=
  task_stack_fragments_rep (fst entry) (snd entry).

Definition store_parked_stacks (stacks : TaskStackMap) : Assertion :=
  store_map task_stack_map_entry stacks.

(** All shared Task storage. Executing/private stacks and borrowed typed
    intervals are owned by their callers, not a second time by this module. *)
Definition task_shared_rep (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) : Assertion :=
  task_public_storage sg tasks ** store_parked_stacks tasks.(parkedTaskStacks).

Definition task_stack_park_fragments (stacks : TaskStackMap) (lease : TaskStackLease)
  (fragments : TaskStackFragments) : TaskStackMap :=
  field_update task_stack_key_eq_dec stacks (task_stack_key lease)
    (Some (lease.(stackLeaseRegion), fragments)).

Definition task_stack_park (stacks : TaskStackMap) (lease : TaskStackLease)
  (words : list (option Z)) : TaskStackMap :=
  task_stack_park_fragments stacks lease
    (task_stack_complete_fragments lease.(stackLeaseRegion) words).

Definition task_stack_take (stacks : TaskStackMap) (lease : TaskStackLease) : TaskStackMap :=
  field_update task_stack_key_eq_dec stacks (task_stack_key lease) None.

Lemma task_stack_park_lookup : forall stacks lease words,
  task_stack_park stacks lease words (task_stack_key lease) =
    Some (lease.(stackLeaseRegion), task_stack_complete_fragments lease.(stackLeaseRegion) words).
Proof. intros; apply field_update_same. Qed.

Lemma task_stack_park_fragments_lookup : forall stacks lease fragments,
  task_stack_park_fragments stacks lease fragments (task_stack_key lease) =
    Some (lease.(stackLeaseRegion), fragments).
Proof. intros; apply field_update_same. Qed.

Lemma task_stack_park_fragments_lookup_other : forall stacks lease fragments key,
  key <> task_stack_key lease ->
  task_stack_park_fragments stacks lease fragments key = stacks key.
Proof. intros; apply field_update_other; assumption. Qed.

Lemma task_stack_park_lookup_other : forall stacks lease words key,
  key <> task_stack_key lease -> task_stack_park stacks lease words key = stacks key.
Proof. intros; apply field_update_other; assumption. Qed.

Lemma task_stack_take_lookup : forall stacks lease,
  task_stack_take stacks lease (task_stack_key lease) = None.
Proof. intros; apply field_update_same. Qed.

Lemma task_stack_take_lookup_other : forall stacks lease key,
  key <> task_stack_key lease -> task_stack_take stacks lease key = stacks key.
Proof. intros; apply field_update_other; assumption. Qed.

Lemma task_stack_keys_distinct_generations : forall first second,
  first.(stackLeaseGeneration) <> second.(stackLeaseGeneration) ->
  task_stack_key first <> task_stack_key second.
Proof. intros first second Hgen Hkey; injection Hkey; congruence. Qed.

Lemma store_parked_stacks_empty :
  emp |-- store_parked_stacks (fun _ => None).
Proof.
  unfold store_parked_stacks, store_map.
  Exists (@nil (TaskID * nat)); simpl; entailer!.
  - apply List.NoDup_nil.
  - intros key; split; [contradiction|intros [entry Hentry]; discriminate].
Qed.

(** Transfer consumes the actual initialized/saved bytes.  It is never a
    rule deriving a stack from a pure lease or a Task lookup. *)
Lemma store_parked_stacks_park_fragments : forall stacks lease fragments,
  stacks (task_stack_key lease) = None ->
  task_stack_fragments_rep lease.(stackLeaseRegion) fragments ** store_parked_stacks stacks |--
  store_parked_stacks (task_stack_park_fragments stacks lease fragments).
Proof.
  intros stacks lease fragments Hnone; unfold store_parked_stacks.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    task_stack_map_entry stacks (task_stack_key lease) Hnone).
  assert (Hframe : forall key, key <> task_stack_key lease ->
    stacks key = task_stack_park_fragments stacks lease fragments key).
  { intros; symmetry; apply task_stack_park_fragments_lookup_other; assumption. }
  rewrite (store_map_missing_i_equiv _ _ _ (task_stack_key lease) Hframe).
  change (task_stack_fragments_rep (stackLeaseRegion lease) fragments) with
    (task_stack_map_entry (task_stack_key lease) (lease.(stackLeaseRegion), fragments)).
  entailer!.
  apply store_map_merge; apply task_stack_park_fragments_lookup.
Qed.

Lemma store_parked_stacks_park : forall stacks lease words,
  stacks (task_stack_key lease) = None ->
  task_stack_storage lease.(stackLeaseRegion) words ** store_parked_stacks stacks |--
  store_parked_stacks (task_stack_park stacks lease words).
Proof.
  intros stacks lease words Hnone; unfold task_stack_park.
  eapply derivable1_trans; [|apply store_parked_stacks_park_fragments; exact Hnone].
  apply derivable1_sepcon_mono; [|reflexivity].
  exact (proj2 (task_stack_fragments_rep_complete lease.(stackLeaseRegion) words)).
Qed.

(** Removing a parked entry transfers its bytes to the receiving context;
    removal alone does not run the task, free application storage, or prove
    that a deleted task has stopped using its stack. *)
Lemma store_parked_stacks_take_fragments : forall stacks lease fragments,
  stacks (task_stack_key lease) = Some (lease.(stackLeaseRegion), fragments) ->
  store_parked_stacks stacks |--
  task_stack_fragments_rep lease.(stackLeaseRegion) fragments **
    store_parked_stacks (task_stack_take stacks lease).
Proof.
  intros stacks lease fragments Hentry; unfold store_parked_stacks.
  sep_apply_l_atomic (store_map_split task_stack_map_entry (task_stack_key lease)
    (lease.(stackLeaseRegion), fragments) stacks Hentry).
  assert (Hframe : forall key, key <> task_stack_key lease ->
    stacks key = task_stack_take stacks lease key).
  { intros; symmetry; apply task_stack_take_lookup_other; assumption. }
  rewrite (store_map_missing_i_equiv _ _ _ (task_stack_key lease) Hframe).
  sep_apply_l_atomic (store_map_missing_equiv_store_map task_stack_map_entry
    (task_stack_take stacks lease) (task_stack_key lease) (task_stack_take_lookup stacks lease)).
  unfold task_stack_map_entry; simpl; entailer!.
Qed.

Lemma store_parked_stacks_take : forall stacks lease words,
  stacks (task_stack_key lease) = Some (lease.(stackLeaseRegion),
    task_stack_complete_fragments lease.(stackLeaseRegion) words) ->
  store_parked_stacks stacks |--
  task_stack_storage lease.(stackLeaseRegion) words **
    store_parked_stacks (task_stack_take stacks lease).
Proof.
  intros stacks lease words Hentry.
  eapply derivable1_trans; [apply store_parked_stacks_take_fragments; exact Hentry|].
  apply derivable1_sepcon_mono; [|reflexivity].
  exact (proj1 (task_stack_fragments_rep_complete lease.(stackLeaseRegion) words)).
Qed.

Lemma store_parked_stacks_switch_fragments : forall stacks outgoing incoming saved resumed,
  stacks (task_stack_key outgoing) = None ->
  task_stack_park_fragments stacks outgoing saved (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), resumed) ->
  task_stack_fragments_rep outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks |--
  task_stack_fragments_rep incoming.(stackLeaseRegion) resumed **
    store_parked_stacks (task_stack_take (task_stack_park_fragments stacks outgoing saved) incoming).
Proof.
  intros stacks outgoing incoming saved resumed Hnone Hincoming.
  sep_apply_l_atomic (store_parked_stacks_park_fragments stacks outgoing saved Hnone).
  apply store_parked_stacks_take_fragments; exact Hincoming.
Qed.

(** The continuation component uses the SAME keys and payloads as the
    physical stack map. It is not a second independently updated ledger.
    [resource] is supplied by the source-bound platform protocol: neither
    a stack lease nor initialized bytes entail this assertion. Keeping it
    separate from [store_parked_stacks] lets existing byte-only clients keep
    their interface without silently upgrading their permissions. A source
    Save/Restore protocol must carry both components at every cut. *)
Definition store_parked_continuations
  (resource : (TaskID * nat) -> (TaskStackRegion * TaskStackFragments) -> Assertion)
  (stacks : TaskStackMap) : Assertion := store_map resource stacks.

Lemma store_parked_continuations_park : forall resource stacks lease fragments,
  stacks (task_stack_key lease) = None ->
  resource (task_stack_key lease) (lease.(stackLeaseRegion), fragments) **
    store_parked_continuations resource stacks |--
  store_parked_continuations resource (task_stack_park_fragments stacks lease fragments).
Proof.
  intros resource stacks lease fragments Hnone; unfold store_parked_continuations.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    resource stacks (task_stack_key lease) Hnone).
  assert (Hframe : forall key, key <> task_stack_key lease ->
    stacks key = task_stack_park_fragments stacks lease fragments key).
  { intros; symmetry; apply task_stack_park_fragments_lookup_other; assumption. }
  rewrite (store_map_missing_i_equiv _ _ _ (task_stack_key lease) Hframe).
  apply store_map_merge; apply task_stack_park_fragments_lookup.
Qed.

Lemma store_parked_continuations_take : forall resource stacks lease fragments,
  stacks (task_stack_key lease) = Some (lease.(stackLeaseRegion), fragments) ->
  store_parked_continuations resource stacks |--
  resource (task_stack_key lease) (lease.(stackLeaseRegion), fragments) **
    store_parked_continuations resource (task_stack_take stacks lease).
Proof.
  intros resource stacks lease fragments Hentry; unfold store_parked_continuations.
  sep_apply_l_atomic (store_map_split resource (task_stack_key lease)
    (lease.(stackLeaseRegion), fragments) stacks Hentry).
  assert (Hframe : forall key, key <> task_stack_key lease ->
    stacks key = task_stack_take stacks lease key).
  { intros; symmetry; apply task_stack_take_lookup_other; assumption. }
  rewrite (store_map_missing_i_equiv _ _ _ (task_stack_key lease) Hframe).
  sep_apply_l_atomic (store_map_missing_equiv_store_map resource
    (task_stack_take stacks lease) (task_stack_key lease) (task_stack_take_lookup stacks lease)).
  entailer!.
Qed.

Lemma store_parked_continuations_switch :
  forall resource stacks outgoing incoming saved resumed,
  stacks (task_stack_key outgoing) = None ->
  task_stack_park_fragments stacks outgoing saved (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), resumed) ->
  resource (task_stack_key outgoing) (outgoing.(stackLeaseRegion), saved) **
    store_parked_continuations resource stacks |--
  resource (task_stack_key incoming) (incoming.(stackLeaseRegion), resumed) **
    store_parked_continuations resource
      (task_stack_take (task_stack_park_fragments stacks outgoing saved) incoming).
Proof.
  intros resource stacks outgoing incoming saved resumed Hnone Hentry.
  sep_apply_l_atomic (store_parked_continuations_park resource stacks outgoing saved Hnone).
  apply store_parked_continuations_take; exact Hentry.
Qed.

Lemma task_stack_commit_park_resources :
  forall tasks priority invocation origin lease node words stacks,
  task_stack_creation_binding tasks priority invocation origin lease ->
  task_commit_identity tasks priority invocation node ->
  task_stack_saved_pointer_in_range lease.(stackLeaseRegion) node.(tcbStkPtr) ->
  stacks (task_stack_key lease) = None ->
  task_stack_storage lease.(stackLeaseRegion) words ** store_parked_stacks stacks |--
  coq_prop (task_stack_live_binding (task_commit tasks priority invocation node) lease) &&
    store_parked_stacks (task_stack_park stacks lease words).
Proof.
  intros tasks priority invocation origin lease node words stacks Hbinding Hidentity Hsp Hnone.
  destruct (task_stack_creation_binding_commit_identity tasks priority invocation origin lease node
    Hbinding Hidentity) as [Hslot Hgeneration].
  pose proof (task_commit_establishes_stack_binding tasks priority invocation lease node
    (conj Hslot (conj Hgeneration Hsp))) as Hlive.
  sep_apply_l_atomic (store_parked_stacks_park stacks lease words Hnone).
  entailer!.
Qed.

(** Resource-side handoff AFTER outgoing bytes have actually been saved
    and the outgoing-stack hook call has returned its required resources.
    The caller must separately establish the source-correct TCB SP writes,
    destination selection, hooks and invocation protocol.  We deliberately
    return the incoming bytes, not another global copy of them.  Interrupt
    entry may already own the outgoing saved frame; first start/self-delete
    use [take] without claiming that a runnable outgoing task was parked. *)
Lemma store_parked_stacks_switch : forall stacks outgoing incoming saved resumed,
  stacks (task_stack_key outgoing) = None ->
  task_stack_park stacks outgoing saved (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), task_stack_complete_fragments incoming.(stackLeaseRegion) resumed) ->
  task_stack_storage outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks |--
  task_stack_storage incoming.(stackLeaseRegion) resumed **
    store_parked_stacks (task_stack_take (task_stack_park stacks outgoing saved) incoming).
Proof.
  intros stacks outgoing incoming saved resumed Hnone Hincoming.
  sep_apply_l_atomic (store_parked_stacks_park stacks outgoing saved Hnone).
  apply store_parked_stacks_take; exact Hincoming.
Qed.

Lemma store_parked_stacks_switch_distinct : forall stacks outgoing incoming saved resumed,
  task_stack_key incoming <> task_stack_key outgoing ->
  stacks (task_stack_key outgoing) = None ->
  stacks (task_stack_key incoming) = Some (incoming.(stackLeaseRegion),
    task_stack_complete_fragments incoming.(stackLeaseRegion) resumed) ->
  task_stack_storage outgoing.(stackLeaseRegion) saved ** store_parked_stacks stacks |--
  task_stack_storage incoming.(stackLeaseRegion) resumed **
    store_parked_stacks (task_stack_take (task_stack_park stacks outgoing saved) incoming).
Proof.
  intros; apply store_parked_stacks_switch; [assumption|].
  rewrite task_stack_park_lookup_other by assumption; assumption.
Qed.

(** A stale priority cache can request a switch to the same task.  There
    are not two copies of its buffer: take consumes the just-saved entry. *)
Lemma store_parked_stacks_switch_same : forall stacks lease saved,
  stacks (task_stack_key lease) = None ->
  task_stack_storage lease.(stackLeaseRegion) saved ** store_parked_stacks stacks |--
  task_stack_storage lease.(stackLeaseRegion) saved **
    store_parked_stacks (task_stack_take (task_stack_park stacks lease saved) lease).
Proof.
  intros; apply store_parked_stacks_switch; [assumption|apply task_stack_park_lookup].
Qed.

Lemma task_stack_take_park_lookup : forall stacks lease saved key,
  stacks (task_stack_key lease) = None ->
  task_stack_take (task_stack_park stacks lease saved) lease key = stacks key.
Proof.
  intros; unfold task_stack_take, task_stack_park, task_stack_park_fragments, field_update.
  destruct (task_stack_key_eq_dec key (task_stack_key lease)); [subst; symmetry|]; auto.
Qed.

(** Consistency of registered fragments, not completeness of all task
    stacks or all bytes of one stack.  A Flag node can be owned separately
    while this map retains its real complement.  Executing fragments and
    borrowed intervals still require their actual call/context partition;
    a saved SP inside the whole extent does not prove a restore frame is
    in the retained fragments.  Publication uses existing history, not a new
    owner/generation ledger.  A retired generation can retain a parked
    buffer until its real retirement/return protocol consumes it; it need
    not still be in the live map.  Restoring a buffer separately requires
    the matching live binding.  These pure facts do not grant any bytes. *)
Definition parked_stacks_consistent (tasks : Glob_TaskAbstractState)
  (stacks : TaskStackMap) : Prop :=
  forall slot generation region fragments,
    stacks (slot, generation) = Some (region, fragments) ->
    valid_task_stack_region region /\
    task_stack_fragments_in_range region.(stackRegionWords) 0 fragments /\
    (exists invocation, task_publication_happened tasks invocation slot generation) /\
    forall node, tasks.(inUsedTaskStates) slot = Some node ->
      node.(taskGeneration) = generation ->
      task_stack_lease_matches_task
        {| stackLeaseRegion := region; stackLeaseSlot := slot;
           stackLeaseGeneration := generation |} node.

Lemma parked_stacks_empty_consistent : forall tasks,
  parked_stacks_consistent tasks (fun _ => None).
Proof. intros tasks slot generation region words Hentry; discriminate. Qed.

Lemma parked_stacks_consistent_transport : forall before after stacks,
  (forall observer slot generation,
    task_publication_happened before observer slot generation ->
    task_publication_happened after observer slot generation) ->
  (forall slot node, after.(inUsedTaskStates) slot = Some node ->
    exists old, before.(inUsedTaskStates) slot = Some old /\
      node.(taskID) = old.(taskID) /\
      node.(taskGeneration) = old.(taskGeneration) /\
      node.(tcbStkPtr) = old.(tcbStkPtr)) ->
  parked_stacks_consistent before stacks -> parked_stacks_consistent after stacks.
Proof.
  intros before after stacks Hhistory Hnodes Hconsistent slot generation region fragments Hentry.
  destruct (Hconsistent slot generation region fragments Hentry)
    as [Hregion [Hgeometry [[observer Hobserved] Hbinding]]].
  split; [exact Hregion|]. split; [exact Hgeometry|]. split.
  - exists observer; apply Hhistory; exact Hobserved.
  - intros node Hnode Hgeneration.
    destruct (Hnodes slot node Hnode) as [old [Hold [Hid [Hgen Hsp]]]].
    eapply task_stack_lease_matches_task_frame; [exact Hid|exact Hgen|exact Hsp|].
    apply Hbinding; [exact Hold|congruence].
Qed.

Lemma parked_stacks_consistent_task_map_frame : forall before after stacks,
  before.(inUsedTaskStates) = after.(inUsedTaskStates) ->
  (forall invocation slot generation,
    task_publication_happened before invocation slot generation ->
    task_publication_happened after invocation slot generation) ->
  parked_stacks_consistent before stacks -> parked_stacks_consistent after stacks.
Proof.
  intros before after stacks Hused Hhistory Hconsistent slot generation region words Hentry.
  destruct (Hconsistent slot generation region words Hentry)
    as [Hregion [Hgeometry [[inv Hinv] Hbinding]]].
  split; [exact Hregion|]. split; [exact Hgeometry|]. split.
  - exists inv; apply Hhistory; exact Hinv.
  - rewrite <- Hused; exact Hbinding.
Qed.

Lemma parked_stacks_consistent_update_task : forall tasks tid old new stacks,
  tasks.(inUsedTaskStates) tid = Some old ->
  new.(taskID) = old.(taskID) ->
  new.(taskGeneration) = old.(taskGeneration) ->
  new.(tcbStkPtr) = old.(tcbStkPtr) ->
  parked_stacks_consistent tasks stacks ->
  parked_stacks_consistent (glob_task_set_usedtask tasks tid new) stacks.
Proof.
  intros tasks tid old new stacks Hold Hid Hgen Hsp Hconsistent
    slot generation region fragments Hentry.
  destruct (Hconsistent slot generation region fragments Hentry)
    as [Hregion [Hgeometry [Hhistory Hbinding]]].
  split; [exact Hregion|]. split; [exact Hgeometry|]. split; [exact Hhistory|].
  intros node Hnode Hgeneration; simpl in Hnode.
  destruct (Z.eqb slot tid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot.
    injection Hnode as Hnode; subst node.
    eapply task_stack_lease_matches_task_frame; [exact Hid|exact Hgen|exact Hsp|].
    apply Hbinding; [exact Hold|congruence].
  - exact (Hbinding node Hnode Hgeneration).
Qed.

Lemma parked_stacks_consistent_set_parked_stacks_eq : forall tasks stored observed,
  parked_stacks_consistent (glob_task_set_parked_stacks tasks stored) observed =
  parked_stacks_consistent tasks observed.
Proof. reflexivity. Qed.

Lemma task_stack_take_preserves_consistency : forall tasks stacks lease,
  parked_stacks_consistent tasks stacks ->
  parked_stacks_consistent tasks (task_stack_take stacks lease).
Proof.
  intros tasks stacks lease Hconsistent slot generation region words Hentry.
  destruct (task_stack_key_eq_dec (slot, generation) (task_stack_key lease)) as [Heq|Hneq].
  - rewrite Heq, task_stack_take_lookup in Hentry; discriminate.
  - rewrite task_stack_take_lookup_other in Hentry by exact Hneq.
    exact (Hconsistent slot generation region words Hentry).
Qed.

(** A pure map update is not a resource-transfer rule.  The corresponding
    spatial rule [store_parked_stacks_park] additionally consumes the current
    buffer and requires an absent key. *)
Lemma task_stack_park_fragments_preserves_consistency : forall tasks stacks lease fragments invocation,
  parked_stacks_consistent tasks stacks ->
  valid_task_stack_region lease.(stackLeaseRegion) ->
  task_stack_fragments_in_range lease.(stackLeaseRegion).(stackRegionWords) 0 fragments ->
  task_stack_live_binding tasks lease ->
  task_publication_happened tasks invocation lease.(stackLeaseSlot) lease.(stackLeaseGeneration) ->
  parked_stacks_consistent tasks (task_stack_park_fragments stacks lease fragments).
Proof.
  intros tasks stacks [region slot generation] fragments invocation
    Hconsistent Hregion Hgeometry Hlive Hhistory.
  intros other other_generation other_region other_words Hentry.
  destruct (task_stack_key_eq_dec (other, other_generation) (slot, generation)) as [Heq|Hneq].
  - injection Heq as Hslot Hgeneration; subst other other_generation.
    change (task_stack_park_fragments stacks
      {| stackLeaseRegion := region; stackLeaseSlot := slot; stackLeaseGeneration := generation |}
      fragments (task_stack_key
        {| stackLeaseRegion := region; stackLeaseSlot := slot; stackLeaseGeneration := generation |}) =
      Some (other_region, other_words)) in Hentry.
    rewrite task_stack_park_fragments_lookup in Hentry.
    injection Hentry as Hregion_eq Hwords_eq; subst other_region other_words.
    split; [exact Hregion|]. split; [exact Hgeometry|].
    split; [exists invocation; exact Hhistory|].
    intros node Hnode Hgeneration.
    destruct Hlive as [live [Hget Hbinding]]; simpl in Hget.
    assert (node = live) by congruence; subst node; exact Hbinding.
  - rewrite task_stack_park_fragments_lookup_other in Hentry by exact Hneq.
    exact (Hconsistent other other_generation other_region other_words Hentry).
Qed.

Lemma task_stack_park_preserves_consistency : forall tasks stacks lease words invocation,
  parked_stacks_consistent tasks stacks ->
  valid_task_stack_region lease.(stackLeaseRegion) ->
  task_stack_live_binding tasks lease ->
  task_publication_happened tasks invocation lease.(stackLeaseSlot) lease.(stackLeaseGeneration) ->
  parked_stacks_consistent tasks (task_stack_park stacks lease words).
Proof.
  intros tasks stacks lease words invocation Hconsistent Hregion Hlive Hhistory.
  apply task_stack_park_fragments_preserves_consistency with (invocation := invocation);
    try assumption.
  apply task_stack_complete_fragments_in_range; exact Hregion.
Qed.

Lemma task_commit_stack_key_absent : forall sg tasks priority invocation node stacks,
  task_in_range sg tasks ->
  task_commit_identity tasks priority invocation node ->
  parked_stacks_consistent tasks stacks ->
  stacks (node.(taskID), node.(taskGeneration)) = None.
Proof.
  intros sg tasks priority invocation node stacks Htasks Hidentity Hconsistent.
  destruct (stacks (node.(taskID), node.(taskGeneration))) as [[region fragments]|]
    eqn:Hentry; [|reflexivity].
  destruct (Hconsistent _ _ _ _ Hentry) as [_ [_ [[observer Hpublished] _]]].
  exfalso; exact (task_commit_identity_unpublished sg tasks priority invocation node
    Htasks Hidentity observer Hpublished).
Qed.

Lemma task_commit_preserves_stack_live_binding : forall tasks priority invocation node lease,
  tasks.(inUsedTaskStates) node.(taskID) = None ->
  task_stack_live_binding tasks lease ->
  task_stack_live_binding (task_commit tasks priority invocation node) lease.
Proof.
  intros tasks priority invocation node lease Hnone [old [Hold Hbinding]].
  destruct (task_commit_transports_old_fields tasks priority invocation node
    lease.(stackLeaseSlot) old Hnone Hold) as [updated [Hupdated Hfields]].
  exists updated; split; [exact Hupdated|].
  eapply task_stack_lease_matches_task_frame; [| | |exact Hbinding].
  - exact (f_equal taskID Hfields).
  - exact (f_equal taskGeneration Hfields).
  - exact (f_equal tcbStkPtr Hfields).
Qed.

Lemma task_commit_preserves_parked_stacks_consistency : forall tasks priority invocation node stacks,
  stacks (node.(taskID), node.(taskGeneration)) = None ->
  parked_stacks_consistent tasks stacks ->
  parked_stacks_consistent (task_commit tasks priority invocation node) stacks.
Proof.
  intros tasks priority invocation node stacks Hnone Hconsistent.
  intros slot generation region words Hentry.
  destruct (Hconsistent slot generation region words Hentry)
    as [Hregion [Hgeometry [[observer Hhistory] Hbinding]]].
  split; [exact Hregion|]. split; [exact Hgeometry|]. split.
  - exists observer; unfold task_publication_happened in *; simpl; right; exact Hhistory.
  - intros updated Hupdated Hgeneration.
    destruct (Z.eq_dec slot node.(taskID)) as [Heq|Hneq].
    + subst slot.
      pose proof (proj1 (task_commit_publication_fields_eq tasks priority invocation node)) as Hnew.
      assert (updated = task_set_links node tasks.(tcbListHead) None) by congruence.
      subst updated; change (node.(taskGeneration) = generation) in Hgeneration.
      rewrite <- Hgeneration, Hnone in Hentry; discriminate.
    + destruct (task_commit_lookup_old_fields tasks priority invocation node slot updated Hneq Hupdated)
        as [old [Hold Hfields]].
      assert (Hgen : old.(taskGeneration) = generation).
      { pose proof (f_equal taskGeneration Hfields) as Hsame; simpl in Hsame; congruence. }
      eapply task_stack_lease_matches_task_frame; [| | |exact (Hbinding old Hold Hgen)].
      * exact (f_equal taskID Hfields).
      * exact (f_equal taskGeneration Hfields).
      * exact (f_equal tcbStkPtr Hfields).
Qed.

(** This is the protected publication ENDPOINT.  The caller transfers the
    current initialized buffer before the first public link write while
    retaining its private phase resources; only after the commit is it a
    consistent published entry.  Neither this entailment nor publication
    history proves that the intervening C writes or Restore have executed. *)
Lemma task_stack_commit_park_consistent_resources :
  forall tasks priority invocation origin lease node words stacks,
  parked_stacks_consistent tasks stacks ->
  stacks (task_stack_key lease) = None ->
  task_stack_creation_binding tasks priority invocation origin lease ->
  task_commit_identity tasks priority invocation node ->
  valid_task_stack_region lease.(stackLeaseRegion) ->
  task_stack_saved_pointer_in_range lease.(stackLeaseRegion) node.(tcbStkPtr) ->
  task_stack_storage lease.(stackLeaseRegion) words ** store_parked_stacks stacks |--
  coq_prop (parked_stacks_consistent (task_commit tasks priority invocation node)
    (task_stack_park stacks lease words)) &&
    store_parked_stacks (task_stack_park stacks lease words).
Proof.
  intros tasks priority invocation origin lease node words stacks
    Hconsistent Hnone Hbinding Hidentity Hregion Hsp.
  destruct (task_stack_creation_binding_commit_identity tasks priority invocation origin lease node
    Hbinding Hidentity) as [Hslot Hgeneration].
  assert (Hpost : parked_stacks_consistent (task_commit tasks priority invocation node)
    (task_stack_park stacks lease words)).
  { apply task_stack_park_preserves_consistency with (invocation := invocation).
    - apply task_commit_preserves_parked_stacks_consistency; [|exact Hconsistent].
      rewrite Hslot, Hgeneration; exact Hnone.
    - exact Hregion.
    - apply task_commit_establishes_stack_binding; exact (conj Hslot (conj Hgeneration Hsp)).
    - rewrite <- Hslot, <- Hgeneration; apply task_commit_records_history. }
  sep_apply_l_atomic (store_parked_stacks_park stacks lease words Hnone).
  entailer!.
Qed.
