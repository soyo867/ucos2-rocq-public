Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** The input of WaitMulti/RemoveMulti is a borrowed, NULL-terminated
    pointer array.  Its base and its elements are different addresses.
    Interior NULLs would terminate the C loop early, while duplicate
    pointers are allowed and remain in their original order.  Empty arrays
    are valid for these internal traversals; PendMulti's public first-entry
    check is an additional caller branch, not part of array ownership. *)
Definition event_multi_array_valid (base : addr) (pointers : list addr) : Prop :=
  0 < base /\ base + 4 * (Zlength pointers + 1) <= 4294967296 /\
    Forall (fun pointer => pointer <> 0) pointers.

Definition event_multi_array_rep (base : addr) (pointers : list addr) : Assertion :=
  coq_prop (event_multi_array_valid base pointers) &&
    PtrArray.full base (Zlength pointers + 1) (pointers ++ [0]).

(** Generations identify the live objects denoted by the observed pointer
    sequence.  They are ghost identities, not extra words in the C array.
    This pure binding supplies neither array cells nor Event ownership. *)
Definition event_multi_array_binding (sg : StableGlobVars) (events : Glob_EventAbstractState)
  (pointers : list addr) (instances : list (EventID * nat)) : Prop :=
  Forall2 (fun pointer instance =>
    pointer = event_addr sg (fst instance) /\
    exists e, events.(inUsedEventStates) (fst instance) = Some e /\
      e.(eventGeneration) = snd instance) pointers instances.

Lemma event_multi_array_binding_addresses : forall sg events pointers instances,
  event_multi_array_binding sg events pointers instances ->
  pointers = map (fun instance => event_addr sg (fst instance)) instances.
Proof.
  intros sg events pointers instances Hbinding; induction Hbinding; [reflexivity|].
  destruct H as [Hpointer _]; simpl; rewrite Hpointer, IHHbinding; reflexivity.
Qed.

Lemma event_multi_array_binding_live : forall sg events pointers instances,
  event_multi_array_binding sg events pointers instances ->
  Forall (fun instance => exists e,
    events.(inUsedEventStates) (fst instance) = Some e /\ e.(eventGeneration) = snd instance) instances.
Proof.
  intros sg events pointers instances Hbinding; induction Hbinding; constructor; [exact (proj2 H)|assumption].
Qed.

Lemma event_multi_array_binding_index : forall sg events pointers instances index,
  event_multi_array_binding sg events pointers instances -> 0 <= index < Zlength pointers ->
  let instance := Znth index instances (0, 0%nat) in
  Znth index (pointers ++ [0]) 0 = event_addr sg (fst instance) /\
  exists e, events.(inUsedEventStates) (fst instance) = Some e /\
    e.(eventGeneration) = snd instance.
Proof.
  intros sg events pointers instances index Hbinding Hindex; cbn zeta.
  unfold event_multi_array_binding in Hbinding.
  apply (Forall2_nth_iff _ _ _ _ _ 0 (0, 0%nat)) in Hbinding.
  destruct Hbinding as [_ Hnth]; rewrite app_Znth1 by exact Hindex.
  apply (Hnth (Z.to_nat index)).
  apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia.
  rewrite <- Zlength_correct; exact (proj2 Hindex).
Qed.

Lemma event_multi_array_values_length : forall pointers : list addr,
  Zlength (pointers ++ [0]) = Zlength pointers + 1.
Proof. intros; apply Zlength_app_cons. Qed.

Lemma event_multi_array_terminator : forall pointers : list addr,
  Znth (Zlength pointers) (pointers ++ [0]) 0 = 0.
Proof.
  intros; rewrite app_Znth2 by lia.
  replace (Zlength pointers - Zlength pointers) with 0 by lia; reflexivity.
Qed.

Lemma event_multi_array_before_terminator : forall base pointers index,
  event_multi_array_valid base pointers -> 0 <= index < Zlength pointers ->
  Znth index (pointers ++ [0]) 0 <> 0.
Proof.
  intros base pointers index [_ [_ Hnonzero]] Hindex.
  rewrite app_Znth1 by exact Hindex.
  rewrite Forall_forall in Hnonzero; apply Hnonzero.
  unfold Znth; apply nth_In; rewrite Zlength_correct in Hindex; lia.
Qed.

Lemma event_multi_array_null_iff_end : forall base pointers index,
  event_multi_array_valid base pointers -> 0 <= index <= Zlength pointers ->
  (Znth index (pointers ++ [0]) 0 = 0 <-> index = Zlength pointers).
Proof.
  intros base pointers index Hvalid Hindex; split.
  - intro Hnull; destruct (Z.eq_dec index (Zlength pointers)); [assumption|].
    exfalso; exact (event_multi_array_before_terminator base pointers index Hvalid ltac:(lia) Hnull).
  - intro Heq; subst index; apply event_multi_array_terminator.
Qed.

(** QCP owns the generic array split/merge.  Retain validity outside the
    missing-element residual, so reading an entry does not lose the facts
    needed to traverse and ultimately return the original borrowed array. *)
Lemma event_multi_array_split_index : forall base pointers index,
  0 <= index <= Zlength pointers ->
  event_multi_array_rep base pointers |--
  coq_prop (event_multi_array_valid base pointers) &&
    ((base + index * 4) # Ptr |-> (Znth index (pointers ++ [0]) 0) **
     PtrArray.missing_i base index 0 (Zlength pointers + 1) (pointers ++ [0])).
Proof.
  intros base pointers index Hindex; unfold event_multi_array_rep; Intros.
  entailer!; apply PtrArray.full_split_to_missing_i; lia.
Qed.

Lemma event_multi_array_merge_index : forall base pointers index,
  event_multi_array_valid base pointers -> 0 <= index <= Zlength pointers ->
  (base + index * 4) # Ptr |-> (Znth index (pointers ++ [0]) 0) **
    PtrArray.missing_i base index 0 (Zlength pointers + 1) (pointers ++ [0]) |--
  event_multi_array_rep base pointers.
Proof.
  intros base pointers index Hvalid Hindex.
  eapply derivable1_trans;
    [exact (PtrArray.missing_i_merge_to_full base index (Zlength pointers + 1)
      (Znth index (pointers ++ [0]) 0) (pointers ++ [0]) ltac:(lia))|].
  rewrite replace_Znth_Znth; unfold event_multi_array_rep; entailer!.
Qed.

Lemma event_multi_array_nonnull_step : forall base pointers index,
  event_multi_array_valid base pointers -> 0 <= index <= Zlength pointers ->
  Znth index (pointers ++ [0]) 0 <> 0 ->
  0 <= index + 1 <= Zlength pointers /\
  0 <= Zlength pointers - (index + 1) < Zlength pointers - index.
Proof.
  intros base pointers index Hvalid Hindex Hnonnull.
  assert (index <> Zlength pointers).
  { intro Heq; subst index; apply Hnonnull; apply event_multi_array_terminator. }
  lia.
Qed.

Lemma event_multi_array_cell_address_in_range : forall base pointers index,
  event_multi_array_valid base pointers -> 0 <= index <= Zlength pointers ->
  0 < base + index * 4 /\ base + index * 4 + 4 <= 4294967296.
Proof. intros base pointers index [Hbase [Hend _]] Hindex; lia. Qed.

(** The continuation, not the non-NULL TCB pointer alone, retains the
    borrowed bytes.  In a woken phase [current_array] is zero, but the
    original [borrowed_array] remains available to PendMulti's cleanup.
    This is a local resource component; global wait-phase validity must
    separately relate current_array/ready to registration and status. *)
Definition event_multi_borrowed_array_rep (tcb current_array ready borrowed_array : addr)
  (pointers : list addr) : Assertion :=
  task_multi_fields_rep tcb current_array ready **
    event_multi_array_rep borrowed_array pointers.

(** Connect the local continuation slice to the whole enabled-Multi TCB.
    The residual contains its actual current common fields, including
    shifted padding; it is not the old 64-byte representation. *)
Lemma event_multi_borrowed_array_split_tcb : forall profile tcb image current ready base pointers,
  image TCBEventMultiPtr = Some current -> image TCBEventMultiRdy = Some ready ->
  tcb_configured_storage_rep true profile tcb image ** event_multi_array_rep base pointers |--
  event_multi_borrowed_array_rep tcb current ready base pointers **
    tcb_configured_without_multi profile tcb image.
Proof.
  intros; sep_apply (tcb_configured_storage_split_multi profile tcb image current ready H H0).
  unfold event_multi_borrowed_array_rep; entailer!.
Qed.

Lemma event_multi_borrowed_array_merge_tcb : forall profile tcb image current ready base pointers,
  event_multi_borrowed_array_rep tcb current ready base pointers **
    tcb_configured_without_multi profile tcb image |--
  tcb_configured_storage_rep true profile tcb (tcb_layout_set_multi image current ready) **
    event_multi_array_rep base pointers.
Proof.
  intros; unfold event_multi_borrowed_array_rep.
  sep_apply (tcb_configured_storage_merge_multi profile tcb image current ready); entailer!.
Qed.

Lemma event_multi_borrowed_array_split_index : forall tcb current ready base pointers index,
  0 <= index <= Zlength pointers ->
  event_multi_borrowed_array_rep tcb current ready base pointers |--
  coq_prop (event_multi_array_valid base pointers) &&
    ((base + index * 4) # Ptr |-> (Znth index (pointers ++ [0]) 0) **
     (task_multi_fields_rep tcb current ready **
      PtrArray.missing_i base index 0 (Zlength pointers + 1) (pointers ++ [0]))).
Proof.
  intros; unfold event_multi_borrowed_array_rep.
  sep_apply (event_multi_array_split_index base pointers index H); entailer!.
Qed.

Lemma event_multi_borrowed_array_merge_index : forall tcb current ready base pointers index,
  event_multi_array_valid base pointers -> 0 <= index <= Zlength pointers ->
  (base + index * 4) # Ptr |-> (Znth index (pointers ++ [0]) 0) **
    (task_multi_fields_rep tcb current ready **
     PtrArray.missing_i base index 0 (Zlength pointers + 1) (pointers ++ [0])) |--
  event_multi_borrowed_array_rep tcb current ready base pointers.
Proof.
  intros; unfold event_multi_borrowed_array_rep.
  sep_apply (event_multi_array_merge_index base pointers index H H0); entailer!.
Qed.

(** Endpoint for the Event-only effects of RemoveMulti.  Non-live entries
    are not fabricated; source-order refinement below requires the actual
    lookup used by each C dereference.  Pointer-array and TCB writes are not
    hidden in this transformer. *)
Definition event_multi_remove_waiters (events : Glob_EventAbstractState)
  (tid : TaskID) (ids : list EventID) : Glob_EventAbstractState :=
  {| inUsedEventStates := fun eid =>
       match events.(inUsedEventStates) eid with
       | Some e => Some (if in_dec Z.eq_dec eid ids then
           event_set_wait_list e (remove_Z_eqb tid e.(waitList)) else e)
       | None => None
       end;
     eventLifecycle := events.(eventLifecycle);
     publishedQueueBytes := events.(publishedQueueBytes);
     unUsedEventStates := events.(unUsedEventStates) |}.

Lemma event_multi_remove_waiters_unlisted : forall events tid ids eid,
  ~ In eid ids ->
  (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid =
    events.(inUsedEventStates) eid.
Proof.
  intros; simpl; destruct (events.(inUsedEventStates) eid); [|reflexivity].
  destruct in_dec; [contradiction|reflexivity].
Qed.

Lemma event_multi_remove_waiters_listed : forall events tid ids eid e,
  In eid ids -> events.(inUsedEventStates) eid = Some e ->
  (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid =
    Some (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
Proof. intros; simpl; rewrite H0; destruct in_dec; [reflexivity|contradiction]. Qed.

Lemma event_multi_remove_waiters_clears_member : forall events tid ids eid e,
  In eid ids -> (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid = Some e ->
  ~ In tid e.(waitList).
Proof.
  intros events tid ids eid e Hin Hlookup; simpl in Hlookup.
  destruct (events.(inUsedEventStates) eid); [|discriminate].
  destruct in_dec; [|contradiction]; inversion Hlookup; subst e; apply remove_Z_eqb_notin.
Qed.

Lemma event_multi_remove_waiters_nil : forall events tid,
  event_multi_remove_waiters events tid [] = events.
Proof.
  intros [used free bytes life] tid; unfold event_multi_remove_waiters; simpl.
  f_equal; apply functional_extensionality; intro eid; destruct (used eid); reflexivity.
Qed.

Lemma event_remove_waiter_idempotent : forall e tid,
  event_set_wait_list (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))
    (remove_Z_eqb tid (remove_Z_eqb tid e.(waitList))) =
  event_set_wait_list e (remove_Z_eqb tid e.(waitList)).
Proof.
  intros; rewrite event_set_wait_list_last_write.
  rewrite remove_Z_eqb_notin_eq by apply remove_Z_eqb_notin; reflexivity.
Qed.

Lemma event_multi_remove_waiters_source_order : forall events tid eid ids e,
  events.(inUsedEventStates) eid = Some e ->
  event_multi_remove_waiters events tid (eid :: ids) =
    event_multi_remove_waiters
      (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))) tid ids.
Proof.
  intros [used free bytes life] tid eid ids e Hlookup; simpl in Hlookup.
  unfold event_multi_remove_waiters, update_event_field_raw;
    cbn [inUsedEventStates eventLifecycle publishedQueueBytes unUsedEventStates]; f_equal.
  apply functional_extensionality; intro slot.
  destruct (Z.eqb slot eid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; rewrite Hlookup.
    destruct (in_dec Z.eq_dec eid (eid :: ids)); [|exfalso; apply n; left; reflexivity].
    destruct (in_dec Z.eq_dec eid ids); [|reflexivity].
    f_equal; symmetry; apply event_remove_waiter_idempotent.
  - apply Z.eqb_neq in Hslot; destruct (used slot); [|reflexivity].
    destruct (in_dec Z.eq_dec slot (eid :: ids)); destruct (in_dec Z.eq_dec slot ids);
      try reflexivity; exfalso; simpl in *; intuition congruence.
Qed.

Lemma event_multi_remove_waiters_preserves_binding : forall sg events tid ids pointers instances,
  event_multi_array_binding sg events pointers instances ->
  event_multi_array_binding sg (event_multi_remove_waiters events tid ids) pointers instances.
Proof.
  intros sg events tid ids pointers instances Hbinding; induction Hbinding; constructor.
  - destruct H as [Hpointer [e [Hlookup Hgeneration]]]; split; [exact Hpointer|].
    simpl; rewrite Hlookup; destruct (in_dec Z.eq_dec (fst y) ids);
      (eexists; split; [reflexivity|exact Hgeneration]).
  - exact IHHbinding.
Qed.

Lemma event_multi_remove_waiters_singleton : forall events tid eid e,
  events.(inUsedEventStates) eid = Some e ->
  event_multi_remove_waiters events tid [eid] =
    update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
Proof.
  intros; rewrite (event_multi_remove_waiters_source_order events tid eid [] e H).
  apply event_multi_remove_waiters_nil.
Qed.

(** Source-order traversal.  [None] records a missing logical pointee,
    not an extra error branch or a skipped dereference in the C helper.
    The array binding proves that this outcome cannot occur in its defined
    domain.  Each body step's physical row/group stores are justified by
    event_remove_waiter_image_eq, including already absent waiters. *)
Fixpoint event_multi_remove_loop (events : Glob_EventAbstractState) (tid : TaskID)
  (ids : list EventID) : option Glob_EventAbstractState :=
  match ids with
  | [] => Some events
  | eid :: rest =>
      match events.(inUsedEventStates) eid with
      | Some e => event_multi_remove_loop
          (update_event_field_raw events eid (event_set_wait_list e (remove_Z_eqb tid e.(waitList)))) tid rest
      | None => None
      end
  end.

Lemma event_multi_remove_loop_eq_endpoint : forall ids events tid,
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  event_multi_remove_loop events tid ids = Some (event_multi_remove_waiters events tid ids).
Proof.
  induction ids as [|eid rest IH]; intros events tid Hlive.
  - simpl; rewrite event_multi_remove_waiters_nil; reflexivity.
  - inversion Hlive as [|id tail Hhead Htail]; subst id tail.
    destruct Hhead as [e Hlookup]; simpl; rewrite Hlookup.
    rewrite (event_multi_remove_waiters_source_order events tid eid rest e Hlookup); apply IH.
    rewrite Forall_forall in Htail |- *; intros slot Hin.
    destruct (Htail slot Hin) as [node Hnode]; simpl.
    destruct (Z.eqb slot eid); eexists; [reflexivity|exact Hnode].
Qed.

Lemma event_multi_remove_loop_from_binding : forall sg events tid pointers instances,
  event_multi_array_binding sg events pointers instances ->
  event_multi_remove_loop events tid (map fst instances) =
    Some (event_multi_remove_waiters events tid (map fst instances)) /\
  event_multi_array_binding sg (event_multi_remove_waiters events tid (map fst instances)) pointers instances.
Proof.
  intros sg events tid pointers instances Hbinding; split.
  - apply event_multi_remove_loop_eq_endpoint.
    pose proof (event_multi_array_binding_live sg events pointers instances Hbinding) as Hlive.
    rewrite Forall_forall in Hlive |- *; intros eid Hin.
    apply in_map_iff in Hin; destruct Hin as [instance [Heid Hmember]]; subst eid.
    destruct (Hlive instance Hmember) as [e [Hlookup _]]; exists e; exact Hlookup.
  - apply event_multi_remove_waiters_preserves_binding; exact Hbinding.
Qed.

(** This loop operates on the observed ECB byte images.  The cached TCB
    row/masks are arguments, so every iteration uses the same values.
    It preserves input order and performs repeated clears for duplicates;
    it does not consult abstract wait-list membership as a branch. *)
Fixpoint event_multi_remove_image_loop (images : EventID -> option EventStorage)
  (row bit_x bit_y : Z) (ids : list EventID) : option (EventID -> option EventStorage) :=
  match ids with
  | [] => Some images
  | eid :: rest =>
      match images eid with
      | None => None
      | Some image =>
          match event_clear_waiter_from_image image row bit_x bit_y with
          | None => None
          | Some written => event_multi_remove_image_loop
              (kernel_map_set images eid (Some written)) row bit_x bit_y rest
          end
      end
  end.

Lemma event_multi_remove_waiters_preserves_canonical : forall sg tasks events tid ids,
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList)) ->
  forall eid e, (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList).
Proof.
  intros sg tasks events tid ids Hcanonical eid e Hlookup; simpl in Hlookup.
  destruct (events.(inUsedEventStates) eid) as [old|] eqn:E; [|discriminate].
  destruct in_dec; injection Hlookup as He; subst e.
  - apply event_waitList_canonical_remove; apply (Hcanonical eid old E).
  - apply (Hcanonical eid old E).
Qed.

Lemma event_multi_remove_image_loop_eq_endpoint : forall ids sg tasks events tid t,
  valid_stable_glob_vars sg -> task_priority_unique tasks ->
  valid_task_prio sg t.(curPrio) -> tasks.(inUsedTaskStates) tid = Some t ->
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList)) ->
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  event_multi_remove_image_loop (event_used_images sg tasks events)
    (t.(curPrio) / 8) (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8)) ids =
  Some (event_used_images sg tasks (event_multi_remove_waiters events tid ids)).
Proof.
  induction ids as [|eid rest IH]; intros sg tasks events tid t Hsg Hunique Hprio Ht Hcanonical Hlive.
  - simpl; rewrite event_multi_remove_waiters_nil; reflexivity.
  - inversion Hlive as [|id tail Hhead Htail]; subst id tail; destruct Hhead as [e He].
    assert (Himage : event_used_images sg tasks events eid = Some (event_image sg tasks e)).
    { unfold event_used_images; rewrite He; reflexivity. }
    assert (Hrow : 0 <= t.(curPrio) / 8 < 8).
    { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
      unfold valid_task_prio in Hprio.
      split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
    cbn [event_multi_remove_image_loop]; rewrite Himage.
    rewrite (event_clear_waiter_from_image_eq
      (event_image sg tasks e) (t.(curPrio) / 8)
      (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8))
      (event_table_image_eq sg tasks e _ Hrow) eq_refl).
    rewrite <- (event_remove_waiter_image_eq sg tasks e tid t
      Hsg Hunique (Hcanonical eid e He) Hprio Ht).
    rewrite <- event_used_images_update.
    rewrite (event_multi_remove_waiters_source_order events tid eid rest e He).
    apply IH; try assumption.
    + rewrite <- (event_multi_remove_waiters_singleton events tid eid e He).
      apply event_multi_remove_waiters_preserves_canonical; exact Hcanonical.
    + rewrite Forall_forall in Htail |- *; intros slot Hin.
      destruct (Htail slot Hin) as [node Hnode]; simpl.
      destruct (Z.eqb slot eid); eexists; [reflexivity|exact Hnode].
Qed.

(** Event-only registration endpoint.  WaitMulti's TCB pointer stores and
    final ready removal are distinct source phases, not hidden here. *)
Definition event_multi_insert_waiters (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) (tid : TaskID) (ids : list EventID) : Glob_EventAbstractState :=
  {| inUsedEventStates := fun eid =>
       match events.(inUsedEventStates) eid with
       | Some e => Some (if in_dec Z.eq_dec eid ids then event_insert_waiter sg tasks e tid else e)
       | None => None
       end;
     eventLifecycle := events.(eventLifecycle);
     publishedQueueBytes := events.(publishedQueueBytes);
     unUsedEventStates := events.(unUsedEventStates) |}.

Lemma event_multi_insert_waiters_nil : forall sg tasks events tid,
  event_multi_insert_waiters sg tasks events tid [] = events.
Proof.
  intros sg tasks [used free bytes life] tid; unfold event_multi_insert_waiters; simpl.
  f_equal; apply functional_extensionality; intro eid; destruct (used eid); reflexivity.
Qed.

Lemma event_multi_insert_waiters_source_order : forall sg tasks events tid eid ids e,
  events.(inUsedEventStates) eid = Some e ->
  event_multi_insert_waiters sg tasks events tid (eid :: ids) =
    event_multi_insert_waiters sg tasks
      (update_event_field_raw events eid (event_insert_waiter sg tasks e tid)) tid ids.
Proof.
  intros sg tasks [used free bytes life] tid eid ids e Hlookup; simpl in Hlookup.
  unfold event_multi_insert_waiters, update_event_field_raw;
    cbn [inUsedEventStates eventLifecycle publishedQueueBytes unUsedEventStates]; f_equal.
  apply functional_extensionality; intro slot.
  destruct (Z.eqb slot eid) eqn:Hslot.
  - apply Z.eqb_eq in Hslot; subst slot; rewrite Hlookup.
    destruct (in_dec Z.eq_dec eid (eid :: ids)); [|exfalso; apply n; left; reflexivity].
    destruct (in_dec Z.eq_dec eid ids); [|reflexivity].
    f_equal; symmetry; apply event_insert_waiter_idempotent.
  - apply Z.eqb_neq in Hslot; destruct (used slot); [|reflexivity].
    destruct (in_dec Z.eq_dec slot (eid :: ids)); destruct (in_dec Z.eq_dec slot ids);
      try reflexivity; exfalso; simpl in *; intuition congruence.
Qed.

Lemma event_multi_insert_waiters_membership : forall sg tasks events tid ids eid e,
  events.(inUsedEventStates) eid = Some e ->
  exists after, (event_multi_insert_waiters sg tasks events tid ids).(inUsedEventStates) eid = Some after /\
    forall member, In member after.(waitList) <->
      (In eid ids /\ member = tid) \/ In member e.(waitList).
Proof.
  intros sg tasks events tid ids eid e He; simpl; rewrite He.
  destruct in_dec as [Hin|Hnot].
  - exists (event_insert_waiter sg tasks e tid); split; [reflexivity|].
    intro member; rewrite event_insert_waiter_membership; tauto.
  - exists e; split; [reflexivity|]; intro member; tauto.
Qed.

Lemma event_multi_insert_waiters_preserves_binding : forall sg tasks events tid ids pointers instances,
  event_multi_array_binding sg events pointers instances ->
  event_multi_array_binding sg (event_multi_insert_waiters sg tasks events tid ids) pointers instances.
Proof.
  intros sg tasks events tid ids pointers instances Hbinding; induction Hbinding; constructor.
  - destruct H as [Hpointer [e [Hlookup Hgeneration]]]; split; [exact Hpointer|].
    simpl; rewrite Hlookup; destruct (in_dec Z.eq_dec (fst y) ids);
      (eexists; split; [reflexivity|exact Hgeneration]).
  - exact IHHbinding.
Qed.

Lemma event_multi_insert_waiters_preserves_canonical : forall sg tasks events tid t ids,
  task_priority_unique tasks -> tasks.(inUsedTaskStates) tid = Some t -> valid_task_prio sg t.(curPrio) ->
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList)) ->
  forall eid e, (event_multi_insert_waiters sg tasks events tid ids).(inUsedEventStates) eid = Some e ->
    event_waitList_canonical sg tasks e.(waitList).
Proof.
  intros sg tasks events tid t ids Hunique Ht Hprio Hcanonical eid e Hlookup; simpl in Hlookup.
  destruct (events.(inUsedEventStates) eid) as [old|] eqn:E; [|discriminate].
  destruct in_dec; injection Hlookup as He; subst e.
  - eapply event_insert_waiter_preserves_canonical; [exact (Hcanonical eid old E)|eassumption..].
  - exact (Hcanonical eid old E).
Qed.

Fixpoint event_multi_wait_loop (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (events : Glob_EventAbstractState) (tid : TaskID) (ids : list EventID) : option Glob_EventAbstractState :=
  match ids with
  | [] => Some events
  | eid :: rest =>
      match events.(inUsedEventStates) eid with
      | None => None
      | Some e => event_multi_wait_loop sg tasks
          (update_event_field_raw events eid (event_insert_waiter sg tasks e tid)) tid rest
      end
  end.

Lemma event_multi_wait_loop_eq_endpoint : forall ids sg tasks events tid,
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  event_multi_wait_loop sg tasks events tid ids = Some (event_multi_insert_waiters sg tasks events tid ids).
Proof.
  induction ids as [|eid rest IH]; intros sg tasks events tid Hlive.
  - simpl; rewrite event_multi_insert_waiters_nil; reflexivity.
  - inversion Hlive as [|id tail Hhead Htail]; subst id tail; destruct Hhead as [e He].
    simpl; rewrite He.
    rewrite (event_multi_insert_waiters_source_order sg tasks events tid eid rest e He); apply IH.
    rewrite Forall_forall in Htail |- *; intros slot Hin.
    destruct (Htail slot Hin) as [node Hnode]; simpl.
    destruct (Z.eqb slot eid); eexists; [reflexivity|exact Hnode].
Qed.

Lemma event_multi_wait_loop_from_binding : forall sg tasks events tid pointers instances,
  event_multi_array_binding sg events pointers instances ->
  event_multi_wait_loop sg tasks events tid (map fst instances) =
    Some (event_multi_insert_waiters sg tasks events tid (map fst instances)) /\
  event_multi_array_binding sg
    (event_multi_insert_waiters sg tasks events tid (map fst instances)) pointers instances.
Proof.
  intros sg tasks events tid pointers instances Hbinding; split.
  - apply event_multi_wait_loop_eq_endpoint.
    pose proof (event_multi_array_binding_live sg events pointers instances Hbinding) as Hlive.
    rewrite Forall_forall in Hlive |- *; intros eid Hin.
    apply in_map_iff in Hin; destruct Hin as [instance [Heid Hmember]]; subst eid.
    destruct (Hlive instance Hmember) as [e [Hlookup _]]; exists e; exact Hlookup.
  - apply event_multi_insert_waiters_preserves_binding; exact Hbinding.
Qed.

Fixpoint event_multi_wait_image_loop (images : EventID -> option EventStorage)
  (row bit_x bit_y : Z) (ids : list EventID) : option (EventID -> option EventStorage) :=
  match ids with
  | [] => Some images
  | eid :: rest =>
      match images eid with
      | None => None
      | Some image =>
          match event_mark_waiter_from_image image row bit_x bit_y with
          | None => None
          | Some written => event_multi_wait_image_loop
              (kernel_map_set images eid (Some written)) row bit_x bit_y rest
          end
      end
  end.

Lemma event_multi_wait_image_loop_eq_endpoint : forall ids sg tasks events tid t,
  tasks.(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) / 8 < 8 ->
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  event_multi_wait_image_loop (event_used_images sg tasks events)
    (t.(curPrio) / 8) (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8)) ids =
  Some (event_used_images sg tasks (event_multi_insert_waiters sg tasks events tid ids)).
Proof.
  induction ids as [|eid rest IH]; intros sg tasks events tid t Ht Hrow Hlive.
  - simpl; rewrite event_multi_insert_waiters_nil; reflexivity.
  - inversion Hlive as [|id tail Hhead Htail]; subst id tail; destruct Hhead as [e He].
    assert (Himage : event_used_images sg tasks events eid = Some (event_image sg tasks e)).
    { unfold event_used_images; rewrite He; reflexivity. }
    cbn [event_multi_wait_image_loop]; rewrite Himage.
    rewrite (event_mark_waiter_from_image_eq
      (event_image sg tasks e) (t.(curPrio) / 8)
      (encode_event_wait_tbl_at_or e.(waitList) tasks (t.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) tasks)
      (Z.shiftl 1 (t.(curPrio) mod 8)) (Z.shiftl 1 (t.(curPrio) / 8))
      (event_table_image_eq sg tasks e _ Hrow) eq_refl).
    rewrite <- (event_insert_waiter_image_eq sg tasks e tid t Ht Hrow).
    rewrite <- event_used_images_update.
    rewrite (event_multi_insert_waiters_source_order sg tasks events tid eid rest e He).
    apply IH; try assumption.
    rewrite Forall_forall in Htail |- *; intros slot Hin.
    destruct (Htail slot Hin) as [node Hnode]; simpl.
    destruct (Z.eqb slot eid); eexists; [reflexivity|exact Hnode].
Qed.

(** The complete Event membership relation for one Multi waiter.  The
    ordered array remains a separate borrowed resource; membership here is
    only its derived set view.  No duplicate-free input premise is needed. *)
Definition event_multi_wait_set (events : Glob_EventAbstractState)
  (tid : TaskID) (ids : list EventID) : Prop :=
  forall eid e, events.(inUsedEventStates) eid = Some e ->
    (In tid e.(waitList) <-> In eid ids).

Lemma event_multi_insert_waiters_establishes_wait_set : forall sg tasks events tid ids,
  (forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)) ->
  event_multi_wait_set (event_multi_insert_waiters sg tasks events tid ids) tid ids.
Proof.
  intros sg tasks events tid ids Habsent eid after Hlookup; simpl in Hlookup.
  destruct (events.(inUsedEventStates) eid) as [before|] eqn:Hbefore; [|discriminate].
  destruct in_dec as [Hin|Hnot]; injection Hlookup as Heq; subst after.
  - rewrite event_insert_waiter_membership; tauto.
  - specialize (Habsent eid before Hbefore); tauto.
Qed.

Lemma event_multi_remove_waiters_clears_wait_set : forall events tid ids,
  event_multi_wait_set events tid ids ->
  forall eid e, (event_multi_remove_waiters events tid ids).(inUsedEventStates) eid = Some e ->
    ~ In tid e.(waitList).
Proof.
  intros events tid ids Hset eid after Hlookup; simpl in Hlookup.
  destruct (events.(inUsedEventStates) eid) as [before|] eqn:Hbefore; [|discriminate].
  destruct in_dec as [Hin|Hnot]; injection Hlookup as Heq; subst after.
  - apply remove_Z_eqb_notin.
  - intro Hin; apply Hnot; apply (proj1 (Hset eid before Hbefore)); exact Hin.
Qed.

(** Source-ordered effects of WaitMulti on the three existing owners.
    [tasks] supplies only the priority lookup used to encode bitmaps; the
    actual mutable TCB fields are [image], not its old single-kind status
    projection.  The equality with the current-task cache is a pointer
    observation, not a new runtime guard.  Array ownership/binding is
    supplied separately by event_multi_array_rep/binding at the call site. *)
Definition event_multi_wait_step (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (tid : TaskID) (array : addr) (ids : list EventID)
  (image : TCBLayoutImage) (events : Glob_EventAbstractState) (s : SchedAbstractState)
  (after_image : TCBLayoutImage) (after_events : Glob_EventAbstractState)
  (after_sched : SchedAbstractState) : Prop :=
  s.(curTaskID) = Some tid /\
  after_image = tcb_multi_wait_image image array /\
  event_multi_wait_loop sg tasks events tid ids = Some after_events /\
  after_sched = sched_remove_ready_task s tid.

Lemma event_multi_wait_step_from_live_array : forall sg tasks tid array ids image events s,
  s.(curTaskID) = Some tid ->
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  event_multi_wait_step sg tasks tid array ids image events s
    (tcb_multi_wait_image image array)
    (event_multi_insert_waiters sg tasks events tid ids) (sched_remove_ready_task s tid).
Proof.
  intros; split; [assumption|]; split; [reflexivity|]; split; [|reflexivity].
  apply event_multi_wait_loop_eq_endpoint; assumption.
Qed.

Lemma event_multi_wait_step_observations : forall sg tasks tid array ids image events s after_image after_events after_sched,
  event_multi_wait_step sg tasks tid array ids image events s after_image after_events after_sched ->
  after_image TCBEventMultiPtr = Some array /\ after_image TCBEventMultiRdy = Some 0 /\
  (forall field, after_image (TCBCommonField field) = image (TCBCommonField field)) /\
  ~ In tid after_sched.(readyList) /\
  sched_physical_rep sg after_sched = sched_physical_rep sg s.
Proof.
  intros sg tasks tid array ids image events s after_image after_events after_sched [_ [-> [_ ->]]].
  split; [reflexivity|]; split; [reflexivity|]; split;
    [apply tcb_multi_wait_image_common_frame|].
  split; [apply remove_Z_eqb_notin|reflexivity].
Qed.

Lemma event_multi_wait_step_establishes_wait_set : forall sg tasks tid array ids image events s after_image after_events after_sched,
  event_multi_wait_step sg tasks tid array ids image events s after_image after_events after_sched ->
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  (forall eid e, events.(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)) ->
  event_multi_wait_set after_events tid ids.
Proof.
  intros sg tasks tid array ids image events s after_image after_events after_sched [_ [_ [Hloop _]]] Hlive Habsent.
  rewrite (event_multi_wait_loop_eq_endpoint ids sg tasks events tid Hlive) in Hloop.
  injection Hloop as Heq; subst after_events; apply event_multi_insert_waiters_establishes_wait_set; exact Habsent.
Qed.

Lemma event_multi_wait_step_image_loop : forall sg tasks tid t array ids image events s after_image after_events after_sched,
  event_multi_wait_step sg tasks tid array ids image events s after_image after_events after_sched ->
  tasks.(inUsedTaskStates) tid = Some t -> 0 <= t.(curPrio) / 8 < 8 ->
  image (TCBCommonField TCBY) = Some (t.(curPrio) / 8) ->
  image (TCBCommonField TCBBitX) = Some (Z.shiftl 1 (t.(curPrio) mod 8)) ->
  image (TCBCommonField TCBBitY) = Some (Z.shiftl 1 (t.(curPrio) / 8)) ->
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e) ids ->
  (match image (TCBCommonField TCBY), image (TCBCommonField TCBBitX), image (TCBCommonField TCBBitY) with
   | Some row, Some bit_x, Some bit_y =>
       event_multi_wait_image_loop (event_used_images sg tasks events) row bit_x bit_y ids
   | _, _, _ => None
   end) = Some (event_used_images sg tasks after_events).
Proof.
  intros sg tasks tid t array ids image events s after_image after_events after_sched
    [_ [_ [Hloop _]]] Ht Hrow Hy Hx Hb Hlive; rewrite Hy, Hx, Hb.
  rewrite (event_multi_wait_loop_eq_endpoint ids sg tasks events tid Hlive) in Hloop.
  injection Hloop as Heq; subst after_events.
  apply event_multi_wait_image_loop_eq_endpoint; assumption.
Qed.

(** The already-selected, MultiPtr-non-NULL suffix of EventTaskRdy.  The
    first removal is the selected Event, then the original whole array is
    traversed, even when it contains that Event again.  Selection and the
    pointer-array/instance binding are separate entry obligations; this is
    not a replacement for the full selector or a second global state. *)
Definition event_multi_wake_selected_step (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (tid : TaskID) (selected : EventID) (array : addr) (ids : list EventID)
  (bits mask message : Z) (result : PendStatus)
  (image : TCBLayoutImage) (events : Glob_EventAbstractState) (s : SchedAbstractState)
  (after_image : TCBLayoutImage) (after_events : Glob_EventAbstractState)
  (after_sched : SchedAbstractState) : Prop :=
  image (TCBCommonField TCBStat) = Some bits /\ image TCBEventMultiPtr = Some array /\ array <> 0 /\
  after_image = tcb_multi_wake_image image bits mask message result (event_addr sg selected) /\
  event_multi_remove_loop events tid (selected :: ids) = Some after_events /\
  after_sched = sched_wake_by_status sg tasks s tid (task_status_clear_wait bits mask).

Lemma event_multi_wake_selected_step_ready_membership : forall sg tasks tid selected array ids bits mask message result
    image events s after_image after_events after_sched slot,
  event_multi_wake_selected_step sg tasks tid selected array ids bits mask message result
    image events s after_image after_events after_sched ->
  (In slot after_sched.(readyList) <-> In slot s.(readyList) \/
    (slot = tid /\ task_status_is_suspended (task_status_clear_wait bits mask) = false)).
Proof.
  intros sg tasks tid selected array ids bits mask message result image events s after_image after_events after_sched slot
    [_ [_ [_ [_ [_ ->]]]]]; apply sched_wake_by_status_membership.
Qed.

Lemma event_multi_wake_selected_step_fields : forall sg tasks tid selected array ids bits kind message result
    image events s after_image after_events after_sched,
  event_multi_wake_selected_step sg tasks tid selected array ids bits (task_pend_mask kind) message result
    image events s after_image after_events after_sched ->
  task_status_is_multi bits = true -> kind <> PendMulti -> event_addr sg selected <> 0 ->
  task_multi_woken_fields after_image (event_addr sg selected) result.
Proof.
  intros sg tasks tid selected array ids bits kind message result image events s after_image after_events after_sched
    [_ [_ [_ [-> _]]]] Hmulti Hkind Haddr; apply tcb_multi_wake_woken_fields; assumption.
Qed.

Lemma event_multi_wake_with_remaining_pending_is_ready : forall sg tasks s tid,
  In tid (sched_wake_by_status sg tasks s tid
    (task_status_clear_wait (encode_multi_wait_status 5 false) (task_pend_mask PendSem))).(readyList) /\
  task_status_has_pending
    (task_status_clear_wait (encode_multi_wait_status 5 false) (task_pend_mask PendSem)) = true.
Proof.
  intros; split; [apply sched_wake_by_status_membership; right; split|]; reflexivity.
Qed.

(** Connect the existing source-ordered image/bitmap step to the actual
    Task map.  No single-Event [event_in_range] premise is used here: its
    current backlink clause excludes Multi registrations.  These are the
    structural and source-phase components needed by the configured global
    invariant, not a claim that the entire invariant is already restored. *)
Lemma event_multi_wake_selected_task_composition :
  forall sg tasks events s tid old selected kind message result,
  tasks.(inUsedTaskStates) tid = Some old ->
  old.(tcbEventMultiPtr) <> 0 ->
  Forall (fun eid => exists e, events.(inUsedEventStates) eid = Some e)
    (selected :: old.(eventMultiWaitEvents)) ->
  task_in_range sg tasks -> task_priority_unique tasks ->
  task_priority_in_range sg old.(curPrio) -> sched_ready_structure sg tasks s ->
  let written := task_multi_wake old kind message result selected in
  let after_tasks := glob_task_set_usedtask tasks tid written in
  let after_events := event_multi_remove_waiters events tid
    (selected :: old.(eventMultiWaitEvents)) in
  let after_sched := sched_wake_by_status sg tasks s tid
    (task_status_clear_wait (encode_task_status old.(stat)) (task_pend_mask kind)) in
  event_multi_wake_selected_step sg tasks tid selected old.(tcbEventMultiPtr)
    old.(eventMultiWaitEvents) (encode_task_status old.(stat)) (task_pend_mask kind)
    message result (task_layout_image sg old) events s
    (task_layout_image sg written) after_events after_sched /\
  task_in_range sg after_tasks /\
  sched_ready_structure sg after_tasks after_sched /\
  (forall slot, In slot after_sched.(readyList) <->
    In slot s.(readyList) \/ (slot = tid /\ task_is_suspended old.(stat) = false)).
Proof.
  intros sg tasks events s tid old selected kind message result
    Htask Harray Hlive Htasks Hunique Hprio Hready; cbn zeta.
  split.
  - split; [reflexivity|]. split; [reflexivity|]. split; [exact Harray|].
    split; [apply task_multi_wake_layout_image_eq|].
    split; [apply event_multi_remove_loop_eq_endpoint; exact Hlive|reflexivity].
  - split.
    + eapply task_update_preserves_in_range; try eassumption; reflexivity.
    + split.
      * eapply sched_ready_structure_update_task; [exact Htask|reflexivity|].
        eapply sched_wake_by_status_preserves_structure; eassumption.
      * intro slot; rewrite sched_wake_by_status_membership.
        assert (Hsusp : task_status_is_suspended
          (task_status_clear_wait (encode_task_status old.(stat)) (task_pend_mask kind)) =
          task_is_suspended old.(stat)).
        { pose proof (task_clear_pending_status_preserves_suspension old.(stat) kind) as H.
          unfold task_is_suspended in H; rewrite task_clear_pending_status_encoding in H.
          exact H. }
        rewrite Hsusp; reflexivity.
Qed.

(** EventTaskRdy removes the selected Event first, then traverses the whole
    original array.  The selected Event may occur again; repetitions do not
    leave a registration behind.  Keeping that array in the continuation
    does not mean that its Events still contain this task. *)
Lemma event_multi_wake_selected_clears_wait_set : forall events tid selected ids,
  In selected ids -> event_multi_wait_set events tid ids ->
  forall eid e,
    (event_multi_remove_waiters events tid (selected :: ids)).(inUsedEventStates) eid = Some e ->
    ~ In tid e.(waitList).
Proof.
  intros events tid selected ids Hselected Hset.
  apply event_multi_remove_waiters_clears_wait_set.
  intros eid e He; rewrite (Hset eid e He); simpl; split; [auto|].
  intros [<-|Hin]; assumption.
Qed.

(** Consume the actual updated TCB bytes and restore the public Task map.
    The original borrowed array remains owned by the caller even though
    MultiPtr is now NULL.  This rule creates neither array ownership nor
    a new Event/Task generation, and retains all configured profiling cells. *)
Lemma event_multi_wake_merge_task_storage :
  forall sg tasks tid old kind message result selected pointers,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true ->
  task_slot_storage_rep sg tid
    (tcb_multi_wake_image (task_layout_image sg old) (encode_task_status old.(stat))
      (task_pend_mask kind) message result (event_addr sg selected)) **
    (task_public_storage_without_task sg tasks tid **
     event_multi_array_rep old.(tcbEventMultiPtr) pointers) |--
  task_public_storage sg
    (glob_task_set_usedtask tasks tid (task_multi_wake old kind message result selected)) **
    event_multi_array_rep old.(tcbEventMultiPtr) pointers.
Proof.
  intros; change (event_addr sg selected) with (event_pool_addr sg selected).
  rewrite <- task_multi_wake_layout_image_eq.
  change (used_task_rep sg tid (task_multi_wake old kind message result selected) **
    (task_public_storage_without_task sg tasks tid **
     event_multi_array_rep old.(tcbEventMultiPtr) pointers) |--
    task_public_storage sg
      (glob_task_set_usedtask tasks tid (task_multi_wake old kind message result selected)) **
    event_multi_array_rep old.(tcbEventMultiPtr) pointers).
  rewrite (logic_equiv_sepcon_assoc _ _ _).
  apply derivable1_sepcon_mono; [apply task_public_storage_merge_updated_task|reflexivity].
Qed.

(** A source-level distinction required by the configured ready relation:
    a suspended Sem+Q Multi waiter posted on Sem retains Q|MULTI.  Resume
    clears SUSPEND but does not insert it, since PEND_ANY still contains Q.
    Therefore MultiRdy<>NULL and Dly=0 alone cannot force ready membership.
    This is a theorem about these model operations, not a complete C proof
    or a claim about a liveness guarantee of the original kernel. *)
Lemma event_multi_wake_resume_with_remaining_pending_not_ready :
  forall sg tasks s tid old selected message,
  ~ In tid s.(readyList) ->
  let waiting := task_set_status old (Byte.repr (encode_multi_wait_status 5 true)) in
  let woken := task_multi_wake waiting PendSem message PendOK selected in
  ~ In tid (sched_resume_task sg (glob_task_set_usedtask tasks tid woken) s tid woken).(readyList) /\
  (task_resume woken).(eventMultiRdy) = Some selected /\
  (task_resume woken).(tcbEventMultiPtr) = 0 /\
  (task_resume woken).(dly) = 0 /\
  task_is_suspended (task_resume woken).(stat) = false /\
  task_status_has_pending (encode_task_status (task_resume woken).(stat)) = true.
Proof. intros; cbn zeta; split; [exact H|]; repeat split; reflexivity. Qed.
