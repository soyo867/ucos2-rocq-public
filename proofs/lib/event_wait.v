Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From SimpleC.SL Require Import IntLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.

Import ListNotations.
Import TaskStateDef.
Import EventStateDef.

Local Open Scope Z_scope.
Local Open Scope list.

Definition event_type_to_pend_type (ty : OSEventType) : option PendType :=
  match ty with
  | OS_EVENT_TYPE_SEM => Some PendSem
  | OS_EVENT_TYPE_MUTEX => Some PendMutex
  | OS_EVENT_TYPE_MBOX => Some PendMbox
  | OS_EVENT_TYPE_Q => Some PendQ
  | OS_EVENT_TYPE_UNUSED => None
  | OS_EVENT_TYPE_FLAG => None
  end.

(** OSEventPendMulti accumulates only the types of unavailable resources.
    These are the Sem/Mbox/Q-enabled cases; Mutex, Flag and UNUSED take the
    source's type-error branch.  The list preserves traversal order and
    repetitions.  This mask calculation does not model resource acquisition
    or its output writes, and an enabled-Multi configuration still needs its
    actual TCB layout and borrowed-array continuation. *)
Definition event_multi_type_mask (ty : OSEventType) : option Z :=
  match ty with
  | OS_EVENT_TYPE_SEM => Some (task_pend_mask PendSem)
  | OS_EVENT_TYPE_MBOX => Some (task_pend_mask PendMbox)
  | OS_EVENT_TYPE_Q => Some (task_pend_mask PendQ)
  | _ => None
  end.

Fixpoint event_multi_wait_mask (types : list OSEventType) : option Z :=
  match types with
  | [] => Some 0
  | ty :: rest =>
      match event_multi_type_mask ty, event_multi_wait_mask rest with
      | Some first, Some remaining => Some (Z.lor first remaining)
      | _, _ => None
      end
  end.

Lemma event_multi_type_mask_in_range : forall ty mask,
  event_multi_type_mask ty = Some mask -> 0 < mask < 8.
Proof. intros [] mask H; simpl in H; try discriminate; inversion H; cbn; lia. Qed.

Lemma event_multi_wait_mask_in_range : forall types mask,
  event_multi_wait_mask types = Some mask -> 0 <= mask < 8.
Proof.
  induction types as [|ty rest IH]; intros mask Hmask; simpl in Hmask.
  - inversion Hmask; lia.
  - destruct (event_multi_type_mask ty) as [first|] eqn:Hfirst;
      destruct (event_multi_wait_mask rest) as [remaining|] eqn:Hrest; try discriminate.
    inversion Hmask; subst mask.
    pose proof (event_multi_type_mask_in_range ty first Hfirst) as HfirstRange.
    pose proof (IH remaining eq_refl) as HrestRange.
    pose proof (unsigned_Lastnbits_range (Z.lor first remaining) 3 ltac:(lia)) as Hrange.
    rewrite unsigned_last_nbits_lor_distr_missing in Hrange by (cbn; lia); exact Hrange.
Qed.

Lemma event_multi_wait_mask_nonempty : forall types mask,
  types <> [] -> event_multi_wait_mask types = Some mask -> 0 < mask < 8.
Proof.
  intros types mask Hnonempty Hmask.
  pose proof (event_multi_wait_mask_in_range types mask Hmask) as Hrange.
  destruct types as [|ty rest]; [contradiction|]; simpl in Hmask.
  destruct (event_multi_type_mask ty) as [first|] eqn:Hfirst;
    destruct (event_multi_wait_mask rest) as [remaining|] eqn:Hrest; try discriminate.
  inversion Hmask; subst mask.
  pose proof (event_multi_type_mask_in_range ty first Hfirst) as HfirstRange.
  assert (Z.lor first remaining <> 0).
  { intro Hzero; apply Z.lor_eq_0_l in Hzero; lia. }
  lia.
Qed.

(** Appending a scan suffix is exactly the source accumulator's OR update. *)
Lemma event_multi_wait_mask_app : forall left right before after,
  event_multi_wait_mask left = Some before -> event_multi_wait_mask right = Some after ->
  event_multi_wait_mask (left ++ right) = Some (Z.lor before after).
Proof.
  induction left as [|ty rest IH]; intros right before after Hleft Hright.
  - simpl in Hleft; inversion Hleft; subst before; simpl; exact Hright.
  - simpl in Hleft.
    destruct (event_multi_type_mask ty) as [first|] eqn:Hfirst;
      destruct (event_multi_wait_mask rest) as [remaining|] eqn:Hrest; try discriminate.
    inversion Hleft; subst before.
    simpl; rewrite Hfirst, (IH right remaining after eq_refl Hright).
    f_equal; apply Z.lor_assoc.
Qed.

Lemma event_multi_wait_mask_duplicate : forall ty rest,
  event_multi_wait_mask (ty :: ty :: rest) = event_multi_wait_mask (ty :: rest).
Proof.
  intros ty rest; cbn [event_multi_wait_mask];
    destruct (event_multi_type_mask ty) as [mask|];
    destruct (event_multi_wait_mask rest) as [remaining|]; try reflexivity.
  rewrite Z.lor_assoc, Z.lor_diag; reflexivity.
Qed.

(** This is only the blocking caller's three TCB stores, after its scan has
    established that no resource was acquired.  The subsequent WaitMulti
    helper, Scheduler and output-array branches are deliberately separate. *)
Definition event_multi_prepare_wait_image (image : TCBCommonImage)
  (bits timeout : Z) (unavailable_types : list OSEventType) : option TCBCommonImage :=
  match event_multi_wait_mask unavailable_types with
  | Some mask => Some (tcb_prepare_multi_wait_image image bits mask timeout)
  | None => None
  end.

Lemma event_multi_prepare_wait_image_status_in_range : forall image bits timeout types post,
  0 <= bits < 256 -> event_multi_prepare_wait_image image bits timeout types = Some post ->
  exists status, post TCBStat = Some status /\ 0 <= status < 256.
Proof.
  intros image bits timeout types post Hbits Hpost; unfold event_multi_prepare_wait_image in Hpost.
  destruct (event_multi_wait_mask types) as [mask|] eqn:Hmask; [|discriminate].
  inversion Hpost; subst post.
  exists (task_status_set_multi_wait bits mask); split; [reflexivity|].
  apply task_status_set_multi_wait_in_range; [exact Hbits|].
  eapply event_multi_wait_mask_in_range; exact Hmask.
Qed.

Lemma event_multi_prepare_wait_image_frame : forall image bits timeout types post field,
  event_multi_prepare_wait_image image bits timeout types = Some post ->
  field <> TCBStat -> field <> TCBStatPend -> field <> TCBDly -> post field = image field.
Proof.
  intros image bits timeout types post field Hpost Hstat Hpend Hdly.
  unfold event_multi_prepare_wait_image in Hpost.
  destruct (event_multi_wait_mask types); [|discriminate]; inversion Hpost; subst post.
  apply tcb_prepare_wait_image_frame; assumption.
Qed.

Lemma event_multi_wait_timeout_encoding : forall types mask suspended,
  types <> [] -> event_multi_wait_mask types = Some mask ->
  task_status_timeout (encode_multi_wait_status mask suspended) =
    (encode_multi_wait_status 0 suspended, PendTimeout).
Proof.
  intros; apply task_status_timeout_multi; eapply event_multi_wait_mask_nonempty; eauto.
Qed.

Definition wait_prio_key
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState) (tid : TaskID) : Z :=
  match tskSt.(inUsedTaskStates) tid with
  | Some t => t.(curPrio)
  | None => sg.(osLowestPrio) + 1
  end.

Definition event_waitList_canonical
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState) (wl : list TaskID) : Prop :=
  NoDup wl /\
  strictly_sorted_by (wait_prio_key sg tskSt) wl /\
  forall tid,
    In tid wl ->
    exists t,
      tskSt.(inUsedTaskStates) tid = Some t /\
      valid_task_prio sg t.(curPrio).

Definition verification_slice_event_wait_entry_consistency
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Prop :=
  event_waitList_canonical sg tskSt e.(waitList) /\
  match event_type_to_pend_type e.(eventType) with
  | Some pty =>
      forall tid,
        In tid e.(waitList) ->
        exists t,
          tskSt.(inUsedTaskStates) tid = Some t /\
          t.(eventPtr) = Some eid /\
          t.(eventMultiWaitEvents) = [] /\
          (task_non_suspension_bits t.(stat)) = task_pend_mask pty
  | None => e.(waitList) = []
  end.

Definition event_wait_entry_consistency
  (sg : StableGlobVars) (tskSt : Glob_TaskAbstractState)
  (eid : EventID) (e : OSEventAbstractState) : Prop :=
  event_waitList_canonical sg tskSt e.(waitList) /\
  match event_type_to_pend_type e.(eventType) with
  | Some pty => forall tid, In tid e.(waitList) -> exists t,
      tskSt.(inUsedTaskStates) tid = Some t /\
      t.(eventPtr) = Some eid /\ t.(eventMultiWaitEvents) = [] /\
      task_linked_wait_phase t pty
  | None => e.(waitList) = []
  end.

Lemma event_wait_entry_consistency_empty : forall sg tasks eid e,
  e.(waitList) = [] -> event_wait_entry_consistency sg tasks eid e.
Proof.
  intros sg tasks eid e Hempty; unfold event_wait_entry_consistency,
    event_waitList_canonical; rewrite Hempty; split.
  - split; [constructor|]; split; [constructor|intros tid Hin; contradiction].
  - destruct (event_type_to_pend_type e.(eventType)); [intros tid Hin; contradiction|reflexivity].
Qed.

Lemma event_wait_active_implies_linked : forall sg tskSt eid e,
  verification_slice_event_wait_entry_consistency sg tskSt eid e ->
  event_wait_entry_consistency sg tskSt eid e.
Proof.
  intros sg tskSt eid e [Horder Hphase].
  split; [exact Horder|].
  destruct (event_type_to_pend_type (eventType e)) as [pty|]; [|exact Hphase].
  intros tid Hin; destruct (Hphase tid Hin) as [t [Hget [Hev [Hmulti Hp]]]].
  exists t; repeat split; try assumption.
  unfold task_linked_wait_phase; left; exact Hp.
Qed.

(* Every live TCB reference is represented in the referenced event's wait
   list. This backlink is independent of the single-pend encoding and therefore
   covers both [eventPtr] and every member of [eventMultiWaitEvents].  Together
   with [task_event_reference_closure] it gives the two directions needed
   for sound live-to-free event transitions. *)
Definition task_event_reference_backlink_consistency
  (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState) : Prop :=
  forall tid t eid e,
    tskSt.(inUsedTaskStates) tid = Some t ->
    evSt.(inUsedEventStates) eid = Some e ->
    (t.(eventPtr) = Some eid \/ In eid t.(eventMultiWaitEvents)) ->
    In tid e.(waitList).

(* Every event identifier stored in a live TCB denotes a live event object.
   This is independent of the pend-type/backlink clause: that clause begins
   only after an event lookup has succeeded and cannot exclude a dangling
   reference to a free event slot. *)
Definition task_event_reference_closure
  (tskSt : Glob_TaskAbstractState) (evSt : Glob_EventAbstractState) : Prop :=
  forall tid t,
    tskSt.(inUsedTaskStates) tid = Some t ->
    (forall eid,
        t.(eventPtr) = Some eid ->
        exists e, evSt.(inUsedEventStates) eid = Some e) /\
    (forall eid,
        In eid t.(eventMultiWaitEvents) ->
        exists e, evSt.(inUsedEventStates) eid = Some e).

Definition task_event_id_unreferenced_prop
  (s : UCOS2_Verify_State) (eid : EventID) : Prop :=
  forall tid t,
    s.(TskState).(inUsedTaskStates) tid = Some t ->
    t.(eventPtr) <> Some eid /\ ~ In eid t.(eventMultiWaitEvents).

Lemma task_event_reference_closure_implies_unreferenced :
  forall s eid,
    s.(EventState).(inUsedEventStates) eid = None ->
    task_event_reference_closure s.(TskState) s.(EventState) ->
    task_event_id_unreferenced_prop s eid.
Proof.
  intros s eid Hfree Hclosed tid t Htask.
  specialize (Hclosed tid t Htask) as [Hsingle Hmulti].
  split.
  - intro Hptr. destruct (Hsingle eid Hptr) as [e He].
    rewrite Hfree in He. discriminate.
  - intro Hin. destruct (Hmulti eid Hin) as [e He].
    rewrite Hfree in He. discriminate.
Qed.

Lemma task_event_reference_closure_preserved_by_tskSt_ext :
  forall tskSt1 tskSt2 evSt,
    (forall tid,
        tskSt1.(inUsedTaskStates) tid =
        tskSt2.(inUsedTaskStates) tid) ->
    task_event_reference_closure tskSt1 evSt ->
    task_event_reference_closure tskSt2 evSt.
Proof.
  intros tskSt1 tskSt2 evSt Heq Hclosed tid t Htask.
  apply (Hclosed tid t). rewrite Heq. exact Htask.
Qed.

Lemma task_event_reference_closure_preserved_by_event_extension :
  forall tskSt evSt1 evSt2,
    (forall eid,
        (exists e, evSt1.(inUsedEventStates) eid = Some e) ->
        exists e, evSt2.(inUsedEventStates) eid = Some e) ->
    task_event_reference_closure tskSt evSt1 ->
    task_event_reference_closure tskSt evSt2.
Proof.
  intros tskSt evSt1 evSt2 Hext Hclosed tid t Htask.
  specialize (Hclosed tid t Htask) as [Hsingle Hmulti]. split.
  - intros eid Hptr. apply Hext. apply Hsingle. exact Hptr.
  - intros eid Hin. apply Hext. apply Hmulti. exact Hin.
Qed.

Definition verification_slice_event_wait_object_consistency
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Prop :=
  (forall eid e,
      s.(EventState).(inUsedEventStates) eid = Some e ->
      verification_slice_event_wait_entry_consistency sg s.(TskState) eid e) /\
  task_event_reference_backlink_consistency s.(TskState) s.(EventState) /\
  task_event_reference_closure s.(TskState) s.(EventState).

Definition event_wait_object_consistency
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Prop :=
  (forall eid e, s.(EventState).(inUsedEventStates) eid = Some e ->
     event_wait_entry_consistency sg s.(TskState) eid e) /\
  task_event_reference_backlink_consistency s.(TskState) s.(EventState) /\
  task_event_reference_closure s.(TskState) s.(EventState).

(** A previously unpublished slot has no live TCB reference, by the old
    reference closure.  Publication extends the existing map; it neither
    creates waiter registrations nor assumes a new global invariant. *)
Lemma event_wait_object_consistency_event_publish : forall sg s events eid node,
  s.(EventState).(inUsedEventStates) eid = None -> node.(waitList) = [] ->
  events.(inUsedEventStates) = kernel_map_set s.(EventState).(inUsedEventStates) eid (Some node) ->
  event_wait_object_consistency sg s ->
  event_wait_object_consistency sg (replace_EventS events s).
Proof.
  intros sg s events eid node Hnone Hempty Hmap [Hentries [Hback Hclosed]].
  pose proof (task_event_reference_closure_implies_unreferenced s eid Hnone Hclosed) as Hsafe.
  unfold event_wait_object_consistency; cbn [replace_EventS TskState EventState]; split.
  - intros slot e He; rewrite Hmap in He; unfold kernel_map_set in He.
    destruct (Z.eq_dec slot eid) as [->|Hne].
    + injection He as He; subst e; apply event_wait_entry_consistency_empty; exact Hempty.
    + exact (Hentries slot e He).
  - split.
    + intros tid t slot e Htask He Href; rewrite Hmap in He; unfold kernel_map_set in He.
      destruct (Z.eq_dec slot eid) as [->|Hne].
      * exfalso; destruct (Hsafe tid t Htask) as [HnoSingle HnoMulti]; tauto.
      * eapply Hback; eassumption.
    + eapply task_event_reference_closure_preserved_by_event_extension; [|exact Hclosed].
      intros slot [e He]; exists e; rewrite Hmap; unfold kernel_map_set.
      destruct (Z.eq_dec slot eid) as [->|Hne]; [congruence|exact He].
Qed.

Lemma event_wait_entry_preserved_by_link_updates : forall sg before after eid e,
  (forall tid old, In tid e.(waitList) -> before.(inUsedTaskStates) tid = Some old -> exists new,
     after.(inUsedTaskStates) tid = Some new /\
     task_set_links new None None = task_set_links old None None) ->
  event_wait_entry_consistency sg before eid e ->
  event_wait_entry_consistency sg after eid e.
Proof.
  intros sg before after eid e Htransport [[Hnd [Hsorted Hmembers]] Hphase].
  assert (Hkey : forall tid, In tid e.(waitList) ->
    wait_prio_key sg before tid = wait_prio_key sg after tid).
  { intros tid Hin; destruct (Hmembers tid Hin) as [old [Hold Hprio]].
    destruct (Htransport tid old Hin Hold) as [new [Hnew Hfields]].
    pose proof (f_equal curPrio Hfields) as Hprioeq; simpl in Hprioeq.
    unfold wait_prio_key; rewrite Hold, Hnew; symmetry; exact Hprioeq. }
  split.
  - split; [exact Hnd|]. split.
    + eapply strictly_sorted_by_key_eq_on; [exact Hkey|exact Hsorted].
    + intros tid Hin; destruct (Hmembers tid Hin) as [old [Hold Hprio]].
      destruct (Htransport tid old Hin Hold) as [new [Hnew Hfields]].
      pose proof (f_equal curPrio Hfields) as Hprioeq; simpl in Hprioeq.
      exists new; split; [exact Hnew|rewrite Hprioeq; exact Hprio].
  - destruct (event_type_to_pend_type e.(eventType)) as [pty|]; [|exact Hphase].
    intros tid Hin; destruct (Hphase tid Hin) as [old [Hold [Hptr [Hmulti Hlinked]]]].
    destruct (Htransport tid old Hin Hold) as [new [Hnew Hfields]].
    pose proof (f_equal eventPtr Hfields) as HptrEq; simpl in HptrEq.
    pose proof (f_equal eventMultiWaitEvents Hfields) as HmultiEq; simpl in HmultiEq.
    pose proof (f_equal stat Hfields) as HstatEq; simpl in HstatEq.
    pose proof (f_equal statPend Hfields) as HpendEq; simpl in HpendEq.
    pose proof (f_equal dly Hfields) as HdlyEq; simpl in HdlyEq.
    exists new; split; [exact Hnew|].
    split; [rewrite HptrEq; exact Hptr|]. split; [rewrite HmultiEq; exact Hmulti|].
    unfold task_linked_wait_phase in *; rewrite HstatEq, HpendEq, HdlyEq; exact Hlinked.
Qed.

Lemma task_commit_preserves_event_wait_entry : forall sg tasks p invocation node eid e,
  tasks.(inUsedTaskStates) node.(taskID) = None ->
  event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg (task_commit tasks p invocation node) eid e.
Proof.
  intros sg tasks p invocation node eid e Hnone Hentry.
  eapply event_wait_entry_preserved_by_link_updates; [|exact Hentry].
  intros tid old Hin Hold.
  pose proof (task_commit_observation TaskAbstractState
    (fun t => task_set_links t None None) tasks p invocation node tid
    (fun _ _ _ => eq_refl)) as Hfields.
  destruct (Z.eq_dec tid node.(taskID)); [subst; congruence|].
  rewrite Hold in Hfields.
  destruct ((task_commit tasks p invocation node).(inUsedTaskStates) tid)
    as [new|] eqn:Hnew; [|discriminate].
  change (Some (task_set_links new None None) =
          Some (task_set_links old None None)) in Hfields.
  assert (Heq : task_set_links new None None = task_set_links old None None)
    by congruence.
  exists new; split; [reflexivity|exact Heq].
Qed.

Lemma task_commit_preserves_event_wait_object_consistency :
  forall sg s p invocation node sched',
    s.(TskState).(inUsedTaskStates) node.(taskID) = None ->
    node.(eventPtr) = None -> node.(eventMultiWaitEvents) = [] ->
    event_wait_object_consistency sg s ->
    event_wait_object_consistency sg
      (replace_SchedS sched' (replace_TskS (task_commit s.(TskState) p invocation node) s)).
Proof.
  intros sg s p invocation node sched' Hnone Hnodeptr Hnodemulti
    [Hentry [Hback Hclosed]].
  assert (Hlookup : forall tid new,
    (task_commit s.(TskState) p invocation node).(inUsedTaskStates) tid = Some new ->
    (tid = node.(taskID) /\ new.(eventPtr) = None /\ new.(eventMultiWaitEvents) = []) \/
    exists old, s.(TskState).(inUsedTaskStates) tid = Some old /\
      task_set_links new None None = task_set_links old None None).
  { intros tid new Hnew.
    pose proof (task_commit_observation TaskAbstractState
      (fun t => task_set_links t None None) s.(TskState) p invocation node tid
      (fun _ _ _ => eq_refl)) as Hfields.
    rewrite Hnew in Hfields.
    destruct (Z.eq_dec tid node.(taskID)) as [Heq|Hneq].
    - change (Some (task_set_links new None None) =
              Some (task_set_links node None None)) in Hfields.
      assert (HfieldsEq : task_set_links new None None = task_set_links node None None)
        by congruence.
      left; split; [exact Heq|].
      pose proof (f_equal eventPtr HfieldsEq) as Hptr; simpl in Hptr.
      pose proof (f_equal eventMultiWaitEvents HfieldsEq) as Hmulti; simpl in Hmulti.
      split; congruence.
    - destruct (s.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
      change (Some (task_set_links new None None) =
              Some (task_set_links old None None)) in Hfields.
      assert (HfieldsEq : task_set_links new None None = task_set_links old None None)
        by congruence.
      right; exists old; split; [reflexivity|exact HfieldsEq]. }
  split.
  - intros eid e He; apply task_commit_preserves_event_wait_entry; auto.
  - split.
    + intros tid new eid e Hnew He Href.
      destruct (Hlookup tid new Hnew) as [[_ [Hnull Hnil]]|[old [Hold Hfields]]].
      * destruct Href as [Hptr|Hin]; [congruence|rewrite Hnil in Hin; contradiction].
      * pose proof (f_equal eventPtr Hfields) as Hp; simpl in Hp.
        pose proof (f_equal eventMultiWaitEvents Hfields) as Hm; simpl in Hm.
        eapply Hback; eauto; rewrite <- Hp, <- Hm; exact Href.
    + intros tid new Hnew.
      destruct (Hlookup tid new Hnew) as [[_ [Hnull Hnil]]|[old [Hold Hfields]]].
      * split; intros eid Href; [congruence|rewrite Hnil in Href; contradiction].
      * pose proof (f_equal eventPtr Hfields) as Hp; simpl in Hp.
        pose proof (f_equal eventMultiWaitEvents Hfields) as Hm; simpl in Hm.
        destruct (Hclosed tid old Hold) as [Hc1 Hc2]; split; intros eid Href.
        -- apply Hc1; rewrite <- Hp; exact Href.
        -- apply Hc2; rewrite <- Hm; exact Href.
Qed.

Lemma event_wait_object_active_implies : forall sg state,
  verification_slice_event_wait_object_consistency sg state ->
  event_wait_object_consistency sg state.
Proof.
  intros sg state [Hentry Hrest]; split; [|exact Hrest].
  intros eid e Hlookup; apply event_wait_active_implies_linked.
  apply Hentry; exact Hlookup.
Qed.

Lemma event_wait_empty_implies_unreferenced :
  forall sg s eid e,
    s.(EventState).(inUsedEventStates) eid = Some e ->
    e.(waitList) = [] ->
    verification_slice_event_wait_object_consistency sg s ->
    task_event_id_unreferenced_prop s eid.
Proof.
  intros sg s eid e Hlookup Hempty Hconsistent tid t Htask.
  unfold verification_slice_event_wait_object_consistency in Hconsistent.
  destruct Hconsistent as [_ [Hback _]].
  split.
  - intro Hptr.
    specialize (Hback tid t eid e Htask Hlookup (or_introl Hptr)).
    rewrite Hempty in Hback. inversion Hback.
  - intro Hmulti.
    specialize (Hback tid t eid e Htask Hlookup (or_intror Hmulti)).
    rewrite Hempty in Hback. inversion Hback.
Qed.

(* ================================================================== *)
(* Preservation lemmas: inUsedTaskStates extensional equality         *)
(*                                                                    *)
(* These lemmas allow transferring event_wait_* consistency from one  *)
(* TskState to another when only inUsedTaskStates is preserved.       *)
(* This is needed when an atomic step modifies only TskState fields   *)
(* other than inUsedTaskStates.                                       *)
(* ================================================================== *)

Lemma wait_prio_key_ext :
  forall sg tskSt1 tskSt2,
    (forall tid, tskSt1.(inUsedTaskStates) tid = tskSt2.(inUsedTaskStates) tid) ->
    forall tid, wait_prio_key sg tskSt1 tid = wait_prio_key sg tskSt2 tid.
Proof.
  intros sg tskSt1 tskSt2 Heq tid.
  unfold wait_prio_key. rewrite Heq. reflexivity.
Qed.

Lemma event_waitList_canonical_preserved_by_tskSt_ext :
  forall sg tskSt1 tskSt2 wl,
    (forall tid, tskSt1.(inUsedTaskStates) tid = tskSt2.(inUsedTaskStates) tid) ->
    event_waitList_canonical sg tskSt1 wl ->
    event_waitList_canonical sg tskSt2 wl.
Proof.
  intros sg tskSt1 tskSt2 wl Heq Hcanon.
  unfold event_waitList_canonical in *.
  destruct Hcanon as [Hnd [Hss Hinv]].
  split; [| split].
  - exact Hnd.
  - apply (strictly_sorted_by_key_ext _ (wait_prio_key sg tskSt1) (wait_prio_key sg tskSt2) wl).
    intro x. apply (wait_prio_key_ext sg tskSt1 tskSt2 Heq).
    exact Hss.
  - intros tid Hin. destruct (Hinv tid Hin) as [t [Hgett Hprio]].
    exists t. split.
    + rewrite Heq in Hgett. exact Hgett.
    + exact Hprio.
Qed.

Lemma verification_slice_event_wait_entry_consistency_preserved_by_tskSt_ext :
  forall sg tskSt1 tskSt2 eid e,
    (forall tid, tskSt1.(inUsedTaskStates) tid = tskSt2.(inUsedTaskStates) tid) ->
    verification_slice_event_wait_entry_consistency sg tskSt1 eid e ->
    verification_slice_event_wait_entry_consistency sg tskSt2 eid e.
Proof.
  intros sg tskSt1 tskSt2 eid e Heq Hentry.
  unfold verification_slice_event_wait_entry_consistency in *.
  destruct Hentry as [Hcanon Hback].
  split.
  - apply (event_waitList_canonical_preserved_by_tskSt_ext sg tskSt1 tskSt2 _ Heq).
    exact Hcanon.
  - destruct (event_type_to_pend_type e.(eventType)) as [pty|] eqn:Hpty.
    + intros tid Hin. destruct (Hback tid Hin) as [t [Hgett [Hptr [Hmult Hpty_t]]]].
      exists t. split; [| split; [| split]].
      * rewrite Heq in Hgett. exact Hgett.
      * exact Hptr. * exact Hmult. * exact Hpty_t.
    + exact Hback.
Qed.

Lemma task_event_reference_backlink_consistency_preserved_by_tskSt_ext :
  forall tskSt1 tskSt2 evSt,
    (forall tid,
        tskSt1.(inUsedTaskStates) tid =
        tskSt2.(inUsedTaskStates) tid) ->
    task_event_reference_backlink_consistency tskSt1 evSt ->
    task_event_reference_backlink_consistency tskSt2 evSt.
Proof.
  intros tskSt1 tskSt2 evSt Heq Hback tid t eid e Htask Hevent Href.
  apply (Hback tid t eid e).
  - rewrite Heq. exact Htask.
  - exact Hevent.
  - exact Href.
Qed.

Lemma event_wait_entry_task_lookup_ext : forall sg before after eid e,
  (forall tid, In tid e.(waitList) ->
     after.(inUsedTaskStates) tid = before.(inUsedTaskStates) tid) ->
  event_wait_entry_consistency sg before eid e ->
  event_wait_entry_consistency sg after eid e.
Proof.
  intros sg before after eid e Heq [[Hnd [Hsort Hmembers]] Hphase].
  split.
  - split; [exact Hnd|]. split.
    + eapply strictly_sorted_by_key_eq_on; [|exact Hsort].
      intros tid Hin; unfold wait_prio_key; rewrite Heq by exact Hin; reflexivity.
    + intros tid Hin; rewrite Heq by exact Hin; exact (Hmembers tid Hin).
  - destruct (event_type_to_pend_type e.(eventType)) as [pty|]; [|exact Hphase].
    intros tid Hin; rewrite Heq by exact Hin; exact (Hphase tid Hin).
Qed.

Lemma event_wait_entry_update_unlisted_task : forall sg tasks tid new eid e,
  ~ In tid e.(waitList) -> event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg (glob_task_set_usedtask tasks tid new) eid e.
Proof.
  intros sg tasks tid new eid e Habsent Hentry.
  eapply event_wait_entry_task_lookup_ext; [|exact Hentry].
  intros slot Hin; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
  apply Z.eqb_eq in E; subst slot; contradiction.
Qed.

Lemma event_wait_object_update_unlisted_task : forall sg s tid old new,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  new.(eventPtr) = old.(eventPtr) -> new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  (forall eid e, s.(EventState).(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)) ->
  event_wait_object_consistency sg s ->
  event_wait_object_consistency sg
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s).
Proof.
  intros sg s tid old new Hold Hp Hm Habsent [Hentries [Hback Hclosed]].
  assert (Horigin : forall slot t,
    (glob_task_set_usedtask s.(TskState) tid new).(inUsedTaskStates) slot = Some t ->
    exists before, s.(TskState).(inUsedTaskStates) slot = Some before /\
      t.(eventPtr) = before.(eventPtr) /\ t.(eventMultiWaitEvents) = before.(eventMultiWaitEvents)).
  { intros slot t Ht; simpl in Ht; destruct (Z.eqb slot tid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Ht as Heq; subst t; exists old; auto.
    - exists t; auto. }
  split.
  - intros eid e He; apply event_wait_entry_update_unlisted_task;
      [eapply Habsent|eapply Hentries]; eauto.
  - split.
    + intros slot t eid e Ht He Href.
      destruct (Horigin slot t Ht) as [before [Hb [HptrEq HmultiEq]]].
      eapply Hback; [exact Hb|exact He|]. rewrite <- HptrEq, <- HmultiEq; exact Href.
    + intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb [HptrEq HmultiEq]]].
      destruct (Hclosed slot before Hb) as [HsingleClosed HmultiClosed].
      split; intros eid Href; [apply HsingleClosed; congruence|].
      apply HmultiClosed; rewrite <- HmultiEq; exact Href.
Qed.

(** The bitmap's logical waiter list is changed independently of payload,
    object identity and padding.  TCB pointer cleanup has its own Task owner. *)
Definition event_set_wait_list (e : OSEventAbstractState) (waiters : list TaskID)
  : OSEventAbstractState :=
  {| eventType := e.(eventType); mutexFields := e.(mutexFields); semFields := e.(semFields);
     mboxFields := e.(mboxFields); queueFields := e.(queueFields); waitList := waiters;
     eventGeneration := e.(eventGeneration); eventName := e.(eventName);
     eventPadding1 := e.(eventPadding1);
     eventPadding2 := e.(eventPadding2);
     eventPadding3 := e.(eventPadding3);
     eventPadding19 := e.(eventPadding19) |}.

Lemma event_set_wait_list_put_back : forall e, event_set_wait_list e e.(waitList) = e.
Proof. intros []; reflexivity. Qed.

Lemma event_set_wait_list_last_write : forall e before after,
  event_set_wait_list (event_set_wait_list e before) after = event_set_wait_list e after.
Proof. reflexivity. Qed.

Lemma event_waitList_canonical_remove : forall sg tasks waiters tid,
  event_waitList_canonical sg tasks waiters ->
  event_waitList_canonical sg tasks (remove_Z_eqb tid waiters).
Proof.
  intros sg tasks waiters tid [Hnd [Hsorted Hmembers]]; split.
  - apply remove_Z_eqb_NoDup; exact Hnd.
  - split; [apply remove_Z_eqb_strictly_sorted_by; exact Hsorted|].
    intros other Hin; apply Hmembers; eapply remove_Z_eqb_in; exact Hin.
Qed.

Lemma event_wait_entry_remove_waiter : forall sg tasks eid e tid,
  event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg tasks eid
    (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
Proof.
  intros sg tasks eid e tid [Hcanonical Hphase]; split.
  - apply event_waitList_canonical_remove; exact Hcanonical.
  - simpl; destruct (event_type_to_pend_type e.(eventType));
      [intros other Hin; apply Hphase; eapply remove_Z_eqb_in; exact Hin|].
    rewrite Hphase; reflexivity.
Qed.

Lemma event_wait_entry_remove_update_task : forall sg tasks eid e tid new,
  event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg (glob_task_set_usedtask tasks tid new) eid
    (event_set_wait_list e (remove_Z_eqb tid e.(waitList))).
Proof.
  intros; apply event_wait_entry_update_unlisted_task.
  - apply remove_Z_eqb_notin.
  - apply event_wait_entry_remove_waiter; assumption.
Qed.

Lemma event_waiter_task_fields : forall sg tasks eid e tid,
  event_wait_entry_consistency sg tasks eid e -> In tid e.(waitList) ->
  exists t kind, tasks.(inUsedTaskStates) tid = Some t /\
    event_type_to_pend_type e.(eventType) = Some kind /\
    t.(eventPtr) = Some eid /\ t.(eventMultiWaitEvents) = [] /\ task_linked_wait_phase t kind.
Proof.
  intros sg tasks eid e tid [_ Hphase] Hin.
  destruct (event_type_to_pend_type e.(eventType)) as [kind|] eqn:Hkind.
  - destruct (Hphase tid Hin) as [t [Hget [Hptr [Hmulti Hlinked]]]]; exists t, kind; auto.
  - rewrite Hphase in Hin; contradiction.
Qed.

Lemma event_waiter_unique_event : forall sg tasks events first second e1 e2 tid,
  (forall eid e, events.(inUsedEventStates) eid = Some e ->
    event_wait_entry_consistency sg tasks eid e) ->
  events.(inUsedEventStates) first = Some e1 -> events.(inUsedEventStates) second = Some e2 ->
  In tid e1.(waitList) -> In tid e2.(waitList) -> first = second.
Proof.
  intros sg tasks events first second e1 e2 tid Hentries Hfirst Hsecond Hin1 Hin2.
  destruct (event_waiter_task_fields sg tasks first e1 tid (Hentries first e1 Hfirst) Hin1)
    as [t1 [kind1 [Ht1 [_ [Hp1 _]]]]].
  destruct (event_waiter_task_fields sg tasks second e2 tid (Hentries second e2 Hsecond) Hin2)
    as [t2 [kind2 [Ht2 [_ [Hp2 _]]]]].
  assert (t1 = t2) by congruence; subst t2; congruence.
Qed.

(** This is the logical effect of setting one bit in an Event's wait
    bitmap, not a TCB write.  Removal before insertion makes the model
    idempotent even if the source sets an already-present bit. *)
Definition event_insert_waiter (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (e : OSEventAbstractState) (tid : TaskID) : OSEventAbstractState :=
  event_set_wait_list e
    (insert_sorted_by (wait_prio_key sg tasks) tid (remove_Z_eqb tid e.(waitList))).

Lemma event_insert_waiter_membership : forall sg tasks e tid slot,
  In slot (event_insert_waiter sg tasks e tid).(waitList) <->
    slot = tid \/ In slot e.(waitList).
Proof.
  intros; unfold event_insert_waiter; simpl; rewrite insert_sorted_by_in; simpl.
  split.
  - intros [Heq|Hin]; [left; congruence|right; eapply remove_Z_eqb_in; exact Hin].
  - intros [Heq|Hin]; [left; congruence|].
    destruct (Z.eq_dec slot tid) as [Heq|Hne]; [left; congruence|].
    right; apply remove_Z_eqb_in_neq; assumption.
Qed.

Lemma event_insert_waiter_idempotent : forall sg tasks e tid,
  event_insert_waiter sg tasks (event_insert_waiter sg tasks e tid) tid =
    event_insert_waiter sg tasks e tid.
Proof.
  intros sg tasks e tid.
  assert (Hremove : forall waiters,
    remove_Z_eqb tid (insert_sorted_by (wait_prio_key sg tasks) tid waiters) =
      remove_Z_eqb tid waiters).
  { induction waiters as [|head rest IH]; simpl; [rewrite Z.eqb_refl; reflexivity|].
    destruct (Z.ltb _ _); simpl.
    - rewrite Z.eqb_refl; reflexivity.
    - destruct (Z.eqb head tid); rewrite IH; reflexivity. }
  unfold event_insert_waiter; simpl; rewrite Hremove.
  rewrite (remove_Z_eqb_notin_eq tid (remove_Z_eqb tid e.(waitList))
    (remove_Z_eqb_notin tid e.(waitList))).
  rewrite event_set_wait_list_last_write; reflexivity.
Qed.

Lemma event_insert_waiter_preserves_canonical : forall sg tasks e tid t,
  event_waitList_canonical sg tasks e.(waitList) -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some t -> valid_task_prio sg t.(curPrio) ->
  event_waitList_canonical sg tasks (event_insert_waiter sg tasks e tid).(waitList).
Proof.
  intros sg tasks e tid t [Hnd [Hsorted Hmembers]] Hunique Ht Hprio.
  split.
  - apply insert_sorted_by_preserves_NoDup; [apply remove_Z_eqb_NoDup; exact Hnd|apply remove_Z_eqb_notin].
  - split.
    + apply insert_sorted_by_preserves; [apply remove_Z_eqb_strictly_sorted_by; exact Hsorted|].
      intros slot Hin Heq.
      destruct (Hmembers slot (remove_Z_eqb_in tid slot e.(waitList) Hin)) as [node [Hnode Hrange]].
      unfold wait_prio_key in Heq; rewrite Hnode, Ht in Heq.
      assert (slot = tid) by (eapply Hunique; eauto); subst slot.
      exact (remove_Z_eqb_notin tid e.(waitList) Hin).
    + intros slot Hin; apply event_insert_waiter_membership in Hin; destruct Hin as [->|Hin].
      * exists t; auto.
      * exact (Hmembers slot Hin).
Qed.

Lemma event_wait_entry_insert_waiter : forall sg tasks eid e tid t kind,
  event_wait_entry_consistency sg tasks eid e -> task_priority_unique tasks ->
  tasks.(inUsedTaskStates) tid = Some t -> valid_task_prio sg t.(curPrio) ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  t.(eventPtr) = Some eid -> t.(eventMultiWaitEvents) = [] -> task_linked_wait_phase t kind ->
  event_wait_entry_consistency sg tasks eid (event_insert_waiter sg tasks e tid).
Proof.
  intros sg tasks eid e tid t kind [Hcanonical Hphase] Hunique Ht Hprio Hkind Hptr Hmulti Hlinked.
  split; [eapply event_insert_waiter_preserves_canonical; eauto|].
  change (match event_type_to_pend_type e.(eventType) with
    | Some actual => forall slot, In slot (event_insert_waiter sg tasks e tid).(waitList) ->
        exists node, tasks.(inUsedTaskStates) slot = Some node /\ node.(eventPtr) = Some eid /\
          node.(eventMultiWaitEvents) = [] /\ task_linked_wait_phase node actual
    | None => (event_insert_waiter sg tasks e tid).(waitList) = [] end).
  rewrite Hkind in Hphase |- *; intros slot Hin; apply event_insert_waiter_membership in Hin.
  destruct Hin as [->|Hin]; [exists t; auto|exact (Hphase slot Hin)].
Qed.

(** The caller has already set its pending status and delay.  The helper
    writes only EventPtr in this TCB stage; it neither resets StatPend nor
    replays the caller's stores. *)
Lemma event_wait_entry_insert_update_task : forall sg tasks eid e tid old kind,
  task_in_range sg tasks -> event_wait_entry_consistency sg tasks eid e ->
  tasks.(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] -> (task_non_suspension_bits old.(stat)) = task_pend_mask kind ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  let updated := glob_task_set_usedtask tasks tid (task_set_event_ptr old (Some eid)) in
  event_wait_entry_consistency sg updated eid (event_insert_waiter sg updated e tid).
Proof.
  intros sg tasks eid e tid old kind Htasks Hentry Hold Hprio Hnull Hmulti Hpending Hkind updated.
  assert (Habsent : ~ In tid e.(waitList)).
  { intro Hin; destruct (event_waiter_task_fields sg tasks eid e tid Hentry Hin)
      as [found [actual [Hfound [_ [Hptr _]]]]].
    assert (found = old) by congruence; subst found; congruence. }
  assert (Hentry_updated : event_wait_entry_consistency sg updated eid e).
  { apply event_wait_entry_update_unlisted_task; assumption. }
  pose proof (task_set_event_ptr_preserves_in_range sg tasks tid old (Some eid) Htasks Hold)
    as Htasks_updated.
  destruct Htasks_updated as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  eapply event_wait_entry_insert_waiter with (t := task_set_event_ptr old (Some eid)) (kind := kind).
  - exact Hentry_updated.
  - exact Hunique.
  - unfold updated; simpl; rewrite Z.eqb_refl; reflexivity.
  - exact Hprio.
  - exact Hkind.
  - reflexivity.
  - exact Hmulti.
  - left; exact Hpending.
Qed.

Lemma event_insert_waiter_update_task_eq : forall sg tasks tid old new e member,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  event_insert_waiter sg (glob_task_set_usedtask tasks tid new) e member =
    event_insert_waiter sg tasks e member.
Proof.
  intros sg tasks tid old new e member Hold Hprio.
  assert (Hkey : forall slot,
    wait_prio_key sg (glob_task_set_usedtask tasks tid new) slot = wait_prio_key sg tasks slot).
  { intro slot; unfold wait_prio_key; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold; exact Hprio. }
  unfold event_insert_waiter; f_equal.
  induction (remove_Z_eqb member e.(waitList)) as [|head tail IH]; cbn [insert_sorted_by].
  - reflexivity.
  - rewrite !Hkey; destruct (Z.ltb (wait_prio_key sg tasks member) (wait_prio_key sg tasks head));
      [reflexivity|f_equal; exact IH].
Qed.

Lemma event_waitList_canonical_update_task : forall sg tasks tid old new ids,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  event_waitList_canonical sg tasks ids ->
  event_waitList_canonical sg (glob_task_set_usedtask tasks tid new) ids.
Proof.
  intros sg tasks tid old new ids Hold Hprio [Hnd [Hsorted Hmembers]].
  split; [exact Hnd|]; split.
  - eapply strictly_sorted_by_key_ext; [|exact Hsorted].
    intro slot; unfold wait_prio_key; simpl; destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold; symmetry; exact Hprio.
  - intros slot Hin; destruct (Hmembers slot Hin) as [node [Hnode Hp]].
    simpl; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (node = old) by congruence; subst node.
      exists new; split; [reflexivity|rewrite Hprio; exact Hp].
    + exists node; auto.
Qed.

(** Task-field updates may preserve a wait registration without preserving
    the entire status/delay tuple.  In particular Tick transports registered
    waiters to timeout-linked waiters.  Pointer/priority equalities and the
    actual phase implication are sufficient; no complete-TCB equality is
    needed and no waiter is silently removed. *)
Lemma event_wait_entry_update_task : forall sg tasks tid old new eid e,
  tasks.(inUsedTaskStates) tid = Some old ->
  new.(curPrio) = old.(curPrio) -> new.(eventPtr) = old.(eventPtr) ->
  new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  (forall kind, task_linked_wait_phase old kind -> task_linked_wait_phase new kind) ->
  event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg (glob_task_set_usedtask tasks tid new) eid e.
Proof.
  intros sg tasks tid old new eid e Hold Hprio Hptr Hmulti Htransport [Hcanonical Hphase]; split.
  - eapply event_waitList_canonical_update_task; [exact Hold|exact Hprio|exact Hcanonical].
  - destruct (event_type_to_pend_type e.(eventType)) as [kind|]; [|exact Hphase].
    intros slot Hin; destruct (Hphase slot Hin) as [node [Hnode [Hp [Hm Hlinked]]]].
    simpl; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (node = old) by congruence; subst node.
      exists new; split; [reflexivity|]; split; [rewrite Hptr; exact Hp|].
      split; [rewrite Hmulti; exact Hm|apply Htransport; exact Hlinked].
    + exists node; auto.
Qed.

Lemma event_wait_object_update_task : forall sg s tid old new,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  new.(curPrio) = old.(curPrio) -> new.(eventPtr) = old.(eventPtr) ->
  new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  (forall kind, task_linked_wait_phase old kind -> task_linked_wait_phase new kind) ->
  event_wait_object_consistency sg s ->
  event_wait_object_consistency sg
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid new) s).
Proof.
  intros sg s tid old new Hold Hprio Hptr Hmulti Htransport [Hentries [Hback Hclosed]].
  assert (Horigin : forall slot t,
    (glob_task_set_usedtask s.(TskState) tid new).(inUsedTaskStates) slot = Some t ->
    exists before, s.(TskState).(inUsedTaskStates) slot = Some before /\
      t.(eventPtr) = before.(eventPtr) /\ t.(eventMultiWaitEvents) = before.(eventMultiWaitEvents)).
  { intros slot t Ht; simpl in Ht; destruct (Z.eqb slot tid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Ht as Ht; subst t.
      exists old; split; [exact Hold|]; split; assumption.
    - exists t; auto. }
  split.
  - intros eid e He; eapply event_wait_entry_update_task;
      [exact Hold|exact Hprio|exact Hptr|exact Hmulti|exact Htransport|exact (Hentries eid e He)].
  - split.
    + intros slot t eid e Ht He Href.
      destruct (Horigin slot t Ht) as [before [Hb [HptrEq HmultiEq]]].
      eapply Hback; [exact Hb|exact He|].
      rewrite <- HptrEq, <- HmultiEq; exact Href.
    + intros slot t Ht; destruct (Horigin slot t Ht) as [before [Hb [HptrEq HmultiEq]]].
      destruct (Hclosed slot before Hb) as [HsingleClosed HmultiClosed]; split; intros eid Href.
      * apply HsingleClosed; congruence.
      * apply HmultiClosed; rewrite <- HmultiEq; exact Href.
Qed.

(** Keep the established suspension/status interfaces as consequences of
    the shared field/phase transport, with their statements unchanged. *)
Lemma event_wait_entry_update_status : forall sg tasks tid old status eid e,
  tasks.(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits status = task_non_suspension_bits old.(stat) ->
  event_wait_entry_consistency sg tasks eid e ->
  event_wait_entry_consistency sg
    (glob_task_set_usedtask tasks tid (task_set_status old status)) eid e.
Proof.
  intros sg tasks tid old status eid e Hold Hbits Hentry.
  eapply event_wait_entry_update_task;
    [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hentry].
  intros kind Hphase; unfold task_linked_wait_phase; cbn [task_set_status stat statPend dly].
  rewrite Hbits; exact Hphase.
Qed.

Lemma event_wait_object_update_status : forall sg s tid old status,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  task_non_suspension_bits status = task_non_suspension_bits old.(stat) ->
  event_wait_object_consistency sg s ->
  event_wait_object_consistency sg
    (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_status old status)) s).
Proof.
  intros sg s tid old status Hold Hbits Hwait.
  eapply event_wait_object_update_task;
    [exact Hold|reflexivity|reflexivity|reflexivity| |exact Hwait].
  intros kind Hphase; unfold task_linked_wait_phase; cbn [task_set_status stat statPend dly].
  rewrite Hbits; exact Hphase.
Qed.
