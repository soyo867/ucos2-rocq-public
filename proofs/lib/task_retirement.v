Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.tick.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskDel's three TCB writes after Event/Flag unlinking and before the
    scheduler-lock/Restore window.  The source leaves EventPtr, MultiPtr,
    message, DelReq, generation and links untouched here.  In particular
    this is neither freeing the slot nor retiring any saved invocation. *)
Definition task_prepare_delete (t : TaskAbstractState) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration); tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := Byte.zero; statPend := PendOK; dly := 0;
     eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Definition tcb_prepare_delete_image (image : TCBLayoutImage)
  : TCBLayoutImage :=
  tcb_layout_write
    (tcb_layout_write
      (tcb_layout_write image (TCBCommonField TCBDly) (Some 0))
      (TCBCommonField TCBStat) (Some 0))
    (TCBCommonField TCBStatPend) (Some 0).

Lemma task_prepare_delete_layout_image_eq : forall sg t,
  task_layout_image sg (task_prepare_delete t) =
    tcb_prepare_delete_image (task_layout_image sg t).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |];
    try destruct field; reflexivity.
Qed.

Lemma tcb_prepare_delete_image_frame : forall image field,
  field <> TCBCommonField TCBDly -> field <> TCBCommonField TCBStat ->
  field <> TCBCommonField TCBStatPend ->
  tcb_prepare_delete_image image field = image field.
Proof.
  intros image [field| | | | | | |] Hdly Hstat Hresult; try destruct field;
    try reflexivity; contradiction.
Qed.

Lemma task_prepare_delete_preserves_in_range : forall sg tasks tid old,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_in_range sg (glob_task_set_usedtask tasks tid (task_prepare_delete old)).
Proof.
  intros; eapply task_update_preserves_in_range;
    [exact H|exact H0|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity].
Qed.

Lemma task_prepare_delete_preserves_invocation_active : forall tasks tid old invocation origin,
  tasks.(inUsedTaskStates) tid = Some old -> task_invocation_active tasks invocation origin ->
  task_invocation_active (glob_task_set_usedtask tasks tid (task_prepare_delete old)) invocation origin.
Proof.
  intros; eapply glob_task_set_usedtask_preserves_invocation_active;
    [exact H|reflexivity|exact H0].
Qed.

(** Field focus and the three stores use task_storage's existing QCP
    interfaces.  Once those stores have produced this image, map reassembly
    needs no new field-storage implementation or duplicate TCB ownership. *)
Lemma task_public_storage_merge_prepared_delete : forall sg tasks tid old,
  task_slot_storage_rep sg tid
    (tcb_prepare_delete_image (task_layout_image sg old)) **
  task_public_storage_without_task sg tasks tid |--
    task_public_storage sg (glob_task_set_usedtask tasks tid (task_prepare_delete old)).
Proof.
  intros; rewrite <- task_prepare_delete_layout_image_eq.
  apply task_public_storage_merge_updated_task.
Qed.

(** A retirement-phase index, NOT a new OS field and NOT the normal global
    invariant.  Every other live task still satisfies both directions of
    ready membership.  The indexed slots are absent from ready even if the
    source has already cleared their Stat/Dly to RDY/0.  A caller must tie
    this index to its actual deletion phase and saved instance; it cannot
    pick an arbitrary list to justify lost ready bits.  No stability across
    Restore or arbitrary ISR actions is asserted by this predicate. *)
Definition sched_ready_except (sg : StableGlobVars) (retiring : list TaskID)
  (tasks : Glob_TaskAbstractState) (s : SchedAbstractState) : Prop :=
  sched_ready_structure sg tasks s /\
  (forall tid t, tasks.(inUsedTaskStates) tid = Some t ->
    (In tid s.(readyList) <-> is_effectively_ready t.(stat) t.(dly) = true /\ ~ In tid retiring)).

Lemma sched_ready_except_nil_iff : forall sg tasks s,
  sched_ready_except sg [] tasks s <-> sched_ready_in_range sg tasks s.
Proof.
  intros sg tasks s; split.
  - intros [[Hmembers [Hsorted Hnd]] Hready]; split.
    + intros tid Hin; destruct (Hmembers tid Hin) as [t [Ht Hp]].
      exists t; split; [exact Ht|split; [exact Hp|]].
      exact (proj1 (proj1 (Hready tid t Ht) Hin)).
    + split; [exact Hsorted|split; [|exact Hnd]].
      intros tid t Ht He; apply (proj2 (Hready tid t Ht)); split; [exact He|simpl; tauto].
  - intro Hvalid; split; [apply sched_ready_in_range_implies_structure; exact Hvalid|].
    destruct Hvalid as [Hmembers [_ [Hcomplete _]]].
    intros tid t Ht; split.
    + intro Hin; destruct (Hmembers tid Hin) as [node [Hnode [_ He]]].
      assert (node = t) by congruence; subst node; split; [exact He|simpl; tauto].
    + intros [He _]; eapply Hcomplete; eassumption.
Qed.

Lemma sched_ready_except_remove_updated_task : forall sg retiring tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  sched_ready_except sg retiring tasks s ->
  sched_ready_except sg (tid :: retiring) (glob_task_set_usedtask tasks tid new)
    (sched_remove_ready_task s tid).
Proof.
  intros sg retiring tasks s tid old new Hold Hprio [Hstructure Hready]; split.
  - apply sched_remove_ready_preserves_structure.
    eapply sched_ready_structure_update_task; eassumption.
  - intros slot node Hnode; simpl in Hnode; cbn [sched_remove_ready_task sched_set_ready readyList].
    destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; split.
      * intro Hin; exfalso; exact (remove_Z_eqb_notin tid s.(readyList) Hin).
      * intros [_ Hnot]; exfalso; apply Hnot; left; reflexivity.
    + apply Z.eqb_neq in E; split.
      * intro Hin; destruct (proj1 (Hready slot node Hnode)
          (remove_Z_eqb_in tid slot s.(readyList) Hin)) as [He Hnot].
        split; [exact He|intros [Hsame|Hmember]; [congruence|exact (Hnot Hmember)]].
      * intros [He Hnot]; apply remove_Z_eqb_in_neq; [exact E|].
        apply (proj2 (Hready slot node Hnode)); split; [exact He|].
        intro Hin; apply Hnot; right; exact Hin.
Qed.

(** Once none of the excluded instances remains in the live map, the
    ordinary ready relation follows.  Reallocation at a listed slot needs
    a new phase/instance argument; address equality alone cannot reuse it. *)
Lemma sched_ready_except_recover : forall sg retiring tasks s,
  sched_ready_except sg retiring tasks s ->
  (forall tid, In tid retiring -> tasks.(inUsedTaskStates) tid = None) ->
  sched_ready_in_range sg tasks s.
Proof.
  intros sg retiring tasks s [Hstructure Hready] Hgone.
  apply sched_ready_except_nil_iff; split; [exact Hstructure|].
  intros tid t Ht; rewrite (Hready tid t Ht).
  assert (Hnot : ~ In tid retiring) by (intro Hin; pose proof (Hgone tid Hin); congruence).
  simpl; tauto.
Qed.

Lemma sched_ready_except_update_task : forall sg retiring tasks s tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  is_effectively_ready new.(stat) new.(dly) = is_effectively_ready old.(stat) old.(dly) ->
  sched_ready_except sg retiring tasks s ->
  sched_ready_except sg retiring (glob_task_set_usedtask tasks tid new) s.
Proof.
  intros sg retiring tasks s tid old new Hold Hprio Hr [Hstructure Hready]; split.
  - eapply sched_ready_structure_update_task; eassumption.
  - intros slot node Hnode; simpl in Hnode; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      rewrite Hr; exact (Hready tid old Hold).
    + exact (Hready slot node Hnode).
Qed.

(** A real wake of a different task may run during retirement.  The
    readiness premises connect the source's status-bit guard to the
    current single-wait phase; they are not guards in the raw operation. *)
Lemma sched_wake_by_status_preserves_ready_except :
  forall sg retiring tasks s tid old new bits,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  new.(curPrio) = old.(curPrio) -> ~ In tid retiring ->
  is_effectively_ready new.(stat) new.(dly) = negb (task_status_is_suspended bits) ->
  (is_effectively_ready old.(stat) old.(dly) = true ->
    is_effectively_ready new.(stat) new.(dly) = true) ->
  sched_ready_except sg retiring tasks s ->
  sched_ready_except sg retiring (glob_task_set_usedtask tasks tid new)
    (sched_wake_by_status sg tasks s tid bits).
Proof.
  intros sg retiring tasks s tid old new bits Htasks Hold Hprio Hnot Hr Hmonotone
    [Hstructure Hready].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hprios _]]]]]]]].
  split.
  - eapply sched_ready_structure_update_task; [exact Hold|exact Hprio|].
    eapply sched_wake_by_status_preserves_structure;
      [exact Hunique|exact Hold|eapply Hprios; exact Hold|exact Hstructure].
  - intros slot node Hnode; rewrite sched_wake_by_status_membership.
    simpl in Hnode; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      rewrite (Hready tid old Hold).
      destruct (task_status_is_suspended bits) eqn:Hsus; simpl in Hr.
      * rewrite Hr in Hmonotone |- *; intuition discriminate.
      * rewrite Hr; intuition.
    + apply Z.eqb_neq in E; rewrite (Hready slot node Hnode); intuition.
Qed.

(** This covers a single actual Tick cursor step, including a step on an
    excluded task.  All retiring instances have the zero delay established
    by their source preparation, so such a step is literally a no-op.
    Non-retiring tasks may expire and enter ready normally.  The raw Tick
    transformer also covers Multi; this ordinary-ready closure uses the
    no-Multi reserved-bit protocol explicitly. *)
Lemma tick_task_step_preserves_ready_except : forall sg retiring tid t s,
  task_in_range sg s.(TskState) ->
  sched_ready_except sg retiring s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_status_reserved_bits_clear false t.(stat) ->
  (forall slot node, In slot retiring ->
    s.(TskState).(inUsedTaskStates) slot = Some node -> node.(dly) = 0) ->
  sched_ready_except sg retiring
    (tick_task_step sg tid t s).(TskState)
    (tick_task_step sg tid t s).(SchedState).
Proof.
  intros sg retiring tid t s Htasks Hready Ht Hbits Hexcluded.
  unfold tick_task_step; destruct (Z.eqb t.(dly) 0) eqn:Hzero; [exact Hready|].
  assert (Hprio : (tick_task_update t).(curPrio) = t.(curPrio)).
  { unfold tick_task_update; rewrite Hzero; reflexivity. }
  assert (Hnot : ~ In tid retiring).
  { intro Hin; pose proof (Hexcluded tid t Hin Ht) as Hd; rewrite Hd in Hzero; discriminate. }
  destruct (Z.eqb (tick_task_update t).(dly) 0) eqn:Hexpired.
  - cbn [replace_TskS replace_SchedS TskState SchedState].
    assert (Hd : t.(dly) = 1).
    { unfold tick_task_update in Hexpired; rewrite Hzero in Hexpired.
      cbn [dly] in Hexpired; apply Z.eqb_eq in Hexpired; lia. }
    eapply sched_wake_by_status_preserves_ready_except;
      [exact Htasks|exact Ht|exact Hprio|exact Hnot| | |exact Hready].
    + unfold tick_task_update; rewrite Hd.
      change (is_effectively_ready (task_status_after_timeout t.(stat)) 0 =
        negb (task_status_is_suspended (encode_task_status (task_status_after_timeout t.(stat))))).
      unfold is_effectively_ready.
      rewrite task_status_after_timeout_no_multi_pending_bits by exact Hbits.
      cbn [Z.eqb]; rewrite Bool.andb_true_r; reflexivity.
    + unfold is_effectively_ready; rewrite Hd.
      destruct (Z.eqb (task_non_suspension_bits t.(stat)) 0);
        rewrite ?Bool.andb_false_r; discriminate.
  - cbn [replace_TskS TskState SchedState].
    eapply sched_ready_except_update_task; [exact Ht|exact Hprio| |exact Hready].
    unfold is_effectively_ready; rewrite Hzero, Hexpired.
    destruct (Z.eqb (task_non_suspension_bits (tick_task_update t).(stat)) 0);
      destruct (Z.eqb (task_non_suspension_bits t.(stat)) 0);
      rewrite ?Bool.andb_false_r; reflexivity.
Qed.

Lemma task_prepare_delete_ready_phase : forall sg tasks s tid old,
  tasks.(inUsedTaskStates) tid = Some old -> sched_ready_in_range sg tasks s ->
  sched_ready_except sg [tid] (glob_task_set_usedtask tasks tid (task_prepare_delete old))
    (sched_remove_ready_task s tid).
Proof.
  intros; eapply sched_ready_except_remove_updated_task;
    [exact H|reflexivity|apply sched_ready_except_nil_iff; exact H0].
Qed.

(** Source writes to the two surviving neighbors, then the live-map
    interpretation removes the target slot.  A source binding must supply
    the actual neighbor cells (OSTaskDel always dereferences Next); this
    total value transformer does not add a NULL-neighbor success branch. *)
Definition task_unlink_used_map (used : TaskID -> option TaskAbstractState)
  (tid : TaskID) (node : TaskAbstractState) : TaskID -> option TaskAbstractState :=
  fun slot => if Z.eq_dec slot tid then None else
    match used slot with
    | None => None
    | Some t => Some (task_set_links t
        (match node.(prevTCB) with
         | Some previous => if Z.eq_dec slot previous then node.(nextTCB) else t.(nextTCB)
         | None => t.(nextTCB)
         end)
        (match node.(nextTCB) with
         | Some next => if Z.eq_dec slot next then node.(prevTCB) else t.(prevTCB)
         | None => t.(prevTCB)
         end))
    end.

Lemma task_unlink_used_map_observation : forall (A : Type) (observe : TaskAbstractState -> A)
  used tid node slot,
  (forall t next previous, observe (task_set_links t next previous) = observe t) ->
  option_map observe (task_unlink_used_map used tid node slot) =
    if Z.eq_dec slot tid then None else option_map observe (used slot).
Proof.
  intros A observe used tid node slot Hframe; unfold task_unlink_used_map.
  destruct (Z.eq_dec slot tid); [reflexivity|].
  destruct (used slot); simpl; [rewrite Hframe|]; reflexivity.
Qed.

Lemma task_unlink_used_map_live_iff : forall used tid node slot,
  (exists t, task_unlink_used_map used tid node slot = Some t) <->
    slot <> tid /\ exists t, used slot = Some t.
Proof.
  intros; unfold task_unlink_used_map; destruct (Z.eq_dec slot tid) as [Heq|Hne].
  - split; [intros [t H]; discriminate|tauto].
  - destruct (used slot) as [t|].
    + split; [intros _; split; [exact Hne|eexists; reflexivity]|intros _; eexists; reflexivity].
    + split; [intros [t H]; discriminate|intros [_ [t H]]; discriminate].
Qed.

Lemma task_unlink_used_map_preserves_other_fields : forall used tid node slot old,
  slot <> tid -> used slot = Some old -> exists new,
    task_unlink_used_map used tid node slot = Some new /\
    task_set_links new None None = task_set_links old None None.
Proof.
  intros used tid node slot old Hne Hold.
  pose proof (task_unlink_used_map_observation TaskAbstractState
    (fun t => task_set_links t None None) used tid node slot (fun _ _ _ => eq_refl)) as Hobs.
  destruct (Z.eq_dec slot tid); [contradiction|].
  rewrite Hold in Hobs.
  destruct (task_unlink_used_map used tid node slot) as [new|] eqn:Hnew; [|discriminate].
  exists new; split; [reflexivity|].
  exact (f_equal (fun value : option TaskAbstractState =>
    match value with Some t => t | None => old end) Hobs).
Qed.

Lemma task_unlink_used_map_lookup_origin : forall used tid node slot new,
  task_unlink_used_map used tid node slot = Some new ->
  slot <> tid /\ exists old, used slot = Some old /\
    task_set_links new None None = task_set_links old None None.
Proof.
  intros used tid node slot new Hnew.
  destruct (proj1 (task_unlink_used_map_live_iff used tid node slot)
    (ex_intro _ new Hnew)) as [Hne [old Hold]].
  destruct (task_unlink_used_map_preserves_other_fields used tid node slot old Hne Hold)
    as [after [Hafter Hfields]].
  rewrite Hnew in Hafter; injection Hafter as Hafter; subst after.
  split; [exact Hne|exists old; split; assumption].
Qed.

Definition task_recycle_image (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (node : TaskAbstractState) (default_name : addr) : TCBLayoutImage :=
  let linked := tcb_recycle_image sg (hd_error tasks.(unUsedTaskStates))
    (task_layout_image sg node) in
  if sg.(osKernelConfig).(cfgTaskNames)
  then tcb_layout_write linked (TCBCommonField TCBTaskName) (Some default_name)
  else linked.

(** Logical endpoint of OSTaskDel's post-hook unlink/recycle suffix.  The
    saved [priority] is the table index actually cleared; other aliases are
    NOT silently erased.  [node] is the post-hook image, not an assumed
    pre-Restore snapshot.  default_name is the source's "?" address, whose
    read-only storage remains a separate resource.

    The actual count is an INT8U.  Current/high caches, the caller's saved
    invocation entries and all pending creation reservations are outside
    this Task update.  Removing a live origin does not claim that the source
    has already switched contexts, stopped executing or returned. *)
Definition task_recycle (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (tid : TaskID) (priority : Priority) (node : TaskAbstractState) (default_name : addr)
  : Glob_TaskAbstractState :=
  let life := tasks.(taskLifecycle) in
  {| inUsedTaskStates := task_unlink_used_map tasks.(inUsedTaskStates) tid node;
     unUsedTaskStates := tid :: tasks.(unUsedTaskStates);
     tcbListHead := match node.(prevTCB) with None => node.(nextTCB) | Some _ => tasks.(tcbListHead) end;
     prioTbl := fun p => if Z.eq_dec p priority then PTFree else tasks.(prioTbl) p;
     taskCount := (tasks.(taskCount) - 1) mod 256;
     taskRegNextID := tasks.(taskRegNextID);
     parkedTaskStacks := tasks.(parkedTaskStacks);
     taskLifecycle :=
       {| taskFreeStorage := fun slot => if Z.eq_dec slot tid
            then Some (task_recycle_image sg tasks node default_name) else life.(taskFreeStorage) slot;
          taskReservations := life.(taskReservations);
          taskActiveOrder := remove_Z_eqb tid life.(taskActiveOrder);
          taskNextGeneration := life.(taskNextGeneration);
          taskInvocations := life.(taskInvocations);
          taskRetiredInvocations := life.(taskRetiredInvocations);
          taskNextInvocation := life.(taskNextInvocation);
          taskPublications := life.(taskPublications) |} |}.

Lemma task_recycle_slot_fields : forall sg tasks tid priority node name,
  let post := task_recycle sg tasks tid priority node name in
  post.(inUsedTaskStates) tid = None /\
  post.(unUsedTaskStates) = tid :: tasks.(unUsedTaskStates) /\
  post.(prioTbl) priority = PTFree /\
  post.(taskLifecycle).(taskFreeStorage) tid = Some (task_recycle_image sg tasks node name).
Proof.
  intros; cbn zeta; unfold task_recycle; simpl; unfold task_unlink_used_map.
  destruct (Z.eq_dec tid tid); [|contradiction].
  destruct (Z.eq_dec priority priority); [repeat split; reflexivity|contradiction].
Qed.

Lemma task_recycle_other_priority_frame : forall sg tasks tid priority node name p,
  p <> priority ->
  (task_recycle sg tasks tid priority node name).(prioTbl) p = tasks.(prioTbl) p.
Proof. intros; simpl; destruct (Z.eq_dec p priority); congruence. Qed.

Lemma task_recycle_preserves_pool_partition : forall sg tasks tid priority node name old,
  task_pool_partition sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  task_pool_partition sg (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name old
    [Hdomain [Hused [Hprivate [Hnd [Hstorage Hunique]]]]] Hold.
  destruct (Hused tid old Hold) as [Hnotfree Hnotprivate].
  assert (Hslot : task_slot_in_range sg tid).
  { apply Hdomain; left; exists old; exact Hold. }
  assert (Hlive : forall slot,
    (exists t, (task_recycle sg tasks tid priority node name).(inUsedTaskStates) slot = Some t) <->
    slot <> tid /\ exists t, tasks.(inUsedTaskStates) slot = Some t).
  { intro slot; apply task_unlink_used_map_live_iff. }
  split.
  - intro slot; rewrite Hlive; change (task_slot_in_range sg slot <->
      (slot <> tid /\ exists t, tasks.(inUsedTaskStates) slot = Some t) \/
      In slot (tid :: tasks.(unUsedTaskStates)) \/ task_private_slot tasks slot).
    split.
    + intro Hin; destruct (Z.eq_dec slot tid) as [->|Hne]; [right; left; left; reflexivity|].
      apply Hdomain in Hin; destruct Hin as [Hpresent|[Hfree|Hpriv]].
      * left; auto.
      * right; left; right; exact Hfree.
      * right; right; exact Hpriv.
    + intros [[_ Hpresent]|[[Heq|Hfree]|Hpriv]].
      * apply Hdomain; left; exact Hpresent.
      * subst slot; exact Hslot.
      * apply Hdomain; right; left; exact Hfree.
      * apply Hdomain; right; right; exact Hpriv.
  - split.
    + intros slot after Hafter.
      destruct (proj1 (Hlive slot) (ex_intro _ after Hafter)) as [Hne [before Hbefore]].
      destruct (Hused slot before Hbefore) as [Hfree Hpriv].
      split; [intros [Heq|Hin]; [congruence|exact (Hfree Hin)]|exact Hpriv].
    + split.
      * intros slot [Heq|Hin]; [subst slot; exact Hnotprivate|exact (Hprivate slot Hin)].
      * split; [constructor; assumption|split; [|exact Hunique]].
        intro slot; change (In slot (tid :: tasks.(unUsedTaskStates)) <-> exists image,
          (if Z.eq_dec slot tid then Some (task_recycle_image sg tasks node name)
           else tasks.(taskLifecycle).(taskFreeStorage) slot) = Some image).
        destruct (Z.eq_dec slot tid) as [->|Hne].
        -- split; [intros _; eexists; reflexivity|intros _; left; reflexivity].
        -- rewrite <- Hstorage; simpl; split; [intros [Heq|Hin]; [congruence|exact Hin]|auto].
Qed.

Lemma task_recycle_invalidates_origin : forall sg tasks tid priority node name generation,
  ~ task_invocation_origin_live (task_recycle sg tasks tid priority node name)
      (RunningInvocation tid generation).
Proof.
  intros sg tasks tid priority node name generation [t [Ht _]].
  rewrite (proj1 (task_recycle_slot_fields sg tasks tid priority node name)) in Ht; discriminate.
Qed.

Lemma task_recycle_other_invocation_active : forall sg tasks tid priority node name invocation origin,
  (forall generation, origin <> RunningInvocation tid generation) ->
  task_invocation_active tasks invocation origin ->
  task_invocation_active (task_recycle sg tasks tid priority node name) invocation origin.
Proof.
  intros sg tasks tid priority node name invocation origin Hother [Hinv [Hretired Hlive]].
  split; [exact Hinv|split; [exact Hretired|]].
  destruct origin as [|slot generation]; [exact I|].
  assert (Hne : slot <> tid) by (intro E; subst slot; apply (Hother generation); reflexivity).
  destruct Hlive as [t [Ht Hg]].
  unfold task_invocation_origin_live; simpl; unfold task_unlink_used_map.
  destruct (Z.eq_dec slot tid); [contradiction|rewrite Ht].
  eexists; split; [reflexivity|exact Hg].
Qed.

Lemma task_recycle_count_eq : forall sg tasks tid priority node name,
  0 < tasks.(taskCount) <= 255 ->
  (task_recycle sg tasks tid priority node name).(taskCount) = tasks.(taskCount) - 1.
Proof. intros; simpl; apply Z.mod_small; lia. Qed.

Lemma task_recycle_image_frame : forall sg tasks node name field,
  field <> TCBCommonField TCBNext -> field <> TCBCommonField TCBTaskName ->
  task_recycle_image sg tasks node name field = task_layout_image sg node field.
Proof.
  intros sg tasks node name [field| | | | | | |] Hnext Hname;
    unfold task_recycle_image, tcb_recycle_image;
    destruct sg.(osKernelConfig).(cfgTaskNames); try destruct field;
    try reflexivity; contradiction.
Qed.

Lemma task_recycle_free_storage_merge : forall sg tasks tid priority node name,
  ~ In tid tasks.(unUsedTaskStates) ->
  task_slot_storage_rep sg tid (task_recycle_image sg tasks node name) **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) |--
  task_free_storage_rep sg
    (task_recycle sg tasks tid priority node name).(taskLifecycle).(taskFreeStorage)
    (task_recycle sg tasks tid priority node name).(unUsedTaskStates).
Proof.
  intros sg tasks tid priority node name Hnotfree.
  assert (Hrest : task_free_storage_rep sg
      (task_recycle sg tasks tid priority node name).(taskLifecycle).(taskFreeStorage)
      tasks.(unUsedTaskStates) =
    task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates)).
  { apply task_free_storage_rep_ext; intros slot Hin; simpl.
    destruct (Z.eq_dec slot tid) as [->|Hne]; [contradiction|reflexivity]. }
  change (task_slot_storage_rep sg tid (task_recycle_image sg tasks node name) **
    task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) |--
    task_free_storage_rep sg
    (task_recycle sg tasks tid priority node name).(taskLifecycle).(taskFreeStorage)
    (tid :: tasks.(unUsedTaskStates))).
  rewrite task_free_storage_open_head, Hrest.
  Exists (task_recycle_image sg tasks node name).
  entailer!; simpl; destruct (Z.eq_dec tid tid); congruence.
Qed.

(** Once the source has unlinked the still-live target, ordinary readiness
    is restored from the retirement phase.  This does not supply the separate
    active-list, alias/owner, Event/Flag, stack, or platform obligations. *)
Lemma task_recycle_restores_ready : forall sg tasks s tid priority node name,
  tasks.(inUsedTaskStates) tid = Some node -> sched_ready_except sg [tid] tasks s ->
  sched_ready_in_range sg (task_recycle sg tasks tid priority node name) s.
Proof.
  intros sg tasks s tid priority node name Hold [[Hmembers [Hsorted Hnd]] Hready].
  assert (Hnot : ~ In tid s.(readyList)).
  { intro Hin; destruct (proj1 (Hready tid node Hold) Hin) as [_ Hnot].
    apply Hnot; left; reflexivity. }
  assert (Hothers : forall slot before, slot <> tid -> tasks.(inUsedTaskStates) slot = Some before ->
    exists after, (task_recycle sg tasks tid priority node name).(inUsedTaskStates) slot = Some after /\
      after.(curPrio) = before.(curPrio) /\ after.(stat) = before.(stat) /\ after.(dly) = before.(dly)).
  { intros slot before Hne Hbefore; simpl; unfold task_unlink_used_map.
    destruct (Z.eq_dec slot tid); [contradiction|rewrite Hbefore].
    eexists; repeat split; reflexivity. }
  split.
  - intros slot Hin; destruct (Hmembers slot Hin) as [before [Hbefore Hp]].
    assert (Hne : slot <> tid) by (intro E; subst slot; contradiction).
    destruct (Hothers slot before Hne Hbefore) as [after [Hafter [Hprio [Hstat Hdly]]]].
    exists after; split; [exact Hafter|split; [rewrite Hprio; exact Hp|]].
    rewrite Hstat, Hdly; exact (proj1 (proj1 (Hready slot before Hbefore) Hin)).
  - split.
    + eapply strictly_sorted_by_key_eq_on; [|exact Hsorted].
      intros slot Hin; destruct (Hmembers slot Hin) as [before [Hbefore _]].
      assert (Hne : slot <> tid) by (intro E; subst slot; contradiction).
      destruct (Hothers slot before Hne Hbefore) as [after [Hafter [Hprio _]]].
      unfold sched_task_key; rewrite Hbefore, Hafter; symmetry; exact Hprio.
    + split; [|exact Hnd].
      intros slot after Hafter He.
      destruct (proj1 (task_unlink_used_map_live_iff tasks.(inUsedTaskStates) tid node slot)
        (ex_intro _ after Hafter)) as [Hne [before Hbefore]].
      destruct (Hothers slot before Hne Hbefore) as [same [Hsame [Hprio [Hstat Hdly]]]].
      assert (same = after) by congruence; subst same.
      apply (proj2 (Hready slot before Hbefore)); split.
      * rewrite Hstat, Hdly in He; exact He.
      * intros [Heq|Hnil]; [congruence|contradiction].
Qed.

Lemma task_active_links_neighbors : forall ids used previous tid node,
  task_active_links used previous ids -> In tid ids -> used tid = Some node ->
  (node.(prevTCB) = previous \/ exists p, node.(prevTCB) = Some p /\ In p ids) /\
  (node.(nextTCB) = None \/ exists next, node.(nextTCB) = Some next /\ In next ids).
Proof.
  intro ids; induction ids as [|head rest IH]; intros used previous tid node Hlinks Hin Hnode;
    [contradiction|].
  destruct Hlinks as [first [Hfirst [_ [Hprev [Hnext Htail]]]]].
  destruct Hin as [->|Hin].
  - assert (first = node) by congruence; subst first; split; [left; exact Hprev|].
    destruct rest as [|next tail]; simpl in Hnext; [left; exact Hnext|].
    right; exists next; split; [exact Hnext|right; left; reflexivity].
  - destruct (IH used (Some head) tid node Htail Hin Hnode) as [Hpre Hnxt]; split.
    + right; destruct Hpre as [Hpre|[p [Hpre Hp]]].
      * exists head; split; [exact Hpre|left; reflexivity].
      * exists p; split; [exact Hpre|right; exact Hp].
    + destruct Hnxt as [Hnxt|[next [Hnxt Hn]]]; [left; exact Hnxt|].
      right; exists next; split; [exact Hnxt|right; exact Hn].
Qed.

(** A pure list-link consequence of exactly the two neighbor writes.
    The external predecessor is outside this segment.  Physical focus and
    reassembly still use the existing QCP map/field interfaces. *)
Lemma task_active_links_unlink : forall ids used tid node previous,
  NoDup ids -> (forall p, previous = Some p -> ~ In p ids) ->
  task_active_links used previous ids -> In tid ids -> used tid = Some node ->
  task_active_links (task_unlink_used_map used tid node) previous (remove_Z_eqb tid ids).
Proof.
  intro ids; induction ids as [|head rest IH]; intros used tid node previous Hnd Houtside Hlinks Hin Hnode;
    [contradiction|].
  apply NoDup_cons_iff in Hnd; destruct Hnd as [Hheadnot Hrestnd].
  destruct Hlinks as [first [Hfirst [Hid [Hprev [Hnext Htail]]]]].
  destruct (Z.eq_dec head tid) as [->|Hheadne].
  - assert (first = node) by congruence; subst first.
    rewrite remove_Z_eqb_x_cons_x, remove_Z_eqb_notin_eq by exact Hheadnot.
    destruct rest as [|next tail]; [exact I|].
    apply NoDup_cons_iff in Hrestnd; destruct Hrestnd as [Hnextnot Htailnd].
    destruct Htail as [successor [Hsuccessor [Hsid [Hsprev [Hsnext Hstail]]]]].
    simpl in Hnext.
    assert (Hnextne : next <> tid) by (intro E; apply Hheadnot; left; exact E).
    assert (HwrittenNext :
      (match node.(prevTCB) with
       | Some p => if Z.eq_dec next p then node.(nextTCB) else successor.(nextTCB)
       | None => successor.(nextTCB) end) = successor.(nextTCB)).
    { rewrite Hprev; destruct previous as [p|]; [|reflexivity].
      destruct (Z.eq_dec next p) as [->|Hne]; [|reflexivity].
      exfalso; apply (Houtside p eq_refl); right; left; reflexivity. }
    assert (HwrittenPrev :
      (match node.(nextTCB) with
       | Some p => if Z.eq_dec next p then node.(prevTCB) else successor.(prevTCB)
       | None => successor.(prevTCB) end) = previous).
    { rewrite Hnext; destruct (Z.eq_dec next next); [exact Hprev|contradiction]. }
    exists (task_set_links successor successor.(nextTCB) previous); split.
    + unfold task_unlink_used_map; destruct (Z.eq_dec next tid); [contradiction|].
      rewrite Hsuccessor, HwrittenNext, HwrittenPrev; reflexivity.
    + split; [exact Hsid|split; [reflexivity|split; [exact Hsnext|]]].
      eapply task_active_links_ext; [|exact Hstail].
      intros slot Hslot; unfold task_unlink_used_map.
      destruct (Z.eq_dec slot tid) as [->|Hne].
      * exfalso; apply Hheadnot; right; exact Hslot.
      * destruct (used slot) as [t|]; [|reflexivity].
        rewrite Hprev, Hnext.
        destruct (Z.eq_dec slot next) as [->|Hn]; [contradiction|].
        destruct previous as [p|].
        -- destruct (Z.eq_dec slot p) as [->|Hp]; [|destruct t; reflexivity].
           exfalso; apply (Houtside p eq_refl); right; right; exact Hslot.
        -- destruct t; reflexivity.
  - assert (Hintail : In tid rest) by (destruct Hin as [E|Hin]; [congruence|exact Hin]).
    rewrite remove_Z_eqb_ne_cons by (apply Z.eqb_neq; exact Hheadne).
    assert (HwrittenPrev :
      (match node.(nextTCB) with
       | Some p => if Z.eq_dec head p then node.(prevTCB) else first.(prevTCB)
       | None => first.(prevTCB) end) = previous).
    { pose proof (proj2 (task_active_links_neighbors rest used (Some head) tid node
        Htail Hintail Hnode)) as Hrange.
      destruct node.(nextTCB) as [p|] eqn:E; [|exact Hprev].
      destruct (Z.eq_dec head p) as [->|Hne]; [|exact Hprev].
      destruct Hrange as [Hnone|[q [Heq Hq]]]; [discriminate|].
      injection Heq as Heq; subst q; contradiction. }
    assert (HwrittenNext :
      (match node.(prevTCB) with
       | Some p => if Z.eq_dec head p then node.(nextTCB) else first.(nextTCB)
       | None => first.(nextTCB) end) = hd_error (remove_Z_eqb tid rest)).
    { destruct rest as [|next tail]; [contradiction|].
      destruct Htail as [successor [Hsuccessor [_ [Hsprev [Hsnext Hstail]]]]].
      apply NoDup_cons_iff in Hrestnd; destruct Hrestnd as [Hnextnot Htailnd].
      destruct (Z.eq_dec next tid) as [->|Hnextne].
      - assert (successor = node) by congruence; subst successor.
        rewrite Hsprev; destruct (Z.eq_dec head head); [|contradiction].
        rewrite remove_Z_eqb_x_cons_x, remove_Z_eqb_notin_eq by exact Hnextnot; exact Hsnext.
      - assert (Hintail' : In tid tail) by
          (destruct Hintail as [E|Hremaining]; [congruence|exact Hremaining]).
        pose proof (proj1 (task_active_links_neighbors tail used (Some next) tid node
          Hstail Hintail' Hnode)) as Hrange.
        assert (Hnothead : node.(prevTCB) <> Some head).
        { intro E; rewrite E in Hrange; destruct Hrange as [Heq|[p [Heq Hp]]].
          - injection Heq as Heq; subst next; apply Hheadnot; left; reflexivity.
          - injection Heq as Heq; subst p; apply Hheadnot; right; exact Hp. }
        rewrite remove_Z_eqb_ne_cons by (apply Z.eqb_neq; exact Hnextne); simpl.
        destruct node.(prevTCB) as [p|] eqn:E; [|exact Hnext].
        destruct (Z.eq_dec head p) as [->|Hne]; [contradiction|exact Hnext]. }
    exists (task_set_links first (hd_error (remove_Z_eqb tid rest)) previous); split.
    + unfold task_unlink_used_map; destruct (Z.eq_dec head tid); [contradiction|].
      rewrite Hfirst, HwrittenNext, HwrittenPrev; reflexivity.
    + split; [exact Hid|split; [reflexivity|split; [reflexivity|]]].
      apply IH; [exact Hrestnd| |exact Htail|exact Hintail|exact Hnode].
      intros p Heq; injection Heq as Heq; subst p; exact Hheadnot.
Qed.

Lemma task_recycle_preserves_active_closure : forall sg tasks tid priority node name,
  task_active_closure tasks -> tasks.(inUsedTaskStates) tid = Some node ->
  tasks.(taskCount) <= 255 ->
  task_active_closure (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name [Hnd [Hhead [Hcount [Hcover Hlinks]]]] Hnode Hbound.
  unfold TaskID in Hcount.
  assert (Hin : In tid tasks.(taskLifecycle).(taskActiveOrder)) by (apply Hcover; eauto).
  pose proof (Permutation_length
    (remove_Z_eqb_perm_cons tid _ Hin Hnd)) as Hlength.
  cbn [List.length] in Hlength.
  assert (Hcount_remove : tasks.(taskCount) =
    1 + Z.of_nat (List.length (remove_Z_eqb tid tasks.(taskLifecycle).(taskActiveOrder)))).
  { rewrite Hcount, Hlength, Nat2Z.inj_succ; lia. }
  split; [apply remove_Z_eqb_NoDup; exact Hnd|].
  split.
  - cbn [task_recycle tcbListHead taskLifecycle taskActiveOrder].
    rewrite Hhead.
    destruct tasks.(taskLifecycle).(taskActiveOrder) as [|head rest] eqn:Horder; [contradiction|].
    destruct Hlinks as [first [Hfirst [_ [Hprev [Hnext Htail]]]]].
    apply NoDup_cons_iff in Hnd; destruct Hnd as [Hnothead Hrestnd].
    destruct (Z.eq_dec head tid) as [->|Hne].
    + assert (first = node) by congruence; subst first.
      rewrite Hprev, remove_Z_eqb_x_cons_x, remove_Z_eqb_notin_eq by exact Hnothead.
      exact Hnext.
    + rewrite remove_Z_eqb_ne_cons by (apply Z.eqb_neq; exact Hne).
      assert (Hintail : In tid rest) by (destruct Hin as [E|Hremaining]; [congruence|exact Hremaining]).
      pose proof (proj1 (task_active_links_neighbors rest _ (Some head) tid node
        Htail Hintail Hnode)) as Hprevious.
      destruct node.(prevTCB) as [p|] eqn:E; [reflexivity|].
      destruct Hprevious as [Heq|[p [Heq _]]]; discriminate.
  - split.
    + assert (Hpositive : 0 < tasks.(taskCount) <= 255) by lia.
      change ((task_recycle sg tasks tid priority node name).(taskCount) =
        Z.of_nat (List.length (remove_Z_eqb tid tasks.(taskLifecycle).(taskActiveOrder)))).
      rewrite (task_recycle_count_eq sg tasks tid priority node name Hpositive).
      lia.
    + split.
      * intro slot; change (In slot (remove_Z_eqb tid tasks.(taskLifecycle).(taskActiveOrder)) <->
          exists t, task_unlink_used_map tasks.(inUsedTaskStates) tid node slot = Some t).
        rewrite task_unlink_used_map_live_iff, <- Hcover; split.
        -- intro Hmember; split.
           ++ intro E; subst slot; exact (remove_Z_eqb_notin tid _ Hmember).
           ++ eapply remove_Z_eqb_in; exact Hmember.
        -- intros [Hne Hmember]; apply remove_Z_eqb_in_neq; assumption.
      * apply task_active_links_unlink; try assumption.
        intros p Hnone; discriminate.
Qed.

Lemma task_recycle_preserves_free_links : forall sg tasks tid priority node name,
  ~ In tid tasks.(unUsedTaskStates) ->
  task_free_links sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) ->
  task_free_links sg
    (task_recycle sg tasks tid priority node name).(taskLifecycle).(taskFreeStorage)
    (task_recycle sg tasks tid priority node name).(unUsedTaskStates).
Proof.
  intros sg tasks tid priority node name Hnotfree Hlinks.
  exists (task_recycle_image sg tasks node name); split.
  - simpl; destruct (Z.eq_dec tid tid); congruence.
  - split.
    + unfold task_recycle_image, tcb_recycle_image.
      destruct sg.(osKernelConfig).(cfgTaskNames); reflexivity.
    + eapply task_free_links_storage_ext; [|exact Hlinks].
      intros slot Hin; simpl; destruct (Z.eq_dec slot tid) as [->|Hne];
        [contradiction|reflexivity].
Qed.

Lemma task_recycle_preserves_registration : forall sg tasks tid priority node name,
  task_current_prio_registered tasks -> tasks.(prioTbl) priority = PTTask tid ->
  task_current_prio_registered (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name Hreg Hselected slot after Hafter.
  change (task_unlink_used_map tasks.(inUsedTaskStates) tid node slot = Some after) in Hafter.
  pose proof (task_unlink_used_map_observation Z curPrio
    tasks.(inUsedTaskStates) tid node slot (fun _ _ _ => eq_refl)) as Hobs.
  rewrite Hafter in Hobs; simpl in Hobs.
  destruct (Z.eq_dec slot tid) as [->|Hne]; [discriminate|].
  destruct (tasks.(inUsedTaskStates) slot) as [before|] eqn:Hbefore; [|discriminate].
  simpl in Hobs; injection Hobs as Hprio.
  pose proof (Hreg slot before Hbefore) as Hregistered.
  simpl; rewrite Hprio; destruct (Z.eq_dec before.(curPrio) priority) as [E|E];
    [rewrite E, Hselected in Hregistered; congruence|exact Hregistered].
Qed.

(** The upper count bound is supplied by the actual UChar counter cell (or
    the selected pool bound), not by an extra source guard.  The selected
    table entry is the one read by OSTaskDel: aliases are not silently
    erased.  This is the Task owner's invariant, not global Mutex/Event
    alias closure, a hook contract, or a proof of the Restore window. *)
Lemma task_recycle_preserves_in_range : forall sg tasks tid priority node name,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some node ->
  tasks.(prioTbl) priority = PTTask tid -> tasks.(taskCount) <= 255 ->
  task_in_range sg (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name
    [Hpool [Hactive [Hlinks [Hres [Hgen [Hreg [Hunique [Hprio [Hreuse Hallocator]]]]]]]]]
    Hnode Hselected Hbound.
  assert (Hnotfree : ~ In tid tasks.(unUsedTaskStates)).
  { destruct Hpool as [_ [Hdisjoint _]]; exact (proj1 (Hdisjoint tid node Hnode)). }
  assert (Hregpost : task_current_prio_registered (task_recycle sg tasks tid priority node name))
    by (apply task_recycle_preserves_registration; assumption).
  split; [eapply task_recycle_preserves_pool_partition; eassumption|].
  split; [apply task_recycle_preserves_active_closure; assumption|].
  split; [apply task_recycle_preserves_free_links; assumption|].
  split.
  - destruct Hres as [Hbinding Hresunique]; split.
    + intros p entry Hentry; simpl in Hentry |- *.
      destruct (Hbinding p entry Hentry) as [Hp [Hreserved Hinv]].
      split; [exact Hp|split; [|exact Hinv]].
      destruct (Z.eq_dec p priority) as [->|Hne]; [congruence|exact Hreserved].
    + exact Hresunique.
  - split.
    + destruct Hgen as [Hlive [Hprivate [Hinv [Hhistory Hpublications]]]].
      split; [|split; [exact Hprivate|split; [exact Hinv|split; assumption]]].
      intros slot after Hafter.
      change (task_unlink_used_map tasks.(inUsedTaskStates) tid node slot = Some after) in Hafter.
      pose proof (task_unlink_used_map_observation nat taskGeneration
        tasks.(inUsedTaskStates) tid node slot (fun _ _ _ => eq_refl)) as Hobs.
      rewrite Hafter in Hobs; simpl in Hobs |- *.
      destruct (Z.eq_dec slot tid); [discriminate|].
      destruct (tasks.(inUsedTaskStates) slot) as [before|] eqn:Hbefore; [|discriminate].
      simpl in Hobs; injection Hobs as Hg; rewrite Hg; eapply Hlive; exact Hbefore.
    + split; [exact Hregpost|].
      split; [apply task_registration_implies_priority_unique; exact Hregpost|].
      split.
      * intros slot after Hafter.
        change (task_unlink_used_map tasks.(inUsedTaskStates) tid node slot = Some after) in Hafter.
        pose proof (task_unlink_used_map_observation Z curPrio
          tasks.(inUsedTaskStates) tid node slot (fun _ _ _ => eq_refl)) as Hobs.
        rewrite Hafter in Hobs; simpl in Hobs.
        destruct (Z.eq_dec slot tid); [discriminate|].
        destruct (tasks.(inUsedTaskStates) slot) as [before|] eqn:Hbefore; [|discriminate].
        simpl in Hobs; injection Hobs as Hp; rewrite Hp; eapply Hprio; exact Hbefore.
      * split; [|exact Hallocator].
        intros slot image Himage; simpl in Himage.
        destruct (Z.eq_dec slot tid) as [->|Hne]; [|eapply Hreuse; exact Himage].
        injection Himage as E; rewrite <- E.
        rewrite task_recycle_image_frame by discriminate.
        exists node.(tcbFlagsRdy); reflexivity.
Qed.

Lemma task_active_links_non_last_successor : forall prefix last used previous tid node,
  task_active_links used previous (prefix ++ [last]) ->
  In tid prefix -> used tid = Some node ->
  exists next successor, node.(nextTCB) = Some next /\ used next = Some successor.
Proof.
  intro prefix; induction prefix as [|head rest IH];
    intros last used previous tid node Hlinks Hin Hnode; [contradiction|].
  destruct Hlinks as [first [Hfirst [_ [_ [Hnext Htail]]]]].
  destruct Hin as [->|Hin].
  - assert (first = node) by congruence; subst first.
    destruct rest as [|next tail]; simpl in Hnext.
    + destruct Htail as [successor [Hsuccessor _]]; exists last, successor; auto.
    + destruct Htail as [successor [Hsuccessor _]]; exists next, successor; auto.
  - eapply IH; eassumption.
Qed.

(** The native source dereferences Next without a NULL test.  A live
    non-idle target has a real successor because idle terminates the active
    list.  Argument-priority tests alone do not establish this property:
    SELF and priority aliases must resolve to the actual selected task. *)
Lemma task_idle_tail_successor : forall sg tasks tid node,
  task_active_closure tasks -> task_idle_tail sg tasks ->
  tasks.(inUsedTaskStates) tid = Some node -> node.(curPrio) <> sg.(osLowestPrio) ->
  exists next successor, node.(nextTCB) = Some next /\
    tasks.(inUsedTaskStates) next = Some successor.
Proof.
  intros sg tasks tid node [_ [_ [_ [Hcover Hlinks]]]]
    [prefix [idle [idle_node [Horder [Hidle [Hprio _]]]]]] Hnode Hnonidle.
  assert (Hne : tid <> idle) by (intro E; subst tid; assert (node = idle_node) by congruence; congruence).
  assert (Hin : In tid prefix).
  { assert (Hin : In tid tasks.(taskLifecycle).(taskActiveOrder)) by (apply Hcover; eauto).
    rewrite Horder, in_app_iff in Hin; destruct Hin as [Hin|[E|Hnil]];
      [exact Hin|congruence|contradiction]. }
  rewrite Horder in Hlinks; eapply task_active_links_non_last_successor; eassumption.
Qed.

Lemma task_recycle_preserves_idle_tail : forall sg tasks tid priority node name,
  task_idle_tail sg tasks -> tasks.(inUsedTaskStates) tid = Some node ->
  node.(curPrio) <> sg.(osLowestPrio) ->
  task_idle_tail sg (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name
    [prefix [idle [idle_node [Horder [Hidle [Hprio Hprefix]]]]]] Hnode Hnonidle.
  assert (Hne : idle <> tid) by (intro E; subst idle; assert (node = idle_node) by congruence; congruence).
  assert (Hremove : remove_Z_eqb tid (prefix ++ [idle]) = remove_Z_eqb tid prefix ++ [idle]).
  { clear Horder Hprefix; induction prefix as [|head rest IH]; simpl.
    - rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity.
    - destruct (Z.eqb head tid); simpl; rewrite IH; reflexivity. }
  pose proof (task_unlink_used_map_observation Z curPrio
    tasks.(inUsedTaskStates) tid node idle (fun _ _ _ => eq_refl)) as Hobs.
  destruct (Z.eq_dec idle tid); [contradiction|].
  rewrite Hidle in Hobs.
  destruct (task_unlink_used_map tasks.(inUsedTaskStates) tid node idle)
    as [after|] eqn:Hafter; [|discriminate].
  simpl in Hobs; injection Hobs as Hafterprio.
  exists (remove_Z_eqb tid prefix), idle, after; split.
  - change (remove_Z_eqb tid tasks.(taskLifecycle).(taskActiveOrder) =
      remove_Z_eqb tid prefix ++ [idle]).
    rewrite Horder; exact Hremove.
  - split; [exact Hafter|split; [rewrite Hafterprio; exact Hprio|]].
    intros slot other Hin Hother.
    change (task_unlink_used_map tasks.(inUsedTaskStates) tid node slot = Some other) in Hother.
    pose proof (task_unlink_used_map_observation Z curPrio
      tasks.(inUsedTaskStates) tid node slot (fun _ _ _ => eq_refl)) as Hfields.
    rewrite Hother in Hfields; simpl in Hfields.
    destruct (Z.eq_dec slot tid); [discriminate|].
    destruct (tasks.(inUsedTaskStates) slot) as [before|] eqn:Hbefore; [|discriminate].
    simpl in Hfields; injection Hfields as Hp; rewrite Hp.
    eapply Hprefix; [eapply remove_Z_eqb_in; exact Hin|exact Hbefore].
Qed.

(** All cells below are the actual post-write resources.  In particular,
    the caller has already applied the neighbor stores to [remaining]; a
    pure link theorem cannot supply those cells.  QCP's missing-map rules
    remove the old ownership, and the same bytes enter free storage. *)
Lemma task_recycle_public_storage_merge : forall sg tasks tid priority node name remaining,
  ~ In tid tasks.(unUsedTaskStates) ->
  (forall slot, slot <> tid -> remaining slot =
    task_unlink_used_map tasks.(inUsedTaskStates) tid node slot) ->
  store_map_missing_i (used_task_rep sg) remaining tid **
  task_slot_storage_rep sg tid (task_recycle_image sg tasks node name) **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (Some tid) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg
    (match node.(prevTCB) with None => node.(nextTCB) | Some _ => tasks.(tcbListHead) end) **
  sg.(g_OSTaskCtr) # UChar |-> ((tasks.(taskCount) - 1) mod 256) **
  store_prio_tbl sg (fun p => if Z.eq_dec p priority then PTFree else tasks.(prioTbl) p) **
  task_reg_allocator_rep sg tasks |--
  task_public_storage sg (task_recycle sg tasks tid priority node name).
Proof.
  intros sg tasks tid priority node name remaining Hnotfree Hremaining.
  assert (Hremoved : task_unlink_used_map tasks.(inUsedTaskStates) tid node tid = None).
  { unfold task_unlink_used_map; destruct (Z.eq_dec tid tid); congruence. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv (used_task_rep sg)
    remaining (task_unlink_used_map tasks.(inUsedTaskStates) tid node) tid Hremaining)).
  sep_apply_l_atomic (store_map_missing_equiv_store_map (used_task_rep sg) _ tid Hremoved).
  sep_apply_l_atomic (task_recycle_free_storage_merge sg tasks tid priority node name Hnotfree).
  unfold task_public_storage, store_used_task_map; entailer!.
Qed.
