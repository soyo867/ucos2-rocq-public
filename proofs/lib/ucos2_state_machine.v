Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.cross_module_invariants.

Import ListNotations.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(**
  A small, reusable catalogue for the UC/OS-II state-machine boundary.

  [UCOS2_Verify_State] has eleven abstract projections, while the concrete
  heap has twelve physical owners.  Queue deliberately remains a separate
  owner even though it shares the Event abstract state.  This file does not
  add state fields or a second invariant; it packages the existing projection
  replacements and spatial split/merge laws so later module proofs can depend
  on one checked interface.
*)

Inductive UCOS2StateComponent : Type :=
| IntrComponent
| TaskComponent
| SchedComponent
| EventComponent
| TickComponent
| FlagComponent
| MemoryComponent
| TimerComponent
| StatisticsComponent
| ControlComponent
| NameComponent.

Definition ucos2_state_components : list UCOS2StateComponent :=
  [IntrComponent; TaskComponent; SchedComponent; EventComponent;
   TickComponent; FlagComponent; MemoryComponent; TimerComponent;
   StatisticsComponent; ControlComponent; NameComponent].

Lemma ucos2_state_components_length :
  length ucos2_state_components = 11%nat.
Proof. reflexivity. Qed.

Lemma ucos2_state_component_catalog_complete :
  forall component, In component ucos2_state_components.
Proof.
  intros component; destruct component; simpl; tauto.
Qed.

Lemma ucos2_state_component_catalog_nodup :
  NoDup ucos2_state_components.
Proof. repeat constructor; simpl; intuition congruence. Qed.

Definition ucos2_module_owners : list UCOS2Module :=
  [TaskModule; SchedModule; InterruptModule; EventModule; QueueModule;
   TickModule; FlagModule; MemoryModule; TimerModule; StatisticsModule;
   ControlModule; NamesModule].

Lemma ucos2_module_owners_length :
  length ucos2_module_owners = 12%nat.
Proof. reflexivity. Qed.

Lemma ucos2_module_owner_catalog_complete :
  forall owner, In owner ucos2_module_owners.
Proof.
  intros owner; destruct owner; simpl; tauto.
Qed.

Lemma ucos2_module_owner_catalog_nodup :
  NoDup ucos2_module_owners.
Proof. repeat constructor; simpl; intuition congruence. Qed.

(** The abstract projection owned by each physical owner is explicit.  Queue
    is intentionally mapped to [EventComponent]: a queue has a separate
    concrete QCB/ring owner, but its ECB-facing abstract fields live in the
    shared [EventState] projection.  Keeping this distinction in one mapping
    prevents later queue proofs from silently duplicating Event ownership. *)
Definition ucos2_owner_component (owner : UCOS2Module) : UCOS2StateComponent :=
  match owner with
  | TaskModule => TaskComponent
  | SchedModule => SchedComponent
  | InterruptModule => IntrComponent
  | EventModule => EventComponent
  | QueueModule => EventComponent
  | TickModule => TickComponent
  | FlagModule => FlagComponent
  | MemoryModule => MemoryComponent
  | TimerModule => TimerComponent
  | StatisticsModule => StatisticsComponent
  | ControlModule => ControlComponent
  | NamesModule => NameComponent
  end.

Lemma ucos2_owner_component_in_catalog : forall owner,
  In (ucos2_owner_component owner) ucos2_state_components.
Proof.
  intros owner; destruct owner; simpl; tauto.
Qed.

Lemma ucos2_queue_owner_shares_event_component :
  ucos2_owner_component QueueModule = EventComponent.
Proof. reflexivity. Qed.

Lemma ucos2_owner_component_is_unique_for_distinct_projections : forall owner,
  owner <> QueueModule ->
  owner <> EventModule ->
  ucos2_owner_component owner = EventComponent -> False.
Proof.
  intros owner Hqueue Hevent; destruct owner; simpl in *; congruence.
Qed.

(** The projection updates are total, restore the old state when fed its
    projection, and have last-write semantics.  The stronger frame and
    commutation laws remain the named lemmas in [ucos2_verify_state_def]. *)
Record UCOS2StateReplacementLaws : Prop := {
  intr_replace_put_back : forall s,
    replace_IntrS s.(IntrState) s = s;
  tick_replace_put_back : forall s,
    replace_TickS s.(TickState) s = s;
  task_replace_put_back : forall s,
    replace_TskS s.(TskState) s = s;
  sched_replace_put_back : forall s,
    replace_SchedS s.(SchedState) s = s;
  event_replace_put_back : forall s,
    replace_EventS s.(EventState) s = s;
  flag_replace_put_back : forall s,
    replace_FlagS s.(FlagState) s = s;
  memory_replace_put_back : forall s,
    replace_MemoryS s.(MemoryState) s = s;
  timer_replace_put_back : forall s,
    replace_TimerS s.(TimerState) s = s;
  statistics_replace_put_back : forall s,
    replace_StatsS s.(StatsState) s = s;
  control_replace_put_back : forall s,
    replace_ControlS s.(ControlState) s = s;
  name_replace_put_back : forall s,
    replace_NameS s.(NameState) s = s;

  intr_replace_last_write : forall a b s,
    replace_IntrS b (replace_IntrS a s) = replace_IntrS b s;
  tick_replace_last_write : forall a b s,
    replace_TickS b (replace_TickS a s) = replace_TickS b s;
  task_replace_last_write : forall a b s,
    replace_TskS b (replace_TskS a s) = replace_TskS b s;
  sched_replace_last_write : forall a b s,
    replace_SchedS b (replace_SchedS a s) = replace_SchedS b s;
  event_replace_last_write : forall a b s,
    replace_EventS b (replace_EventS a s) = replace_EventS b s;
  flag_replace_last_write : forall a b s,
    replace_FlagS b (replace_FlagS a s) = replace_FlagS b s;
  memory_replace_last_write : forall a b s,
    replace_MemoryS b (replace_MemoryS a s) = replace_MemoryS b s;
  timer_replace_last_write : forall a b s,
    replace_TimerS b (replace_TimerS a s) = replace_TimerS b s;
  statistics_replace_last_write : forall a b s,
    replace_StatsS b (replace_StatsS a s) = replace_StatsS b s;
  control_replace_last_write : forall a b s,
    replace_ControlS b (replace_ControlS a s) = replace_ControlS b s;
  name_replace_last_write : forall a b s,
    replace_NameS b (replace_NameS a s) = replace_NameS b s
}.

Definition ucos2_state_replacement_laws : UCOS2StateReplacementLaws.
Proof.
  refine {| intr_replace_put_back := replace_IntrS_put_back;
            tick_replace_put_back := replace_TickS_put_back;
            task_replace_put_back := replace_TskS_put_back;
            sched_replace_put_back := replace_SchedS_put_back;
            event_replace_put_back := replace_EventS_put_back;
            flag_replace_put_back := replace_FlagS_put_back;
            memory_replace_put_back := replace_MemoryS_put_back;
            timer_replace_put_back := replace_TimerS_put_back;
            statistics_replace_put_back := replace_StatsS_put_back;
            control_replace_put_back := replace_ControlS_put_back;
            name_replace_put_back := replace_NameS_put_back;
            intr_replace_last_write := replace_IntrS_last_write;
            tick_replace_last_write := replace_TickS_last_write;
            task_replace_last_write := replace_TskS_last_write;
            sched_replace_last_write := replace_SchedS_last_write;
            event_replace_last_write := replace_EventS_last_write;
            flag_replace_last_write := replace_FlagS_last_write;
            memory_replace_last_write := replace_MemoryS_last_write;
            timer_replace_last_write := replace_TimerS_last_write;
            statistics_replace_last_write := replace_StatsS_last_write;
            control_replace_last_write := replace_ControlS_last_write;
            name_replace_last_write := replace_NameS_last_write |}.
Defined.

(** The physical owner boundary and invariant boundary are exposed through
    the existing generic laws, rather than copied into another definition. *)
Record UCOS2StateMachineCoverage : Prop := {
  coverage_raw_split : forall sg s owner,
    UCOS2_raw_rep sg s --||--
      UCOS2_module_rep sg s owner ** UCOS2_raw_rep_missing_module sg s owner;
  coverage_inv_split : forall sg s owner,
    UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
      (UCOS2_module_rep sg s owner ** UCOS2_raw_rep_missing_module sg s owner);
  coverage_raw_merge : forall sg before after owner,
    (UCOS2_raw_rep_missing_module sg before owner |--
      UCOS2_raw_rep_missing_module sg after owner) ->
    UCOS2_module_rep sg after owner **
      UCOS2_raw_rep_missing_module sg before owner |--
      UCOS2_raw_rep sg after;
  coverage_inv_merge : forall sg before after owner,
    UCOS2_state_inv sg after ->
    (UCOS2_raw_rep_missing_module sg before owner |--
      UCOS2_raw_rep_missing_module sg after owner) ->
    UCOS2_module_rep sg after owner **
      UCOS2_raw_rep_missing_module sg before owner |--
      UCOS2_inv sg after
}.

Definition ucos2_state_machine_coverage : UCOS2StateMachineCoverage.
Proof.
  refine {| coverage_raw_split := UCOS2_raw_rep_split_module;
            coverage_inv_split := UCOS2_inv_split_module;
            coverage_raw_merge := UCOS2_raw_rep_merge_updated_module;
            coverage_inv_merge := UCOS2_inv_merge_updated_module |}.
Defined.

(** A transition is the smallest reusable state-machine interface needed by
    a module proof.  It does not invent a universal transition relation: the
    caller supplies the source-faithful [step] relation and proves validity
    and residual transport for that relation.  Thus an unmodelled operation
    cannot obtain a successor merely by instantiating a vacuous record. *)
Record UCOS2OwnerTransition (owner : UCOS2Module)
  (step : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) : Prop := {
  owner_transition_valid : forall sg before after,
    UCOS2_state_inv sg before -> step before after ->
    UCOS2_state_inv sg after;
  owner_transition_residual : forall sg before after,
    step before after ->
    UCOS2_raw_rep_missing_module sg before owner --||--
      UCOS2_raw_rep_missing_module sg after owner
}.

Lemma ucos2_owner_transition_composes : forall owner step sg before after,
  UCOS2OwnerTransition owner step ->
  UCOS2_state_inv sg before ->
  step before after ->
  UCOS2_module_rep sg after owner **
    UCOS2_raw_rep_missing_module sg before owner |-- UCOS2_inv sg after.
Proof.
  intros owner step sg before after Htransition Hbefore Hstep.
  destruct Htransition as [Hvalid Hresidual].
  apply (UCOS2_inv_merge_updated_module sg before after owner).
  - eapply Hvalid; eassumption.
  - exact (proj1 (Hresidual sg before after Hstep)).
Qed.

(** Arbitrary selections use the existing twelve-owner representation.
    Each physical owner occurs once, even if a client conceptually names
    Event and Queue through the same abstract projection.  A boolean
    selection also avoids duplicate ownership in a caller-supplied list. *)
Local Lemma sepcon_partition_by_bool : forall (P : Assertion) (selected : bool),
  P --||--
    (if selected then P else emp) ** (if negb selected then P else emp).
Proof. intros P []; cbn [negb]; split; entailer!. Qed.

Local Lemma sepcon_partition_combine : forall P P1 P2 Q Q1 Q2,
  P --||-- P1 ** P2 -> Q --||-- Q1 ** Q2 ->
  P ** Q --||-- (P1 ** Q1) ** (P2 ** Q2).
Proof.
  intros P P1 P2 Q Q1 Q2 HP HQ; rewrite HP, HQ; split; entailer!.
Qed.

Lemma UCOS2_raw_rep_split_selected : forall sg s selected,
  UCOS2_raw_rep sg s --||--
    UCOS2_selected_rep sg s selected **
    UCOS2_selected_rep sg s (fun owner => negb (selected owner)).
Proof.
  intros; rewrite UCOS2_raw_rep_all_modules_eq.
  unfold UCOS2_selected_rep; cbn beta iota zeta.
  repeat first [apply sepcon_partition_combine | apply sepcon_partition_by_bool].
Qed.

Lemma UCOS2_inv_split_selected : forall sg s selected,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (UCOS2_selected_rep sg s selected **
     UCOS2_selected_rep sg s (fun owner => negb (selected owner))).
Proof.
  intros; unfold UCOS2_inv; rewrite (UCOS2_raw_rep_split_selected sg s selected).
  split; reflexivity.
Qed.

Lemma UCOS2_selected_rep_mono : forall sg before after selected,
  (forall owner, selected owner = true ->
    UCOS2_module_rep sg before owner |-- UCOS2_module_rep sg after owner) ->
  UCOS2_selected_rep sg before selected |-- UCOS2_selected_rep sg after selected.
Proof.
  intros sg before after selected Hframe.
  assert (Howner : forall owner,
    (if selected owner then UCOS2_module_rep sg before owner else emp) |--
    (if selected owner then UCOS2_module_rep sg after owner else emp)).
  { intro owner; destruct (selected owner) eqn:Hselected;
      [apply Hframe; exact Hselected|reflexivity]. }
  unfold UCOS2_selected_rep; repeat apply derivable1_sepcon_mono; apply Howner.
Qed.

Lemma UCOS2_raw_rep_merge_updated_selected : forall sg before after selected,
  (UCOS2_selected_rep sg before (fun owner => negb (selected owner)) |--
   UCOS2_selected_rep sg after (fun owner => negb (selected owner))) ->
  UCOS2_selected_rep sg after selected **
    UCOS2_selected_rep sg before (fun owner => negb (selected owner)) |--
  UCOS2_raw_rep sg after.
Proof.
  intros sg before after selected Hframe.
  eapply derivable1_trans; [apply derivable1_sepcon_mono; [reflexivity|exact Hframe]|].
  apply (proj2 (UCOS2_raw_rep_split_selected sg after selected)).
Qed.

Lemma UCOS2_inv_merge_updated_selected : forall sg before after selected,
  UCOS2_state_inv sg after ->
  (UCOS2_selected_rep sg before (fun owner => negb (selected owner)) |--
   UCOS2_selected_rep sg after (fun owner => negb (selected owner))) ->
  UCOS2_selected_rep sg after selected **
    UCOS2_selected_rep sg before (fun owner => negb (selected owner)) |--
  UCOS2_inv sg after.
Proof.
  intros sg before after selected Hvalid Hframe; unfold UCOS2_inv.
  apply _derivable1_andp_intros; [entailer!|].
  apply UCOS2_raw_rep_merge_updated_selected; exact Hframe.
Qed.

(** This certificate is a theorem about a supplied source relation, not a
    guard that filters its successors by the desired invariant.  In the
    retained owners it requires transport of the actual heap predicates:
    unchanged abstract fields alone need not preserve a Task-indexed Event
    or ready bitmap.  Validity at the input may be used to prove that frame.
    These are stable segment boundaries. Individual C stores may still use
    the existing partial-initialization or transient-update assertions. *)
Record UCOS2SelectedTransition (sg : StableGlobVars)
  (selected : UCOS2Module -> bool)
  (step : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop) : Prop := {
  selected_transition_valid : forall before after,
    UCOS2_state_inv sg before -> step before after -> UCOS2_state_inv sg after;
  selected_transition_frame : forall before after,
    UCOS2_state_inv sg before -> step before after ->
    forall owner, selected owner = false ->
      UCOS2_module_rep sg before owner |-- UCOS2_module_rep sg after owner
}.

Lemma ucos2_selected_transition_composes : forall sg selected step before after,
  UCOS2SelectedTransition sg selected step ->
  UCOS2_state_inv sg before -> step before after ->
  UCOS2_selected_rep sg after selected **
    UCOS2_selected_rep sg before (fun owner => negb (selected owner)) |--
  UCOS2_inv sg after.
Proof.
  intros sg selected step before after [Hvalid Hframe] Hbefore Hstep.
  apply UCOS2_inv_merge_updated_selected; [eapply Hvalid; eassumption|].
  apply UCOS2_selected_rep_mono.
  intros owner Hkept; apply Bool.negb_true_iff in Hkept.
  exact (Hframe before after Hbefore Hstep owner Hkept).
Qed.

Lemma ucos2_selected_transition_sequence : forall sg first second step1 step2,
  UCOS2SelectedTransition sg first step1 ->
  UCOS2SelectedTransition sg second step2 ->
  UCOS2SelectedTransition sg (fun owner => orb (first owner) (second owner))
    (fun before after => exists middle, step1 before middle /\ step2 middle after).
Proof.
  intros sg first second step1 step2 [Hvalid1 Hframe1] [Hvalid2 Hframe2]; constructor.
  - intros before after Hbefore [middle [Hfirst Hsecond]].
    eapply Hvalid2; [eapply Hvalid1; eassumption|exact Hsecond].
  - intros before after Hbefore [middle [Hfirst Hsecond]] owner Hkept.
    apply Bool.orb_false_iff in Hkept; destruct Hkept as [Hkeep1 Hkeep2].
    eapply derivable1_trans; [exact (Hframe1 before middle Hbefore Hfirst owner Hkeep1)|].
    apply (Hframe2 middle after); [eapply Hvalid1; eassumption|exact Hsecond|exact Hkeep2].
Qed.

Definition task_sched_modules (owner : UCOS2Module) : bool :=
  match owner with TaskModule | SchedModule => true | _ => false end.

Definition task_sched_event_queue_modules (owner : UCOS2Module) : bool :=
  match owner with
  | TaskModule | SchedModule | EventModule | QueueModule => true
  | _ => false
  end.

Lemma task_sched_event_queue_module_frame : forall sg before tasks sched events owner,
  task_sched_event_queue_modules owner = false ->
  UCOS2_module_rep sg before owner =
    UCOS2_module_rep sg
      (replace_EventS events (replace_SchedS sched (replace_TskS tasks before))) owner.
Proof. intros; destruct owner; simpl in *; discriminate || reflexivity. Qed.

(** A concrete consumer: the existing Suspend state transformer changes
    TCB status and ready bits.  Event's predicate depends on the Task map,
    so its frame is proved from unchanged priorities, not assumed from
    equality of EventState.  The source lookup supplies the old TCB. *)
Lemma task_suspend_selected_transition : forall sg,
  UCOS2SelectedTransition sg task_sched_modules
    (fun before after => exists tid old,
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      after = task_suspend_state before tid old).
Proof.
  intro sg; constructor.
  - intros before after Hvalid [tid [old [Hold ->]]].
    apply UCOS2_task_suspend_preserves_validity; assumption.
  - intros before after Hvalid [tid [old [Hold ->]]] owner Hkept.
    destruct owner; simpl in Hkept; try discriminate; try reflexivity.
    unfold UCOS2_module_rep, task_suspend_state; cbn [replace_SchedS replace_TskS TskState EventState].
    rewrite (event_raw_rep_change_task_index sg before.(TskState)
      (glob_task_set_usedtask before.(TskState) tid (task_suspend old)) before.(EventState));
      [reflexivity|].
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity].
Qed.

Lemma task_suspend_selected_resources_merge : forall sg before tid old,
  UCOS2_state_inv sg before -> before.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_selected_rep sg (task_suspend_state before tid old) task_sched_modules **
    UCOS2_selected_rep sg before (fun owner => negb (task_sched_modules owner)) |--
  UCOS2_inv sg (task_suspend_state before tid old).
Proof.
  intros sg before tid old Hvalid Hold.
  eapply ucos2_selected_transition_composes.
  - apply task_suspend_selected_transition.
  - exact Hvalid.
  - exists tid, old; split; [exact Hold|reflexivity].
Qed.

Definition memory_modules (owner : UCOS2Module) : bool :=
  match owner with MemoryModule => true | _ => false end.

(** Successful Get transfers a block out of the shared free representation;
    Put consumes the matching allocated-block domain.  The actual block
    bytes/loan are still caller resources, to be supplied by the existing
    memory split/merge rules. These certificates do not manufacture them. *)
Lemma memory_get_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  UCOS2SelectedTransition sg memory_modules
    (fun before after => exists i loan memory,
      memory_get before.(MemoryState) i = Some (loan, memory) /\
      after = replace_MemoryS memory before).
Proof.
  intros sg Henabled; constructor.
  - intros before after Hvalid [i [loan [memory [Hget ->]]]].
    eapply UCOS2_memory_get_preserves_validity; eassumption.
  - intros before after Hvalid [i [loan [memory [Hget ->]]]] owner Hkept.
    destruct owner; simpl in Hkept; discriminate || reflexivity.
Qed.

Lemma memory_put_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  UCOS2SelectedTransition sg memory_modules
    (fun before after => exists i block partition loan memory,
      before.(MemoryState).(memPartitions) i = Some partition /\
      partition.(memAllocatedBlocks) block = Some loan /\
      memory_put before.(MemoryState) i block = Some memory /\
      after = replace_MemoryS memory before).
Proof.
  intros sg Henabled; constructor.
  - intros before after Hvalid (i & block & partition & loan & memory & Hpart & Hloan & Hput & ->).
    eapply UCOS2_memory_put_preserves_validity; eassumption.
  - intros before after Hvalid (i & block & partition & loan & memory & _ & _ & _ & ->) owner Hkept.
    destruct owner; simpl in Hkept; discriminate || reflexivity.
Qed.

Lemma task_resume_selected_transition : forall sg,
  UCOS2SelectedTransition sg task_sched_modules
    (fun before after => exists tid old,
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      task_is_suspended old.(stat) = true /\
      after = task_resume_state sg before tid old).
Proof.
  intro sg; constructor.
  - intros before after Hvalid (tid & old & Hold & Hsuspended & ->).
    eapply UCOS2_task_resume_preserves_validity; eassumption.
  - intros before after Hvalid (tid & old & Hold & Hsuspended & ->) owner Hkept.
    destruct owner; simpl in Hkept; try discriminate; try reflexivity.
    unfold UCOS2_module_rep, task_resume_state; cbn [replace_SchedS replace_TskS TskState EventState].
    rewrite (event_raw_rep_change_task_index sg before.(TskState)
      (glob_task_set_usedtask before.(TskState) tid (task_resume old)) before.(EventState));
      [reflexivity|].
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity].
Qed.

Definition task_sched_event_modules (owner : UCOS2Module) : bool :=
  match owner with TaskModule | SchedModule | EventModule => true | _ => false end.

(** These are the already modelled stable Pend/Wake endpoints. Pend
    includes its caller's status/delay stores and OS_EventTaskWait; Wake
    includes OS_EventTaskRemove. They are not specifications for each
    intermediate C store, nor whole API/scheduling/return relations.
    Queue bytes stay in the complement: their Event-indexed representation
    is transported by the existing Queue theorem, not duplicated or dropped. *)
Lemma event_pend_selected_transition : forall sg,
  UCOS2SelectedTransition sg task_sched_event_modules
    (fun before after => exists eid e tid old kind timeout,
      before.(EventState).(inUsedEventStates) eid = Some e /\
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      valid_task_prio sg old.(curPrio) /\
      old.(eventPtr) = None /\ old.(eventMultiWaitEvents) = nil /\
      old.(tcbFlagNode) = 0%Z /\ In tid before.(SchedState).(readyList) /\
      event_type_to_pend_type e.(eventType) = Some kind /\
      event_wait_resource_unavailable e /\
      (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX ->
        e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) /\
      after = event_pend_state sg before eid e tid old kind timeout).
Proof.
  intro sg; constructor.
  - intros before after Hvalid
      (eid & e & tid & old & kind & timeout & He & Hold & Hprio & Hptr & Hmulti &
       Hflag & Hready & Hkind & Hunavailable & Hnotowner & ->).
    eapply UCOS2_event_pend_preserves_validity; eassumption.
  - intros before after Hvalid
      (eid & e & tid & old & kind & timeout & He & Hold & Hprio & Hptr & Hmulti &
       Hflag & Hready & Hkind & Hunavailable & Hnotowner & ->) owner Hkept.
    destruct owner; simpl in Hkept; try discriminate; try reflexivity.
    cbn [UCOS2_module_rep event_pend_state event_wait_state
      replace_SchedS replace_EventS replace_TskS EventState].
    unfold event_insert_waiter.
    apply queue_set_event_wait_list_preserves_storage; exact He.
Qed.

Lemma event_wake_selected_transition : forall sg,
  UCOS2SelectedTransition sg task_sched_event_modules
    (fun before after => exists eid e tid old kind message result,
      before.(EventState).(inUsedEventStates) eid = Some e /\ In tid e.(waitList) /\
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      event_type_to_pend_type e.(eventType) = Some kind /\
      after = event_wake_state sg before eid e tid old kind message result).
Proof.
  intro sg; constructor.
  - intros before after Hvalid
      (eid & e & tid & old & kind & message & result & He & Hin & Hold & Hkind & ->).
    eapply UCOS2_event_wake_preserves_validity; eassumption.
  - intros before after Hvalid
      (eid & e & tid & old & kind & message & result & He & Hin & Hold & Hkind & ->)
      owner Hkept.
    destruct owner; simpl in Hkept; try discriminate; try reflexivity.
    cbn [UCOS2_module_rep event_wake_state replace_SchedS replace_EventS replace_TskS EventState].
    apply queue_set_event_wait_list_preserves_storage; exact He.
Qed.
