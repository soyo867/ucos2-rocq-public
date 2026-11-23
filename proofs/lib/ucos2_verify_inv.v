Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.ucos2_spatial.
Import UCOS2_C_Rules.
Import TaskStateDef.
Import EventStateDef.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 6 Task 6.3:UCOS2_verification_slice_inv 组合                                 *)
(* ================================================================== *)

Definition UCOS2_verification_slice_inv (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

(** The current invariant uses the configured source layout. The historical
    verification-slice invariant above is a separate, weaker interface, not
    an alternative proof of this invariant. Private TCBs are accounted for
    in the lifecycle partition, but their storage remains invocation-owned
    and is not duplicated in this shared public invariant. All concrete TCB
    and Event fields are projected directly from their abstract states.
    Registered parked stack fragments are owned separately from the TCBs.
    Executing and private creation stacks remain with their actual callers;
    a borrowed interval is owned by its typed consumer, not again here. *)
(** The ready relation is a proved source-phase assertion, not an omitted
    module or an unconstrained OtherInv.  Every physical owner, metadata
    bound and cross-module relation below remains fixed.  Instantiating
    this constructor does not supply a preservation theorem or authorize
    exposing a phase across Restore. *)
Definition UCOS2_state_inv_with_ready (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (ready : Prop) : Prop :=
  selected_kernel_profile sg /\
  task_in_range sg s.(TskState) /\
  (ready /\ sched_metadata_in_range sg s.(SchedState)) /\
  event_in_range sg s.(TskState) s.(EventState) /\
  cross_module_consistency sg s /\
  (s.(SchedState).(isRunning) = true -> task_idle_tail sg s.(TskState)) /\
  task_reserved_bits_clear sg s.(TskState) /\
  valid_flag_configuration sg s.(FlagState) /\
  valid_memory_configuration sg s.(MemoryState) /\
  valid_timer_configuration sg s.(TimerState) /\
  valid_statistics_configuration sg s.(StatsState) /\
  kernel_control_valid sg.(osKernelConfig) s.(ControlState) /\
  valid_name_resources s.(NameState) /\
  kernel_names_valid sg s /\
  parked_stacks_consistent s.(TskState) s.(TskState).(parkedTaskStacks) /\
  pending_mutex_consistency sg s.(TskState) s.(EventState).

Definition UCOS2_state_inv (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv_with_ready sg s
    (sched_ready_in_range sg s.(TskState) s.(SchedState)).

(** Full-features global invariant bridge.  The historical
    [UCOS2_state_inv] above intentionally remains tied to
    [selected_kernel_profile] (64-byte TCB, names-disabled ECB).  Full
    profile callers use this parallel constructor so an enabled
    [OSEventName] cell and the 92-byte TCB are accounted for by the same
    configured module representations, without weakening old proofs. *)
Definition UCOS2_full_state_inv_with_ready (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (ready : Prop) : Prop :=
  full_features_kernel_profile sg /\
  task_in_range sg s.(TskState) /\
  (ready /\ sched_metadata_in_range sg s.(SchedState)) /\
  event_registered_in_range sg s.(TskState) s.(EventState) /\
  cross_module_registration_consistency sg s /\
  (s.(SchedState).(isRunning) = true -> task_idle_tail sg s.(TskState)) /\
  task_reserved_bits_clear sg s.(TskState) /\
  valid_flag_configuration sg s.(FlagState) /\
  valid_memory_configuration sg s.(MemoryState) /\
  valid_timer_configuration sg s.(TimerState) /\
  valid_statistics_configuration sg s.(StatsState) /\
  kernel_control_valid sg.(osKernelConfig) s.(ControlState) /\
  valid_name_resources s.(NameState) /\
  kernel_names_valid sg s /\
  parked_stacks_consistent s.(TskState) s.(TskState).(parkedTaskStacks) /\
  pending_mutex_consistency sg s.(TskState) s.(EventState).

Definition UCOS2_full_state_inv (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Prop :=
  UCOS2_full_state_inv_with_ready sg s
    (sched_registered_ready_in_range sg s.(TskState) s.(SchedState)).

Lemma UCOS2_state_inv_pending_mutex : forall sg s,
  UCOS2_state_inv sg s -> pending_mutex_consistency sg s.(TskState) s.(EventState).
Proof. intros; unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto. Qed.

Lemma UCOS2_full_state_inv_pending_mutex : forall sg s,
  UCOS2_full_state_inv sg s -> pending_mutex_consistency sg s.(TskState) s.(EventState).
Proof. intros; unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready in H; tauto. Qed.

Lemma UCOS2_state_inv_names_valid : forall sg s,
  UCOS2_state_inv sg s -> kernel_names_valid sg s.
Proof. intros; unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto. Qed.

Lemma UCOS2_full_state_inv_names_valid : forall sg s,
  UCOS2_full_state_inv sg s -> kernel_names_valid sg s.
Proof.
  intros; unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready in H; tauto.
Qed.

Lemma event_update_name_references : forall events eid node name,
  event_name_reference (update_event_field_raw events eid node) name ->
  event_name_reference events name \/ name = node.(eventName).
Proof.
  intros events eid node name [other [found [Hget Hname]]].
  cbn [update_event_field_raw inUsedEventStates] in Hget.
  destruct (Z.eqb other eid).
  - injection Hget as Hnode; subst found; right; exact Hname.
  - left; exists other, found; split; assumption.
Qed.

Lemma kernel_names_valid_event_set_name : forall sg s eid old name chars,
  kernel_names_valid sg s -> readable_name s.(NameState) name chars ->
  kernel_names_valid sg
    (replace_EventS (update_event_field_raw s.(EventState) eid (event_set_name old name)) s).
Proof.
  intros sg s eid old name chars Hvalid Hread.
  eapply kernel_names_valid_replace_event_add_name; [exact Hvalid| |].
  - intros _; exists chars; exact Hread.
  - intros p Hreference; apply event_update_name_references in Hreference; exact Hreference.
Qed.

(** Full-profile pure bridge for [OSEventNameSet].  The readable bytes and
    the post-update [event_in_range] fact are supplied by the caller's
    name/event protocol; this theorem only transports the remaining global
    state facts and never manufactures byte ownership or event validity. *)
Lemma UCOS2_full_state_inv_event_name_set_bridge :
  forall sg s eid old name chars,
  UCOS2_full_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some old ->
  readable_name s.(NameState) name chars ->
  event_registered_in_range sg s.(TskState)
    (update_event_field_raw s.(EventState) eid (event_set_name old name)) ->
  UCOS2_full_state_inv sg
    (replace_EventS
      (update_event_field_raw s.(EventState) eid (event_set_name old name)) s).
Proof.
  intros sg s eid old name chars Hvalid Hold Hread Hevents.
  unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready in Hvalid.
  destruct Hvalid as [Hprofile Hvalid].
  destruct Hvalid as [Htasks Hvalid].
  destruct Hvalid as [Hsched Hvalid].
  destruct Hvalid as [Hevents0 Hvalid].
  destruct Hvalid as [Hcross Hvalid].
  destruct Hvalid as [Hidle Hvalid].
  destruct Hvalid as [Hstatus Hvalid].
  destruct Hvalid as [Hflags Hvalid].
  destruct Hvalid as [Hmemory Hvalid].
  destruct Hvalid as [Htimer Hvalid].
  destruct Hvalid as [Hstats Hvalid].
  destruct Hvalid as [Hcontrol Hvalid].
  destruct Hvalid as [Hnames Hvalid].
  destruct Hvalid as [Hreferences [Hstacks Hpending]].
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_EventS
      (update_event_field_raw s.(EventState) eid (event_set_name old name)) s)).
  { eapply kernel_names_valid_event_set_name; [exact Hreferences|exact Hread]. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (update_event_field_raw s.(EventState) eid (event_set_name old name))).
  { eapply pending_mutex_consistency_event_transport with (events := s.(EventState));
      [reflexivity| |exact Hpending].
    intros slot node Hnode Htype; cbn [update_event_field_raw inUsedEventStates] in Hnode.
    destruct (Z.eqb slot eid) eqn:E.
    - apply Z.eqb_eq in E; subst slot; injection Hnode as Hnode; subst node.
      exists old; split; [exact Hold|]. split; [exact Htype|reflexivity].
    - exists node; split; [exact Hnode|]. split; [exact Htype|reflexivity]. }
  split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|].
  split; [exact Hevents|]. split.
  - eapply cross_module_registration_event_fields_update; [exact Hold| | | |exact Hcross].
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn [replace_EventS]; split; [exact Hidle|]. split; [exact Hstatus|].
    split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
    split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
    split; [exact HreferencesAfter|]. split; [exact Hstacks|exact HpendingAfter].
Qed.

Lemma event_publish_name_references : forall events eid node name,
  event_name_reference (event_publish events eid node) name ->
  event_name_reference events name \/ name = node.(eventName).
Proof.
  intros events eid node name [other [found [Hget Hname]]].
  cbn [event_publish inUsedEventStates] in Hget; unfold kernel_map_set in Hget.
  destruct (Z.eq_dec other eid).
  - injection Hget as Hnode; subst found; right; exact Hname.
  - left; exists other, found; split; assumption.
Qed.

Lemma event_update_preserves_name_references : forall events eid old node,
  events.(inUsedEventStates) eid = Some old ->
  node.(eventName) = old.(eventName) ->
  forall name, event_name_reference (update_event_field_raw events eid node) name ->
    event_name_reference events name.
Proof.
  intros events eid old node Hold Hsame name Hreference.
  apply event_update_name_references in Hreference.
  destruct Hreference as [Hprevious|Hname]; [exact Hprevious|].
  exists eid, old; split; [exact Hold|congruence].
Qed.

Lemma event_recycle_name_references : forall sg events eid image name,
  event_name_reference (event_recycle sg events eid image) name ->
  event_name_reference events name.
Proof.
  intros sg events eid image name [other [node [Hget Hname]]].
  cbn [event_recycle inUsedEventStates] in Hget; unfold kernel_map_set in Hget.
  destruct (Z.eq_dec other eid); [discriminate|].
  exists other, node; split; assumption.
Qed.

Lemma task_update_name_references : forall tasks tid old node,
  tasks.(inUsedTaskStates) tid = Some old -> node.(tcbTaskName) = old.(tcbTaskName) ->
  forall name, task_name_reference (glob_task_set_usedtask tasks tid node) name ->
    task_name_reference tasks name.
Proof.
  intros tasks tid old node Hold Hsame name [j [found [Hlookup Hname]]].
  cbv beta iota zeta delta [glob_task_set_usedtask inUsedTaskStates] in Hlookup.
  destruct (Z.eqb j tid) eqn:Hj.
  - apply Z.eqb_eq in Hj; subst j; injection Hlookup as Hfound; subst found.
    exists tid, old; split; [exact Hold|congruence].
  - exists j, found; split; assumption.
Qed.

(** Profiling stores change no task identity, priority, wait relationship,
    stack-pointer binding or name reference.  This is the pure global
    preservation half of their reconstruction: concrete field ownership
    and the stored values' machine ranges still come from the configured
    storage predicates and the actual C writes, not from this theorem. *)
Lemma UCOS2_full_state_inv_task_set_profile_preserved :
  forall sg s tid old switches cycles start stack_base used,
  UCOS2_full_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_full_state_inv sg
    (replace_TskS
      (glob_task_set_usedtask s.(TskState) tid
        (task_set_profile old switches cycles start stack_base used)) s).
Proof.
  intros sg s tid old switches cycles start stack_base used
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]] Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_TskS
      (glob_task_set_usedtask s.(TskState) tid
        (task_set_profile old switches cycles start stack_base used)) s)).
  { eapply kernel_names_valid_replace_task; [exact Hreferences|].
    eapply task_update_name_references; [exact Hold|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (glob_task_set_usedtask s.(TskState) tid
      (task_set_profile old switches cycles start stack_base used))
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + destruct Hsched as [Hready Hmetadata]; split; [|exact Hmetadata].
      eapply sched_registered_ready_update_task;
        [exact Hold|reflexivity|reflexivity|reflexivity|exact Hready].
    + split.
      * eapply event_registered_in_range_update_task;
          [exact Hold|reflexivity| |exact Hevents].
        intros eid kind Hphase; exact Hphase.
      * split.
        -- destruct Hcross as [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Hinit]]]]]].
           split.
           ++ eapply task_mutex_priotbl_consistency_update_task;
                [exact Hold|reflexivity|exact Htable].
           ++ split; [eapply mutex_owner_snapshot_update_task; eassumption|].
              split.
              ** eapply event_registration_update_task;
                   [exact Hold|reflexivity| | |exact Hwait].
                 --- intros eid; reflexivity.
                 --- intros eid kind Hphase; exact Hphase.
              ** split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Hinit].
                 eapply task_flag_waiter_consistency_update_task;
                   [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag];
                   intros H; exact H.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split.
              ** apply task_reserved_bits_clear_update_task;
                   [exact Hstatus|exact (Hstatus tid old Hold)].
              ** split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
                 split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
                 split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact Hpending].
Qed.

Lemma task_commit_name_references : forall tasks priority invocation node name,
  task_name_reference (task_commit tasks priority invocation node) name ->
  task_name_reference tasks name \/ name = node.(tcbTaskName).
Proof.
  intros tasks priority invocation node name [j [found [Hlookup Hname]]].
  pose proof (task_commit_observation addr tcbTaskName tasks priority invocation node j
    (fun _ _ _ => eq_refl)) as Hobserve.
  rewrite Hlookup in Hobserve; cbn [option_map] in Hobserve.
  destruct (Z.eq_dec j (taskID node)) as [Hnew | Hother].
  - right; congruence.
  - destruct (inUsedTaskStates tasks j) as [old|] eqn:Hold; [|discriminate].
    left; exists j, old; split; [exact Hold|]. cbn [option_map] in Hobserve; congruence.
Qed.

Lemma flag_unlink_name_references : forall flags p waiter after,
  flag_unlink_node flags p = Some (waiter, after) ->
  forall name, flag_name_reference after name -> flag_name_reference flags name.
Proof.
  intros flags p waiter after Hstep.
  unfold flag_unlink_node in Hstep; destruct (flagWaitNodes flags p) as [w|]; [|discriminate].
  destruct (flagUsed flags (flagGroup w)) as [group|] eqn:Hgroup;
    destruct (flagImages flags (flagGroup w)); try discriminate.
  inversion Hstep; subst after waiter; clear Hstep.
  intros name [i [found [Hlookup Hname]]]; cbv beta iota zeta delta [flagUsed] in Hlookup;
    unfold kernel_map_set in Hlookup.
  destruct (Z.eq_dec i (flagGroup w)) as [Heq | Hother].
  - subst i; injection Hlookup as Hfound; subst found.
    exists (flagGroup w), group; split; [exact Hgroup|exact Hname].
  - exists i, found; split; assumption.
Qed.

Lemma timer_link_name_references : forall sg timers i periodic after,
  timer_link sg timers i periodic = Some after ->
  forall name, timer_name_reference after name -> timer_name_reference timers name.
Proof.
  intros sg timers i periodic after Hstep; unfold timer_link in Hstep.
  destruct (timerUsed timers i) as [old|] eqn:Hold;
    destruct (timerImages timers i); try discriminate.
  inversion Hstep; subst after; clear Hstep.
  intros name [j [found [Hlookup Hname]]];
    cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed] in Hlookup;
    unfold kernel_map_set in Hlookup.
  destruct (Z.eq_dec j i) as [Heq | Hother].
  - subst j; injection Hlookup as Hfound; subst found.
    exists i, old; split; [exact Hold|exact Hname].
  - exists j, found; split; assumption.
Qed.

Lemma timer_unlink_name_references : forall sg timers i after,
  timer_unlink sg timers i = Some after ->
  forall name, timer_name_reference after name -> timer_name_reference timers name.
Proof.
  intros sg timers i after Hstep; unfold timer_unlink in Hstep.
  destruct (timerUsed timers i) as [old|] eqn:Hold;
    destruct (timerImages timers i); try discriminate.
  inversion Hstep; subst after; clear Hstep.
  intros name [j [found [Hlookup Hname]]];
    cbv beta iota zeta delta [timer_replace_wheel_objects timerUsed] in Hlookup;
    unfold kernel_map_set in Hlookup.
  destruct (Z.eq_dec j i) as [Heq | Hother].
  - subst j; injection Hlookup as Hfound; subst found.
    exists i, old; split; [exact Hold|exact Hname].
  - exists j, found; split; assumption.
Qed.

Lemma timer_release_name_references : forall sg timers i old name,
  forall p, timer_name_reference (timer_release sg timers i old name) p ->
    timer_name_reference timers p.
Proof.
  intros sg timers i old name p [j [found [Hlookup Hname]]].
  cbv beta iota zeta delta [timer_release timer_name_reference timerUsed] in Hlookup.
  unfold kernel_map_set in Hlookup.
  destruct (Z.eq_dec j i) as [Heq | Hother].
  - subst j; simpl in Hlookup; discriminate.
  - exists j, found; split; [exact Hlookup|exact Hname].
Qed.

Lemma timer_delete_locked_name_references : forall sg before i name ret err after,
  timer_delete_locked sg before i name = Some (ret, err, after) ->
  forall p, timer_name_reference after p -> timer_name_reference before p.
Proof.
  intros sg before i name ret err after Hstep p Hreference.
  unfold timer_delete_locked in Hstep.
  destruct (timerImages before i) as [image|] eqn:Himage; [|discriminate].
  destruct (Z.eqb (timerImageState image) 3) eqn:Hrunning.
  - destruct (timer_unlink sg before i) as [stopped|] eqn:Hunlink; [|discriminate].
    destruct (timerImages stopped i) as [stopped_image|] eqn:Hstopped_image;
      [|discriminate].
    inversion Hstep; subst after.
    pose proof (timer_release_name_references sg stopped i stopped_image name p
      Hreference) as Hstopped_reference.
    exact (timer_unlink_name_references sg before i stopped Hunlink p
      Hstopped_reference).
  - destruct (orb (Z.eqb (timerImageState image) 1)
      (Z.eqb (timerImageState image) 2)).
    + inversion Hstep; subst after.
      eapply timer_release_name_references; exact Hreference.
    + destruct (Z.eqb (timerImageState image) 0).
      * inversion Hstep; subst after; exact Hreference.
      * inversion Hstep; subst after; exact Hreference.
Qed.

(** A submodule focus used by TCB/ready updates: parked Task stacks stay
    in the complement. This is deliberately not missing_task_sched, which
    removes the complete Task owner, including those stacks. *)
Definition UCOS2_raw_rep_missing_task_storage_sched (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  event_raw_rep sg s.(TskState) s.(EventState) **
  queue_storage_rep sg s.(EventState) **
  tick_inv sg s.(TickState) **
  flag_configured_rep sg s.(FlagState) **
  memory_configured_rep sg s.(MemoryState) **
  timer_configured_rep sg s.(TimerState) **
  statistics_rep sg s.(StatsState) **
  kernel_control_rep sg s.(ControlState) **
  store_name_bytes s.(NameState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks).

Definition UCOS2_inv (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) && UCOS2_raw_rep sg s.

(** Full-profile counterpart of [UCOS2_inv].  The raw representation is
    already parameterized by [sg.osKernelConfig], so the only missing
    global bridge is the profile-indexed pure invariant above. *)
Definition UCOS2_full_inv (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_full_state_inv sg s) && UCOS2_raw_rep sg s.

Lemma UCOS2_full_inv_split_module : forall sg s m,
  UCOS2_full_inv sg s --||-- coq_prop (UCOS2_full_state_inv sg s) &&
    (UCOS2_module_rep sg s m ** UCOS2_raw_rep_missing_module sg s m).
Proof.
  intros sg s m; unfold UCOS2_full_inv;
    rewrite (UCOS2_raw_rep_split_module sg s m); split; reflexivity.
Qed.

Lemma UCOS2_full_inv_split_two : forall sg s first second,
  first <> second ->
  UCOS2_full_inv sg s --||-- coq_prop (UCOS2_full_state_inv sg s) &&
    (UCOS2_module_rep sg s first ** UCOS2_module_rep sg s second **
     UCOS2_raw_rep_missing_two sg s first second).
Proof.
  intros sg s first second Hdistinct; unfold UCOS2_full_inv;
    rewrite (UCOS2_raw_rep_split_two sg s first second Hdistinct);
    split; reflexivity.
Qed.

Lemma UCOS2_full_inv_split_event : forall sg s,
  UCOS2_full_inv sg s --||-- coq_prop (UCOS2_full_state_inv sg s) &&
    (event_raw_rep sg s.(TskState) s.(EventState) **
     UCOS2_raw_rep_missing_event sg s).
Proof.
  intros sg s; exact (UCOS2_full_inv_split_module sg s EventModule).
Qed.

Lemma UCOS2_full_inv_split_names : forall sg s,
  UCOS2_full_inv sg s --||-- coq_prop (UCOS2_full_state_inv sg s) &&
    (store_name_bytes s.(NameState) ** UCOS2_raw_rep_missing_names sg s).
Proof.
  intros sg s; exact (UCOS2_full_inv_split_module sg s NamesModule).
Qed.

Lemma UCOS2_full_inv_split_event_queue : forall sg s,
  UCOS2_full_inv sg s --||-- coq_prop (UCOS2_full_state_inv sg s) &&
    (event_raw_rep sg s.(TskState) s.(EventState) **
     queue_storage_rep sg s.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg s).
Proof.
  intros sg s; apply (UCOS2_full_inv_split_two sg s EventModule QueueModule); discriminate.
Qed.

Lemma UCOS2_full_inv_merge_updated_module : forall sg before after m,
  UCOS2_full_state_inv sg after ->
  (UCOS2_raw_rep_missing_module sg before m |--
   UCOS2_raw_rep_missing_module sg after m) ->
  UCOS2_module_rep sg after m ** UCOS2_raw_rep_missing_module sg before m |--
    UCOS2_full_inv sg after.
Proof.
  intros sg before after m Hvalid Hframe.
  eapply derivable1_trans; [eapply UCOS2_raw_rep_merge_updated_module; exact Hframe|].
  unfold UCOS2_full_inv; entailer!.
Qed.

Lemma UCOS2_full_inv_merge_updated_two : forall sg before after first second,
  first <> second -> UCOS2_full_state_inv sg after ->
  (UCOS2_raw_rep_missing_two sg before first second |--
   UCOS2_raw_rep_missing_two sg after first second) ->
  UCOS2_module_rep sg after first ** UCOS2_module_rep sg after second **
    UCOS2_raw_rep_missing_two sg before first second |--
    UCOS2_full_inv sg after.
Proof.
  intros sg before after first second Hdistinct Hvalid Hframe.
  eapply derivable1_trans;
    [eapply UCOS2_raw_rep_merge_updated_two; [exact Hdistinct|exact Hframe]|].
  unfold UCOS2_full_inv; entailer!.
Qed.

Lemma UCOS2_raw_rep_missing_task_storage_sched_equiv : forall sg s,
  UCOS2_raw_rep_missing_task_storage_sched sg s --||--
    store_parked_stacks s.(TskState).(parkedTaskStacks) **
    UCOS2_raw_rep_missing_task_sched sg s.
Proof.
  intros; unfold UCOS2_raw_rep_missing_task_storage_sched,
    UCOS2_raw_rep_missing_task_sched, UCOS2_raw_rep_missing_two, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  split; entailer!.
Qed.

Lemma UCOS2_inv_split_module : forall sg s m,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (UCOS2_module_rep sg s m ** UCOS2_raw_rep_missing_module sg s m).
Proof.
  intros sg s m; unfold UCOS2_inv; rewrite (UCOS2_raw_rep_split_module sg s m).
  split; reflexivity.
Qed.

Lemma UCOS2_inv_split_two : forall sg s first second,
  first <> second ->
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (UCOS2_module_rep sg s first ** UCOS2_module_rep sg s second **
     UCOS2_raw_rep_missing_two sg s first second).
Proof.
  intros sg s first second Hdistinct; unfold UCOS2_inv.
  rewrite (UCOS2_raw_rep_split_two sg s first second Hdistinct).
  split; reflexivity.
Qed.

Lemma UCOS2_inv_split_task : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (task_shared_rep sg s.(TskState) ** UCOS2_raw_rep_missing_task sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s TaskModule). Qed.

Lemma UCOS2_inv_split_sched : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (sched_raw_rep sg s.(TskState) s.(SchedState) ** UCOS2_raw_rep_missing_sched sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s SchedModule). Qed.

Definition UCOS2_raw_rep_missing_running (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  sched_raw_rep_without_running sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_sched sg s.

Lemma UCOS2_raw_rep_split_running : forall sg s,
  UCOS2_raw_rep sg s --||--
    (sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0) **
     UCOS2_raw_rep_missing_running sg s).
Proof.
  intros; rewrite (UCOS2_raw_rep_split_module sg s SchedModule).
  cbn [UCOS2_module_rep].
  rewrite sched_raw_rep_split_running.
  unfold UCOS2_raw_rep_missing_running, UCOS2_raw_rep_missing_sched.
  split; entailer!.
Qed.

Lemma UCOS2_inv_split_running : forall sg s,
  UCOS2_inv sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0) **
     UCOS2_raw_rep_missing_running sg s).
Proof.
  intros; unfold UCOS2_inv; rewrite UCOS2_raw_rep_split_running.
  split; reflexivity.
Qed.

Lemma UCOS2_inv_split_event : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (event_raw_rep sg s.(TskState) s.(EventState) ** UCOS2_raw_rep_missing_event sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s EventModule). Qed.

Lemma UCOS2_inv_split_queue : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (queue_storage_rep sg s.(EventState) ** UCOS2_raw_rep_missing_queue sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s QueueModule). Qed.

Lemma UCOS2_inv_split_tick : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (tick_inv sg s.(TickState) ** UCOS2_raw_rep_missing_tick sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s TickModule). Qed.

Lemma UCOS2_inv_split_statistics : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (statistics_rep sg s.(StatsState) ** UCOS2_raw_rep_missing_statistics sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s StatisticsModule). Qed.

Lemma UCOS2_inv_split_control : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (kernel_control_rep sg s.(ControlState) ** UCOS2_raw_rep_missing_control sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s ControlModule). Qed.

Lemma UCOS2_inv_split_names : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (store_name_bytes s.(NameState) ** UCOS2_raw_rep_missing_names sg s).
Proof. intros sg s; exact (UCOS2_inv_split_module sg s NamesModule). Qed.

Lemma UCOS2_inv_split_task_sched : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (task_shared_rep sg s.(TskState) **
     sched_raw_rep sg s.(TskState) s.(SchedState) **
     UCOS2_raw_rep_missing_task_sched sg s).
Proof.
  intros sg s; apply (UCOS2_inv_split_two sg s TaskModule SchedModule); discriminate.
Qed.

(** Spatial reassembly does not prove abstract-state validity. Its caller
    supplies the operation's proved post-state invariant and transport of
    the actual non-focused resources; no old validity fact is discarded. *)
Lemma UCOS2_inv_merge_updated_module : forall sg before after m,
  UCOS2_state_inv sg after ->
  (UCOS2_raw_rep_missing_module sg before m |-- UCOS2_raw_rep_missing_module sg after m) ->
  UCOS2_module_rep sg after m ** UCOS2_raw_rep_missing_module sg before m |--
    UCOS2_inv sg after.
Proof.
  intros sg before after m Hvalid Hframe.
  eapply derivable1_trans; [eapply UCOS2_raw_rep_merge_updated_module; exact Hframe|].
  unfold UCOS2_inv; entailer!.
Qed.

Lemma UCOS2_inv_merge_updated_two : forall sg before after first second,
  first <> second -> UCOS2_state_inv sg after ->
  (UCOS2_raw_rep_missing_two sg before first second |--
    UCOS2_raw_rep_missing_two sg after first second) ->
  UCOS2_module_rep sg after first ** UCOS2_module_rep sg after second **
    UCOS2_raw_rep_missing_two sg before first second |-- UCOS2_inv sg after.
Proof.
  intros sg before after first second Hdistinct Hvalid Hframe.
  eapply derivable1_trans;
    [eapply UCOS2_raw_rep_merge_updated_two; [exact Hdistinct|exact Hframe]|].
  unfold UCOS2_inv; entailer!.
Qed.

Lemma UCOS2_raw_rep_missing_task_storage_sched_task_map_frame : forall sg s tasks,
  s.(TskState).(inUsedTaskStates) = tasks.(inUsedTaskStates) ->
  s.(TskState).(parkedTaskStacks) = tasks.(parkedTaskStacks) ->
  UCOS2_raw_rep_missing_task_storage_sched sg s =
    UCOS2_raw_rep_missing_task_storage_sched sg (replace_TskS tasks s).
Proof.
  intros sg s tasks Hused Hstacks; unfold UCOS2_raw_rep_missing_task_storage_sched; simpl.
  rewrite Hstacks.
  rewrite (event_raw_rep_change_task_index sg s.(TskState) tasks s.(EventState));
    [reflexivity|].
  apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin.
  rewrite Hused; reflexivity.
Qed.

Lemma UCOS2_raw_rep_task_map_frame : forall sg s tasks,
  s.(TskState).(inUsedTaskStates) = tasks.(inUsedTaskStates) ->
  task_public_storage sg s.(TskState) = task_public_storage sg tasks ->
  s.(TskState).(parkedTaskStacks) = tasks.(parkedTaskStacks) ->
  UCOS2_raw_rep sg s = UCOS2_raw_rep sg (replace_TskS tasks s).
Proof.
  intros sg s tasks Hused Hstorage Hstacks; unfold UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
  rewrite Hstorage, (sched_raw_rep_change_task_index sg s.(TskState) tasks s.(SchedState) Hused),
    Hstacks.
  rewrite (event_raw_rep_change_task_index sg s.(TskState) tasks s.(EventState));
    [reflexivity|].
  apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin.
  rewrite Hused; reflexivity.
Qed.

(** Taking or returning a stack interval changes this resource map, not
    the public TCB storage. The complement retains every other owner;
    in particular, a typed Flag node is not hidden inside a stack hole. *)
Definition UCOS2_raw_rep_missing_parked_stacks (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_public_storage sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  interrupt_inv sg s.(IntrState) **
  event_raw_rep sg s.(TskState) s.(EventState) **
  queue_storage_rep sg s.(EventState) **
  tick_inv sg s.(TickState) **
  flag_configured_rep sg s.(FlagState) **
  memory_configured_rep sg s.(MemoryState) **
  timer_configured_rep sg s.(TimerState) **
  statistics_rep sg s.(StatsState) **
  kernel_control_rep sg s.(ControlState) ** store_name_bytes s.(NameState).

Lemma UCOS2_raw_rep_missing_parked_stacks_equiv : forall sg s,
  UCOS2_raw_rep_missing_parked_stacks sg s --||--
    task_public_storage sg s.(TskState) ** UCOS2_raw_rep_missing_task sg s.
Proof.
  intros; unfold UCOS2_raw_rep_missing_parked_stacks, UCOS2_raw_rep_missing_task,
    UCOS2_raw_rep_missing_module, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  split; entailer!.
Qed.

Lemma UCOS2_inv_split_parked_stacks : forall sg s,
  UCOS2_inv sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
      (store_parked_stacks s.(TskState).(parkedTaskStacks) **
       UCOS2_raw_rep_missing_parked_stacks sg s).
Proof.
  intros; unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_parked_stacks, task_shared_rep.
  split; entailer!.
Qed.

Lemma UCOS2_replace_parked_stacks_preserves_validity : forall sg s stacks,
  UCOS2_state_inv sg s ->
  parked_stacks_consistent s.(TskState) stacks ->
  UCOS2_state_inv sg
    (replace_TskS (glob_task_set_parked_stacks s.(TskState) stacks) s).
Proof.
  intros sg s stacks
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus
      [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hold Hpending]]]]]]]]]]]]]]]
    Hstacks.
  repeat (split; [assumption|]); exact Hpending.
Qed.

Lemma UCOS2_raw_rep_missing_parked_stacks_replace_eq : forall sg s stacks,
  UCOS2_raw_rep_missing_parked_stacks sg
    (replace_TskS (glob_task_set_parked_stacks s.(TskState) stacks) s) =
  UCOS2_raw_rep_missing_parked_stacks sg s.
Proof.
  intros sg s stacks; unfold UCOS2_raw_rep_missing_parked_stacks.
  cbn [replace_TskS TskState SchedState IntrState EventState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState].
  rewrite (sched_raw_rep_change_task_index sg
    (glob_task_set_parked_stacks s.(TskState) stacks)
    s.(TskState) s.(SchedState) eq_refl).
  rewrite (event_raw_rep_change_task_index sg
    (glob_task_set_parked_stacks s.(TskState) stacks)
    s.(TskState) s.(EventState)); [reflexivity|].
  apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin; reflexivity.
Qed.

Lemma UCOS2_inv_merge_updated_parked_stacks : forall sg s stacks,
  UCOS2_state_inv sg s ->
  parked_stacks_consistent s.(TskState) stacks ->
  store_parked_stacks stacks ** UCOS2_raw_rep_missing_parked_stacks sg s |--
    UCOS2_inv sg
      (replace_TskS (glob_task_set_parked_stacks s.(TskState) stacks) s).
Proof.
  intros sg s stacks Hvalid Hstacks.
  pose proof (UCOS2_replace_parked_stacks_preserves_validity sg s stacks Hvalid Hstacks)
    as Hpost.
  rewrite UCOS2_inv_split_parked_stacks,
    UCOS2_raw_rep_missing_parked_stacks_replace_eq; simpl; entailer!.
Qed.

(** Counter updates own only the two Intr cells.  Scheduler selection and
    context switching are subsequent stages with different write footprints. *)
Lemma UCOS2_validity_replace_interrupt_eq : forall sg s counters,
  UCOS2_state_inv sg (replace_IntrS counters s) =
    UCOS2_state_inv sg s.
Proof. reflexivity. Qed.

Lemma UCOS2_raw_rep_missing_interrupt_replace_interrupt_eq : forall sg s counters,
  UCOS2_raw_rep_missing_interrupt sg (replace_IntrS counters s) =
    UCOS2_raw_rep_missing_interrupt sg s.
Proof. reflexivity. Qed.

Lemma UCOS2_inv_split_interrupt : forall sg s,
  UCOS2_inv sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
      (interrupt_inv sg s.(IntrState) ** UCOS2_raw_rep_missing_interrupt sg s).
Proof.
  intros sg s; exact (UCOS2_inv_split_module sg s InterruptModule).
Qed.

Lemma UCOS2_inv_merge_updated_interrupt : forall sg s counters,
  UCOS2_state_inv sg s ->
  interrupt_inv sg counters ** UCOS2_raw_rep_missing_interrupt sg s |--
    UCOS2_inv sg (replace_IntrS counters s).
Proof.
  intros sg s counters Hvalid; rewrite UCOS2_inv_split_interrupt.
  rewrite UCOS2_validity_replace_interrupt_eq,
    UCOS2_raw_rep_missing_interrupt_replace_interrupt_eq; simpl.
  entailer!.
Qed.

(** Pool interfaces specialize the same module split/update laws. *)
Lemma UCOS2_inv_split_flag : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (flag_configured_rep sg s.(FlagState) ** UCOS2_raw_rep_missing_flag sg s).
Proof.
  intros sg s; exact (UCOS2_inv_split_module sg s FlagModule).
Qed.

Lemma UCOS2_inv_merge_updated_flag : forall sg before after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep_missing_flag sg before = UCOS2_raw_rep_missing_flag sg after ->
  flag_configured_rep sg after.(FlagState) ** UCOS2_raw_rep_missing_flag sg before |--
    UCOS2_inv sg after.
Proof.
  intros sg before after Hvalid Hframe.
  apply (UCOS2_inv_merge_updated_module sg before after FlagModule); [exact Hvalid|].
  change (UCOS2_raw_rep_missing_flag sg before |-- UCOS2_raw_rep_missing_flag sg after).
  rewrite Hframe; reflexivity.
Qed.

Lemma UCOS2_inv_split_memory : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (memory_configured_rep sg s.(MemoryState) ** UCOS2_raw_rep_missing_memory sg s).
Proof.
  intros sg s; exact (UCOS2_inv_split_module sg s MemoryModule).
Qed.

Lemma UCOS2_inv_merge_updated_memory : forall sg before after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep_missing_memory sg before = UCOS2_raw_rep_missing_memory sg after ->
  memory_configured_rep sg after.(MemoryState) ** UCOS2_raw_rep_missing_memory sg before |--
    UCOS2_inv sg after.
Proof.
  intros sg before after Hvalid Hframe.
  apply (UCOS2_inv_merge_updated_module sg before after MemoryModule); [exact Hvalid|].
  change (UCOS2_raw_rep_missing_memory sg before |-- UCOS2_raw_rep_missing_memory sg after).
  rewrite Hframe; reflexivity.
Qed.

Lemma UCOS2_inv_split_timer : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (timer_configured_rep sg s.(TimerState) ** UCOS2_raw_rep_missing_timer sg s).
Proof.
  intros sg s; exact (UCOS2_inv_split_module sg s TimerModule).
Qed.

Lemma UCOS2_inv_merge_updated_timer : forall sg before after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep_missing_timer sg before = UCOS2_raw_rep_missing_timer sg after ->
  timer_configured_rep sg after.(TimerState) ** UCOS2_raw_rep_missing_timer sg before |--
    UCOS2_inv sg after.
Proof.
  intros sg before after Hvalid Hframe.
  apply (UCOS2_inv_merge_updated_module sg before after TimerModule); [exact Hvalid|].
  change (UCOS2_raw_rep_missing_timer sg before |-- UCOS2_raw_rep_missing_timer sg after).
  rewrite Hframe; reflexivity.
Qed.

Lemma UCOS2_raw_rep_missing_memory_replace_eq : forall sg s memory,
  UCOS2_raw_rep_missing_memory sg (replace_MemoryS memory s) = UCOS2_raw_rep_missing_memory sg s.
Proof. reflexivity. Qed.
Lemma UCOS2_raw_rep_missing_flag_replace_eq : forall sg s flags,
  UCOS2_raw_rep_missing_flag sg (replace_FlagS flags s) = UCOS2_raw_rep_missing_flag sg s.
Proof. reflexivity. Qed.
Lemma UCOS2_raw_rep_missing_timer_replace_eq : forall sg s timers,
  UCOS2_raw_rep_missing_timer sg (replace_TimerS timers s) = UCOS2_raw_rep_missing_timer sg s.
Proof. reflexivity. Qed.

Lemma memory_replace_partition_name_references : forall s i old post,
  s.(memControlImages) i = Some (memory_partition_image old) ->
  post.(memName) = old.(memName) ->
  forall name, memory_name_reference (memory_replace_partition s i post) name ->
    memory_name_reference s name.
Proof.
  intros s i old post Himage Hname name [[j [v [Hv Hp]]] | [j [v [Hv Hp]]]].
  - left; cbv beta iota zeta delta [memory_replace_partition memControlImages] in Hv;
      unfold kernel_map_set in Hv.
    destruct (Z.eq_dec j i) as [Heq | Hne].
    + subst j; injection Hv as Hv; subst v; exists i, (memory_partition_image old).
      split; [exact Himage|]. change (name = memName old).
      change (name = memName post) in Hp; congruence.
    + exists j, v; split; assumption.
  - right; exists j, v; split; assumption.
Qed.

Lemma memory_get_name_references : forall sg s i loan post,
  valid_memory_state sg s -> memory_get s i = Some (loan, post) ->
  forall name, memory_name_reference post name -> memory_name_reference s name.
Proof.
  intros sg s i loan post [_ [Hparts _]] Hget.
  unfold memory_get in Hget; destruct (memPartitions s i) as [old|] eqn:Hold; [|discriminate].
  destruct (memory_get_partition i old) as [[item updated]|] eqn:Hpart; [|discriminate].
  inversion Hget; subst post item.
  apply memory_replace_partition_name_references with (old := old).
  - exact (proj2 (proj2 (Hparts i old Hold))).
  - unfold memory_get_partition in Hpart; destruct (memFreeBlocks old); [discriminate|].
    inversion Hpart; reflexivity.
Qed.

Lemma memory_put_name_references : forall sg s i block post,
  valid_memory_state sg s -> memory_put s i block = Some post ->
  forall name, memory_name_reference post name -> memory_name_reference s name.
Proof.
  intros sg s i block post [_ [Hparts _]] Hput.
  unfold memory_put in Hput; destruct (memPartitions s i) as [old|] eqn:Hold; [|discriminate].
  inversion Hput; subst post.
  apply memory_replace_partition_name_references with (old := old); [|reflexivity].
  exact (proj2 (proj2 (Hparts i old Hold))).
Qed.

Lemma UCOS2_replace_memory_preserves_validity : forall sg s memory,
  UCOS2_state_inv sg s -> valid_memory_configuration sg memory ->
  (forall name, memory_name_reference memory name -> memory_name_reference s.(MemoryState) name) ->
  UCOS2_state_inv sg (replace_MemoryS memory s).
Proof.
  intros sg s memory Hvalid Hmemory Hreferences.
  pose proof (kernel_names_valid_replace_memory sg s memory
    (UCOS2_state_inv_names_valid sg s Hvalid) Hreferences) as Hnames.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [replace_MemoryS] in *; tauto.
Qed.

Lemma UCOS2_memory_get_preserves_validity : forall sg s i loan memory,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  memory_get s.(MemoryState) i = Some (loan, memory) ->
  UCOS2_state_inv sg (replace_MemoryS memory s).
Proof.
  intros sg s i loan memory Henabled Hvalid Hget.
  assert (Hmemory : valid_memory_configuration sg s.(MemoryState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  unfold valid_memory_configuration in Hmemory; rewrite Henabled in Hmemory.
  apply UCOS2_replace_memory_preserves_validity; [exact Hvalid| |].
  - unfold valid_memory_configuration; rewrite Henabled.
    eapply memory_get_preserves_state_validity; eauto.
  - eapply memory_get_name_references; eauto.
Qed.

Lemma UCOS2_memory_put_preserves_validity : forall sg s i block partition loan memory,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  s.(MemoryState).(memPartitions) i = Some partition ->
  partition.(memAllocatedBlocks) block = Some loan ->
  memory_put s.(MemoryState) i block = Some memory ->
  UCOS2_state_inv sg (replace_MemoryS memory s).
Proof.
  intros sg s i block partition loan memory Henabled Hvalid Hpart Hloan Hput.
  assert (Hmemory : valid_memory_configuration sg s.(MemoryState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  unfold valid_memory_configuration in Hmemory; rewrite Henabled in Hmemory.
  apply UCOS2_replace_memory_preserves_validity; [exact Hvalid| |].
  - unfold valid_memory_configuration; rewrite Henabled.
    eapply memory_put_preserves_state_validity; eauto.
  - eapply memory_put_name_references; eauto.
Qed.

(** Timer is not an opaque frame: its initialization phase is related to
    OSRunning. Resource reconstruction still requires the actual updated
    timer_configured_rep, via UCOS2_inv_merge_updated_timer. *)
Lemma UCOS2_replace_timer_preserves_validity : forall sg s timers,
  UCOS2_state_inv sg s -> valid_timer_configuration sg timers ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true ->
   s.(SchedState).(isRunning) = true -> timer_api_initialized timers) ->
  (forall name, timer_name_reference timers name -> timer_name_reference s.(TimerState) name) ->
  UCOS2_state_inv sg (replace_TimerS timers s).
Proof.
  intros sg s timers Hvalid Htimers Hphase Hreferences.
  pose proof (kernel_names_valid_replace_timer sg s timers
    (UCOS2_state_inv_names_valid sg s Hvalid) Hreferences) as HnamesAfter.
  destruct Hvalid as [Hp [Ht [Hs [He [Hcross [Hi [Hstatus [Hf [Hm [Htm Hrest]]]]]]]]]].
  destruct Hrest as [Hstats [Hcontrol [Hnames [Hroots Hstacks]]]].
  split; [exact Hp|]. split; [exact Ht|]. split; [exact Hs|]. split; [exact He|].
  split.
  - destruct Hcross as [Ha [Ho [Hw [Hprotocol [Hunique [Hflags Holdphase]]]]]].
    split; [exact Ha|]. split; [exact Ho|]. split; [exact Hw|].
    split; [exact Hprotocol|]. split; [exact Hunique|]. split; [exact Hflags|exact Hphase].
  - split; [exact Hi|]. split; [exact Hstatus|]. split; [exact Hf|]. split; [exact Hm|].
    repeat (split; [assumption|]); exact Hstacks.
Qed.

Lemma UCOS2_timer_pool_initialize_preserves_validity : forall sg s name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg s ->
  s.(SchedState).(isRunning) = false -> s.(TimerState).(timerInitPhase) = TimerUninitialized ->
  UCOS2_state_inv sg (replace_TimerS (timer_pool_initialize sg name) s).
Proof.
  intros sg s name Henabled Hvalid Hstopped Huninitialized.
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid| | |].
  - pose proof (proj1 Hvalid) as [_ [_ [_ [Hconfig _]]]].
    destruct Hconfig as [_ [_ [_ [Hcapacity _]]]].
    destruct (Hcapacity Henabled) as [Htimers Hwheel].
    apply timer_pool_initialize_configuration_valid; [exact Henabled|lia|lia].
  - intros _ Hrunning; congruence.
  - intros p [i [t [Hlookup Hname]]]; discriminate.
Qed.

Lemma UCOS2_timer_record_lock_preserves_validity : forall sg s result timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg s ->
  s.(SchedState).(isRunning) = false ->
  timer_record_lock_result s.(TimerState) result = Some timers ->
  UCOS2_state_inv sg (replace_TimerS timers s).
Proof.
  intros sg s result timers Henabled Hvalid Hstopped Hstep.
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid| | |].
  - eapply timer_record_lock_preserves_configuration; [exact Henabled| |exact Hstep].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
  - intros _ Hrunning; congruence.
  - unfold timer_record_lock_result in Hstep; destruct (timerInitPhase (TimerState s)); try discriminate.
    inversion Hstep; subst timers; intros; assumption.
Qed.

Lemma UCOS2_timer_record_signal_preserves_validity : forall sg s result timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg s ->
  s.(SchedState).(isRunning) = false ->
  timer_record_signal_result s.(TimerState) result = Some timers ->
  UCOS2_state_inv sg (replace_TimerS timers s).
Proof.
  intros sg s result timers Henabled Hvalid Hstopped Hstep.
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid| | |].
  - eapply timer_record_signal_preserves_configuration; [exact Henabled| |exact Hstep].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
  - intros _ Hrunning; congruence.
  - unfold timer_record_signal_result in Hstep; destruct (timerInitPhase (TimerState s)); try discriminate.
    inversion Hstep; subst timers; intros; assumption.
Qed.

Lemma UCOS2_timer_finish_initialization_preserves_validity : forall sg s task_result timers,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg s ->
  timer_finish_initialization s.(TimerState) task_result = Some timers ->
  UCOS2_state_inv sg (replace_TimerS timers s).
Proof.
  intros sg s task_result timers Henabled Hvalid Hstep.
  assert (Htimer : valid_timer_configuration sg s.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  destruct (timer_finish_initialization_preserves_configuration sg s.(TimerState)
    task_result timers Henabled Htimer Hstep) as [Hpost Hphase].
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid|exact Hpost| |].
  - intros _ _; exact Hphase.
  - unfold timer_finish_initialization in Hstep; destruct (timerInitPhase (TimerState s)); try discriminate.
    inversion Hstep; subst timers; intros; assumption.
Qed.

Lemma UCOS2_timer_service_advance_preserves_validity : forall sg s,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> UCOS2_state_inv sg s ->
  timer_api_initialized s.(TimerState) ->
  UCOS2_state_inv sg (replace_TimerS (timer_service_advance s.(TimerState)) s).
Proof.
  intros sg s Henabled Hvalid Hphase.
  assert (Htimer : valid_timer_configuration sg s.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  destruct (timer_service_advance_preserves_configuration sg s.(TimerState) Henabled Htimer Hphase)
    as [Hpost Hpostphase].
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid|exact Hpost| |].
  - intros _ _; exact Hpostphase.
  - intros; assumption.
Qed.

Lemma UCOS2_inv_open_task_storage_sched : forall sg s,
  UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s) &&
  (task_public_storage sg s.(TskState) **
   sched_raw_rep sg s.(TskState) s.(SchedState) **
   UCOS2_raw_rep_missing_task_storage_sched sg s).
Proof.
  intros; unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Lemma UCOS2_inv_merge_updated_task_storage_sched : forall sg old post,
  UCOS2_state_inv sg post ->
  UCOS2_raw_rep_missing_task_storage_sched sg old = UCOS2_raw_rep_missing_task_storage_sched sg post ->
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg old |-- UCOS2_inv sg post.
Proof.
  intros sg old post Hvalid Hframe; rewrite Hframe.
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Lemma UCOS2_replace_sched_preserves_validity : forall sg s sched',
  UCOS2_state_inv sg s -> sched_in_range sg s.(TskState) sched' ->
  sched'.(isRunning) = s.(SchedState).(isRunning) ->
  UCOS2_state_inv sg (replace_SchedS sched' s).
Proof.
  intros sg s sched' [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hrest]]]]]] Hnew Hrunning.
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hnew|].
  split; [exact Hevents|]; split.
  - apply cross_module_consistency_sched_frame; assumption.
  - split; [|exact Hrest].
    intro Hrun; apply Hidle; rewrite <- Hrunning; exact Hrun.
Qed.

Lemma UCOS2_begin_task_invocation_preserves_validity : forall sg s origin,
  UCOS2_state_inv sg s -> task_invocation_origin_live s.(TskState) origin ->
  UCOS2_state_inv sg
    (replace_TskS (task_begin_invocation origin s.(TskState)) s).
Proof.
  intros sg s origin
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hmodules]]]]]] Horigin.
  split; [exact Hprofile|]. split.
  - apply task_begin_invocation_preserves_in_range; assumption.
  - split; [exact Hsched|]. split; [exact Hevents|]. split; [exact Hcross|].
    exact (conj Hidle Hmodules).
Qed.

Lemma UCOS2_task_reserve_preserves_validity : forall sg s p invocation origin,
  UCOS2_state_inv sg s ->
  task_reserve_guard sg s.(TskState) p invocation origin ->
  UCOS2_state_inv sg
    (replace_TskS (task_reserve s.(TskState) p invocation origin) s).
Proof.
  intros sg s p invocation origin
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hmodules]]]]]] Hguard.
  destruct Hmodules as (Hstatus & Hflags & Hmemory & Htimer & Hstats & Hcontrol &
    Hnames & Hreferences & Hstacks & Hpending).
  pose proof (pending_mutex_consistency_task_reserve sg s.(TskState) s.(EventState)
    p invocation origin Hpending Hguard) as HpendingAfter.
  split; [exact Hprofile|]. split.
  - apply task_reserve_preserves_in_range; assumption.
  - split; [exact Hsched|]. split; [exact Hevents|]. split.
    + apply task_reserve_preserves_cross_module_consistency; assumption.
    + split; [exact Hidle|]. repeat (split; [assumption|]); exact HpendingAfter.
Qed.

Lemma UCOS2_task_rollback_preserves_validity : forall sg s p invocation,
  UCOS2_state_inv sg s ->
  task_rollback_guard s.(TskState) p invocation ->
  UCOS2_state_inv sg
    (replace_TskS (task_rollback_reservation s.(TskState) p) s).
Proof.
  intros sg s p invocation
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hmodules]]]]]] Hguard.
  destruct Hmodules as (Hstatus & Hflags & Hmemory & Htimer & Hstats & Hcontrol &
    Hnames & Hreferences & Hstacks & Hpending).
  pose proof (pending_mutex_consistency_task_rollback sg s.(TskState) s.(EventState)
    p invocation Hpending Hguard) as HpendingAfter.
  split; [exact Hprofile|]. split.
  - eapply task_rollback_preserves_in_range; eauto.
  - split; [exact Hsched|]. split; [exact Hevents|]. split.
    + eapply task_rollback_preserves_cross_module_consistency; eauto.
    + split; [exact Hidle|]. repeat (split; [assumption|]); exact HpendingAfter.
Qed.

(** Registering a fresh logical invocation changes no physical owner.  In
    contrast, reserve/rollback below require the actual priority-cell store. *)
Lemma UCOS2_inv_begin_task_invocation : forall sg s origin,
  task_invocation_origin_live s.(TskState) origin ->
  UCOS2_inv sg s |--
    UCOS2_inv sg (replace_TskS (task_begin_invocation origin s.(TskState)) s).
Proof.
  intros sg s origin Horigin; unfold UCOS2_inv; Intros.
  pose proof (UCOS2_begin_task_invocation_preserves_validity sg s origin H Horigin) as Hpost.
  assert (Hraw : UCOS2_raw_rep sg
    (replace_TskS (task_begin_invocation origin s.(TskState)) s) = UCOS2_raw_rep sg s)
    by (symmetry; apply UCOS2_raw_rep_task_map_frame; reflexivity).
  rewrite Hraw; entailer!.
Qed.

(** Focusing one priority-table cell retains every other public Task byte,
    the remaining table entries, Scheduler bytes and all other modules. *)
Definition UCOS2_raw_rep_missing_priority_table (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_public_storage_without_prio_tbl sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Lemma UCOS2_raw_rep_priority_table_equiv : forall sg s,
  UCOS2_raw_rep sg s --||--
    store_prio_tbl sg s.(TskState).(prioTbl) ** UCOS2_raw_rep_missing_priority_table sg s.
Proof.
  intros; unfold UCOS2_raw_rep, UCOS2_raw_rep_missing_priority_table, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched.
  rewrite task_public_storage_prio_tbl_equiv; split; entailer!.
Qed.

Lemma UCOS2_raw_rep_missing_priority_table_reserve_eq : forall sg s p invocation origin,
  UCOS2_raw_rep_missing_priority_table sg s = UCOS2_raw_rep_missing_priority_table sg
    (replace_TskS (task_reserve s.(TskState) p invocation origin) s).
Proof.
  intros; unfold UCOS2_raw_rep_missing_priority_table.
  rewrite (sched_raw_rep_change_task_index sg s.(TskState)
    (task_reserve s.(TskState) p invocation origin) s.(SchedState) eq_refl),
    (UCOS2_raw_rep_missing_task_storage_sched_task_map_frame sg s
      (task_reserve s.(TskState) p invocation origin) eq_refl eq_refl); reflexivity.
Qed.

Lemma UCOS2_raw_rep_missing_priority_table_rollback_eq : forall sg s p,
  UCOS2_raw_rep_missing_priority_table sg s = UCOS2_raw_rep_missing_priority_table sg
    (replace_TskS (task_rollback_reservation s.(TskState) p) s).
Proof.
  intros; unfold UCOS2_raw_rep_missing_priority_table.
  rewrite (sched_raw_rep_change_task_index sg s.(TskState)
    (task_rollback_reservation s.(TskState) p) s.(SchedState) eq_refl),
    (UCOS2_raw_rep_missing_task_storage_sched_task_map_frame sg s
      (task_rollback_reservation s.(TskState) p) eq_refl eq_refl); reflexivity.
Qed.

Lemma UCOS2_inv_split_priority_cell : forall sg s p,
  0 <= p < 64 -> UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s) &&
    ((sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |->
       prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) p) **
     store_prio_tbl_missing_i sg s.(TskState).(prioTbl) p **
     UCOS2_raw_rep_missing_priority_table sg s).
Proof.
  intros sg s p Hp; unfold UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv; Intros.
  sep_apply_l_atomic (store_prio_tbl_split_cell sg s.(TskState).(prioTbl) p Hp); entailer!.
Qed.

Lemma UCOS2_inv_merge_reserved_priority : forall sg s p invocation origin,
  UCOS2_state_inv sg s -> task_reserve_guard sg s.(TskState) p invocation origin ->
  (sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |-> 1 **
    store_prio_tbl_missing_i sg s.(TskState).(prioTbl) p **
    UCOS2_raw_rep_missing_priority_table sg s |--
  UCOS2_inv sg (replace_TskS (task_reserve s.(TskState) p invocation origin) s).
Proof.
  intros sg s p invocation origin Hvalid Hguard.
  pose proof (UCOS2_task_reserve_preserves_validity sg s p invocation origin Hvalid Hguard) as Hpost.
  assert (Hp : 0 <= p < 64).
  { pose proof (proj1 Hguard) as Hp; pose proof (proj1 (proj1 Hvalid)) as Hsg.
    unfold task_priority_in_range in Hp; unfold valid_stable_glob_vars in Hsg; intuition lia. }
  pose proof (store_prio_tbl_merge_updated_cell sg s.(TskState).(prioTbl) p PTReserved Hp) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv.
  rewrite <- UCOS2_raw_rep_missing_priority_table_reserve_eq; entailer!.
Qed.

Lemma UCOS2_inv_merge_rollback_priority : forall sg s p invocation,
  UCOS2_state_inv sg s -> task_rollback_guard s.(TskState) p invocation ->
  (sg.(g_OSTCBPrioTbl) + p * sizeof(PTR)) # Ptr |-> 0 **
    store_prio_tbl_missing_i sg s.(TskState).(prioTbl) p **
    UCOS2_raw_rep_missing_priority_table sg s |--
  UCOS2_inv sg (replace_TskS (task_rollback_reservation s.(TskState) p) s).
Proof.
  intros sg s p invocation Hvalid Hguard.
  pose proof (UCOS2_task_rollback_preserves_validity sg s p invocation Hvalid Hguard) as Hpost.
  assert (Hp : 0 <= p < 64).
  { pose proof (proj1 (proj2 Hvalid)) as Htasks.
    pose proof (proj1 (proj2 (proj2 (proj2 Htasks)))) as Hreservations.
    destruct Hguard as [entry [Hentry Hrest]].
    pose proof (proj1 (proj1 Hreservations p entry Hentry)) as Hp.
    pose proof (proj1 (proj1 Hvalid)) as Hsg.
    unfold task_priority_in_range in Hp; unfold valid_stable_glob_vars in Hsg; intuition lia. }
  pose proof (store_prio_tbl_merge_updated_cell sg s.(TskState).(prioTbl) p PTFree Hp) as Hmerge.
  cbn [prio_tbl_entry_to_addr] in Hmerge.
  sep_apply_l_atomic Hmerge.
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv.
  rewrite <- UCOS2_raw_rep_missing_priority_table_rollback_eq; entailer!.
Qed.

Lemma UCOS2_private_image_update_preserves_validity :
  forall sg s p entry allocation image,
    UCOS2_state_inv sg s ->
    s.(TskState).(taskLifecycle).(taskReservations) p = Some entry ->
    entry.(creationAllocation) = Some allocation ->
    UCOS2_state_inv sg (replace_TskS
      (task_update_private_image s.(TskState) p entry allocation image) s).
Proof.
  intros sg s p entry allocation image
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hmodules]]]]]] Hentry Ha.
  destruct Hmodules as (Hstatus & Hflags & Hmemory & Htimer & Hstats & Hcontrol &
    Hnames & Hreferences & Hstacks & Hpending).
  pose proof (pending_mutex_consistency_task_private_image sg s.(TskState) s.(EventState)
    p entry allocation image Hpending Hentry) as HpendingAfter.
  split; [exact Hprofile|]. split.
  - eapply task_update_private_image_preserves_in_range; eauto.
  - split; [exact Hsched|]. split; [exact Hevents|]. split.
    + eapply task_update_private_image_preserves_cross_module_consistency; eauto.
    + split; [exact Hidle|]. repeat (split; [assumption|]); exact HpendingAfter.
Qed.

Lemma UCOS2_task_detach_preserves_validity : forall sg s p entry tid rest image,
  UCOS2_state_inv sg s ->
  task_detach_guard s.(TskState) p entry tid rest image ->
  UCOS2_state_inv sg
    (replace_TskS (task_detach_head s.(TskState) p entry tid rest image) s).
Proof.
  intros sg s p entry tid rest image
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle Hmodules]]]]]] Hguard.
  destruct Hmodules as (Hstatus & Hflags & Hmemory & Htimer & Hstats & Hcontrol &
    Hnames & Hreferences & Hstacks & Hpending).
  pose proof (pending_mutex_consistency_task_detach sg s.(TskState) s.(EventState)
    p entry tid rest image Hpending Hguard) as HpendingAfter.
  split; [exact Hprofile|]. split.
  - eapply task_detach_preserves_in_range; eauto.
  - split; [exact Hsched|]. split; [exact Hevents|]. split.
    + eapply task_detach_preserves_cross_module_consistency; eauto.
    + split; [exact Hidle|]. repeat (split; [assumption|]); exact HpendingAfter.
Qed.

Lemma UCOS2_retire_invocation_preserves_validity : forall sg s invocation,
  UCOS2_state_inv sg s ->
  UCOS2_state_inv sg
    (replace_TskS (task_retire_invocation s.(TskState) invocation) s).
Proof. intros; exact H. Qed.

(** Private storage belongs to the invocation, outside this public heap.
    Its ghost image changes while every public byte is framed. *)
Lemma UCOS2_inv_update_private_image : forall sg s p entry allocation image,
  s.(TskState).(taskLifecycle).(taskReservations) p = Some entry ->
  entry.(creationAllocation) = Some allocation ->
  UCOS2_inv sg s |-- UCOS2_inv sg (replace_TskS
    (task_update_private_image s.(TskState) p entry allocation image) s).
Proof.
  intros sg s p entry allocation image Hentry Ha.
  unfold UCOS2_inv; Intros.
  pose proof (UCOS2_private_image_update_preserves_validity
    sg s p entry allocation image H Hentry Ha) as Hpost.
  assert (Hraw : UCOS2_raw_rep sg s = UCOS2_raw_rep sg (replace_TskS
    (task_update_private_image s.(TskState) p entry allocation image) s)).
  { pose proof (sched_raw_rep_change_task_index sg s.(TskState)
      (task_update_private_image s.(TskState) p entry allocation image)
      s.(SchedState) eq_refl) as Hsched.
    assert (Hevent : event_raw_rep sg s.(TskState) s.(EventState) =
      event_raw_rep sg
        (task_update_private_image s.(TskState) p entry allocation image) s.(EventState)).
    { apply event_raw_rep_change_task_index.
      apply event_wait_priority_agreement_encodes; intros eid e tid Hget Hin; reflexivity. }
    unfold UCOS2_raw_rep, UCOS2_raw_rep_missing_task_storage_sched, task_shared_rep.
    cbn [replace_TskS TskState SchedState EventState IntrState TickState].
    rewrite Hsched, Hevent; reflexivity. }
  rewrite <- Hraw; entailer!.
Qed.

Lemma UCOS2_task_commit_residual_frame : forall sg s p invocation node sched',
  event_in_range sg s.(TskState) s.(EventState) ->
  s.(TskState).(inUsedTaskStates) node.(taskID) = None ->
  UCOS2_raw_rep_missing_task_storage_sched sg s =
  UCOS2_raw_rep_missing_task_storage_sched sg
    (replace_SchedS sched' (replace_TskS (task_commit s.(TskState) p invocation node) s)).
Proof.
  intros sg s p invocation node sched' Hevent Hnone.
  unfold UCOS2_raw_rep_missing_task_storage_sched; simpl.
  rewrite (event_raw_rep_change_task_index sg s.(TskState)
    (task_commit s.(TskState) p invocation node) s.(EventState)).
  - reflexivity.
  - eapply event_task_commit_encoding_frame; eauto.
Qed.

Lemma task_commit_preserves_idle_tail : forall sg tasks p invocation node,
  task_in_range sg tasks -> task_commit_identity tasks p invocation node ->
  task_idle_tail sg tasks ->
  task_idle_tail sg (task_commit tasks p invocation node).
Proof.
  intros sg tasks p invocation node Htasks Hidentity
    [prefix [idle [old [Horder [Hold [Hidle Hprefix]]]]]].
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg tasks node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  destruct Hidentity as [entry [allocation [Hentry [Hinv [Ha [Hid [Hg Hp]]]]]]].
  destruct Htasks as [_ [Hactive [_ [Hres [_ [Hregistered _]]]]]].
  pose proof (proj1 Hres p entry Hentry) as [_ [Hreserved _]].
  assert (Hnodeprio : node.(curPrio) <> sg.(osLowestPrio)).
  { intro Heq; pose proof (Hregistered idle old Hold) as Hreg.
    replace (curPrio old) with p in Hreg by congruence.
    rewrite Hreserved in Hreg; discriminate. }
  assert (Hfresh : ~ In node.(taskID) prefix).
  { intro Hin; destruct Hactive as [_ [_ [_ [Hcover _]]]].
    assert (Hinall : In node.(taskID) tasks.(taskLifecycle).(taskActiveOrder)).
    { rewrite Horder; apply in_or_app; left; exact Hin. }
    destruct (proj1 (Hcover node.(taskID)) Hinall) as [t Ht]; congruence. }
  destruct (task_commit_transports_old_priority tasks p invocation node idle old Hnone Hold)
    as [new [Hnew Hnewprio]].
  exists (node.(taskID) :: prefix), idle, new; split.
  - simpl; rewrite Horder; reflexivity.
  - split; [exact Hnew|]. split; [congruence|].
    intros tid other Hin Hget; simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst tid; pose proof (proj1 (task_commit_publication_fields_eq tasks p invocation node)) as Hnode.
      rewrite Hnode in Hget; inversion Hget; subst other; exact Hnodeprio.
    + pose proof (task_commit_observation Z curPrio tasks p invocation node tid
        (fun _ _ _ => eq_refl)) as Hprio.
      rewrite Hget in Hprio; destruct (Z.eq_dec tid node.(taskID)); [subst; contradiction|].
      destruct (tasks.(inUsedTaskStates) tid) as [before|] eqn:Hbefore; [|discriminate].
      simpl in Hprio; injection Hprio as Hprio.
      rewrite Hprio; eapply Hprefix; eauto.
Qed.

Definition task_sched_commit_state (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (p : Priority) (invocation : nat) (node : TaskAbstractState)
  : UCOS2_Verify_State :=
  replace_SchedS (sched_commit_ready sg s.(TskState) s.(SchedState) p invocation node)
    (replace_TskS (task_commit s.(TskState) p invocation node) s).

Lemma UCOS2_task_commit_preserves_validity : forall sg s p invocation node,
  UCOS2_state_inv sg s ->
  task_commit_identity s.(TskState) p invocation node ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = nil ->
  node.(tcbFlagNode) = 0 ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name s.(NameState) node.(tcbTaskName) chars) ->
  UCOS2_state_inv sg (task_sched_commit_state sg s p invocation node).
Proof.
  intros sg s p invocation node [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]]
    Hidentity Hready Hptr Hmulti Hflag Hnewname.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  pose proof (pending_mutex_consistency_task_commit sg s.(TskState) s.(EventState)
    p invocation node Hpending Hidentity) as HpendingAfter.
  assert (HreferencesAfter : kernel_names_valid sg (task_sched_commit_state sg s p invocation node)).
  { intros name [[Henabled Href] | Hother].
    - destruct (task_commit_name_references s.(TskState) p invocation node name Href)
        as [Hbefore | Heq].
      + apply Hreferences; left; split; assumption.
      + subst name; apply Hnewname; exact Henabled.
    - apply Hreferences; right; exact Hother. }
  assert (HstacksAfter : parked_stacks_consistent
    (task_commit s.(TskState) p invocation node) s.(TskState).(parkedTaskStacks)).
  { apply task_commit_preserves_parked_stacks_consistency; [|exact Hstacks].
    eapply task_commit_stack_key_absent; eassumption. }
  assert (HbitsAfter : task_reserved_bits_clear sg
    (task_sched_commit_state sg s p invocation node).(TskState)).
  { apply task_commit_preserves_reserved_bits_clear; [exact Hstatus|].
    apply task_effectively_ready_reserved_bits_clear; exact Hready. }
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (task_private_excludes_public sg s.(TskState) node.(taskID) (proj1 Htasks) Hprivate)
    as [Hnone Hnotfree].
  pose proof (sched_commit_preserves_in_range sg s.(TskState) s.(SchedState)
    p invocation node Htasks Hidentity Hsched Hready) as HschedPost.
  split; [exact Hprofile|]. split.
  - apply task_commit_preserves_in_range; assumption.
  - split; [exact HschedPost|]. split.
    + apply task_commit_preserves_event_in_range; assumption.
    + split.
      * apply task_commit_preserves_cross_module_consistency; try assumption.
        -- apply task_effectively_ready_has_no_pending; exact Hready.
        -- reflexivity.
      * split.
        2: { split; [exact HbitsAfter|].
             repeat (split; [assumption|]); exact HpendingAfter. }
        intro Hrunning; apply task_commit_preserves_idle_tail; try assumption.
        apply Hidle; exact Hrunning.
Qed.

Lemma UCOS2_task_commit_merge_task_sched : forall sg s p invocation node,
  UCOS2_state_inv sg s ->
  task_commit_identity s.(TskState) p invocation node ->
  is_effectively_ready node.(stat) node.(dly) = true ->
  node.(eventPtr) = None -> node.(eventMultiWaitEvents) = nil ->
  node.(tcbFlagNode) = 0 ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name s.(NameState) node.(tcbTaskName) chars) ->
  let post := task_sched_commit_state sg s p invocation node in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s p invocation node Hvalid Hidentity Hready Hptr Hmulti Hflag Hnewname; cbv zeta.
  apply UCOS2_inv_merge_updated_task_storage_sched.
  - apply UCOS2_task_commit_preserves_validity; assumption.
  - apply UCOS2_task_commit_residual_frame.
    + exact (proj1 (proj2 (proj2 (proj2 Hvalid)))).
    + exact (proj1 (task_private_excludes_public sg s.(TskState) node.(taskID)
        (proj1 (proj1 (proj2 Hvalid)))
        (task_commit_identity_private s.(TskState) p invocation node Hidentity))).
Qed.

(* Pure closure facts separated from the source-total spatial
   representation.  Keeping this a Prop permits [&&] to attach it to the
   same heap without duplicating ownership. *)
Definition UCOS2_verification_slice_state_inv
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Prop :=
  verification_slice_task_validity sg s.(TskState) /\
  verification_slice_sched_in_range sg s.(TskState) s.(SchedState) /\
  verification_slice_event_in_range sg s.(TskState) s.(EventState) /\
  verification_slice_cross_module_consistency sg s.

(* Public task APIs which reject ISR calls are source-total over the ISR
   error arm, but their non-ISR state-changing arm starts at the stable task
   call boundary.  Keep this operation-family scenario separate from the
   permanent validity bundle: blocking code may temporarily leave the task
   boundary before scheduler selection. *)
Definition UCOS2_isr_or_task_call_boundary_prop
  (s : UCOS2_Verify_State) : Prop :=
  s.(IntrState).(intNesting) > 0 \/
  (s.(IntrState).(intNesting) <= 0 /\
   sched_task_call_boundary s.(TskState) s.(SchedState)).

(* The trailing [TT] is the explicit residual induced by the legacy global
   invariant's spatial [** coq_prop verification_slice_cross_module_consistency].  By
   [sepcon_prop_equiv] that pure conjunct exposes the spatial core together
   with an arbitrary frame; silently discarding that frame would be
   unsound. *)
Definition UCOS2_verification_slice_raw_rep
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_raw_rep sg s.(TskState) **
  verification_slice_sched_raw_rep sg s.(TskState) s.(SchedState) **
  verification_slice_event_raw_rep sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  TT.

(* Global ready-priority stage.  Task/event ownership represents the post
   state; scheduler bitmap/current cells represent the post state while the
   high-ready cache pair is still anchored in the entry state.  It preserves
   the same explicit legacy [TT] residual as [UCOS2_verification_slice_raw_rep]. *)
Definition UCOS2_verification_slice_raw_ready_prio_stage
  (sg : StableGlobVars)
  (entry post : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg post.(IntrState) **
  verification_slice_task_raw_rep sg post.(TskState) **
  verification_slice_sched_raw_ready_prio_stage
    sg entry.(SchedState) post.(SchedState) post.(TskState) **
  verification_slice_event_raw_rep sg post.(TskState) post.(EventState) **
  verification_slice_tick_inv sg post.(TickState) **
  TT.

(* Only the sound direction is automatic: a full invariant exposes its raw
   ownership and pure closure bundle on the same heap.  There is
   intentionally no unconditional raw-to-full theorem. *)
Lemma UCOS2_verification_slice_inv_split_raw_validity :
  forall sg s,
    UCOS2_verification_slice_inv sg s |--
      UCOS2_verification_slice_raw_rep sg s &&
      coq_prop (UCOS2_verification_slice_state_inv sg s).
Proof.
  intros sg s.
  unfold UCOS2_verification_slice_inv.
  sep_apply_l_atomic
    (verification_slice_task_inv_split_raw_validity sg s.(TskState)).
  pureIntros.
  sep_apply_l_atomic
    (verification_slice_sched_inv_split_raw_validity
      sg s.(TskState) s.(SchedState) H0).
  pureIntros.
  sep_apply_l_atomic
    (verification_slice_event_inv_split_raw_validity
      sg s.(TskState) s.(EventState) H0).
  pureIntros.
  unfold UCOS2_verification_slice_raw_rep, UCOS2_verification_slice_state_inv.
  entailer!.
Qed.

(* Stable task-context API boundary.  This wrapper strengthens a particular
   call-site assertion with the reusable scheduler protocol stage while
   leaving [UCOS2_verification_slice_inv] itself unchanged.  Blocking paths leave this
   wrapper through [sched_current_blocked_before_schedule] and recover it
   only after scheduler selection. *)
Definition UCOS2_verification_slice_task_call_boundary_inv
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  UCOS2_verification_slice_inv sg s &&
  coq_prop (sched_task_call_boundary s.(TskState) s.(SchedState)).

Lemma UCOS2_verification_slice_task_call_boundary_inv_to_verify_inv :
  forall sg s,
    UCOS2_verification_slice_task_call_boundary_inv sg s |-- UCOS2_verification_slice_inv sg s.
Proof.
  intros sg s.
  unfold UCOS2_verification_slice_task_call_boundary_inv.
  entailer!.
Qed.

Lemma UCOS2_verification_slice_task_call_boundary_inv_expose :
  forall sg s,
    UCOS2_verification_slice_task_call_boundary_inv sg s |--
    coq_prop (sched_task_call_boundary s.(TskState) s.(SchedState)).
Proof.
  intros sg s.
  unfold UCOS2_verification_slice_task_call_boundary_inv.
  entailer!.
Qed.

Lemma UCOS2_verification_slice_inv_add_task_call_boundary :
  forall sg s,
    sched_task_call_boundary s.(TskState) s.(SchedState) ->
    UCOS2_verification_slice_inv sg s |-- UCOS2_verification_slice_task_call_boundary_inv sg s.
Proof.
  intros sg s Hboundary.
  unfold UCOS2_verification_slice_task_call_boundary_inv.
  entailer!.
Qed.

Definition UCOS2_verification_slice_inv_no_int_nesting
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv sg s.(TskState) s.(EventState) **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Definition UCOS2_verification_slice_inv_focus_event_int
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_no_eid sg s.(TskState) s.(EventState) eid **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

(* Total public-event-type focus.  Unlike [verification_slice_event_inv_no_eid], this residual
   is valid for both live and free OS_EVENT slots and removes only the
   OSEventType byte. *)
Definition UCOS2_verification_slice_inv_no_event_type
  (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (eid : EventID) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  verification_slice_task_inv sg s.(TskState) **
  verification_slice_sched_inv sg s.(TskState) s.(SchedState) **
  verification_slice_event_inv_no_type_at sg s.(TskState) s.(EventState) eid **
  verification_slice_tick_inv sg s.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg s).

Lemma UCOS2_verification_slice_inv_split_event_type_total :
  forall sg s eid,
    valid_event_id sg eid ->
    UCOS2_verification_slice_inv sg s |--
      (event_addr sg eid + OSEventType_off) # UChar |->
        event_slot_type_value s.(EventState) eid **
      UCOS2_verification_slice_inv_no_event_type sg s eid.
Proof.
  intros sg s eid Heid.
  unfold UCOS2_verification_slice_inv, UCOS2_verification_slice_inv_no_event_type.
  sep_apply_l_atomic
    (verification_slice_event_inv_split_type_total
      sg s.(TskState) s.(EventState) eid Heid).
  entailer!.
Qed.

Lemma UCOS2_verification_slice_inv_merge_event_type_total :
  forall sg s eid,
    valid_event_id sg eid ->
    (event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value s.(EventState) eid **
    UCOS2_verification_slice_inv_no_event_type sg s eid |--
      UCOS2_verification_slice_inv sg s.
Proof.
  intros sg s eid Heid.
  unfold UCOS2_verification_slice_inv_no_event_type, UCOS2_verification_slice_inv.
  sep_apply_l_atomic
    (verification_slice_event_inv_merge_type_total
      sg s.(TskState) s.(EventState) eid Heid).
  entailer!.
Qed.

(* 缺一变体 *)
Definition UCOS2_verification_slice_inv_missing_usedtask (sg : StableGlobVars)
  (st : UCOS2_Verify_State) (tid : TaskID) (t : TaskAbstractState) : Assertion :=
  interrupt_inv sg st.(IntrState) **
  verification_slice_task_inv_missing_usedtask sg st.(TskState) tid t **
  verification_slice_sched_inv sg st.(TskState) st.(SchedState) **
  verification_slice_event_inv sg st.(TskState) st.(EventState) **
  verification_slice_tick_inv sg st.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg st).

Definition UCOS2_verification_slice_inv_missing_usedevent (sg : StableGlobVars)
  (st : UCOS2_Verify_State) (eid : EventID) (e : OSEventAbstractState) : Assertion :=
  interrupt_inv sg st.(IntrState) **
  verification_slice_task_inv sg st.(TskState) **
  verification_slice_sched_inv sg st.(TskState) st.(SchedState) **
  verification_slice_event_inv_missing_usedevent sg st.(TskState) st.(EventState) eid e **
  verification_slice_tick_inv sg st.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg st).

Definition UCOS2_verification_slice_inv_missing_priotbl (sg : StableGlobVars)
  (st : UCOS2_Verify_State) (p : Priority) : Assertion :=
  interrupt_inv sg st.(IntrState) **
  verification_slice_task_inv_missing_priotbl sg st.(TskState) p **
  verification_slice_sched_inv sg st.(TskState) st.(SchedState) **
  verification_slice_event_inv sg st.(TskState) st.(EventState) **
  verification_slice_tick_inv sg st.(TickState) **
  coq_prop (verification_slice_cross_module_consistency sg st).

(* Exact decompositions retain every global-invariant frame component. *)
Lemma UCOS2_verification_slice_inv_replace_TskS_split :
  forall sg st ms,
    UCOS2_verification_slice_inv sg (replace_TskS ms st) |--
    interrupt_inv sg st.(IntrState) **
    verification_slice_task_inv sg ms **
    verification_slice_sched_inv sg ms st.(SchedState) **
    verification_slice_event_inv sg ms st.(EventState) **
    verification_slice_tick_inv sg st.(TickState) **
    coq_prop (verification_slice_cross_module_consistency sg (replace_TskS ms st)).
Proof.
  intros sg st ms.
  unfold UCOS2_verification_slice_inv.
  rewrite replace_TskS_other_Intr.
  rewrite replace_TskS_TskState.
  rewrite replace_TskS_other_Sched.
  rewrite replace_TskS_other_Event.
  rewrite replace_TskS_other_Tick.
  entailer!.
Qed.

Lemma UCOS2_verification_slice_inv_replace_EventS_split :
  forall sg st ms,
    UCOS2_verification_slice_inv sg (replace_EventS ms st) |--
    interrupt_inv sg st.(IntrState) **
    verification_slice_task_inv sg st.(TskState) **
    verification_slice_sched_inv sg st.(TskState) st.(SchedState) **
    verification_slice_event_inv sg st.(TskState) ms **
    verification_slice_tick_inv sg st.(TickState) **
    coq_prop (verification_slice_cross_module_consistency sg (replace_EventS ms st)).
Proof.
  intros sg st ms.
  unfold UCOS2_verification_slice_inv.
  rewrite replace_EventS_other_Intr.
  rewrite replace_EventS_other_Tsk.
  rewrite replace_EventS_other_Sched.
  rewrite replace_EventS_EventState.
  rewrite replace_EventS_other_Tick.
  entailer!.
Qed.

Require Import Coq.micromega.Lia.
Lemma UCOS2_isr_or_task_call_boundary_non_isr :
  forall s,
    s.(IntrState).(intNesting) <= 0 ->
    UCOS2_isr_or_task_call_boundary_prop s ->
    sched_task_call_boundary s.(TskState) s.(SchedState).
Proof.
  intros s Hnonisr Hscenario.
  unfold UCOS2_isr_or_task_call_boundary_prop in Hscenario.
  destruct Hscenario as [Hisr | [_ Hboundary]].
  - lia.
  - exact Hboundary.
Qed.

Lemma unsigned_last_nbits_32_nonpositive_uchar__focus_and_pure :
  forall x,
    0 <= x <= 255 ->
    unsigned_last_nbits x 32 <= 0 ->
    x <= 0.
Proof.
  intros x Hrange Hbits.
  rewrite unsigned_last_nbits_eq in Hbits.
  - lia.
  - split; [lia | change (x < 4294967296); lia].
Qed.
Lemma verification_slice_used_complete_task_split_prio__focus_and_pure :
  forall sg p tid t,
    verification_slice_used_complete_task sg p tid t |--
      (p + verification_slice_OSTCBPrio_off) # UChar |-> curPrio t **
      used_task_no_prio sg p tid t.
Proof.
  intros.
  unfold verification_slice_used_complete_task, used_task_no_prio.
  entailer!.
Qed.
Lemma verification_slice_sched_inv_split_tcb_cur__focus_and_pure :
  forall sg tskSt s,
    verification_slice_sched_inv sg tskSt s |--
      sg.(g_OSTCBCur) # Ptr |->
        (match s.(curTaskID) with
         | Some tid => verification_slice_tcb_addr sg tid
         | None => 0
         end) **
      verification_slice_sched_inv_no_tcb_cur sg tskSt s.
Proof.
  intros.
  unfold verification_slice_sched_inv, verification_slice_store_sched_state,
    verification_slice_sched_inv_no_tcb_cur, verification_slice_store_sched_state_no_tcb_cur.
  entailer!.
Qed.
Lemma verification_slice_task_inv_split_prio__focus_and_pure :
  forall sg st tid t,
    inUsedTaskStates st tid = Some t ->
    verification_slice_task_inv sg st |--
      (verification_slice_tcb_addr sg tid + verification_slice_OSTCBPrio_off) # UChar |-> curPrio t **
      used_task_no_prio sg (verification_slice_tcb_addr sg tid) tid t **
      verification_slice_task_inv_no_tid sg st tid.
Proof.
  intros sg st tid t Hmap.
  unfold verification_slice_task_inv, verification_slice_store_used_task_map.
  pureIntros.
  sepcon_lift (store_map
    (fun tid0 t0 => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    (inUsedTaskStates st)).
  sep_apply_l_atomic (store_map_split
    (fun tid0 t0 => verification_slice_used_complete_task sg (verification_slice_tcb_addr sg tid0) tid0 t0)
    tid t (inUsedTaskStates st) Hmap).
  sep_apply_l_atomic
    (verification_slice_used_complete_task_split_prio__focus_and_pure
       sg (verification_slice_tcb_addr sg tid) tid t).
  unfold verification_slice_task_inv_no_tid.
  entailer!.
Qed.
Lemma verification_slice_task_inv_split_prio_at__focus_and_pure :
  forall sg st tid t tcbcur tcbprio prio_addr,
    inUsedTaskStates st tid = Some t ->
    tcbcur = verification_slice_tcb_addr sg tid ->
    tcbprio = curPrio t ->
    prio_addr = tcbcur + verification_slice_OSTCBPrio_off ->
    verification_slice_task_inv sg st |--
      prio_addr # UChar |-> tcbprio **
      used_task_no_prio sg tcbcur tid t **
      verification_slice_task_inv_no_tid sg st tid.
Proof.
  intros sg st tid t tcbcur tcbprio prio_addr
    Hmap Htcb Hprio Haddr.
  subst tcbcur.
  subst tcbprio.
  subst prio_addr.
  apply verification_slice_task_inv_split_prio__focus_and_pure; assumption.
Qed.
Lemma verification_slice_sched_inv_split_tcb_cur_at__focus_and_pure :
  forall sg tskSt s tcb_addr_cell tcbcur,
    tcb_addr_cell = sg.(g_OSTCBCur) ->
    tcbcur =
      (match s.(curTaskID) with
       | Some tid => verification_slice_tcb_addr sg tid
       | None => 0
       end) ->
    verification_slice_sched_inv sg tskSt s |--
      tcb_addr_cell # Ptr |-> tcbcur **
      verification_slice_sched_inv_no_tcb_cur sg tskSt s.
Proof.
  intros sg tskSt s tcb_addr_cell tcbcur Haddr Hsnapshot.
  subst tcb_addr_cell.
  subst tcbcur.
  apply verification_slice_sched_inv_split_tcb_cur__focus_and_pure.
Qed.

(** Source transformers and guards are defined before, and independently of,
    their certificates.  In particular no action tests post-state validity.
    Retire is a represented action, not an impossible environment step. *)
Inductive TaskLifecycleAction : Type :=
| TaskDetachFreeHead (priority : Priority) (entry : TaskCreationEntry)
    (slot : TaskID) (rest : list TaskID) (image : TCBLayoutImage)
| TaskWritePrivateImage (priority : Priority) (entry : TaskCreationEntry)
    (allocation : TaskPrivateAllocation) (image : TCBLayoutImage)
| TaskPublish (priority : Priority) (invocation : nat) (node : TaskAbstractState)
| TaskRetireInvocation (invocation : nat).

Definition task_lifecycle_action_actor (action : TaskLifecycleAction) : option nat :=
  match action with
  | TaskDetachFreeHead _ entry _ _ _ | TaskWritePrivateImage _ entry _ _ =>
      Some entry.(creationInvocation)
  | TaskPublish _ invocation _ => Some invocation
  | TaskRetireInvocation _ => None
  end.

Definition task_lifecycle_action_stops (action : TaskLifecycleAction) (observer : nat) : bool :=
  match action with TaskRetireInvocation invocation => Nat.eqb invocation observer | _ => false end.

Definition task_lifecycle_action_guard (sg : StableGlobVars)
  (action : TaskLifecycleAction) (s : UCOS2_Verify_State) : Prop :=
  match action with
  | TaskDetachFreeHead p entry slot rest image =>
      task_detach_guard s.(TskState) p entry slot rest image
  | TaskWritePrivateImage p entry allocation _ =>
      s.(TskState).(taskLifecycle).(taskReservations) p = Some entry /\
      entry.(creationAllocation) = Some allocation
  | TaskPublish p invocation node =>
      task_commit_identity s.(TskState) p invocation node /\
      is_effectively_ready node.(stat) node.(dly) = true /\
      node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = nil /\
      node.(tcbFlagNode) = 0
  | TaskRetireInvocation _ => True
  end.

(** This is the caller's lifetime obligation for the pointer being
    published, not a new C guard or a test of post-state validity. The
    source transformer and its physical checks above remain unchanged. *)
Definition task_lifecycle_name_protocol (sg : StableGlobVars)
  (action : TaskLifecycleAction) (s : UCOS2_Verify_State) : Prop :=
  match action with
  | TaskPublish _ _ node => sg.(osKernelConfig).(cfgTaskNames) = true ->
      exists chars, readable_name s.(NameState) node.(tcbTaskName) chars
  | _ => True
  end.

Definition task_lifecycle_action_state (sg : StableGlobVars)
  (action : TaskLifecycleAction) (s : UCOS2_Verify_State) : UCOS2_Verify_State :=
  match action with
  | TaskDetachFreeHead p entry slot rest image =>
      replace_TskS (task_detach_head s.(TskState) p entry slot rest image) s
  | TaskWritePrivateImage p entry allocation image =>
      replace_TskS (task_update_private_image s.(TskState) p entry allocation image) s
  | TaskPublish p invocation node => task_sched_commit_state sg s p invocation node
  | TaskRetireInvocation invocation => replace_TskS (task_retire_invocation s.(TskState) invocation) s
  end.

(** An extension client declares its source relation, acting invocation, and
    which saved continuations its source step retires.  The certificate is a
    separate proof obligation.  There is deliberately no all-kernel instance:
    a Mutex/Queue/Tick/Delete source binding must discharge its own fields. *)
Record KernelClientAction : Type := {
  (** Task execution/creation invocation and Event allocation invocation
      are distinct namespaces.  These are action parameters, not new OS
      fields; an actual call binding supplies their source identities. *)
  kernel_client_actor : option nat;
  kernel_client_event_actor : option nat;
  kernel_client_stops : nat -> bool;
  kernel_client_step : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop;
}.

Record KernelClientCertificate (action : KernelClientAction) : Prop := {
  kernel_client_preserves_validity : forall sg before after,
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    UCOS2_state_inv sg after;
  kernel_client_frames_creation : forall sg before after observer,
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    kernel_client_actor action <> Some observer ->
    task_creation_frame observer before.(TskState) after.(TskState);
  kernel_client_preserves_continuation : forall sg before after observer origin,
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    kernel_client_stops action observer = false ->
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin;
  kernel_client_frames_event_creation : forall sg before after observer,
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    kernel_client_event_actor action <> Some observer ->
    event_creation_frame observer before.(EventState) after.(EventState);
}.

Definition task_creation_client (action : TaskLifecycleAction) : KernelClientAction :=
  {| kernel_client_actor := task_lifecycle_action_actor action;
     kernel_client_event_actor := None;
     kernel_client_stops := task_lifecycle_action_stops action;
     kernel_client_step := fun sg before after =>
       task_lifecycle_action_guard sg action before /\
       task_lifecycle_name_protocol sg action before /\
       after = task_lifecycle_action_state sg action before |}.

Lemma task_creation_client_certificate : forall action,
  KernelClientCertificate (task_creation_client action).
Proof.
  intro action; constructor.
  - intros sg before after Hvalid [Hguard [Hname ->]]; destruct action; simpl in Hguard, Hname |- *.
    + eapply UCOS2_task_detach_preserves_validity; eauto.
    + destruct Hguard; eapply UCOS2_private_image_update_preserves_validity; eauto.
    + destruct Hguard as [Hidentity [Hready [Hptr [Hmulti Hflag]]]].
      eapply UCOS2_task_commit_preserves_validity; eauto.
    + apply UCOS2_retire_invocation_preserves_validity; exact Hvalid.
  - intros sg before after observer Hvalid [Hguard [Hname ->]] Hforeign.
    destruct action; simpl in Hguard, Hforeign |- *.
    + apply task_detach_frames_other_invocation.
      * exact (proj1 (proj2 Hguard)).
      * congruence.
    + apply task_private_image_frames_other_invocation.
      * exact (proj1 Hguard).
      * congruence.
    + apply task_commit_frames_other_invocation; [exact (proj1 Hguard)|congruence].
    + reflexivity.
  - intros sg before after observer origin Hvalid [Hguard [Hname ->]] Hresume Hactive.
    destruct action; simpl in Hguard, Hresume |- *.
    + exact Hactive.
    + exact Hactive.
    + eapply task_commit_preserves_invocation_active.
      * exact (proj1 (proj2 Hvalid)).
      * exact (proj1 Hguard).
      * exact Hactive.
    + apply Nat.eqb_neq in Hresume.
      destruct Hactive as [Hinv [Hnotretired Hlive]].
      split; [exact Hinv|]. split; [|exact Hlive].
      simpl; destruct (Nat.eq_dec observer invocation); congruence.
  - intros sg before after observer Hvalid [Hguard [Hname ->]] Hforeign.
    destruct action; reflexivity.
Qed.

(** The Boolean is a source-continuation outcome, not a validity filter on
    the endpoint.  A stopped trace and all its subsequent environment actions
    are still represented.  Only the normal-return client theorem requires
    the original continuation not to have stopped. *)
Inductive kernel_client_resource_trace (clients : KernelClientAction -> Prop)
  (sg : StableGlobVars) (observer : nat) (event_observer : option nat)
  : UCOS2_Verify_State -> bool -> UCOS2_Verify_State -> Prop :=
| KernelClientTraceNil : forall s, kernel_client_resource_trace clients sg observer event_observer s false s
| KernelClientTraceStep : forall action before middle after stopped,
    clients action -> kernel_client_actor action <> Some observer ->
    (forall invocation, event_observer = Some invocation -> kernel_client_event_actor action <> Some invocation) ->
    kernel_client_step action sg before middle ->
    kernel_client_resource_trace clients sg observer event_observer middle stopped after ->
    kernel_client_resource_trace clients sg observer event_observer before
      (orb (kernel_client_stops action observer) stopped) after.

(** Existing Task-only clients observe no Event allocation.  Adding an
    Event observer refines the SAME source trace, rather than introducing
    a second environment relation or identifying the two nat namespaces. *)
Definition kernel_client_trace (clients : KernelClientAction -> Prop) (sg : StableGlobVars) (observer : nat) :=
  kernel_client_resource_trace clients sg observer None.

Lemma kernel_client_resource_trace_transports_resources : forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before ->
  UCOS2_state_inv sg after /\
  task_creation_frame observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation before.(EventState) after.(EventState)) /\
  (stopped = false -> forall origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros clients sg observer event_observer before stopped after Hcert Htrace.
  induction Htrace as [s|action before middle after stopped Hin Hforeign HeventForeign Hstep Htail IH];
    intro Hvalid.
  - split; [exact Hvalid|]. split; [reflexivity|]. split; [intros; reflexivity|auto].
  - specialize (Hcert action Hin) as Haction.
    pose proof (kernel_client_preserves_validity action Haction sg before middle Hvalid Hstep)
      as Hmiddle.
    destruct (IH Hmiddle) as [Hafter [Hframe [HeventFrame Hresume]]].
    split; [exact Hafter|]. split.
    + unfold task_creation_frame in *; rewrite Hframe.
      exact (kernel_client_frames_creation action Haction sg before middle observer
        Hvalid Hstep Hforeign).
    + split.
      * intros invocation Hobserver; unfold event_creation_frame in *.
        rewrite (HeventFrame invocation Hobserver).
        exact (kernel_client_frames_event_creation action Haction sg before middle invocation
          Hvalid Hstep (HeventForeign invocation Hobserver)).
      * intro Hnormal; apply orb_false_iff in Hnormal; destruct Hnormal as [Hfirst Hrest].
        intros origin Hactive; apply (Hresume Hrest origin).
        exact (kernel_client_preserves_continuation action Haction sg before middle observer origin
          Hvalid Hstep Hfirst Hactive).
Qed.

Lemma kernel_client_trace_transports_resources : forall clients sg observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  kernel_client_trace clients sg observer before stopped after ->
  UCOS2_state_inv sg before ->
  UCOS2_state_inv sg after /\
  task_creation_frame observer before.(TskState) after.(TskState) /\
  (stopped = false -> forall origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros clients sg observer before stopped after Hcert Htrace Hvalid.
  destruct (kernel_client_resource_trace_transports_resources clients sg observer None before stopped after
    Hcert Htrace Hvalid) as [Hpost [Htask [_ Hresume]]].
  split; [exact Hpost|]; split; assumption.
Qed.

Lemma kernel_client_resource_trace_trans : forall clients sg observer event_observer
  before stopped1 middle stopped2 after,
  kernel_client_resource_trace clients sg observer event_observer before stopped1 middle ->
  kernel_client_resource_trace clients sg observer event_observer middle stopped2 after ->
  kernel_client_resource_trace clients sg observer event_observer before (orb stopped1 stopped2) after.
Proof.
  intros clients sg observer event_observer before stopped1 middle stopped2 after Hleft Hright.
  induction Hleft.
  - exact Hright.
  - rewrite <- Bool.orb_assoc; econstructor; eauto.
Qed.

(** A resumption cut groups a foreign Timer creation through its
    publication. The raw client trace above still represents internal
    allocations, stopped continuations and intermediate states. This second
    trace records the Timer source segments completed before another caller
    executes again; it is not a test of endpoint validity or image equality.

    TimerPublicCreate is Alloc followed by initialization/publication before
    Unlock. Other Timer writes are Link, Unlink, Release, Complete or time
    advancement. Start/Stop/Del/service composition is proved in
    timer_execution. Non-Timer source actions use the unchanged segment.
    A source embedding must supply these constructors, as it already supplies
    the client action and saved-continuation binding. No new certificate
    field or platform axiom asserts the desired storage property. *)
Inductive kernel_resumption_resource_trace (clients : KernelClientAction -> Prop)
  (sg : StableGlobVars) (observer : nat) (event_observer : option nat)
  : UCOS2_Verify_State -> bool -> UCOS2_Verify_State -> Prop :=
| KernelResumptionTraceNil : forall s,
    kernel_resumption_resource_trace clients sg observer event_observer s false s
| KernelResumptionTraceStep : forall action before middle after stopped,
    clients action -> kernel_client_actor action <> Some observer ->
    (forall invocation, event_observer = Some invocation ->
      kernel_client_event_actor action <> Some invocation) ->
    kernel_client_step action sg before middle ->
    timer_public_trace sg before.(TimerState) middle.(TimerState) ->
    kernel_resumption_resource_trace clients sg observer event_observer middle stopped after ->
    kernel_resumption_resource_trace clients sg observer event_observer before
      (orb (kernel_client_stops action observer) stopped) after
| KernelResumptionTraceSegment : forall before stopped1 middle stopped2 after,
    kernel_client_resource_trace clients sg observer event_observer before stopped1 middle ->
    timer_public_trace sg before.(TimerState) middle.(TimerState) ->
    kernel_resumption_resource_trace clients sg observer event_observer middle stopped2 after ->
    kernel_resumption_resource_trace clients sg observer event_observer before
      (orb stopped1 stopped2) after.

Definition kernel_resumption_trace (clients : KernelClientAction -> Prop)
  (sg : StableGlobVars) (observer : nat) :=
  kernel_resumption_resource_trace clients sg observer None.

Lemma kernel_resumption_resource_trace_erases :
  forall clients sg observer event_observer before stopped after,
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after.
Proof.
  intros clients sg observer event_observer before stopped after Htrace; induction Htrace.
  - constructor.
  - econstructor; eassumption.
  - eapply kernel_client_resource_trace_trans; eassumption.
Qed.

Lemma kernel_resumption_resource_trace_timer_projection :
  forall clients sg observer event_observer before stopped after,
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros clients sg observer event_observer before stopped after Htrace; induction Htrace.
  - constructor.
  - eapply timer_public_trace_trans; eassumption.
  - eapply timer_public_trace_trans; eassumption.
Qed.

Lemma kernel_resumption_trace_erases : forall clients sg observer before stopped after,
  kernel_resumption_trace clients sg observer before stopped after ->
  kernel_client_trace clients sg observer before stopped after.
Proof.
  intros; eapply kernel_resumption_resource_trace_erases; exact H.
Qed.

Lemma kernel_resumption_trace_timer_projection : forall clients sg observer before stopped after,
  kernel_resumption_trace clients sg observer before stopped after ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof.
  intros; eapply kernel_resumption_resource_trace_timer_projection; exact H.
Qed.

(** Actual non-Timer clients do not need a second, assumed preservation
    certificate. Their source equation transports the old trace into the
    resumption trace. This includes task reservation/private writes,
    publication and retirement, which need not be atomic as a whole. *)
Lemma kernel_client_trace_timer_unchanged_resumption :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action -> KernelClientCertificate action) ->
  (forall action initial final,
    clients action -> UCOS2_state_inv sg initial ->
    kernel_client_step action sg initial final ->
    final.(TimerState) = initial.(TimerState)) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after.
Proof.
  intros clients sg observer event_observer before stopped after Hcert Hframe Htrace.
  induction Htrace as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intro Hvalid.
  - constructor.
  - eapply KernelResumptionTraceStep; try eassumption.
    + rewrite (Hframe action before middle Hin Hvalid Hstep); constructor.
    + apply IH; exact (kernel_client_preserves_validity action (Hcert action Hin)
        sg before middle Hvalid Hstep).
Qed.

Lemma task_creation_client_timer_state_eq : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  after.(TimerState) = before.(TimerState).
Proof.
  intros action sg before after [_ [_ ->]]; destruct action; reflexivity.
Qed.

(** The assertion handles are logical CSL region handles, indexed by the
    original invocation.  They are not an ARM masking axiom.  The generic
    save/restore wrapper must link these handles and its source trace to the
    platform's saved continuation.  No concrete embedding is declared here. *)
Record CriticalRegionResources : Type := {
  critical_region_outside_without_running :
    StableGlobVars -> nat -> UCOS2_Verify_State -> Assertion;
  (** The outside handle is the physical kernel complement with the
      OSRunning cell removed.  This is the representation bridge used by
      Save/Restore callers; it is a contract field, not a theorem that an
      ARM/BSP implementation is proved here.  Keeping the bridge indexed by
      the observed state prevents a caller from manufacturing a frame from
      a ghost state or from silently reusing a stale snapshot. *)
  critical_region_outside_without_running_rep :
    forall sg invocation s,
      critical_region_outside_without_running sg invocation s --||--
      UCOS2_raw_rep_missing_running sg s;
  critical_region_inside : StableGlobVars -> nat -> UCOS2_Verify_State -> Assertion;
  critical_region_clients : KernelClientAction -> Prop;
  critical_region_client_certificates : forall action,
    critical_region_clients action -> KernelClientCertificate action;
  (** Name pointers are shared bytes.  The critical-region client contract
      therefore states explicitly that its registered environment steps do
      not replace the NameState projection.  This is a frame property of the
      selected client family, not a claim that arbitrary ISR/platform code is
      harmless. *)
  critical_region_client_name_frame : forall action,
    critical_region_clients action ->
    forall sg before after,
      kernel_client_step action sg before after ->
      before.(NameState) = after.(NameState);
}.

(** A protected call owns both the current IRQ/FIQ-masked execution
    resource and the separately saved return value.  A saved word alone
    does not describe the current mask.  This is the common CPU/CSL
    resource bundle used by task and ISR Save/Restore specializations;
    its components are existing platform resources, not new axioms. *)
Definition critical_region_masked (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (entry : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin 192 **
  interrupt_platform_saved platform (save_token saved invocation origin) **
  critical_region_inside critical sg invocation entry.

(** One closed entry for BOTH ordinary acquisition and source observation.
    The observation view is its actual spatial decomposition, not another
    independently supplied handle.  In particular the residual projection
    alone is NEVER a valid precondition for acquiring the whole kernel.

    This packages the already explicit observation-loan CPU/CSL contract;
    it does not prove a platform implementation, give an unmasked heap
    opening rule, or assert additional environment stability.  Creation of
    this view must receive the real byte (e.g. from a masked full invariant
    before the contracted Restore), not manufacture it from ghost state. *)
Definition critical_region_outside (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0) **
  critical_region_outside_without_running critical sg invocation s.

Lemma critical_region_outside_split_running : forall critical sg invocation s,
  critical_region_outside critical sg invocation s --||--
    (sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0) **
     critical_region_outside_without_running critical sg invocation s).
Proof. intros; split; reflexivity. Qed.

(** A regression property of the interface, not a way to discharge a C
    branch: ordinary acquisition cannot coexist with a separately framed
    observation at the same address, regardless of either state's index. *)
Lemma critical_region_outside_excludes_running_loan : forall critical sg invocation s byte,
  sg.(g_OSRunning) # UChar |-> byte **
  critical_region_outside critical sg invocation s |-- coq_prop False.
Proof.
  intros; unfold critical_region_outside, store_uchar; pureIntros.
  sep_apply_l_atomic (dup_store_byte sg.(g_OSRunning) byte
    (if s.(SchedState).(isRunning) then 1 else 0)); entailer!.
Qed.

Definition critical_region_interval (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before after : UCOS2_Verify_State) : Prop :=
  kernel_resumption_trace critical.(critical_region_clients) sg invocation before false after.

Definition critical_region_event_interval (critical : CriticalRegionResources)
  (sg : StableGlobVars) (task_invocation event_invocation : nat) (before after : UCOS2_Verify_State) : Prop :=
  kernel_resumption_resource_trace critical.(critical_region_clients) sg task_invocation
    (Some event_invocation) before false after.

Lemma critical_region_interval_raw_trace : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  kernel_client_trace critical.(critical_region_clients) sg invocation before false after.
Proof. intros; apply kernel_resumption_trace_erases; exact H. Qed.

Lemma kernel_client_resource_trace_preserves_name_state :
  forall clients sg observer event_observer before stopped after,
  (forall action, clients action ->
    forall sg0 before0 after0,
      kernel_client_step action sg0 before0 after0 ->
      before0.(NameState) = after0.(NameState)) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  before.(NameState) = after.(NameState).
Proof.
  intros clients sg observer event_observer before stopped after Hframe Htrace.
  induction Htrace as [s|action before middle after stopped Hin Hforeign HeventForeign
    Hstep Htail IH].
  - reflexivity.
  - rewrite (Hframe action Hin sg before middle Hstep).
    exact IH.
Qed.

Lemma critical_region_interval_preserves_name_state :
  forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  before.(NameState) = after.(NameState).
Proof.
  intros critical sg invocation before after Hinterval.
  apply kernel_client_resource_trace_preserves_name_state
    with (clients := critical.(critical_region_clients))
         (sg := sg) (observer := invocation) (event_observer := None)
         (before := before) (stopped := false) (after := after).
  - intros action Hclient sg0 before0 after0 Hstep.
    eapply critical_region_client_name_frame; eassumption.
  - apply critical_region_interval_raw_trace; exact Hinterval.
Qed.

Lemma critical_region_event_interval_raw_trace :
  forall critical sg task_invocation event_invocation before after,
  critical_region_event_interval critical sg task_invocation event_invocation before after ->
  kernel_client_resource_trace critical.(critical_region_clients) sg task_invocation
    (Some event_invocation) before false after.
Proof. intros; apply kernel_resumption_resource_trace_erases; exact H. Qed.

Lemma critical_region_interval_timer_public_trace : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  timer_public_trace sg before.(TimerState) after.(TimerState).
Proof. intros; eapply kernel_resumption_trace_timer_projection; exact H. Qed.

Lemma critical_region_event_interval_transports_resources :
  forall critical sg task_invocation event_invocation before after,
  critical_region_event_interval critical sg task_invocation event_invocation before after ->
  UCOS2_state_inv sg before ->
  UCOS2_state_inv sg after /\
  task_creation_frame task_invocation before.(TskState) after.(TskState) /\
  event_creation_frame event_invocation before.(EventState) after.(EventState) /\
  (forall origin, task_invocation_active before.(TskState) task_invocation origin ->
    task_invocation_active after.(TskState) task_invocation origin).
Proof.
  intros critical sg task_invocation event_invocation before after Htrace Hvalid.
  apply critical_region_event_interval_raw_trace in Htrace.
  destruct (kernel_client_resource_trace_transports_resources _ _ _ _ _ _ _
    critical.(critical_region_client_certificates) Htrace Hvalid) as [Hpost [Htask [Hevent Hresume]]].
  split; [exact Hpost|]; split; [exact Htask|]; split.
  - apply Hevent; reflexivity.
  - apply Hresume; reflexivity.
Qed.

Lemma critical_region_interval_transports_resources : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before ->
  UCOS2_state_inv sg after /\
  task_creation_frame invocation before.(TskState) after.(TskState) /\
  (forall origin, task_invocation_active before.(TskState) invocation origin ->
    task_invocation_active after.(TskState) invocation origin).
Proof.
  intros critical sg invocation before after Htrace Hvalid.
  apply critical_region_interval_raw_trace in Htrace.
  destruct (kernel_client_trace_transports_resources _ _ _ _ _ _
    critical.(critical_region_client_certificates) Htrace Hvalid) as [Hpost [Hframe Hresume]].
  split; [exact Hpost|]. split; [exact Hframe|]. apply Hresume; reflexivity.
Qed.

Lemma critical_region_interval_open_invariant : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before ->
  UCOS2_raw_rep sg after |-- UCOS2_inv sg after.
Proof.
  intros; pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before after H H0)) as Hvalid.
  unfold UCOS2_inv; entailer!.
Qed.

(** An unbounded family: future invocation numbers need not be enumerated in
    a finite list when the region is created.  Other source families can be
    included only with their independently proved certificates. *)
Definition task_creation_client_family (client : KernelClientAction) : Prop :=
  exists action, client = task_creation_client action.

Lemma task_creation_client_family_certificates : forall client,
  task_creation_client_family client -> KernelClientCertificate client.
Proof. intros client [action ->]; apply task_creation_client_certificate. Qed.

Lemma kernel_client_trace_represents_retirement : forall sg invocation s,
  kernel_client_trace task_creation_client_family sg invocation s true
    (replace_TskS (task_retire_invocation s.(TskState) invocation) s).
Proof.
  intros; replace true with (orb (kernel_client_stops
    (task_creation_client (TaskRetireInvocation invocation)) invocation) false)
    by (simpl; rewrite Nat.eqb_refl; reflexivity).
  eapply KernelClientTraceStep with
    (action := task_creation_client (TaskRetireInvocation invocation)).
  - exists (TaskRetireInvocation invocation); reflexivity.
  - discriminate.
  - intros other Hnone; discriminate.
  - split; [exact I|]. split; [exact I|reflexivity].
  - constructor.
Qed.

Lemma task_sched_commit_after_private_image_eq :
  forall sg s p entry allocation image invocation node,
  task_sched_commit_state sg
    (replace_TskS (task_update_private_image s.(TskState) p entry allocation image) s)
    p invocation node = task_sched_commit_state sg s p invocation node.
Proof.
  intros; unfold task_sched_commit_state, sched_commit_ready.
  cbn [replace_TskS TskState SchedState].
  rewrite task_commit_after_private_image_eq.
  destruct s; reflexivity.
Qed.

(** Modular checkpoint after Misc/Rdy/TCB/Event/Flag/Mem/Q initialization,
    before the first system TaskCreate. Timer memory still has its initial
    BSS representation: OSTmr_Init is called later by the actual OSInit.
    Separate name pointers avoid assuming compiler string-literal pooling.
    This state constructor is not a proof of the C initialization loops. *)
Definition UCOS2_boot_state (sg : StableGlobVars)
  (task_name flag_name memory_name : addr) (names : NameResourceState) : UCOS2_Verify_State :=
  {| IntrState := {| intNesting := 0; lockNesting := 0 |};
     TskState := task_boot sg task_name; SchedState := sched_boot;
     EventState := initial_event_abstract_state sg;
     TickState := {| ostime := 0; tickStepState := 0 |};
     FlagState := if sg.(osKernelConfig).(cfgFlagEnabled) then flag_initial sg flag_name else flag_disabled;
     MemoryState := if sg.(osKernelConfig).(cfgMemoryEnabled) then memory_initial sg memory_name else memory_disabled;
     TimerState := timer_uninitialized; StatsState := statistics_initial;
     ControlState := kernel_control_initial sg.(osKernelConfig); NameState := names |}.

Lemma UCOS2_boot_cross_module_consistency : forall sg task_name flag_name memory_name names,
  cross_module_consistency sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros sg task_name flag_name memory_name names; split.
  - split; [intros p entry H; discriminate|]. split.
    + intros p Hrange [mid [e [m [H _]]]]; discriminate.
    + intros tid t H; discriminate.
  - split; [intros mid e m owner H; discriminate|]. split.
    + unfold event_wait_object_consistency,
        task_event_reference_backlink_consistency, task_event_reference_closure.
      repeat split; intros; discriminate.
    + split; [intros mid e m H; discriminate|]. split.
      * intros mid1 mid2 e1 e2 m1 m2 H; discriminate.
      * split.
        -- apply task_flag_waiter_consistency_empty.
           ++ intro p; simpl; destruct (cfgFlagEnabled (osKernelConfig sg)); reflexivity.
           ++ intros tid t H; discriminate.
        -- intros Henabled Hrunning; discriminate.
Qed.

Lemma UCOS2_boot_validity : forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros sg task_name flag_name memory_name names Hprofile Hnames Hmemoryname.
  pose proof Hprofile as [_ [_ [_ [Hconfig [Hlayout _]]]]].
  pose proof Hlayout as [HflagEnabled [HflagBits _]].
  pose proof Hconfig as [_ [_ [_ [_ [_ [_ [Hregs _]]]]]]].
  split; [exact Hprofile|]. split; [apply task_boot_in_range; lia|].
  split; [apply sched_boot_in_range; reflexivity|].
  split; [apply initial_event_abstract_state_valid|].
  split; [apply UCOS2_boot_cross_module_consistency|].
  split; [discriminate|]. split; [apply task_boot_reserved_bits_clear|]. split.
  - unfold valid_flag_configuration; simpl; rewrite HflagEnabled.
    apply flag_initial_valid.
    + lia.
    + unfold flag_group_name_offset, flag_word_bytes, kernel_align4; rewrite HflagBits; simpl; lia.
  - split.
    + unfold valid_memory_configuration; simpl; destruct (cfgMemoryEnabled (osKernelConfig sg));
        [apply memory_initial_valid|reflexivity].
    + split; [apply timer_uninitialized_configuration_valid|].
      split; [apply statistics_initial_configuration_valid|].
      split; [apply kernel_control_initial_valid|]. split; [exact Hnames|].
      split; [|split; [apply parked_stacks_empty_consistent|intros eid pcp queue Hlease; discriminate]].
      intros name [[Henabled [i [t [Hlookup Hname]]]] |
        [[Henabled [i [e [Hlookup Hname]]]] |
        [[Henabled [Hnamed [i [g [Hlookup Hname]]]]] |
        [[Henabled [Hnamed Hreference]] | [Henabled [Hnamed [i [t [Hlookup Hname]]]]]]]]].
      * discriminate.
      * discriminate.
      * cbn [UCOS2_boot_state FlagState] in Hlookup; rewrite Henabled in Hlookup; discriminate.
      * destruct Hreference as [[i [v [Hlookup Hname]]] | [i [v [Hlookup Hname]]]];
          cbn [UCOS2_boot_state MemoryState] in Hlookup; rewrite Henabled in Hlookup.
        -- cbv beta iota zeta delta [memory_initial memControlImages] in Hlookup.
           destruct (andb (0 <=? i) (i <? cfgMaxMemPartitions (osKernelConfig sg))); [|discriminate].
           injection Hlookup as Himage; subst v.
           cbv beta iota zeta delta [memory_initial_image memImageName] in Hname.
           subst name; apply Hmemoryname; assumption.
        -- discriminate.
      * discriminate.
Qed.

(** This is a pure global preservation theorem. The Flag node's stack
    storage and the changed TCB/bitmap cells still need their focused heap
    proofs; they are not supplied by validity or by the transition equation. *)
Lemma UCOS2_flag_wake_preserves_validity : forall sg s p w after old bits result,
  UCOS2_state_inv sg s ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  UCOS2_state_inv sg (flag_wake_state sg s w after old bits result).
Proof.
  intros sg s p w after old bits result
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]] Hstep Hold.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  pose proof Hpending as HpendingAfter.
  assert (HreferencesAfter : kernel_names_valid sg (flag_wake_state sg s w after old bits result)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - intros; assumption.
    - eapply flag_unlink_name_references; exact Hstep.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (flag_wake_state sg s w after old bits result).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HbitsAfter : task_reserved_bits_clear sg
    (flag_wake_state sg s w after old bits result).(TskState)).
  { apply task_reserved_bits_clear_update_task; [exact Hstatus|].
    apply task_status_clear_wait_preserves_reserved_bits; exact (Hstatus _ old Hold). }
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  assert (Hwaiters : task_flag_waiter_consistency sg s.(TskState) s.(FlagState)).
  { unfold cross_module_consistency in Hcross; tauto. }
  split; [exact Hprofile|]. split.
  - eapply task_flag_wake_preserves_in_range; [exact Htasks|exact Hold].
  - split.
    + eapply sched_flag_wake_preserves_in_range; eauto.
    + split.
      * eapply event_update_unlisted_task_preserves_in_range; [|exact Hevents].
        intros eid e He; eapply task_flag_waiter_not_in_event_wait_list; eauto.
      * split.
        -- eapply flag_wake_preserves_cross_module_consistency; eauto.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split; [exact HbitsAfter|]. split.
              2: { repeat (split; [assumption|]); exact HpendingAfter. }
              unfold valid_flag_configuration in *.
              destruct sg.(osKernelConfig).(cfgFlagEnabled) eqn:Hen.
              ** eapply flag_unlink_preserves_state_validity; eauto.
              ** rewrite Hflags in Hstep; discriminate.
Qed.

Lemma UCOS2_flag_task_rdy_preserves_validity : forall sg s p bits result schedule post,
  UCOS2_state_inv sg s ->
  flag_task_rdy sg s p bits result = Some (schedule, post) ->
  UCOS2_state_inv sg post.
Proof.
  intros sg s p bits result schedule post Hvalid Hstep.
  destruct (flag_task_rdy_result sg s p bits result schedule post Hstep)
    as [w [after [old [Hunlink [Hold [Hpost Hschedule]]]]]].
  subst post; eapply UCOS2_flag_wake_preserves_validity; eassumption.
Qed.

(** IPC wake touches Task, Scheduler and Flag resources together. Every
    other configured owner remains explicitly present in the residual. *)
Definition UCOS2_raw_rep_missing_task_storage_sched_flag (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  event_raw_rep sg s.(TskState) s.(EventState) **
  queue_storage_rep sg s.(EventState) **
  tick_inv sg s.(TickState) **
  memory_configured_rep sg s.(MemoryState) **
  timer_configured_rep sg s.(TimerState) **
  statistics_rep sg s.(StatsState) **
  kernel_control_rep sg s.(ControlState) ** store_name_bytes s.(NameState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks).

Lemma UCOS2_inv_open_task_storage_sched_flag : forall sg s,
  UCOS2_inv sg s |-- coq_prop (UCOS2_state_inv sg s) &&
    (task_public_storage sg s.(TskState) **
     sched_raw_rep sg s.(TskState) s.(SchedState) **
     flag_configured_rep sg s.(FlagState) ** UCOS2_raw_rep_missing_task_storage_sched_flag sg s).
Proof.
  intros; unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_flag, task_shared_rep; entailer!.
Qed.

Lemma UCOS2_flag_wake_residual_eq : forall sg s w after old bits result,
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg (flag_wake_state sg s w after old bits result) =
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s.
Proof.
  intros sg s w after old bits result Hold.
  assert (Hevents : event_raw_rep sg s.(TskState) s.(EventState) =
    event_raw_rep sg
      (glob_task_set_usedtask s.(TskState) w.(flagTask) (task_flag_wake old bits result)) s.(EventState)).
  { apply event_raw_rep_change_task_index.
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_wake_state; simpl.
  rewrite <- Hevents; reflexivity.
Qed.

Lemma UCOS2_inv_merge_flag_wake : forall sg s p w after old bits result,
  UCOS2_state_inv sg s ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  let post := flag_wake_state sg s w after old bits result in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  flag_configured_rep sg post.(FlagState) ** UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
  UCOS2_inv sg post.
Proof.
  intros sg s p w after old bits result Hvalid Hstep Hold post.
  pose proof (UCOS2_flag_wake_preserves_validity
    sg s p w after old bits result Hvalid Hstep Hold) as Hpost.
  fold post in Hpost.
  rewrite <- (UCOS2_flag_wake_residual_eq sg s w after old bits result Hold).
  fold post.
  unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_flag, task_shared_rep; entailer!.
Qed.

Lemma UCOS2_flag_timeout_cleanup_preserves_validity : forall sg s p w after old,
  UCOS2_state_inv sg s ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old -> (task_non_suspension_bits old.(stat)) = 0 ->
  UCOS2_state_inv sg (flag_timeout_cleanup_state s w after old).
Proof.
  intros sg s p w after old
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]] Hstep Hold Hp.
  destruct Hmodules as [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  pose proof Hpending as HpendingAfter.
  assert (HreferencesAfter : kernel_names_valid sg (flag_timeout_cleanup_state s w after old)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - intros; assumption.
    - eapply flag_unlink_name_references; exact Hstep.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (flag_timeout_cleanup_state s w after old).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HbitsAfter : task_reserved_bits_clear sg
    (flag_timeout_cleanup_state s w after old).(TskState)).
  { apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus _ old Hold)]. }
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  assert (Hwaiters : task_flag_waiter_consistency sg s.(TskState) s.(FlagState)).
  { unfold cross_module_consistency in Hcross; tauto. }
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; eauto; reflexivity.
  - split.
    + eapply sched_update_task_preserves_in_range; [exact Hsched|exact Hold|reflexivity|reflexivity].
    + split.
      * eapply event_update_unlisted_task_preserves_in_range; [|exact Hevents].
        intros eid e He; eapply task_flag_waiter_not_in_event_wait_list; eauto.
      * split.
        -- eapply flag_timeout_cleanup_preserves_cross_module_consistency; eauto.
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Hold|reflexivity|apply Hidle; exact Hrunning].
           ++ split; [exact HbitsAfter|]. split.
              2: { repeat (split; [assumption|]); exact HpendingAfter. }
              unfold valid_flag_configuration in *.
              destruct sg.(osKernelConfig).(cfgFlagEnabled) eqn:Hen.
              ** eapply flag_unlink_preserves_state_validity; eauto.
              ** rewrite Hflags in Hstep; discriminate.
Qed.

Lemma UCOS2_timer_link_preserves_validity : forall sg s i t periodic after,
  UCOS2_state_inv sg s -> sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized s.(TimerState) -> s.(TimerState).(timerUsed) i = Some t ->
  t.(timerState) <> TimerRunning -> timer_link sg s.(TimerState) i periodic = Some after ->
  UCOS2_state_inv sg (replace_TimerS after s).
Proof.
  intros sg s i t periodic after Hvalid Hen Hphase Ht Hstate Hstep.
  assert (Htimers : valid_timer_configuration sg s.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  assert (Hconfig : valid_kernel_configuration sg.(osKernelConfig)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  destruct Hconfig as [_ [_ [_ [HtimerConfig _]]]].
  destruct (HtimerConfig Hen) as [_ Hsize].
  destruct (timer_link_preserves_configuration sg s.(TimerState) i t periodic after
    Hen ltac:(lia) Htimers Hphase Ht Hstate Hstep) as [Hafter HafterPhase].
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid|exact Hafter| |].
  - intros _ _; exact HafterPhase.
  - eapply timer_link_name_references; exact Hstep.
Qed.

Lemma UCOS2_timer_unlink_preserves_validity : forall sg s i t after,
  UCOS2_state_inv sg s -> sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  timer_api_initialized s.(TimerState) -> s.(TimerState).(timerUsed) i = Some t ->
  t.(timerState) = TimerRunning -> timer_unlink sg s.(TimerState) i = Some after ->
  UCOS2_state_inv sg (replace_TimerS after s).
Proof.
  intros sg s i t after Hvalid Hen Hphase Ht Hstate Hstep.
  pose proof (selected_kernel_profile_timer_pool_region_valid sg
    (proj1 Hvalid) Hen) as Hlayout.
  assert (Htimers : valid_timer_configuration sg s.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  destruct (timer_unlink_preserves_configuration sg s.(TimerState) i t after
    Hen Hlayout Htimers Hphase Ht Hstate Hstep) as [Hafter HafterPhase].
  apply UCOS2_replace_timer_preserves_validity; [exact Hvalid|exact Hafter| |].
  - intros _ _; exact HafterPhase.
  - eapply timer_unlink_name_references; exact Hstep.
Qed.

Lemma UCOS2_inv_merge_updated_task_storage_sched_flag : forall sg before after,
  UCOS2_state_inv sg after ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg before = UCOS2_raw_rep_missing_task_storage_sched_flag sg after ->
  task_public_storage sg after.(TskState) **
  sched_raw_rep sg after.(TskState) after.(SchedState) **
  flag_configured_rep sg after.(FlagState) ** UCOS2_raw_rep_missing_task_storage_sched_flag sg before |--
  UCOS2_inv sg after.
Proof.
  intros sg before after Hvalid Hframe; rewrite Hframe.
  unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_flag, task_shared_rep; entailer!.
Qed.

Lemma UCOS2_flag_timeout_cleanup_residual_eq : forall sg s w after old,
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg (flag_timeout_cleanup_state s w after old) =
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s.
Proof.
  intros sg s w after old Hold.
  assert (Hevents : event_raw_rep sg s.(TskState) s.(EventState) =
    event_raw_rep sg
      (glob_task_set_usedtask s.(TskState) w.(flagTask) (task_set_flag_node old 0)) s.(EventState)).
  { apply event_raw_rep_change_task_index.
    apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_timeout_cleanup_state; simpl.
  rewrite <- Hevents; reflexivity.
Qed.

Lemma UCOS2_inv_merge_flag_timeout_cleanup : forall sg s p w after old,
  UCOS2_state_inv sg s ->
  flag_unlink_node s.(FlagState) p = Some (w, after) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old -> (task_non_suspension_bits old.(stat)) = 0 ->
  let post := flag_timeout_cleanup_state s w after old in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  flag_configured_rep sg post.(FlagState) ** UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
  UCOS2_inv sg post.
Proof.
  intros sg s p w after old Hvalid Hstep Hold Hp post.
  apply UCOS2_inv_merge_updated_task_storage_sched_flag.
  - eapply UCOS2_flag_timeout_cleanup_preserves_validity; eauto.
  - symmetry; apply UCOS2_flag_timeout_cleanup_residual_eq; exact Hold.
Qed.

(** This closes the existing pure global bundle, including configured
    owners not written by Event wake.  It supplies no TCB/ECB/ready cells;
    their actual source-ordered writes and heap reconstruction stay separate. *)
Lemma UCOS2_event_wake_preserves_validity : forall sg s eid e tid old kind message result,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  UCOS2_state_inv sg (event_wake_state sg s eid e tid old kind message result).
Proof.
  intros sg s eid e tid old kind message result
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] He Hin Hold Hkind.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HpendingAfter : pending_mutex_consistency sg
    (event_wake_state sg s eid e tid old kind message result).(TskState)
    (event_wake_state sg s eid e tid old kind message result).(EventState)).
  { eapply pending_mutex_consistency_event_fields_update with (old := e);
      [exact He|reflexivity|reflexivity|exact Hpending]. }
  assert (HreferencesAfter : kernel_names_valid sg (event_wake_state sg s eid e tid old kind message result)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - eapply event_update_preserves_name_references; [exact He|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (event_wake_state sg s eid e tid old kind message result).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HbitsAfter : task_reserved_bits_clear sg
    (event_wake_state sg s eid e tid old kind message result).(TskState)).
  { apply task_reserved_bits_clear_update_task; [exact Hstatus|].
    apply task_status_clear_wait_preserves_reserved_bits; exact (Hstatus tid old Hold). }
  pose proof Hcross as [_ [_ [Hwait _]]].
  destruct (event_waiter_task_fields sg s.(TskState) eid e tid
    (proj1 Hwait eid e He) Hin)
    as [found [actual [Hfound [Hactual [Hptr [Hmulti Hphase]]]]]].
  assert (found = old) by congruence; subst found.
  assert (actual = kind) by congruence; subst actual.
  destruct (event_wake_preserves_task_sched sg s eid e tid old kind message result
    Htasks Hsched Hold Hphase) as [HtasksAfter HschedAfter].
  split; [exact Hprofile|]; split; [exact HtasksAfter|]; split; [exact HschedAfter|]; split.
  - eapply event_wake_preserves_event_in_range; eauto.
  - split.
    + eapply event_wake_preserves_cross_module_consistency; eauto.
    + split.
      2: { split; [exact HbitsAfter|].
           repeat (split; [assumption|]); exact HpendingAfter. }
      intro Hrunning; eapply task_update_preserves_idle_tail;
        [exact Hold|reflexivity|apply Hidle].
      change ((sched_wake_by_status sg s.(TskState) s.(SchedState) tid
        (encode_task_status (task_event_wake_single old kind message result).(stat))).(isRunning) = true)
        in Hrunning.
      rewrite sched_wake_by_status_running_eq in Hrunning; exact Hrunning.
Qed.

Lemma UCOS2_event_task_rdy_preserves_validity :
  forall sg s eid e head tail kind message result priority after,
    UCOS2_state_inv sg s ->
    s.(EventState).(inUsedEventStates) eid = Some e -> e.(waitList) = head :: tail ->
    event_type_to_pend_type e.(eventType) = Some kind ->
    event_task_rdy sg s eid kind message result = Some (priority, after) ->
    UCOS2_state_inv sg after.
Proof.
  intros sg s eid e head tail kind message result priority after Hvalid He Hlist Hkind Hstep.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  pose proof (Hentries eid e He) as Hentry.
  assert (Hin : In head e.(waitList)) by (rewrite Hlist; left; reflexivity).
  destruct (event_waiter_task_fields sg s.(TskState) eid e head Hentry Hin)
    as [old [actual [Hold Hfields]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  rewrite (event_task_rdy_selects_waiter sg s eid e head tail old kind message result
    Hsg Htasks Hentry He Hlist Hold) in Hstep.
  injection Hstep as Hpriority Hafter; subst after.
  eapply UCOS2_event_wake_preserves_validity; eauto.
Qed.

(** Event wake changes the Task, ready bitmap and ECB images together.
    QCB/ring storage and every other configured owner remain in the real
    residual, even for an Event whose primitive is not a Queue. *)
Definition UCOS2_raw_rep_missing_task_storage_sched_event (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv sg s.(IntrState) **
  queue_storage_rep sg s.(EventState) **
  tick_inv sg s.(TickState) **
  flag_configured_rep sg s.(FlagState) **
  memory_configured_rep sg s.(MemoryState) **
  timer_configured_rep sg s.(TimerState) **
  statistics_rep sg s.(StatsState) **
  kernel_control_rep sg s.(ControlState) ** store_name_bytes s.(NameState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks).

Lemma UCOS2_inv_open_task_storage_sched_event : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (task_public_storage sg s.(TskState) **
     sched_raw_rep sg s.(TskState) s.(SchedState) **
     event_raw_rep sg s.(TskState) s.(EventState) **
     UCOS2_raw_rep_missing_task_storage_sched_event sg s).
Proof.
  intros; split; unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event, task_shared_rep; entailer!.
Qed.

Lemma UCOS2_event_wake_preserves_residual : forall sg s eid e tid old kind message result,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg (event_wake_state sg s eid e tid old kind message result).
Proof.
  intros sg s eid e tid old kind message result He.
  unfold UCOS2_raw_rep_missing_task_storage_sched_event, event_wake_state; simpl.
  sep_apply_l_atomic (queue_set_event_wait_list_preserves_storage
    sg s.(EventState) eid e (remove_Z_eqb tid e.(waitList)) He); entailer!.
Qed.

(** The ECB resource can still carry the pre-wake Task index: the wake
    stores preserve every task priority, so the bytes of all surviving
    wait bitmaps are identical under the post-wake Task map. *)
Lemma UCOS2_inv_merge_event_wake : forall sg s eid e tid old kind message result,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  let post := event_wake_state sg s eid e tid old kind message result in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg s.(TskState) post.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old kind message result Hvalid He Hin Hold Hkind post.
  pose proof (UCOS2_event_wake_preserves_validity
    sg s eid e tid old kind message result Hvalid He Hin Hold Hkind) as Hpost; fold post in Hpost.
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (UCOS2_event_wake_preserves_residual
    sg s eid e tid old kind message result He); fold post.
  unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event, task_shared_rep; entailer!.
Qed.

(** Connect the actual row/conditional-group writes to the full existing
    global invariant.  Updated Task/Scheduler resources are consumed, not
    synthesized from the pure endpoint validity theorem. *)
Lemma UCOS2_inv_merge_event_wake_storage : forall sg s eid e tid old kind message result,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  event_type_to_pend_type e.(eventType) = Some kind ->
  let post := event_wake_state sg s eid e tid old kind message result in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_clear_waiter (event_image sg s.(TskState) e)
      (old.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) s.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) s.(TskState))
      (Z.shiftl 1 (old.(curPrio) mod 8)) (Z.shiftl 1 (old.(curPrio) / 8))) **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old kind message result Hvalid He Hin Hold Hkind post.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hunique : task_priority_unique s.(TskState)).
  { destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]]; exact Hunique. }
  assert (Hcanonical : event_waitList_canonical sg s.(TskState) e.(waitList)).
  { destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]]; exact (proj1 (Hentries eid e He)). }
  assert (Hprio : valid_task_prio sg old.(curPrio)).
  { destruct Hcanonical as [_ [_ Hmembers]].
    destruct (Hmembers tid Hin) as [found [Hfound Hprio]].
    assert (found = old) by congruence; subst found; exact Hprio. }
  sep_apply_l_atomic (event_remove_waiter_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid e tid old Hsg Hunique Hcanonical Hprio Hold).
  eapply derivable1_trans; [|exact (UCOS2_inv_merge_event_wake
    sg s eid e tid old kind message result Hvalid He Hin Hold Hkind)].
  fold post; fold (post.(EventState)).
  entailer!.
Qed.

(** Complete pre-schedule Pend endpoint.  The side conditions are the
    caller's unavailable-resource observation and single-wait protocol;
    they are not extra branches or post-state validity assumptions.  Ready
    membership is observed before the caller's OR store; scheduler validity
    supplies the initially clear pending bits used by the single-wait law. *)
Lemma UCOS2_event_pend_preserves_validity : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  UCOS2_state_inv sg (event_pend_state sg s eid e tid old kind timeout).
Proof.
  intros sg s eid e tid old kind timeout
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]]
    He Hold Hprio Hnull Hmulti Hflagnull Hready Hkind Hunavailable Hnotowner.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HpendingAfter : pending_mutex_consistency sg
    (event_pend_state sg s eid e tid old kind timeout).(TskState)
    (event_pend_state sg s eid e tid old kind timeout).(EventState)).
  { eapply pending_mutex_consistency_event_fields_update with (old := e);
      [exact He|reflexivity|reflexivity|exact Hpending]. }
  assert (HreferencesAfter : kernel_names_valid sg (event_pend_state sg s eid e tid old kind timeout)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - eapply event_update_preserves_name_references; [exact He|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (event_pend_state sg s eid e tid old kind timeout).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HbitsAfter : task_reserved_bits_clear sg
    (event_pend_state sg s eid e tid old kind timeout).(TskState)).
  { apply task_reserved_bits_clear_update_task; [exact Hstatus|].
    apply task_status_set_wait_preserves_reserved_bits; [exact (Hstatus tid old Hold)|].
    left; intro HmultiKind; subst kind; destruct e.(eventType); discriminate. }
  assert (Hnone : task_non_suspension_bits old.(stat) = 0).
  { destruct (proj1 (proj1 Hsched) tid Hready) as [found [Hfound [_ Heffective]]].
    assert (found = old) by congruence; subst found.
    apply task_effectively_ready_has_no_pending; exact Heffective. }
  destruct (event_pend_preserves_task_sched sg s eid e tid old kind timeout
    Htasks Hsched Hold) as [HtasksAfter HschedAfter].
  split; [exact Hprofile|]; split; [exact HtasksAfter|]; split; [exact HschedAfter|]; split.
  - eapply event_pend_preserves_event_in_range; eauto.
  - split.
    + eapply event_pend_preserves_cross_module_consistency; eauto.
    + split.
      2: { split; [exact HbitsAfter|].
           repeat (split; [assumption|]); exact HpendingAfter. }
      intro Hrunning; eapply task_update_preserves_idle_tail;
        [exact Hold|reflexivity|apply Hidle; exact Hrunning].
Qed.

Lemma UCOS2_event_pend_preserves_residual : forall sg s eid e tid old kind timeout,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg (event_pend_state sg s eid e tid old kind timeout).
Proof.
  intros sg s eid e tid old kind timeout He.
  unfold UCOS2_raw_rep_missing_task_storage_sched_event, event_pend_state, event_wait_state; simpl.
  unfold event_insert_waiter.
  sep_apply_l_atomic (queue_set_event_wait_list_preserves_storage sg s.(EventState) eid e
    (insert_sorted_by
      (wait_prio_key sg (glob_task_set_usedtask s.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid))))
      tid (remove_Z_eqb tid e.(waitList))) He); entailer!.
Qed.

Lemma UCOS2_inv_merge_event_pend : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := event_pend_state sg s eid e tid old kind timeout in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg s.(TskState) post.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old kind timeout Hvalid He Hold Hprio Hnull Hmulti Hflagnull
    Hready Hkind Hunavailable Hnotowner post.
  pose proof (UCOS2_event_pend_preserves_validity sg s eid e tid old kind timeout
    Hvalid He Hold Hprio Hnull Hmulti Hflagnull Hready Hkind Hunavailable Hnotowner) as Hpost; fold post in Hpost.
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (UCOS2_event_pend_preserves_residual
    sg s eid e tid old kind timeout He); fold post.
  unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event, task_shared_rep; entailer!.
Qed.

(** Consume the actual two OR-written ECB fields via their complete image,
    the old map residual, and already-written TCB/ready resources.  The
    untouched Queue buffer and other module owners are preserved. *)
Lemma UCOS2_inv_merge_event_pend_storage : forall sg s eid e tid old kind timeout,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  s.(TskState).(inUsedTaskStates) tid = Some old -> valid_task_prio sg old.(curPrio) ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil -> old.(tcbFlagNode) = 0 ->
  In tid s.(SchedState).(readyList) ->
  event_type_to_pend_type e.(eventType) = Some kind -> event_wait_resource_unavailable e ->
  (forall m, e.(eventType) = OS_EVENT_TYPE_MUTEX -> e.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) ->
  let post := event_pend_state sg s eid e tid old kind timeout in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_mark_waiter (event_image sg s.(TskState) e)
      (old.(curPrio) / 8) (encode_event_wait_tbl_at_or e.(waitList) s.(TskState) (old.(curPrio) / 8))
      (encode_event_wait_grp e.(waitList) s.(TskState))
      (Z.shiftl 1 (old.(curPrio) mod 8)) (Z.shiftl 1 (old.(curPrio) / 8))) **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old kind timeout Hvalid He Hold Hprio Hnull Hmulti Hflagnull
    Hready Hkind Hunavailable Hnotowner post.
  assert (Hsg : valid_stable_glob_vars sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile in Hvalid; tauto. }
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8).
  { destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
    unfold valid_task_prio in Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hevent : post.(EventState) =
    update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
  { unfold post, event_pend_state, event_wait_state; cbn zeta.
    change (update_event_field_raw s.(EventState) eid
      (event_insert_waiter sg (glob_task_set_usedtask s.(TskState) tid
        (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid))) e tid) =
      update_event_field_raw s.(EventState) eid (event_insert_waiter sg s.(TskState) e tid)).
    rewrite (event_insert_waiter_update_task_eq sg s.(TskState) tid old
      (task_set_event_ptr (task_prepare_event_wait old kind timeout) (Some eid)) e tid Hold eq_refl).
    reflexivity. }
  sep_apply_l_atomic (event_insert_waiter_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid e tid old Hold Hrow).
  rewrite <- Hevent.
  eapply derivable1_trans; [|exact (UCOS2_inv_merge_event_pend sg s eid e tid old kind timeout
    Hvalid He Hold Hprio Hnull Hmulti Hflagnull Hready Hkind Hunavailable Hnotowner)].
  fold post; entailer!.
Qed.

(** Selected live-TCB endpoints only.  The existing global bundle now
    carries the source-established status-bit fact needed to identify the
    single-wait Resume test, rather than assuming that fact at each call. *)
Lemma UCOS2_task_suspend_preserves_validity : forall sg s tid t,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  UCOS2_state_inv sg (task_suspend_state s tid t).
Proof.
  intros sg s tid t [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] Ht.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  pose proof Hpending as HpendingAfter.
  assert (HreferencesAfter : kernel_names_valid sg (task_suspend_state s tid t)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Ht|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (task_suspend_state s tid t).(TskState) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Ht|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]; split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + eapply sched_remove_ready_task_preserves_in_range;
        [exact Hsched|exact Ht|reflexivity|apply task_suspend_not_ready].
    + split.
      * eapply event_update_status_preserves_in_range;
          [exact Ht|exact (proj1 (task_status_suspend_observations t.(stat)))|exact Hevents].
      * split.
        -- change (cross_module_consistency sg
             (replace_SchedS (sched_remove_ready_task s.(SchedState) tid)
               (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_suspend t)) s))).
           eapply cross_module_consistency_sched_frame; [reflexivity|].
           eapply task_status_update_preserves_cross_module_consistency;
             [exact Ht|exact (proj1 (task_status_suspend_observations t.(stat)))|exact Hcross].
        -- split.
           ++ intro Hrunning; eapply task_update_preserves_idle_tail;
                [exact Ht|reflexivity|apply Hidle; exact Hrunning].
           ++ split.
              2: { repeat (split; [assumption|]); exact HpendingAfter. }
              apply task_reserved_bits_clear_update_task; [exact Hstatus|].
              apply task_status_suspend_preserves_reserved_bits; exact (Hstatus tid t Ht).
Qed.

Lemma UCOS2_task_resume_preserves_validity : forall sg s tid t,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_is_suspended t.(stat) = true ->
  UCOS2_state_inv sg (task_resume_state sg s tid t).
Proof.
  intros sg s tid t [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] Ht Hsusp.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  pose proof Hpending as HpendingAfter.
  assert (HreferencesAfter : kernel_names_valid sg (task_resume_state sg s tid t)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Ht|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (task_resume_state sg s tid t).(TskState) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Ht|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false).
  { unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto. }
  assert (Hbits : task_status_reserved_bits_clear false t.(stat)).
  { rewrite <- Hmulti; exact (Hstatus tid t Ht). }
  assert (Hrunning : (task_resume_state sg s tid t).(SchedState).(isRunning) =
    s.(SchedState).(isRunning)) by apply sched_resume_task_running_eq.
  split; [exact Hprofile|]; split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + eapply sched_resume_task_preserves_in_range; eassumption.
    + split.
      * eapply event_update_status_preserves_in_range;
          [exact Ht|exact (proj1 (task_status_resume_observations t.(stat)))|exact Hevents].
      * split.
        -- eapply cross_module_consistency_sched_frame;
             [apply sched_resume_task_running_eq|].
           eapply task_status_update_preserves_cross_module_consistency;
             [exact Ht|exact (proj1 (task_status_resume_observations t.(stat)))|exact Hcross].
        -- split.
           ++ intro Hrun; rewrite Hrunning in Hrun.
              eapply task_update_preserves_idle_tail;
                [exact Ht|reflexivity|apply Hidle; exact Hrun].
           ++ split.
              2: { repeat (split; [assumption|]); exact HpendingAfter. }
              apply task_reserved_bits_clear_update_task; [exact Hstatus|].
              apply task_status_resume_preserves_reserved_bits; exact (Hstatus tid t Ht).
Qed.

Lemma UCOS2_task_status_residual_eq : forall sg s tid t status sched',
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  UCOS2_raw_rep_missing_task_storage_sched sg
    (replace_SchedS sched' (replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_status t status)) s)) =
  UCOS2_raw_rep_missing_task_storage_sched sg s.
Proof.
  intros sg s tid t status sched' Ht; unfold UCOS2_raw_rep_missing_task_storage_sched; simpl.
  rewrite (event_raw_rep_change_task_index sg s.(TskState)
    (glob_task_set_usedtask s.(TskState) tid (task_set_status t status)) s.(EventState)); [reflexivity|].
  apply event_wait_priority_agreement_encodes.
  eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Ht|reflexivity].
Qed.

Lemma UCOS2_inv_merge_task_suspend : forall sg s tid t,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  let post := task_suspend_state s tid t in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s tid t Hvalid Ht post; apply UCOS2_inv_merge_updated_task_storage_sched.
  - apply UCOS2_task_suspend_preserves_validity; assumption.
  - symmetry; apply UCOS2_task_status_residual_eq; exact Ht.
Qed.

Lemma UCOS2_inv_merge_task_resume : forall sg s tid t,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_is_suspended t.(stat) = true ->
  let post := task_resume_state sg s tid t in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s tid t Hvalid Ht Hsusp post; apply UCOS2_inv_merge_updated_task_storage_sched.
  - apply UCOS2_task_resume_preserves_validity; assumption.
  - symmetry; apply UCOS2_task_status_residual_eq; exact Ht.
Qed.

(** Event and Queue have separate physical owners but one canonical
    payload/instance relation.  This residual keeps every other configured
    module, and continues to index ready/Event encodings by the same Task. *)
Lemma UCOS2_inv_split_event_queue : forall sg s,
  UCOS2_inv sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
      (event_raw_rep sg s.(TskState) s.(EventState) **
       queue_storage_rep sg s.(EventState) ** UCOS2_raw_rep_missing_event_queue sg s).
Proof.
  intros sg s; apply (UCOS2_inv_split_two sg s EventModule QueueModule); discriminate.
Qed.

Lemma UCOS2_raw_rep_missing_event_queue_replace_event_eq : forall sg s events,
  UCOS2_raw_rep_missing_event_queue sg (replace_EventS events s) =
    UCOS2_raw_rep_missing_event_queue sg s.
Proof. reflexivity. Qed.

Lemma UCOS2_inv_merge_updated_event_queue : forall sg s events,
  UCOS2_state_inv sg (replace_EventS events s) ->
  event_raw_rep sg s.(TskState) events ** queue_storage_rep sg events **
    UCOS2_raw_rep_missing_event_queue sg s |-- UCOS2_inv sg (replace_EventS events s).
Proof.
  intros sg s events Hvalid.
  rewrite UCOS2_inv_split_event_queue,
    UCOS2_raw_rep_missing_event_queue_replace_event_eq.
  cbn [replace_EventS].
  entailer!.
Qed.

(** Private ECB metadata changes do not alter the published Event map.
    Local bytes remain outside the shared heap; these bridges transport
    the actual existing cross-module relations, not a caller-assumed
    replacement global invariant. *)
Lemma UCOS2_event_map_frame_preserves_validity : forall sg s events,
  UCOS2_state_inv sg s ->
  events.(inUsedEventStates) = s.(EventState).(inUsedEventStates) ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  event_in_range sg s.(TskState) events ->
  UCOS2_state_inv sg (replace_EventS events s).
Proof.
  intros sg s events [Hprofile [Htasks [Hsched [_ [Hcross Hrest]]]]] Hmap Hleases Hevents.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (events) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    intros name [eid [node [Hget Hname]]]; exists eid, node.
    rewrite Hmap in Hget; split; assumption. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState) events).
  { eapply pending_mutex_consistency_frame with (tasks := s.(TskState)) (events := s.(EventState));
      [reflexivity|reflexivity|exact Hleases| |tauto].
    intros p Hclaim; rewrite Hmap in Hclaim; exact Hclaim. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split; [exact Hevents|].
  split; [eapply cross_module_consistency_event_map_frame; eassumption|cbn [replace_EventS]; tauto].
Qed.

Lemma UCOS2_event_detach_head_preserves_validity : forall sg s eid rest image,
  UCOS2_state_inv sg s -> s.(EventState).(unUsedEventStates) = eid :: rest ->
  UCOS2_state_inv sg
    (replace_EventS (event_detach_head s.(EventState) eid rest image) s).
Proof.
  intros sg s eid rest image Hvalid Hhead.
  eapply UCOS2_event_map_frame_preserves_validity; [exact Hvalid|reflexivity| |].
  - apply event_mutex_lease_view_detach_head_eq.
    exact (proj2 (event_pool_free_unallocated sg s.(EventState) eid
      (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid)))))
      ltac:(rewrite Hhead; left; reflexivity))).
  - eapply event_detach_head_preserves_in_range;
      [exact (proj1 (proj2 (proj2 (proj2 Hvalid))))|exact Hhead].
Qed.

Lemma UCOS2_inv_merge_event_detach_head : forall sg s eid rest image,
  UCOS2_state_inv sg s -> s.(EventState).(unUsedEventStates) = eid :: rest ->
  s.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  (store_map (used_event_rep sg s.(TskState)) s.(EventState).(inUsedEventStates) **
   event_free_storage_rep sg s.(EventState) **
   sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest)) **
  queue_storage_rep sg s.(EventState) ** UCOS2_raw_rep_missing_event_queue sg s |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
  UCOS2_inv sg (replace_EventS (event_detach_head s.(EventState) eid rest image) s).
Proof.
  intros sg s eid rest image Hvalid Hhead Himage.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_free_unallocated sg s.(EventState) eid Hpool
    ltac:(rewrite Hhead; simpl; auto)) as [_ Hprivate].
  pose proof (UCOS2_event_detach_head_preserves_validity sg s eid rest image Hvalid Hhead) as Hpost.
  sep_apply_l_atomic (event_detach_head_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid rest image Himage).
  rewrite <- (queue_storage_event_detach_head_eq sg s.(EventState) eid rest image Hprivate).
  sep_apply_l_atomic (UCOS2_inv_merge_updated_event_queue sg s
    (event_detach_head s.(EventState) eid rest image) Hpost); entailer!.
Qed.

Lemma UCOS2_event_private_write_preserves_validity : forall sg s eid allocation field value,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  UCOS2_state_inv sg
    (replace_EventS (event_private_write s.(EventState) eid allocation field value) s).
Proof.
  intros sg s eid allocation field value Hvalid Hget.
  eapply UCOS2_event_map_frame_preserves_validity; [exact Hvalid|reflexivity| |].
  - apply event_mutex_lease_view_private_write_eq; exact Hget.
  - eapply event_private_write_preserves_in_range;
      [exact (proj1 (proj2 (proj2 (proj2 Hvalid))))|exact Hget].
Qed.

(** This is only the shared frame of a private field store.  The caller
    still owns and writes that field; no private byte is manufactured. *)
Lemma UCOS2_event_private_write_global_frame : forall sg s eid allocation field value,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  UCOS2_inv sg s |--
    UCOS2_inv sg
      (replace_EventS (event_private_write s.(EventState) eid allocation field value) s).
Proof.
  intros sg s eid allocation field value Hget.
  rewrite (UCOS2_inv_split_event_queue sg s); Intros.
  match goal with H : UCOS2_state_inv sg s |- _ =>
    pose proof (UCOS2_event_private_write_preserves_validity sg s eid allocation field value H Hget)
      as Hpost end.
  eapply derivable1_trans; [|apply UCOS2_inv_merge_updated_event_queue; exact Hpost].
  rewrite (queue_storage_event_private_write_eq sg s.(EventState) eid allocation field value Hget).
  unfold event_raw_rep, event_free_storage_rep, event_free_root_rep;
    cbn [event_private_write event_set_lifecycle]; entailer!.
Qed.

Lemma UCOS2_event_publish_preserves_validity : forall sg s eid allocation node,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = nil ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  event_name_valid sg s.(NameState) node ->
  allocation.(eventPrivateMutexPCP) = None ->
  UCOS2_state_inv sg (replace_EventS (event_publish s.(EventState) eid node) s).
Proof.
  intros sg s eid allocation node [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]]
    Hget Hgeneration Hnonmutex Hqueue Hempty Hfields Hpayload Hname HnoMutexLease.
  pose proof Hevents as [Hpool _].
  destruct (event_pool_private_not_free sg s.(EventState) eid allocation Hpool Hget) as [_ [_ Hnone]].
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (event_publish s.(EventState) eid node) s)).
  { eapply kernel_names_valid_replace_event_add_name; [tauto|exact Hname|].
    intros p Hreference.
    exact (event_publish_name_references s.(EventState) eid node p Hreference). }
  assert (Hleases : event_mutex_lease_view (event_publish s.(EventState) eid node) =
    event_mutex_lease_view s.(EventState))
    by (apply event_mutex_lease_view_publish_eq with (allocation := allocation); assumption).
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (event_publish s.(EventState) eid node)).
  { eapply pending_mutex_consistency_event_transport with (events := s.(EventState));
      [exact Hleases| |tauto].
    intros slot after Hafter Htype; cbn [event_publish inUsedEventStates] in Hafter.
    unfold kernel_map_set in Hafter; destruct (Z.eq_dec slot eid).
    - injection Hafter as Hafter; subst after; contradiction.
    - exists after; split; [exact Hafter|]. split; [exact Htype|reflexivity]. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split.
  - eapply event_publish_preserves_in_range; try eassumption.
    + intros other old q Hold Hqid; unfold event_queue_id in Hqid; rewrite Hqueue in Hqid.
      destruct node.(eventType); discriminate.
    + apply event_wait_entry_consistency_empty; exact Hempty.
  - split; [|cbn [replace_EventS]; tauto].
    eapply cross_module_consistency_event_publish;
      [exact Hnone|exact Hnonmutex|exact Hempty|reflexivity|exact Hleases|exact Hcross].
Qed.

Lemma UCOS2_inv_merge_event_publish : forall sg s eid allocation node,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None ->
  (forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg s.(TskState) node field) ->
  node.(eventGeneration) = allocation.(eventPrivateGeneration) ->
  node.(eventType) <> OS_EVENT_TYPE_MUTEX -> node.(queueFields) = None -> node.(waitList) = nil ->
  event_fields_consistency node -> event_payload_consistency sg node ->
  event_name_valid sg s.(NameState) node ->
  allocation.(eventPrivateMutexPCP) = None ->
  event_private_storage_rep sg eid allocation **
    (event_raw_rep sg s.(TskState) s.(EventState) ** queue_storage_rep sg s.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg s) |--
  UCOS2_inv sg (replace_EventS (event_publish s.(EventState) eid node) s).
Proof.
  intros sg s eid allocation node Hvalid Hget Hprivate Himage Hgeneration Hnonmutex Hqueue Hempty Hfields Hpayload Hname HnoMutexLease.
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  destruct (event_pool_private_not_free sg s.(EventState) eid allocation Hpool Hget) as [_ [_ Hnone]].
  pose proof (UCOS2_event_publish_preserves_validity sg s eid allocation node
    Hvalid Hget Hgeneration Hnonmutex Hqueue Hempty Hfields Hpayload Hname HnoMutexLease) as Hpost.
  sep_apply_l_atomic (event_publish_reconstructs_raw_rep_on_fields
    sg s.(TskState) s.(EventState) eid allocation node Hpool Hget Himage).
  sep_apply_l_atomic (queue_event_publish_preserves_storage
    sg s.(EventState) eid allocation node Hnone Hget Hprivate Hqueue).
  eapply derivable1_trans; [|apply UCOS2_inv_merge_updated_event_queue; exact Hpost]; entailer!.
Qed.

(** A payload owner proves its own new Event invariant.  This bridge
    transports unchanged Task/Sched/Mutex relations and every other
    configured module; it does not assume a new whole-global invariant. *)
Lemma UCOS2_event_payload_update_preserves_validity : forall sg s eid old new,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some old ->
  new.(eventType) = old.(eventType) -> new.(mutexFields) = old.(mutexFields) ->
  new.(waitList) = old.(waitList) -> new.(eventName) = old.(eventName) ->
  event_in_range sg s.(TskState) (update_event_field_raw s.(EventState) eid new) ->
  UCOS2_state_inv sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s).
Proof.
  intros sg s eid old new [Hprofile [Htasks [Hsched [_ [Hcross Hrest]]]]]
    Hold Htype Hmutex Hwait Hname Hevents.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    eapply event_update_preserves_name_references; eassumption. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (update_event_field_raw s.(EventState) eid new)).
  { eapply pending_mutex_consistency_event_fields_update with (old := old); try eassumption; tauto. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split; [exact Hevents|].
  split; [|cbn [replace_EventS]; tauto].
  eapply cross_module_consistency_event_fields_update; eassumption.
Qed.

(** Only one Event node changes.  Queue storage must still be transported
    through its actual Event-indexed representation, even for Sem/Mbox. *)
Lemma UCOS2_inv_merge_updated_event : forall sg s eid old new,
  UCOS2_state_inv sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s) ->
  s.(EventState).(inUsedEventStates) eid = Some old ->
  new.(queueFields) = old.(queueFields) -> new.(eventType) = old.(eventType) ->
  used_event_rep sg s.(TskState) eid new **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
    queue_storage_rep sg s.(EventState) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (update_event_field_raw s.(EventState) eid new) s).
Proof.
  intros sg s eid old new Hvalid Hold Hqueue Htype.
  eapply derivable1_trans with
    (event_raw_rep sg s.(TskState) (update_event_field_raw s.(EventState) eid new) **
     queue_storage_rep sg (update_event_field_raw s.(EventState) eid new) **
     UCOS2_raw_rep_missing_event_queue sg s).
  - sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg s.(TskState) s.(EventState) eid new).
    sep_apply_l_atomic (queue_event_update_preserves_storage sg s.(EventState) eid old new
      Hold Hqueue Htype); entailer!.
  - apply UCOS2_inv_merge_updated_event_queue; exact Hvalid.
Qed.

Lemma UCOS2_sem_count_update_preserves_validity : forall sg s eid e count,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_fields_consistency e.(waitList) {| semCount := count |} ->
  UCOS2_state_inv sg (sem_count_update_state s eid e count).
Proof.
  intros sg s eid e count Hvalid He Htype Hcount.
  pose proof Hvalid as [_ [_ [_ [Hevents _]]]].
  eapply UCOS2_event_payload_update_preserves_validity; try eassumption; try reflexivity.
  eapply sem_set_count_preserves_event_in_range; eassumption.
Qed.

Lemma UCOS2_inv_merge_sem_count : forall sg s eid e count,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_fields_consistency e.(waitList) {| semCount := count |} ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> count **
    sem_rep_no_count sg s.(TskState) eid e **
    event_raw_rep_no_eid sg s.(TskState) s.(EventState) eid **
    queue_storage_rep sg s.(EventState) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (sem_count_update_state s eid e count).
Proof.
  intros sg s eid e count Hvalid He Htype Hcount.
  pose proof (UCOS2_sem_count_update_preserves_validity sg s eid e count
    Hvalid He Htype Hcount) as Hafter.
  sep_apply_l_atomic (sem_rep_merge_updated_count sg s.(TskState) eid e count Htype).
  sep_apply_l_atomic (UCOS2_inv_merge_updated_event sg s eid e (sem_set_count e count)
    Hafter He eq_refl eq_refl); entailer!.
Qed.

(** The Queue operation supplies its proved ring postcondition; no
    post-global-invariant premise is hidden in the transformer.  Queue
    byte binding/partition are reconstructed from the actual cells below. *)
Lemma UCOS2_queue_update_preserves_validity : forall sg s eid node before after slots,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some before -> after.(qID) = before.(qID) ->
  queue_fields_consistency sg node.(waitList) after ->
  UCOS2_state_inv sg
    (replace_EventS (queue_update s.(EventState) eid node after slots) s).
Proof.
  intros sg s eid node before after slots
    [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]] Hnode Htype Hbefore Hsame Hqueue.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (queue_update s.(EventState) eid node after slots) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    eapply event_update_preserves_name_references; [exact Hnode|reflexivity]. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (queue_update s.(EventState) eid node after slots)).
  { eapply pending_mutex_consistency_event_fields_update with (old := node);
      [exact Hnode|reflexivity|reflexivity|tauto]. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split.
  - eapply queue_update_preserves_event_in_range; eassumption.
  - split; [|cbn [replace_EventS]; tauto].
    exact (cross_module_consistency_event_fields_update sg s eid node
      (event_set_queue_fields node after) Hnode eq_refl eq_refl eq_refl Hcross).
Qed.

Lemma UCOS2_queue_flush_preserves_validity : forall sg s eid node q slots,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some q ->
  UCOS2_state_inv sg
    (replace_EventS (queue_update s.(EventState) eid node (queue_flush_state q) slots) s).
Proof.
  intros sg s eid node q slots Hvalid Hnode Htype Hq.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid node Hnode) as Hqueue.
  unfold event_payload_consistency in Hqueue; rewrite Htype, Hq in Hqueue.
  eapply UCOS2_queue_update_preserves_validity;
    [exact Hvalid|exact Hnode|exact Htype|exact Hq|reflexivity|].
  apply queue_flush_preserves_consistency_total; exact Hqueue.
Qed.

(** Once the source has written the QCB and (when needed) one ring slot,
    use Queue's existing missing-node/buffer reassembly.  ECB bytes are
    unchanged by a same-QID payload update, while all other owners frame. *)
Lemma UCOS2_inv_merge_queue_update : forall sg s free eid node before after slots,
  UCOS2_state_inv sg s ->
  queue_published_storage_binding s.(EventState) ->
  queue_pool_partition sg s.(EventState) free ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some before -> after.(qID) = before.(qID) ->
  queue_fields_consistency sg node.(waitList) after -> queue_slots_model after slots ->
  (event_raw_rep sg s.(TskState) s.(EventState) **
    (store_map_missing_i (published_queue_node_rep sg s.(EventState))
       s.(EventState).(inUsedEventStates) eid **
      ((used_queue_control_block sg after ** PtrArray.mixed_full after.(qStart) after.(qSize) slots) **
        store_free_queue_list sg free))) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (queue_update s.(EventState) eid node after slots) s).
Proof.
  intros sg s free eid node before after slots Hvalid Hbinding Hpart Hnode Htype Hbefore Hsame Hqueue Hslots.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + exact (queue_update_reconstructs_event_queue sg s.(TskState) s.(EventState)
        free eid node before after slots Hbinding Hpart Hnode Htype Hbefore Hsame Hslots).
    + reflexivity.
  - apply UCOS2_inv_merge_updated_event_queue.
    eapply UCOS2_queue_update_preserves_validity; eassumption.
Qed.

Lemma UCOS2_queue_dequeue_preserves_validity : forall sg s eid e q message next slots,
  UCOS2_state_inv sg s -> s.(EventState).(inUsedEventStates) eid = Some e ->
  e.(eventType) = OS_EVENT_TYPE_Q -> e.(queueFields) = Some q ->
  queue_dequeue_front q = Some (message, next) ->
  UCOS2_state_inv sg
    (replace_EventS (queue_update s.(EventState) eid e next slots) s).
Proof.
  intros sg s eid e q message next slots Hvalid He Htype Hq Hstep.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
  rewrite Htype, Hq in Hqueue.
  pose proof (queue_dequeue_front_queue_id_eq q message next Hstep) as Hid.
  eapply UCOS2_queue_update_preserves_validity; try eassumption.
  eapply queue_dequeue_front_preserves_consistency_total; eauto.
Qed.

Lemma UCOS2_inv_merge_queue_dequeue : forall sg s eid e q message next slots free,
  UCOS2_state_inv sg s -> queue_published_storage_binding s.(EventState) ->
  queue_pool_partition sg s.(EventState) free ->
  s.(EventState).(inUsedEventStates) eid = Some e -> e.(eventType) = OS_EVENT_TYPE_Q ->
  e.(queueFields) = Some q -> queue_slots_model q slots ->
  queue_dequeue_front q = Some (message, next) ->
  (event_raw_rep sg s.(TskState) s.(EventState) **
    (store_map_missing_i (published_queue_node_rep sg s.(EventState))
       s.(EventState).(inUsedEventStates) eid **
      ((used_queue_control_block sg next ** PtrArray.mixed_full next.(qStart) next.(qSize) slots) **
        store_free_queue_list sg free))) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (queue_update s.(EventState) eid e next slots) s).
Proof.
  intros sg s eid e q message next slots free Hvalid Hbinding Hpartition He Htype Hq Hslots Hstep.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  pose proof (Hpayload eid e He) as Hqueue; unfold event_payload_consistency in Hqueue.
  rewrite Htype, Hq in Hqueue.
  pose proof (queue_dequeue_front_queue_id_eq q message next Hstep) as Hid.
  eapply UCOS2_inv_merge_queue_update; try eassumption.
  - eapply queue_dequeue_front_preserves_consistency_total; eauto.
  - eapply queue_dequeue_front_preserves_slots; eauto.
Qed.

(** ECB-only recycling.  The non-Mutex premise preserves priority-slot
    claims; the empty wait list and existing backlinks prove that no TCB
    reference dangles.  Queue storage is handled by the spatial rule,
    not silently discarded by this pure invariant theorem. *)
Lemma UCOS2_event_recycle_preserves_validity : forall sg s eid node image,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) <> OS_EVENT_TYPE_MUTEX ->
  node.(waitList) = nil ->
  UCOS2_state_inv sg (replace_EventS (event_recycle sg s.(EventState) eid image) s).
Proof.
  intros sg s eid node image [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]]
    Hnode Hnonmutex Hempty.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (event_recycle sg s.(EventState) eid image) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    apply event_recycle_name_references. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (event_recycle sg s.(EventState) eid image)).
  { eapply pending_mutex_consistency_event_transport with (events := s.(EventState));
      [reflexivity| |tauto].
    intros slot after Hafter Htype; cbn [event_recycle inUsedEventStates] in Hafter.
    unfold kernel_map_set in Hafter; destruct (Z.eq_dec slot eid); [discriminate|].
    exists after; split; [exact Hafter|]. split; [exact Htype|reflexivity]. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split.
  - eapply event_recycle_preserves_in_range; eassumption.
  - split; [|cbn [replace_EventS]; tauto].
    eapply cross_module_consistency_event_remove;
      [exact Hnode|exact Hnonmutex|exact Hempty|reflexivity|reflexivity|exact Hcross].
Qed.

Lemma UCOS2_event_recycle_preserves_residual : forall sg s eid node image,
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(queueFields) = None ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg
      (replace_EventS (event_recycle sg s.(EventState) eid image) s).
Proof.
  intros sg s eid node image Hnode Hnone; unfold UCOS2_raw_rep_missing_task_storage_sched_event; simpl.
  sep_apply_l_atomic (queue_event_recycle_preserves_storage sg s.(EventState) eid node image Hnode Hnone).
  entailer!.
Qed.

(** Sem/Mbox recycling consumes the source-written Type/Ptr/Cnt image
    and new free root.  Other ECBs, all QCBs/buffers and the complete
    remaining global resources are retained, with no allocator free. *)
Lemma UCOS2_inv_merge_event_recycle : forall sg s eid node image,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) <> OS_EVENT_TYPE_MUTEX ->
  node.(queueFields) = None -> node.(waitList) = nil ->
  (store_map_missing_i (used_event_rep sg s.(TskState)) s.(EventState).(inUsedEventStates) eid **
   event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
     (event_recycle_image sg s.(EventState).(unUsedEventStates) image) **
   event_free_storage_rep sg s.(EventState) **
   sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid) **
  queue_storage_rep sg s.(EventState) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (event_recycle sg s.(EventState) eid image) s).
Proof.
  intros sg s eid node image Hvalid Hnode Hnonmutex Hnone Hempty.
  pose proof Hvalid as [_ [_ [_ [[Hpool [Hfree _]] _]]]].
  pose proof (UCOS2_event_recycle_preserves_validity sg s eid node image
    Hvalid Hnode Hnonmutex Hempty) as Hpost.
  sep_apply_l_atomic (event_recycle_reconstructs_raw_rep
    sg s.(TskState) s.(EventState) eid node image Hpool Hfree Hnode).
  sep_apply_l_atomic (queue_event_recycle_preserves_storage
    sg s.(EventState) eid node image Hnode Hnone).
  eapply derivable1_trans; [|apply UCOS2_inv_merge_updated_event_queue; exact Hpost]; entailer!.
Qed.

(** Queue deletion does not remove a Mutex claim.  An empty wait list,
    together with the existing backlink/closure invariant, proves that
    recycling cannot leave a dangling TCB Event reference. *)
Lemma UCOS2_queue_recycle_preserves_validity : forall sg s eid node image qid,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(waitList) = nil ->
  UCOS2_state_inv sg
    (replace_EventS (queue_recycle sg s.(EventState) eid image qid) s).
Proof.
  intros sg s eid node image qid [Hprofile [Htasks [Hsched [Hevents [Hcross Hrest]]]]]
    Hnode Htype Hempty.
  assert (HreferencesAfter : kernel_names_valid sg (replace_EventS (queue_recycle sg s.(EventState) eid image qid) s)).
  { apply kernel_names_valid_replace_event; [tauto|].
    apply event_recycle_name_references. }
  assert (HpendingAfter : pending_mutex_consistency sg s.(TskState)
    (queue_recycle sg s.(EventState) eid image qid)).
  { eapply pending_mutex_consistency_event_transport with (events := s.(EventState));
      [reflexivity| |tauto].
    intros slot after Hafter HtypeAfter; cbn [queue_recycle event_recycle inUsedEventStates] in Hafter.
    unfold kernel_map_set in Hafter; destruct (Z.eq_dec slot eid); [discriminate|].
    exists after; split; [exact Hafter|]. split; [exact HtypeAfter|reflexivity]. }
  split; [exact Hprofile|]; split; [exact Htasks|]; split; [exact Hsched|]; split.
  - eapply queue_recycle_preserves_event_in_range; eassumption.
  - split; [|cbn [replace_EventS]; tauto].
    eapply cross_module_consistency_event_remove;
      [exact Hnode|rewrite Htype; discriminate|exact Hempty|reflexivity|reflexivity|exact Hcross].
Qed.

(** Source-written QCB/ECB/free-root cells reconstruct both pool owners;
    the original caller buffer is returned as a separate resource.  No
    pure state transition creates these cells or deallocates the buffer. *)
Lemma UCOS2_inv_merge_queue_recycle : forall sg s free eid node q image slots,
  UCOS2_state_inv sg s ->
  queue_published_storage_binding s.(EventState) ->
  queue_pool_partition sg s.(EventState) free ->
  s.(EventState).(inUsedEventStates) eid = Some node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  node.(queueFields) = Some q -> node.(waitList) = nil ->
  ((store_map_missing_i (used_event_rep sg s.(TskState)) s.(EventState).(inUsedEventStates) eid **
    event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      (event_recycle_image sg s.(EventState).(unUsedEventStates) image) **
    event_free_storage_rep sg s.(EventState) **
    sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid) **
   ((store_map_missing_i (published_queue_node_rep sg s.(EventState))
       s.(EventState).(inUsedEventStates) eid **
     (sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg q.(qID) **
      (free_queue_node sg q.(qID) (queue_free_head sg free) ** store_free_queue_nodes sg free))) **
    queue_buffer_rep q slots)) ** UCOS2_raw_rep_missing_event_queue sg s |--
  UCOS2_inv sg (replace_EventS (queue_recycle sg s.(EventState) eid image q.(qID)) s) **
    PtrArray.mixed_full q.(qStart) q.(qSize) slots.
Proof.
  intros sg s free eid node q image slots Hvalid Hbinding Hpart Hnode Htype Hq Hempty.
  pose proof Hvalid as [_ [_ [_ [[Hpool [Hfree _]] _]]]].
  pose proof (UCOS2_queue_recycle_preserves_validity sg s eid node image q.(qID)
    Hvalid Hnode Htype Hempty) as Hafter.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono.
    + exact (queue_recycle_reconstructs_event_queue sg s.(TskState) s.(EventState)
        free eid node q image slots Hpool Hfree Hbinding Hpart Hnode Hq).
    + reflexivity.
  - sep_apply_l_atomic (UCOS2_inv_merge_updated_event_queue sg s
      (queue_recycle sg s.(EventState) eid image q.(qID)) Hafter); entailer!.
Qed.

Lemma UCOS2_event_task_remove_preserves_validity : forall sg s eid e tid old,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg (event_task_remove_state s eid e tid old).
Proof.
  intros sg s eid e tid old
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] He Hin Hold.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HpendingAfter : pending_mutex_consistency sg
    (event_task_remove_state s eid e tid old).(TskState)
    (event_task_remove_state s eid e tid old).(EventState)).
  { eapply pending_mutex_consistency_event_fields_update with (old := e);
      [exact He|reflexivity|reflexivity|exact Hpending]. }
  assert (HreferencesAfter : kernel_names_valid sg (event_task_remove_state s eid e tid old)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - eapply event_update_preserves_name_references; [exact He|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (event_task_remove_state s eid e tid old).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  unfold event_task_remove_state; split; [exact Hprofile|]; split.
  - eapply task_set_event_ptr_preserves_in_range; eauto.
  - split.
    + eapply sched_update_task_preserves_in_range; eauto; reflexivity.
    + split; [eapply event_remove_waiter_update_task_preserves_in_range; eauto|].
      split; [eapply event_task_remove_preserves_cross_module_consistency; eauto|].
      split.
      * intro Hrun; eapply task_update_preserves_idle_tail;
          [exact Hold|reflexivity|apply Hidle; exact Hrun].
      * split.
        2: { repeat (split; [assumption|]); exact HpendingAfter. }
        apply task_reserved_bits_clear_update_task; [exact Hstatus|exact (Hstatus tid old Hold)].
Qed.

Lemma UCOS2_event_task_remove_preserves_residual : forall sg s eid e tid old,
  s.(EventState).(inUsedEventStates) eid = Some e ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg (event_task_remove_state s eid e tid old).
Proof.
  intros sg s eid e tid old He.
  unfold UCOS2_raw_rep_missing_task_storage_sched_event, event_task_remove_state; simpl.
  sep_apply_l_atomic (queue_set_event_wait_list_preserves_storage
    sg s.(EventState) eid e (remove_Z_eqb tid e.(waitList)) He); entailer!.
Qed.

Lemma UCOS2_inv_merge_event_task_remove : forall sg s eid e tid old,
  UCOS2_state_inv sg s ->
  s.(EventState).(inUsedEventStates) eid = Some e -> In tid e.(waitList) ->
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  let post := event_task_remove_state s eid e tid old in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg post.(TskState) post.(SchedState) **
  event_raw_rep sg s.(TskState) post.(EventState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s eid e tid old Hvalid He Hin Hold post.
  pose proof (UCOS2_event_task_remove_preserves_validity sg s eid e tid old Hvalid He Hin Hold)
    as Hpost; fold post in Hpost.
  assert (Hindex : event_raw_rep sg s.(TskState) post.(EventState) =
    event_raw_rep sg post.(TskState) post.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  rewrite Hindex.
  sep_apply_l_atomic (UCOS2_event_task_remove_preserves_residual sg s eid e tid old He); fold post.
  unfold UCOS2_inv, UCOS2_raw_rep,
    UCOS2_raw_rep_missing_task_storage_sched, UCOS2_raw_rep_missing_task_storage_sched_event, task_shared_rep; entailer!.
Qed.

(** The resumed caller is actually ready, and EventTaskRemove (if needed)
    has already finished.  These are continuation/registration facts, not
    new runtime tests or a guarantee supplied by OS_Sched's name. *)
Lemma UCOS2_event_pend_cleanup_preserves_validity : forall sg s tid old clear_message,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil ->
  old.(tcbFlagNode) = 0 -> In tid s.(SchedState).(readyList) ->
  UCOS2_state_inv sg (event_pend_cleanup_state sg clear_message s tid old).
Proof.
  intros sg s tid old clear_message
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]]
    Hold Hnull Hmulti Hflagnull Hready.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  pose proof Hpending as HpendingAfter.
  assert (HreferencesAfter : kernel_names_valid sg (event_pend_cleanup_state sg clear_message s tid old)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|destruct sg.(osKernelConfig).(cfgEventMultiEnabled), clear_message; reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (event_pend_cleanup_state sg clear_message s tid old).(TskState)
    s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold| | | |exact Hstacks];
      destruct sg.(osKernelConfig).(cfgEventMultiEnabled), clear_message; reflexivity. }
  destruct (proj1 (proj1 Hsched) tid Hready) as [found [Hfound [_ Heffective]]].
  assert (found = old) by congruence; subst found.
  pose proof (task_event_pend_cleanup_preserves_ready
    sg.(osKernelConfig).(cfgEventMultiEnabled) clear_message old Heffective) as Hnewready.
  assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e -> ~ In tid e.(waitList)).
  { eapply event_unregistered_task_not_waiting; [|exact Hold|exact Hnull].
    destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]]; exact Hentries. }
  unfold event_pend_cleanup_state; split; [exact Hprofile|]; split.
  - eapply task_event_pend_cleanup_preserves_in_range; eauto.
  - split.
    + eapply sched_update_task_preserves_in_range; [exact Hsched|exact Hold| |].
      * destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
      * rewrite Hnewready, Heffective; reflexivity.
    + split; [eapply event_update_unlisted_task_preserves_in_range; eauto|].
      split.
      * eapply event_pend_cleanup_preserves_cross_module_consistency; eauto.
      * split.
        -- intro Hrunning; eapply task_update_preserves_idle_tail;
             [exact Hold| |apply Hidle; exact Hrunning].
           destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity.
        -- split.
           2: { repeat (split; [assumption|]); exact HpendingAfter. }
           apply task_reserved_bits_clear_update_task; [exact Hstatus|].
           eapply task_effectively_ready_reserved_bits_clear; exact Hnewready.
Qed.

Lemma UCOS2_message_pend_cleanup_preserves_validity : forall sg s tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil ->
  old.(tcbFlagNode) = 0 -> In tid s.(SchedState).(readyList) ->
  UCOS2_state_inv sg (message_pend_cleanup_state sg s tid old).
Proof. intros; eapply UCOS2_event_pend_cleanup_preserves_validity; eassumption. Qed.

Lemma UCOS2_event_pend_cleanup_preserves_residual : forall sg s tid old clear_message,
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg (event_pend_cleanup_state sg clear_message s tid old).
Proof. intros; reflexivity. Qed.

Lemma UCOS2_inv_merge_event_pend_cleanup : forall sg s tid old clear_message,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  old.(eventPtr) = None -> old.(eventMultiWaitEvents) = nil ->
  old.(tcbFlagNode) = 0 -> In tid s.(SchedState).(readyList) ->
  let post := event_pend_cleanup_state sg clear_message s tid old in
  task_public_storage sg post.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s tid old clear_message Hvalid Hold Hnull Hmulti Hflagnull Hready post.
  assert (Hprio : (task_event_pend_cleanup sg.(osKernelConfig).(cfgEventMultiEnabled) clear_message old).(curPrio)
    = old.(curPrio)) by (destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity).
  assert (Hevent : event_raw_rep sg s.(TskState) s.(EventState) =
    event_raw_rep sg post.(TskState) s.(EventState)).
  { apply event_raw_rep_change_task_index; apply event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; eauto. }
  assert (Hsched : sched_raw_rep sg s.(TskState) s.(SchedState) =
    sched_raw_rep sg post.(TskState) s.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot Hin.
    unfold post, event_pend_cleanup_state; cbn [replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates].
    destruct (Z.eqb slot tid) eqn:E; [|reflexivity].
    apply Z.eqb_eq in E; subst slot; rewrite Hold.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled); reflexivity. }
  pose proof (UCOS2_event_pend_cleanup_preserves_validity
    sg s tid old clear_message Hvalid Hold Hnull Hmulti Hflagnull Hready) as Hpost; fold post in Hpost.
  rewrite Hsched; unfold UCOS2_raw_rep_missing_task_storage_sched; rewrite Hevent.
  unfold UCOS2_inv, UCOS2_raw_rep, UCOS2_raw_rep_missing_task_storage_sched, task_shared_rep;
    unfold post, event_pend_cleanup_state in *; cbn [replace_TskS TskState SchedState EventState];
    entailer!.
  cbn [replace_TskS IntrState TickState FlagState MemoryState TimerState
    StatsState ControlState NameState glob_task_set_usedtask parkedTaskStacks].
  entailer!.
Qed.
