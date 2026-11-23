Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import AUXLib.ListLib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_status.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.task_retirement.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.sem.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_post_spec.

Import ListNotations TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Function-specific mathematical consequences for OSTimeTick.  These
    declarations do not supply a contract for App_TimeTickHook, OSTmrSignal
    or the CPU port, and do not assert an atomic whole-function execution.
    The scan fold below describes a serialized, already selected list of
    task identifiers.  Its source-level use additionally requires a real
    caller protocol for the reads outside the per-task critical intervals. *)

Definition time_tick_counted_state (s : UCOS2_Verify_State)
  : UCOS2_Verify_State := replace_TickS (tick_counter_advance s.(TickState)) s.

Definition time_tick_process_tasks (s : UCOS2_Verify_State) : bool :=
  fst (tick_step_advance s.(SchedState).(isRunning) s.(TickState)).

Definition time_tick_clock_step_state (s : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  replace_TickS (snd (tick_step_advance s.(SchedState).(isRunning) s.(TickState))) s.

Lemma time_tick_clock_observation : forall s,
  (time_tick_clock_step_state s).(TickState).(ostime) =
    (s.(TickState).(ostime) + 1) mod 4294967296.
Proof.
  intro s; unfold time_tick_clock_step_state, tick_step_advance.
  destruct s.(SchedState).(isRunning); [destruct (tick_step_decision _)|];
    reflexivity.
Qed.

Lemma time_tick_clock_step_in_range : forall s,
  0 <= s.(TickState).(tickStepState) < 256 ->
  0 <= (time_tick_clock_step_state s).(TickState).(ostime) < 4294967296 /\
  0 <= (time_tick_clock_step_state s).(TickState).(tickStepState) < 256.
Proof.
  intros s Hstep; split.
  - rewrite time_tick_clock_observation; apply Z.mod_pos_bound; lia.
  - unfold time_tick_clock_step_state, tick_step_advance, tick_step_decision.
    destruct s.(SchedState).(isRunning); [|exact Hstep].
    destruct (Z.eqb s.(TickState).(tickStepState) 0);
      [|destruct (Z.eqb s.(TickState).(tickStepState) 1);
        [|destruct (Z.eqb s.(TickState).(tickStepState) 2)]]; cbn; lia.
Qed.

Lemma time_tick_not_running : forall s,
  s.(SchedState).(isRunning) = false ->
  time_tick_process_tasks s = false /\
  time_tick_clock_step_state s = time_tick_counted_state s.
Proof.
  intros s Hrun; unfold time_tick_process_tasks, time_tick_clock_step_state,
    tick_step_advance; rewrite Hrun; split; reflexivity.
Qed.

Lemma time_tick_running_step_cases : forall s,
  s.(SchedState).(isRunning) = true ->
  (time_tick_process_tasks s,
   (time_tick_clock_step_state s).(TickState).(tickStepState)) =
    tick_step_decision s.(TickState).(tickStepState).
Proof.
  intros s Hrun; unfold time_tick_process_tasks, time_tick_clock_step_state,
    tick_step_advance; rewrite Hrun; destruct (tick_step_decision _); reflexivity.
Qed.

Lemma time_tick_step_wait : forall s,
  s.(SchedState).(isRunning) = true -> s.(TickState).(tickStepState) = 1 ->
  time_tick_process_tasks s = false /\
  (time_tick_clock_step_state s).(TickState).(tickStepState) = 1.
Proof.
  intros s Hrun Hstep; pose proof (time_tick_running_step_cases s Hrun) as H.
  rewrite Hstep in H; inversion H; auto.
Qed.

Lemma time_tick_step_once : forall s,
  s.(SchedState).(isRunning) = true -> s.(TickState).(tickStepState) = 2 ->
  time_tick_process_tasks s = true /\
  (time_tick_clock_step_state s).(TickState).(tickStepState) = 1.
Proof.
  intros s Hrun Hstep; pose proof (time_tick_running_step_cases s Hrun) as H.
  rewrite Hstep in H; inversion H; auto.
Qed.

Lemma time_tick_step_invalid : forall step,
  step <> 0 -> step <> 1 -> step <> 2 -> tick_step_decision step = (true, 0).
Proof.
  intros step H0 H1 H2; unfold tick_step_decision.
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1),
    (proj2 (Z.eqb_neq _ _) H2); reflexivity.
Qed.

Lemma time_tick_clock_step_preserves_state_inv : forall sg s,
  UCOS2_state_inv sg s -> UCOS2_state_inv sg (time_tick_clock_step_state s).
Proof.
  intros sg s H; unfold time_tick_clock_step_state, UCOS2_state_inv,
    UCOS2_state_inv_with_ready in *; exact H.
Qed.

Lemma time_tick_task_step_preserves_ready : forall sg tid t s,
  task_in_range sg s.(TskState) ->
  sched_ready_in_range sg s.(TskState) s.(SchedState) ->
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_status_reserved_bits_clear false t.(stat) ->
  sched_ready_in_range sg (tick_task_step sg tid t s).(TskState)
    (tick_task_step sg tid t s).(SchedState).
Proof.
  intros sg tid t s Htasks Hready Hlookup Hbits.
  apply sched_ready_except_nil_iff.
  eapply tick_task_step_preserves_ready_except;
    [exact Htasks|apply sched_ready_except_nil_iff; exact Hready|
     exact Hlookup|exact Hbits|].
  intros slot node Hin; contradiction.
Qed.

Lemma time_tick_task_step_lifecycle_eq : forall sg tid t s,
  (tick_task_step sg tid t s).(TskState).(taskLifecycle) =
    s.(TskState).(taskLifecycle) /\
  (tick_task_step sg tid t s).(TskState).(parkedTaskStacks) =
    s.(TskState).(parkedTaskStacks).
Proof.
  intros; unfold tick_task_step; destruct (Z.eqb t.(dly) 0);
    [|destruct (Z.eqb (tick_task_update t).(dly) 0)]; split; reflexivity.
Qed.

Lemma time_tick_task_step_preserves_state_inv : forall sg tid t s,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  UCOS2_state_inv sg (tick_task_step sg tid t s).
Proof.
  intros sg tid t s Hmulti Hvalid Hlookup.
  destruct Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hbits Hmodules]]]]]]].
  destruct Hsched as [Hready Hmetadata].
  destruct Hmodules as
    [Hflag [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  pose proof (tick_task_preserves_non_timeout_fields t) as Hfields.
  cbn zeta in Hfields.
  assert (Hprio : (tick_task_update t).(curPrio) = t.(curPrio)) by tauto.
  assert (Hbits_t : task_status_reserved_bits_clear false t.(stat)).
  { rewrite <- Hmulti; apply (Hbits tid t Hlookup). }
  pose proof (time_tick_task_step_preserves_ready sg tid t s Htasks Hready
    Hlookup Hbits_t) as Hready_post.
  pose proof (tick_task_step_preserves_task_in_range sg tid t s Htasks Hlookup)
    as Htasks_post.
  pose proof (tick_task_step_preserves_event_in_range sg s tid t Hlookup Hevents)
    as Hevents_post.
  pose proof (tick_task_step_preserves_cross_module_consistency sg s tid t
    Hlookup Hcross) as Hcross_post.
  assert (Hidle_post :
    (tick_task_step sg tid t s).(SchedState).(isRunning) = true ->
    task_idle_tail sg (tick_task_step sg tid t s).(TskState)).
  { rewrite tick_task_step_task_state_eq by exact Hlookup.
    intros Hrun; eapply task_update_preserves_idle_tail;
      [exact Hlookup|exact Hprio|].
    apply Hidle; unfold tick_task_step, sched_wake_by_status in Hrun.
    destruct (Z.eqb t.(dly) 0) in Hrun;
      [exact Hrun|destruct (Z.eqb (tick_task_update t).(dly) 0) in Hrun;
        [destruct (task_status_is_suspended _) in Hrun|]; exact Hrun]. }
  assert (Hbits_post : task_reserved_bits_clear sg
    (tick_task_step sg tid t s).(TskState)).
  { rewrite tick_task_step_task_state_eq by exact Hlookup.
    apply task_reserved_bits_clear_update_task; [exact Hbits|].
    apply tick_task_preserves_reserved_bits_clear; exact (Hbits tid t Hlookup). }
  assert (Hreferences_post : kernel_names_valid sg (tick_task_step sg tid t s)).
  { unfold tick_task_step; destruct (Z.eqb t.(dly) 0); [exact Hreferences|].
    destruct (Z.eqb (tick_task_update t).(dly) 0).
    all: assert (Hname : (tick_task_update t).(tcbTaskName) = t.(tcbTaskName)) by tauto.
    all: eapply kernel_names_valid_frame;
      [exact Hreferences|reflexivity| | | | |].
    all: first [eapply task_update_name_references; [exact Hlookup|exact Hname]
      | intros; assumption]. }
  assert (Hstacks_post : parked_stacks_consistent
    (tick_task_step sg tid t s).(TskState)
    (tick_task_step sg tid t s).(TskState).(parkedTaskStacks)).
  { rewrite tick_task_step_task_state_eq by exact Hlookup.
    cbn [glob_task_set_usedtask parkedTaskStacks].
    eapply parked_stacks_consistent_update_task; [exact Hlookup| | | |exact Hstacks]; tauto. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]. split; [exact Htasks_post|].
  split; [split; [exact Hready_post|]|].
  - unfold tick_task_step, sched_wake_by_status;
      destruct (Z.eqb t.(dly) 0); [exact Hmetadata|];
      destruct (Z.eqb (tick_task_update t).(dly) 0);
      [destruct (task_status_is_suspended _)|]; exact Hmetadata.
  - split; [exact Hevents_post|]. split; [exact Hcross_post|].
    split; [exact Hidle_post|]. split; [exact Hbits_post|].
    unfold tick_task_step in Hreferences_post, Hstacks_post |- *; destruct (Z.eqb t.(dly) 0);
      [|destruct (Z.eqb (tick_task_update t).(dly) 0)];
      exact (conj Hflag (conj Hmemory (conj Htimer (conj Hstats
        (conj Hcontrol (conj Hnames (conj Hreferences_post
          (conj Hstacks_post Hpending)))))))).
Qed.

(** A fold over task identifiers reuses the canonical per-task operation.
    The absent-lookup arm is only the total mathematical extension; a C
    cursor step needs the separate live lookup and idle-termination facts.
    No source path is removed by an invariant-dependent transformer guard. *)
Definition time_tick_visit (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (tid : TaskID) : UCOS2_Verify_State :=
  match s.(TskState).(inUsedTaskStates) tid with
  | Some t => tick_task_step sg tid t s
  | None => s
  end.

Definition time_tick_scan (sg : StableGlobVars) (initial : UCOS2_Verify_State)
  (visited : list TaskID) : UCOS2_Verify_State :=
  fold_left (time_tick_visit sg) visited initial.

Lemma time_tick_scan_app : forall sg initial first rest,
  time_tick_scan sg initial (first ++ rest) =
  time_tick_scan sg (time_tick_scan sg initial first) rest.
Proof. intros; unfold time_tick_scan; apply fold_left_app. Qed.

Lemma time_tick_scan_preserves_state_inv : forall sg visited initial,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg initial -> UCOS2_state_inv sg (time_tick_scan sg initial visited).
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intros initial Hmulti Hvalid;
    [exact Hvalid|].
  change (UCOS2_state_inv sg (time_tick_scan sg (time_tick_visit sg initial tid) rest)).
  apply IH; [exact Hmulti|]. unfold time_tick_visit.
  destruct (initial.(TskState).(inUsedTaskStates) tid) as [t|] eqn:Hlookup;
    [eapply time_tick_task_step_preserves_state_inv; eassumption|exact Hvalid].
Qed.

Lemma time_tick_scan_preserves_clock : forall sg visited initial,
  (time_tick_scan sg initial visited).(TickState) = initial.(TickState).
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intro initial;
    [reflexivity|].
  change ((time_tick_scan sg (time_tick_visit sg initial tid) rest).(TickState) =
    initial.(TickState)).
  rewrite IH; unfold time_tick_visit.
  destruct (initial.(TskState).(inUsedTaskStates) tid) as [t|]; [|reflexivity].
  pose proof (f_equal TickState (tick_task_step_non_task_sched_state_eq sg tid t initial)) as H.
  exact H.
Qed.

Lemma time_tick_scan_preserves_unvisited_task : forall sg visited initial slot,
  ~ In slot visited ->
  (time_tick_scan sg initial visited).(TskState).(inUsedTaskStates) slot =
    initial.(TskState).(inUsedTaskStates) slot.
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intros initial slot Hnot;
    [reflexivity|].
  change ((time_tick_scan sg (time_tick_visit sg initial tid) rest).(TskState).(inUsedTaskStates)
    slot = initial.(TskState).(inUsedTaskStates) slot).
  rewrite IH by (intro Hin; apply Hnot; right; exact Hin).
  unfold time_tick_visit; destruct (initial.(TskState).(inUsedTaskStates) tid)
    as [t|] eqn:Hlookup; [|reflexivity].
  apply tick_task_step_other_task_eq; intro Heq; apply Hnot; left; symmetry; exact Heq.
Qed.

Lemma time_tick_scan_updates_visited_task_once : forall sg visited initial slot old,
  NoDup visited -> In slot visited ->
  initial.(TskState).(inUsedTaskStates) slot = Some old ->
  (time_tick_scan sg initial visited).(TskState).(inUsedTaskStates) slot =
    Some (tick_task_update old).
Proof.
  intros sg visited; induction visited as [|tid rest IH];
    intros initial slot old Hnodup Hin Hlookup; [contradiction|].
  inversion Hnodup as [|? ? Hnot Hrest]; subst.
  change ((time_tick_scan sg (time_tick_visit sg initial tid) rest).(TskState).(inUsedTaskStates)
    slot = Some (tick_task_update old)).
  destruct Hin as [Heq|Hin].
  - subst slot; rewrite time_tick_scan_preserves_unvisited_task by exact Hnot.
    unfold time_tick_visit; rewrite Hlookup.
    rewrite tick_task_step_task_state_eq by exact Hlookup.
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
  - assert (Hdifferent : slot <> tid).
    { intros ->; contradiction. }
    apply IH; [exact Hrest|exact Hin|]. unfold time_tick_visit.
    destruct (initial.(TskState).(inUsedTaskStates) tid) as [node|] eqn:Hnode;
      [rewrite tick_task_step_other_task_eq by exact Hdifferent|]; exact Hlookup.
Qed.

Lemma time_tick_scan_task_lifecycle_eq : forall sg visited initial,
  (time_tick_scan sg initial visited).(TskState).(taskLifecycle) =
    initial.(TskState).(taskLifecycle).
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intro initial;
    [reflexivity|].
  change ((time_tick_scan sg (time_tick_visit sg initial tid) rest).(TskState).(taskLifecycle) =
    initial.(TskState).(taskLifecycle)).
  rewrite IH; unfold time_tick_visit.
  destruct (initial.(TskState).(inUsedTaskStates) tid) as [t|]; [|reflexivity].
  exact (proj1 (time_tick_task_step_lifecycle_eq sg tid t initial)).
Qed.

Definition time_tick_serialized_after_hook (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : UCOS2_Verify_State :=
  let counted := time_tick_clock_step_state s in
  if time_tick_process_tasks s then
    time_tick_scan sg counted (removelast s.(TskState).(taskLifecycle).(taskActiveOrder))
  else counted.

Lemma time_tick_serialized_after_hook_preserves_state_inv : forall sg s,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> UCOS2_state_inv sg (time_tick_serialized_after_hook sg s).
Proof.
  intros sg s Hmulti Hvalid; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks s).
  - apply time_tick_scan_preserves_state_inv;
      [exact Hmulti|apply time_tick_clock_step_preserves_state_inv; exact Hvalid].
  - apply time_tick_clock_step_preserves_state_inv; exact Hvalid.
Qed.

Lemma time_tick_serialized_after_hook_clock : forall sg s,
  (time_tick_serialized_after_hook sg s).(TickState).(ostime) =
    (s.(TickState).(ostime) + 1) mod 4294967296.
Proof.
  intros sg s; unfold time_tick_serialized_after_hook.
  destruct (time_tick_process_tasks s);
    [rewrite time_tick_scan_preserves_clock|]; apply time_tick_clock_observation.
Qed.

Lemma time_tick_serialized_after_hook_not_running : forall sg s,
  s.(SchedState).(isRunning) = false ->
  time_tick_serialized_after_hook sg s = time_tick_counted_state s.
Proof.
  intros sg s Hrun; destruct (time_tick_not_running s Hrun) as [Hprocess Hstate].
  unfold time_tick_serialized_after_hook; rewrite Hprocess; exact Hstate.
Qed.

Lemma time_tick_task_storage_merge_updated : forall sg tasks tid old,
  task_slot_storage_rep sg tid (task_layout_image sg (tick_task_update old)) **
  task_public_storage_without_task sg tasks tid |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (tick_task_update old)).
Proof. intros; apply task_public_storage_merge_updated_task. Qed.

(** This is the port's private INT16U OSTmrCtr, distinct from OSTime and
    TimerState.timerTime.  It is evaluated after App_TimeTickHook and
    before the optional OSTmrSignal call.  The selected 100/10 frequency
    ratio is explicit; no application callback implementation is selected. *)
Definition time_tick_hook_counter_step (counter : Z) : Z * bool :=
  let advanced := kernel_u16 (counter + 1) in
  if Z.leb (100 / 10) advanced then (0, true) else (advanced, false).

Lemma time_tick_hook_counter_in_range : forall counter,
  0 <= fst (time_tick_hook_counter_step counter) < 10.
Proof.
  intro counter; unfold time_tick_hook_counter_step.
  destruct (Z.leb (100 / 10) (kernel_u16 (counter + 1))) eqn:Htest;
    [cbn; lia|].
  apply Z.leb_gt in Htest; cbn [fst].
  pose proof (kernel_u16_in_range (counter + 1)); change (kernel_u16 (counter + 1) < 10) in Htest.
  lia.
Qed.

Lemma time_tick_hook_counter_regular_step : forall counter,
  0 <= counter < 9 -> time_tick_hook_counter_step counter = (counter + 1, false).
Proof.
  intros counter H; unfold time_tick_hook_counter_step.
  rewrite kernel_u16_identity by lia.
  change ((if 10 <=? counter + 1 then (0, true) else (counter + 1, false)) =
    (counter + 1, false)).
  assert (Htest : (10 <=? counter + 1) = false) by (apply Z.leb_gt; lia).
  rewrite Htest; reflexivity.
Qed.

Lemma time_tick_hook_counter_threshold : time_tick_hook_counter_step 9 = (0, true).
Proof. reflexivity. Qed.

Lemma time_tick_hook_counter_unsigned_wrap : time_tick_hook_counter_step 65535 = (0, false).
Proof. reflexivity. Qed.

(** Supported external callback interface.  The application keeps its own
    independently specified resource and records the ordered OSSemPost
    requests/results it makes while IRQ and FIQ remain masked.  It may do
    arbitrary work on that resource, and may return after any finite number
    of these kernel calls.  This is a callback CLASS, not a selected callback
    body, a claim about arbitrary kernel-mutating callbacks, or termination.
    The application relation does not mention a desired kernel endpoint or
    an invariant-preservation certificate.  Kernel endpoints below are
    derived from the canonical post/wake operations. *)
Definition TimeTickPostResult : Type := OSErrCode * bool.
Definition TimeTickPostLog : Type := list (addr * TimeTickPostResult).

Record TimeTickApplicationResources : Type := {
  time_tick_application_own : Z -> Assertion;
  time_tick_application_return : Z -> TimeTickPostLog -> Z -> Prop;
}.

(** The bool records OS_Sched being CALLED by OSSemPost, not a switch.
    These are the existing canonical ordered argument/type/critical parts.
    A type error needs a readable, live ECB, but does not require SEM type.
    NULL error needs no ECB.  No invalid pointer is silently dereferenced. *)
Inductive time_tick_post_call (sg : StableGlobVars) (pointer : addr)
  : UCOS2_Verify_State -> TimeTickPostResult -> UCOS2_Verify_State -> Prop :=
| time_tick_post_argument_error : forall s error,
    sem_post_argument_error sg pointer = Some error ->
    time_tick_post_call sg pointer s (error, false) s
| time_tick_post_type_error : forall s eid e error,
    sem_post_argument_error sg pointer = None ->
    pointer = event_pool_addr sg eid ->
    s.(EventState).(inUsedEventStates) eid = Some e ->
    sem_post_type_error (encode_event_type e.(eventType)) = Some error ->
    time_tick_post_call sg pointer s (error, false) s
| time_tick_post_critical : forall s eid e result after,
    sem_post_argument_error sg pointer = None ->
    pointer = event_pool_addr sg eid ->
    s.(EventState).(inUsedEventStates) eid = Some e ->
    sem_post_type_error (encode_event_type e.(eventType)) = None ->
    sem_post_critical sg eid s result after ->
    time_tick_post_call sg pointer s result after.

Definition time_tick_post_readable (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (pointer : addr) : Prop :=
  (exists error, sem_post_argument_error sg pointer = Some error) \/
  exists eid e, pointer = event_pool_addr sg eid /\
    s.(EventState).(inUsedEventStates) eid = Some e.

Lemma time_tick_post_type_none : forall e,
  sem_post_type_error (encode_event_type e.(eventType)) = None ->
  e.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros e H; destruct e.(eventType);
    cbn [sem_post_type_error encode_event_type] in H; try discriminate; reflexivity.
Qed.

Lemma time_tick_post_call_exists : forall sg s pointer,
  UCOS2_state_inv sg s -> time_tick_post_readable sg s pointer ->
  exists result after, time_tick_post_call sg pointer s result after.
Proof.
  intros sg s pointer Hvalid Hreadable.
  destruct (sem_post_argument_error sg pointer) as [error|] eqn:Hargument.
  - exists (error, false), s; apply time_tick_post_argument_error; exact Hargument.
  - destruct Hreadable as [[error Hbad]|[eid [e [Hpointer He]]]]; [congruence|].
    destruct (sem_post_type_error (encode_event_type e.(eventType))) as [error|] eqn:Htype.
    + exists (error, false), s; eapply time_tick_post_type_error; eassumption.
    + destruct (sem_post_critical_exists sg s eid e Hvalid He
        (time_tick_post_type_none e Htype)) as [result [after Hstep]].
      exists result, after; eapply time_tick_post_critical; eassumption.
Qed.

Lemma time_tick_post_call_preserves_state_inv : forall sg pointer s result after,
  time_tick_post_call sg pointer s result after ->
  UCOS2_state_inv sg s -> UCOS2_state_inv sg after.
Proof.
  intros sg pointer s result after Hcall Hvalid; destruct Hcall; try exact Hvalid.
  eapply sem_post_critical_preserves_validity; eauto using time_tick_post_type_none.
Qed.

Lemma time_tick_post_call_preserves_residual : forall sg pointer s result after,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg pointer s result after Hcall Hvalid; destruct Hcall; try reflexivity.
  eapply sem_post_critical_preserves_residual; eauto using time_tick_post_type_none.
Qed.

Lemma time_tick_post_call_preserves_invocation : forall sg pointer s result after invocation origin,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg pointer s result after invocation origin Hcall Hvalid Hactive.
  destruct Hcall; try exact Hactive.
  eapply sem_post_critical_preserves_invocation; eauto using time_tick_post_type_none.
Qed.

Lemma time_tick_post_call_state_frame : forall sg pointer s result after,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  replace_TskS s.(TskState)
    (replace_SchedS s.(SchedState) (replace_EventS s.(EventState) after)) = s /\
  after.(TskState).(taskLifecycle) = s.(TskState).(taskLifecycle) /\
  after.(SchedState).(isRunning) = s.(SchedState).(isRunning).
Proof.
  intros sg pointer s result after Hcall Hvalid; destruct Hcall.
  - split; [destruct s; reflexivity|split; reflexivity].
  - split; [destruct s; reflexivity|split; reflexivity].
  - assert (Hkind := time_tick_post_type_none e H2).
    destruct H3 as [node [Hnode Hstep]].
    assert (node = e) by congruence; subst node.
    destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
    + destruct Hstep as [fields [Hfields Hstep]].
      destruct (Z.ltb fields.(semCount) 65535); destruct Hstep as [_ ->];
        (split; [destruct s; reflexivity|split; reflexivity]).
    + destruct Hstep as [_ [priority Hstep]]; apply Z.eqb_neq in Hempty.
      assert (Hpend : event_type_to_pend_type e.(eventType) = Some PendSem)
        by (rewrite Hkind; reflexivity).
      destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after
        Hvalid H1 Hpend Hempty Hstep)
        as [head [tail [old [_ [_ [_ [-> _]]]]]]].
      split; [destruct s; reflexivity|].
      split; [reflexivity|].
      unfold event_wake_state, sched_wake_by_status.
      destruct (task_status_is_suspended _); reflexivity.
Qed.

(** The source OS_Sched guard is the actual nesting byte, not the
    allocation/invocation origin.  With this nonzero byte its entire write
    and context-switch arm is skipped.  Save/Restore and their normal return
    are still platform implementation obligations. *)
Lemma time_tick_post_call_isr_guard_false : forall sg pointer s result after,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  s.(IntrState).(intNesting) <> 0 ->
  Z.eqb after.(IntrState).(intNesting) 0 = false.
Proof.
  intros sg pointer s result after Hcall Hvalid Hnest.
  pose proof (f_equal IntrState
    (proj1 (time_tick_post_call_state_frame sg pointer s result after Hcall Hvalid))) as Hframe.
  cbn in Hframe; rewrite Hframe; apply Z.eqb_neq; exact Hnest.
Qed.

Lemma time_tick_post_call_intr_timer_eq : forall sg pointer s result after,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  after.(IntrState) = s.(IntrState) /\ after.(TimerState) = s.(TimerState).
Proof.
  intros sg pointer s result after Hcall Hvalid.
  pose proof (proj1 (time_tick_post_call_state_frame sg pointer s result after Hcall Hvalid)) as Hframe.
  split; [exact (f_equal IntrState Hframe)|exact (f_equal TimerState Hframe)].
Qed.

Lemma time_tick_post_call_preserves_live_event : forall sg pointer s result after slot,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  (exists event, s.(EventState).(inUsedEventStates) slot = Some event) ->
  exists event, after.(EventState).(inUsedEventStates) slot = Some event.
Proof.
  intros sg pointer s result after slot Hcall Hvalid Hlive; destruct Hcall;
    try exact Hlive.
  assert (Hkind := time_tick_post_type_none e H2).
  destruct H3 as [node [Hnode Hstep]]; assert (node = e) by congruence; subst node.
  destruct (Z.eqb (encode_event_wait_grp e.(waitList) s.(TskState)) 0) eqn:Hempty.
  - destruct Hstep as [fields [_ Hstep]].
    destruct (Z.ltb fields.(semCount) 65535); destruct Hstep as [_ ->]; [|exact Hlive].
    cbn [sem_count_update_state replace_EventS EventState update_event_field_raw inUsedEventStates].
    destruct (Z.eqb slot eid); [eexists; reflexivity|exact Hlive].
  - destruct Hstep as [_ [priority Hstep]]; apply Z.eqb_neq in Hempty.
    assert (Hpend : event_type_to_pend_type e.(eventType) = Some PendSem)
      by (rewrite Hkind; reflexivity).
    destruct (event_wake_decompose sg s eid e PendSem 0 PendOK priority after
      Hvalid H1 Hpend Hempty Hstep)
      as [head [tail [old [_ [_ [_ [-> _]]]]]]].
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS EventState
      update_event_field_raw inUsedEventStates].
    destruct (Z.eqb slot eid); [eexists; reflexivity|exact Hlive].
Qed.

Lemma time_tick_post_call_preserves_readable : forall sg pointer s result after observed,
  time_tick_post_call sg pointer s result after -> UCOS2_state_inv sg s ->
  time_tick_post_readable sg s observed -> time_tick_post_readable sg after observed.
Proof.
  intros sg pointer s result after observed Hcall Hvalid [Herror|[slot [event [Hptr Hlive]]]].
  - left; exact Herror.
  - right; destruct (time_tick_post_call_preserves_live_event sg pointer s result after slot
      Hcall Hvalid (ex_intro _ event Hlive)) as [new Hnew].
    exists slot, new; split; assumption.
Qed.

Inductive time_tick_application_posts (sg : StableGlobVars)
  : UCOS2_Verify_State -> TimeTickPostLog -> UCOS2_Verify_State -> Prop :=
| time_tick_application_posts_nil : forall s,
    time_tick_application_posts sg s [] s
| time_tick_application_posts_cons : forall s pointer result middle rest after,
    time_tick_post_call sg pointer s result middle ->
    time_tick_application_posts sg middle rest after ->
    time_tick_application_posts sg s ((pointer, result) :: rest) after.

Lemma time_tick_application_posts_preserves_state_inv : forall sg s log after,
  time_tick_application_posts sg s log after ->
  UCOS2_state_inv sg s -> UCOS2_state_inv sg after.
Proof.
  intros sg s log after Hposts; induction Hposts; intro Hvalid; [exact Hvalid|].
  apply IHHposts; eapply time_tick_post_call_preserves_state_inv; eassumption.
Qed.

Lemma time_tick_application_posts_preserves_residual : forall sg s log after,
  time_tick_application_posts sg s log after -> UCOS2_state_inv sg s ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros sg s log after Hposts; induction Hposts; intro Hvalid; [reflexivity|].
  sep_apply_l_atomic (time_tick_post_call_preserves_residual sg pointer s result middle H Hvalid).
  sep_apply_l_atomic (IHHposts (time_tick_post_call_preserves_state_inv sg pointer s result middle H Hvalid)).
  entailer!.
Qed.

Lemma time_tick_application_posts_preserves_invocation : forall sg s log after,
  time_tick_application_posts sg s log after -> UCOS2_state_inv sg s ->
  forall invocation origin, task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros sg s log after Hposts; induction Hposts; intros Hvalid invocation origin Hactive;
    [exact Hactive|].
  apply IHHposts; [eapply time_tick_post_call_preserves_state_inv; eassumption|].
  eapply time_tick_post_call_preserves_invocation; eassumption.
Qed.

Lemma time_tick_application_posts_intr_timer_eq : forall sg s log after,
  time_tick_application_posts sg s log after -> UCOS2_state_inv sg s ->
  after.(IntrState) = s.(IntrState) /\ after.(TimerState) = s.(TimerState).
Proof.
  intros sg s log after Hposts; induction Hposts; intro Hvalid;
    [split; reflexivity|].
  destruct (time_tick_post_call_intr_timer_eq sg pointer s result middle H Hvalid)
    as [Hintr Htimer].
  destruct (IHHposts (time_tick_post_call_preserves_state_inv sg pointer s result middle H Hvalid))
    as [Hafter_intr Hafter_timer].
  split; congruence.
Qed.

Lemma time_tick_application_posts_preserves_readable : forall sg s log after observed,
  time_tick_application_posts sg s log after -> UCOS2_state_inv sg s ->
  time_tick_post_readable sg s observed -> time_tick_post_readable sg after observed.
Proof.
  intros sg s log after observed Hposts; induction Hposts; intros Hvalid Hread;
    [exact Hread|].
  apply IHHposts.
  - eapply time_tick_post_call_preserves_state_inv; eassumption.
  - eapply time_tick_post_call_preserves_readable; eassumption.
Qed.

Definition time_tick_hook_result (app : TimeTickApplicationResources)
  (sg : StableGlobVars) (before_app before_counter : Z)
  (before : UCOS2_Verify_State) (after_app after_counter : Z)
  (after : UCOS2_Verify_State) : Prop :=
  exists log middle,
    app.(time_tick_application_return) before_app log after_app /\
    time_tick_application_posts sg before log middle /\
    after_counter = fst (time_tick_hook_counter_step before_counter) /\
    if snd (time_tick_hook_counter_step before_counter) then
      exists result, time_tick_post_call sg middle.(TimerState).(timerSignalSem)
        middle result after
    else after = middle.

(** Any supported normal callback endpoint has a port-hook endpoint.  Posts
    preserve live ECB ownership and the timer handle, so the final signal
    does not gain a hidden readability assumption after callback execution. *)
Lemma time_tick_hook_result_exists_from_application : forall app sg a c s a' log middle,
  app.(time_tick_application_return) a log a' ->
  time_tick_application_posts sg s log middle -> UCOS2_state_inv sg s ->
  time_tick_post_readable sg s s.(TimerState).(timerSignalSem) ->
  exists c' after, time_tick_hook_result app sg a c s a' c' after.
Proof.
  intros app sg a c s a' log middle Hreturn Hposts Hvalid Hread.
  pose proof (time_tick_application_posts_preserves_state_inv sg s log middle Hposts Hvalid) as Hmid.
  pose proof (proj2 (time_tick_application_posts_intr_timer_eq sg s log middle Hposts Hvalid)) as Htimer.
  assert (Hread_mid : time_tick_post_readable sg middle middle.(TimerState).(timerSignalSem)).
  { rewrite Htimer; eapply time_tick_application_posts_preserves_readable; eassumption. }
  destruct (snd (time_tick_hook_counter_step c)) eqn:Hsignal.
  - destruct (time_tick_post_call_exists sg middle middle.(TimerState).(timerSignalSem) Hmid Hread_mid)
      as [result [after Hcall]].
    exists (fst (time_tick_hook_counter_step c)), after, log, middle.
    split; [exact Hreturn|]. split; [exact Hposts|]. split; [reflexivity|].
    rewrite Hsignal; exists result; exact Hcall.
  - exists (fst (time_tick_hook_counter_step c)), middle, log, middle.
    split; [exact Hreturn|]. split; [exact Hposts|]. split; [reflexivity|].
    rewrite Hsignal; reflexivity.
Qed.

Lemma time_tick_hook_result_preserves_state_inv : forall app sg a c s a' c' after,
  time_tick_hook_result app sg a c s a' c' after ->
  UCOS2_state_inv sg s -> UCOS2_state_inv sg after.
Proof.
  intros app sg a c s a' c' after [log [middle [_ [Hposts [_ Hsignal]]]]] Hvalid.
  pose proof (time_tick_application_posts_preserves_state_inv sg s log middle Hposts Hvalid) as Hmid.
  destruct (snd (time_tick_hook_counter_step c)); [|subst after; exact Hmid].
  destruct Hsignal as [result Hsignal]; eapply time_tick_post_call_preserves_state_inv; eassumption.
Qed.

Lemma time_tick_hook_result_counter_in_range : forall app sg a c s a' c' after,
  time_tick_hook_result app sg a c s a' c' after -> 0 <= c' < 10.
Proof.
  intros app sg a c s a' c' after [log [middle [_ [_ [-> _]]]]].
  apply time_tick_hook_counter_in_range.
Qed.

Lemma time_tick_hook_result_preserves_residual : forall app sg a c s a' c' after,
  time_tick_hook_result app sg a c s a' c' after -> UCOS2_state_inv sg s ->
  UCOS2_raw_rep_missing_task_storage_sched_event sg s |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg after.
Proof.
  intros app sg a c s a' c' after [log [middle [_ [Hposts [_ Hsignal]]]]] Hvalid.
  sep_apply_l_atomic (time_tick_application_posts_preserves_residual sg s log middle Hposts Hvalid).
  destruct (snd (time_tick_hook_counter_step c)); [|subst after; reflexivity].
  destruct Hsignal as [result Hsignal].
  eapply time_tick_post_call_preserves_residual; [exact Hsignal|].
  eapply time_tick_application_posts_preserves_state_inv; eassumption.
Qed.

Lemma time_tick_hook_result_preserves_invocation : forall app sg a c s a' c' after invocation origin,
  time_tick_hook_result app sg a c s a' c' after -> UCOS2_state_inv sg s ->
  task_invocation_active s.(TskState) invocation origin ->
  task_invocation_active after.(TskState) invocation origin.
Proof.
  intros app sg a c s a' c' after invocation origin [log [middle [_ [Hposts [_ Hsignal]]]]] Hvalid Hactive.
  pose proof (time_tick_application_posts_preserves_state_inv sg s log middle Hposts Hvalid) as Hmid.
  pose proof (time_tick_application_posts_preserves_invocation sg s log middle Hposts Hvalid
    invocation origin Hactive) as HactiveMid.
  destruct (snd (time_tick_hook_counter_step c)); [|subst after; exact HactiveMid].
  destruct Hsignal as [result Hsignal]; eapply time_tick_post_call_preserves_invocation; eassumption.
Qed.

Lemma time_tick_hook_result_intr_timer_eq : forall app sg a c s a' c' after,
  time_tick_hook_result app sg a c s a' c' after -> UCOS2_state_inv sg s ->
  after.(IntrState) = s.(IntrState) /\ after.(TimerState) = s.(TimerState).
Proof.
  intros app sg a c s a' c' after [log [middle [_ [Hposts [_ Hsignal]]]]] Hvalid.
  destruct (time_tick_application_posts_intr_timer_eq sg s log middle Hposts Hvalid)
    as [Hintr Htimer].
  destruct (snd (time_tick_hook_counter_step c)); [|subst after; split; assumption].
  destruct Hsignal as [result Hsignal].
  destruct (time_tick_post_call_intr_timer_eq sg middle.(TimerState).(timerSignalSem)
    middle result after Hsignal
    (time_tick_application_posts_preserves_state_inv sg s log middle Hposts Hvalid))
    as [Hafter_intr Hafter_timer].
  split; congruence.
Qed.

(** Storage consequence for the external hook implementation.  The
    implementation must produce the actual written Task/ready/ECB cells;
    pure execution does not manufacture them.  Every other owner, including
    timer handles, OSTime/step, stacks, names and padding, is transported. *)
Lemma time_tick_hook_merge_resources : forall app sg a c s a' c' after,
  time_tick_hook_result app sg a c s a' c' after -> UCOS2_state_inv sg s ->
  task_public_storage sg after.(TskState) **
    sched_raw_rep sg after.(TskState) after.(SchedState) **
    event_raw_rep sg after.(TskState) after.(EventState) **
    UCOS2_raw_rep_missing_task_storage_sched_event sg s |-- UCOS2_inv sg after.
Proof.
  intros app sg a c s a' c' after Hhook Hvalid.
  pose proof (time_tick_hook_result_preserves_state_inv app sg a c s a' c' after Hhook Hvalid) as Hafter.
  sep_apply_l_atomic (time_tick_hook_result_preserves_residual app sg a c s a' c' after Hhook Hvalid).
  rewrite UCOS2_inv_open_task_storage_sched_event; entailer!.
Qed.

Lemma time_tick_task_step_preserves_residual : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  UCOS2_raw_rep_missing_task_storage_sched sg s =
    UCOS2_raw_rep_missing_task_storage_sched sg (tick_task_step sg tid t s).
Proof.
  intros sg s tid t Hlookup.
  pose proof (tick_task_step_event_rep_eq sg s tid t Hlookup) as Hevent.
  unfold UCOS2_raw_rep_missing_task_storage_sched.
  rewrite Hevent; unfold tick_task_step;
    destruct (Z.eqb t.(dly) 0); [reflexivity|];
    destruct (Z.eqb (tick_task_update t).(dly) 0); reflexivity.
Qed.

Lemma time_tick_task_step_merge_resources : forall sg s tid t,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_public_storage sg (tick_task_step sg tid t s).(TskState) **
    sched_raw_rep sg (tick_task_step sg tid t s).(TskState)
      (tick_task_step sg tid t s).(SchedState) **
    UCOS2_raw_rep_missing_task_storage_sched sg s |--
    UCOS2_inv sg (tick_task_step sg tid t s).
Proof.
  intros sg s tid t Hmulti Hvalid Hlookup.
  pose proof (time_tick_task_step_preserves_state_inv sg tid t s Hmulti Hvalid Hlookup) as Hpost.
  rewrite (time_tick_task_step_preserves_residual sg s tid t Hlookup).
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched; entailer!.
Qed.

Definition time_tick_global_addresses (sg : StableGlobVars)
  (time step running head group rows : addr) : Prop :=
  time = sg.(g_OSTime) /\ step = sg.(g_OSTickStepState) /\
  running = sg.(g_OSRunning) /\ head = sg.(g_OSTCBList) /\
  group = sg.(g_OSRdyGrp) /\ rows = sg.(g_OSRdyTbl).

Definition time_tick_time (s : UCOS2_Verify_State) : Z := s.(TickState).(ostime).
Definition time_tick_step (s : UCOS2_Verify_State) : Z := s.(TickState).(tickStepState).
Definition time_tick_running (s : UCOS2_Verify_State) : Z :=
  if s.(SchedState).(isRunning) then 1 else 0.
Definition time_tick_process_byte (s : UCOS2_Verify_State) : Z :=
  if time_tick_process_tasks s then 1 else 0.
Definition time_tick_list_head (sg : StableGlobVars) (s : UCOS2_Verify_State) : Z :=
  encode_task_link sg s.(TskState).(tcbListHead).
Definition time_tick_ready_group (s : UCOS2_Verify_State) : Z :=
  encode_ready_grp s.(SchedState).(readyList) s.(TskState).
Definition time_tick_ready_rows (s : UCOS2_Verify_State) : list Z :=
  sched_row_values s.(TskState) s.(SchedState).(readyList).

Definition time_tick_without_time (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSTickStepState) # UChar |-> time_tick_step s ** UCOS2_raw_rep_missing_tick sg s.

Lemma time_tick_split_time : forall sg s,
  UCOS2_inv sg s |--
    coq_prop (UCOS2_state_inv sg s /\
      0 <= time_tick_step s < 256) &&
    (sg.(g_OSTime) # UInt |-> time_tick_time s ** time_tick_without_time sg s).
Proof.
  intros; rewrite UCOS2_inv_split_tick.
  unfold tick_inv, store_tick_state, time_tick_time, time_tick_step, time_tick_without_time;
    entailer!.
Qed.

Lemma time_tick_merge_counted : forall sg s,
  UCOS2_state_inv sg s ->  0 <= time_tick_step s < 256 ->
  sg.(g_OSTime) # UInt |-> ((time_tick_time s + 1) mod 4294967296) **
    time_tick_without_time sg s |-- UCOS2_inv sg (time_tick_counted_state s).
Proof.
  intros sg s Hvalid Hstep.
  rewrite UCOS2_inv_split_tick.
  assert (Hpost : UCOS2_state_inv sg (time_tick_counted_state s)).
  { unfold time_tick_counted_state, UCOS2_state_inv, UCOS2_state_inv_with_ready in *; exact Hvalid. }
  assert (Hrange : 0 <= (time_tick_time s + 1) mod 4294967296 < 4294967296)
    by (apply Z.mod_pos_bound; lia).
  unfold time_tick_without_time, tick_inv, store_tick_state, time_tick_time, time_tick_step,
    time_tick_counted_state, tick_counter_advance in *.
  cbn [replace_TickS TickState].
  assert (Hres : UCOS2_raw_rep_missing_tick sg
    (replace_TickS (tick_counter_advance s.(TickState)) s) =
    UCOS2_raw_rep_missing_tick sg s) by reflexivity.
  change (UCOS2_raw_rep_missing_tick sg
    (replace_TickS {| ostime := (s.(TickState).(ostime) + 1) mod 4294967296;
      tickStepState := s.(TickState).(tickStepState) |} s) =
    UCOS2_raw_rep_missing_tick sg s) in Hres.
  rewrite Hres; entailer!.
Qed.

Definition time_tick_step_write (s : UCOS2_Verify_State) (value : Z)
  : UCOS2_Verify_State :=
  replace_TickS {| ostime := s.(TickState).(ostime);
    tickStepState := value |} s.

Definition time_tick_without_step (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSTime) # UInt |-> time_tick_time s ** UCOS2_raw_rep_missing_tick sg s.

Lemma time_tick_split_step : forall sg s,
  UCOS2_inv sg s |--
    coq_prop (UCOS2_state_inv sg s /\
      0 <= time_tick_time s < 4294967296) &&
    (sg.(g_OSTickStepState) # UChar |-> time_tick_step s ** time_tick_without_step sg s).
Proof.
  intros; rewrite UCOS2_inv_split_tick.
  unfold tick_inv, store_tick_state, time_tick_time, time_tick_step, time_tick_without_step;
    entailer!.
Qed.

Lemma time_tick_merge_step : forall sg s value,
  UCOS2_state_inv sg s -> 
  0 <= time_tick_time s < 4294967296 -> 0 <= value < 256 ->
  sg.(g_OSTickStepState) # UChar |-> value ** time_tick_without_step sg s |--
    UCOS2_inv sg (time_tick_step_write s value).
Proof.
  intros sg s value Hvalid Htime Hvalue; rewrite UCOS2_inv_split_tick.
  assert (Hpost : UCOS2_state_inv sg (time_tick_step_write s value)).
  { unfold time_tick_step_write, UCOS2_state_inv, UCOS2_state_inv_with_ready in *; exact Hvalid. }
  assert (Hres : UCOS2_raw_rep_missing_tick sg (time_tick_step_write s value) =
    UCOS2_raw_rep_missing_tick sg s) by reflexivity.
  unfold time_tick_without_step, tick_inv, store_tick_state.
  rewrite Hres; cbn [time_tick_step_write replace_TickS TickState];
    unfold time_tick_time in *; entailer!.
  cbn; entailer!.
Qed.

Definition time_tick_sched_without_running (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> time_tick_ready_group s **
  UCharArray.full sg.(g_OSRdyTbl) 8 (time_tick_ready_rows s) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(SchedState).(curTaskID) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(SchedState).(ctxSwCtr) **
  UCOS2_raw_rep_missing_sched sg s.

Lemma time_tick_running_resources : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSRunning) # UChar |-> time_tick_running s ** time_tick_sched_without_running sg s).
Proof.
  intros; rewrite UCOS2_inv_split_sched; unfold sched_raw_rep.
  rewrite sched_rows_array_equiv; unfold sched_physical_rep,
    time_tick_sched_without_running, time_tick_running, time_tick_ready_group, time_tick_ready_rows;
    split; entailer!.
Qed.

Definition time_tick_task_without_head (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  store_used_task_map sg s.(TskState).(inUsedTaskStates) **
  task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage)
    s.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error s.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTaskCtr) # UChar |-> s.(TskState).(taskCount) **
  store_prio_tbl sg s.(TskState).(prioTbl) ** task_reg_allocator_rep sg s.(TskState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) ** UCOS2_raw_rep_missing_task sg s.

Lemma time_tick_head_resources : forall sg s,
  UCOS2_inv sg s --||-- coq_prop (UCOS2_state_inv sg s) &&
    (sg.(g_OSTCBList) # Ptr |-> time_tick_list_head sg s ** time_tick_task_without_head sg s).
Proof.
  intros; rewrite UCOS2_inv_split_task.
  unfold task_shared_rep, task_public_storage, time_tick_list_head, time_tick_task_without_head;
    split; entailer!.
Qed.

Definition time_tick_cursor (sg : StableGlobVars) (initial : UCOS2_Verify_State)
  (visited remaining : list TaskID) (current : UCOS2_Verify_State)
  (tid : TaskID) (node : TaskAbstractState) : Prop :=
  initial.(TskState).(taskLifecycle).(taskActiveOrder) = visited ++ tid :: remaining /\
  current = time_tick_scan sg (time_tick_clock_step_state initial) visited /\
  current.(TskState).(inUsedTaskStates) tid = Some node.

Definition time_tick_cursor_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (tid : TaskID) (node : TaskAbstractState) : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid node (TCBCommonField TCBPrio) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Lemma time_tick_scan_running_eq : forall sg visited s,
  (time_tick_scan sg s visited).(SchedState).(isRunning) = s.(SchedState).(isRunning).
Proof.
  intros sg visited; induction visited as [|tid rest IH]; intro s; [reflexivity|].
  change ((time_tick_scan sg (time_tick_visit sg s tid) rest).(SchedState).(isRunning) =
    s.(SchedState).(isRunning)).
  rewrite IH; unfold time_tick_visit.
  destruct (s.(TskState).(inUsedTaskStates) tid) as [node|]; [|reflexivity].
  unfold tick_task_step, sched_wake_by_status.
  destruct (Z.eqb node.(dly) 0); [reflexivity|].
  destruct (Z.eqb (tick_task_update node).(dly) 0); [|reflexivity].
  destruct (task_status_is_suspended _); reflexivity.
Qed.

Lemma time_tick_cursor_active_order : forall sg initial visited remaining current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  current.(TskState).(taskLifecycle).(taskActiveOrder) = visited ++ tid :: remaining.
Proof.
  intros sg initial visited remaining current tid node [Horder [-> Hlookup]].
  rewrite time_tick_scan_task_lifecycle_eq; exact Horder.
Qed.

Lemma time_tick_cursor_scan_step : forall sg initial visited remaining current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  time_tick_scan sg (time_tick_clock_step_state initial) (visited ++ [tid]) =
    tick_task_step sg tid node current.
Proof.
  intros sg initial visited remaining current tid node [_ [Hcurrent Hlookup]].
  rewrite time_tick_scan_app, <- Hcurrent.
  cbn [time_tick_scan fold_left]; unfold time_tick_visit; rewrite Hlookup; reflexivity.
Qed.

Lemma time_tick_active_links_next : forall used prefix previous tid remaining node,
  task_active_links used previous (prefix ++ tid :: remaining) ->
  used tid = Some node -> node.(nextTCB) = hd_error remaining.
Proof.
  intros used prefix; induction prefix as [|head prefix IH];
    intros previous tid remaining node Hlinks Hlookup.
  - destruct Hlinks as [stored [Hstored [_ [_ [Hnext _]]]]]; congruence.
  - destruct Hlinks as [stored [_ [_ [_ [_ Hrest]]]]]; eapply IH; eassumption.
Qed.

Lemma time_tick_cursor_next_link : forall sg initial visited remaining current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  UCOS2_state_inv sg current -> node.(nextTCB) = hd_error remaining.
Proof.
  intros sg initial visited remaining current tid node Hcursor Hvalid.
  pose proof (time_tick_cursor_active_order sg initial visited remaining current tid node Hcursor) as Horder.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  destruct (proj1 (proj2 Htasks)) as [_ [_ [_ [_ Hlinks]]]].
  rewrite Horder in Hlinks.
  eapply time_tick_active_links_next; [exact Hlinks|exact (proj2 (proj2 Hcursor))].
Qed.

Lemma time_tick_process_running : forall s,
  time_tick_process_tasks s = true -> s.(SchedState).(isRunning) = true.
Proof.
  intros s Hprocess; unfold time_tick_process_tasks, tick_step_advance in Hprocess.
  destruct s.(SchedState).(isRunning); [reflexivity|discriminate].
Qed.

Lemma time_tick_cursor_running : forall sg initial visited remaining current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  time_tick_process_tasks initial = true -> current.(SchedState).(isRunning) = true.
Proof.
  intros sg initial visited remaining current tid node [_ [-> _]] Hprocess.
  rewrite time_tick_scan_running_eq.
  change (initial.(SchedState).(isRunning) = true).
  apply time_tick_process_running; exact Hprocess.
Qed.

(** The non-NULL idle tail is a consequence of the existing running
    invariant.  It is not an extra public precondition and does not delete
    the source's priority read outside each nested critical interval. *)
Lemma time_tick_cursor_idle_tail : forall sg initial visited remaining current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  time_tick_process_tasks initial = true -> UCOS2_state_inv sg current ->
  task_idle_tail sg current.(TskState).
Proof.
  intros sg initial visited remaining current tid node Hcursor Hprocess Hvalid.
  destruct Hvalid as [_ [_ [_ [_ [_ [Hidle _]]]]]].
  apply Hidle; eapply time_tick_cursor_running; eassumption.
Qed.

Definition time_tick_retained_field (field : TCBLayoutField) : bool :=
  match field with
  | TCBCommonField TCBNext | TCBCommonField TCBDly | TCBCommonField TCBStat
  | TCBCommonField TCBStatPend | TCBCommonField TCBPrio | TCBCommonField TCBY
  | TCBCommonField TCBBitX | TCBCommonField TCBBitY => false
  | _ => true
  end.

Definition time_tick_retained_fields (multi profile : bool) : list TCBLayoutField :=
  filter time_tick_retained_field (tcb_configured_fields multi profile).

Definition time_tick_task_retained (sg : StableGlobVars) (tid : TaskID)
  (node : TaskAbstractState) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid))
    (time_tick_retained_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
      sg.(osKernelConfig).(cfgTaskProfile)) (task_layout_image sg node).

Definition time_tick_body_residual (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (node : TaskAbstractState) : Assertion :=
  time_tick_task_retained sg tid node ** task_public_storage_without_task sg s.(TskState) tid **
  sched_physical_rep sg s.(SchedState) ** UCOS2_raw_rep_missing_task_storage_sched sg s.

Definition time_tick_body_cells (sg : StableGlobVars) (tid : TaskID)
  (node : TaskAbstractState) (group : Z) (rows : list Z) : Assertion :=
  tcb_field_address (task_slot_addr sg tid) TCBDly # UInt |-> node.(dly) **
  tcb_field_address (task_slot_addr sg tid) TCBStat # UChar |-> encode_task_status node.(stat) **
  tcb_field_address (task_slot_addr sg tid) TCBStatPend # UChar |-> encode_pend_status node.(statPend) **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBNext # Ptr |-> encode_task_link sg node.(nextTCB) **
  tcb_field_address (task_slot_addr sg tid) TCBY # UChar |-> tcb_y_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |-> tcb_bit_x_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |-> tcb_bit_y_of_prio node.(curPrio) **
  sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows.

Lemma time_tick_task_retained_eq : forall sg tid node,
  time_tick_task_retained sg tid (tick_task_update node) = time_tick_task_retained sg tid node.
Proof.
  intros; unfold time_tick_task_retained, TaskFieldStorage.store_fields;
    f_equal; apply functional_extensionality; intro field.
  unfold field_storage.fields_map; destruct in_dec as [Hin|Hin]; [|reflexivity].
  unfold time_tick_retained_fields in Hin; apply filter_In in Hin; destruct Hin as [_ Hin].
  unfold tick_task_update; destruct (Z.eqb node.(dly) 0); [reflexivity|].
  destruct field as [field| | | | | | |]; try destruct field;
    try reflexivity; simpl in Hin; discriminate.
Qed.

(** The already-open caller region is retained throughout this nested,
    masked ISR specialization.  No critical_region_interval is assumed
    to be identity: there is no release of this borrowed heap between
    inner Restore and the next priority read.  The external platform must
    preserve the real continuation and keep IRQ/FIQ masked at 192. *)
Definition time_tick_owned (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (app : TimeTickApplicationResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (region_entry : UCOS2_Verify_State) (app_value counter_address counter : Z)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin 192 **
  critical_region_inside critical sg invocation region_entry **
  time_tick_application_own app app_value **
  counter_address # UShort |-> counter ** UCOS2_inv sg s.

Definition time_tick_client_frame (critical : CriticalRegionResources)
  (application : TimeTickApplicationResources) (sg : StableGlobVars) (invocation : nat)
  (region_entry : UCOS2_Verify_State) (app_value counter_address counter : Z) : Assertion :=
  critical_region_inside critical sg invocation region_entry **
  time_tick_application_own application app_value ** counter_address # UShort |-> counter.

Definition time_tick_sem (app : TimeTickApplicationResources) (sg : StableGlobVars)
  (app_value counter : Z) : program UCOS2_Verify_State unit :=
  fun before result after => result = tt /\ exists app_after counter_after hook_state,
    time_tick_hook_result app sg app_value counter before app_after counter_after hook_state /\
    after = time_tick_serialized_after_hook sg hook_state.

Definition time_tick_exact_state (s : UCOS2_Verify_State) : UCOS2_Verify_State -> Prop :=
  fun observed => observed = s.

Lemma time_tick_sem_preserves_state_inv : forall app sg a c before result after,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg before -> time_tick_sem app sg a c before result after ->
  UCOS2_state_inv sg after.
Proof.
  intros app sg a c before result after Hmulti Hvalid [_ [a' [c' [hook [Hhook ->]]]]].
  apply time_tick_serialized_after_hook_preserves_state_inv; [exact Hmulti|].
  eapply time_tick_hook_result_preserves_state_inv; eassumption.
Qed.

Definition time_tick_entry (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (s : UCOS2_Verify_State) : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\ sg.(osLowestPrio) = 63 /\
  0 < s.(IntrState).(intNesting) /\ task_invocation_active s.(TskState) invocation origin /\
  time_tick_post_readable sg s s.(TimerState).(timerSignalSem).

Definition time_tick_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (application : TimeTickApplicationResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
  (X : UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (time_tick_entry sg invocation origin initial /\
    safeExec (time_tick_exact_state initial) (time_tick_sem application sg app_value counter)
      (fun _ after => X after)) &&
  time_tick_owned platform critical application sg invocation origin region_entry
    app_value counter_address counter initial.

Definition time_tick_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (application : TimeTickApplicationResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (region_entry initial : UCOS2_Verify_State) (app_value counter_address counter : Z)
  (X : UCOS2_Verify_State -> Prop) : Assertion :=
  EX app_after counter_after hook_state,
    coq_prop (time_tick_hook_result application sg app_value counter initial
      app_after counter_after hook_state /\
      X (time_tick_serialized_after_hook sg hook_state)) &&
    time_tick_owned platform critical application sg invocation origin region_entry
      app_after counter_address counter_after (time_tick_serialized_after_hook sg hook_state).

Definition time_tick_delay (node : TaskAbstractState) : Z := node.(dly).
Definition time_tick_status (node : TaskAbstractState) : Z := encode_task_status node.(stat).
Definition time_tick_pend_result (node : TaskAbstractState) : Z := encode_pend_status node.(statPend).
Definition time_tick_priority (node : TaskAbstractState) : Z := node.(curPrio).
Definition time_tick_next (sg : StableGlobVars) (node : TaskAbstractState) : Z :=
  encode_task_link sg node.(nextTCB).
Definition time_tick_y (node : TaskAbstractState) : Z := tcb_y_of_prio node.(curPrio).
Definition time_tick_bit_x (node : TaskAbstractState) : Z := tcb_bit_x_of_prio node.(curPrio).
Definition time_tick_bit_y (node : TaskAbstractState) : Z := tcb_bit_y_of_prio node.(curPrio).
Definition time_tick_lookup (s : UCOS2_Verify_State) (tid : TaskID) (node : TaskAbstractState) : Prop :=
  s.(TskState).(inUsedTaskStates) tid = Some node.
Definition time_tick_body_after (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (tid : TaskID) (node : TaskAbstractState) : UCOS2_Verify_State := tick_task_step sg tid node s.

Definition time_tick_continuation (application : TimeTickApplicationResources)
  (sg : StableGlobVars) (app_value counter : Z) (initial : UCOS2_Verify_State)
  (X : UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (time_tick_exact_state initial) (time_tick_sem application sg app_value counter)
    (fun _ after => X after).

Lemma time_tick_return_continuation : forall application sg app_value counter initial X
  app_after counter_after hook_state,
  time_tick_continuation application sg app_value counter initial X ->
  time_tick_hook_result application sg app_value counter initial app_after counter_after hook_state ->
  X (time_tick_serialized_after_hook sg hook_state).
Proof.
  intros application sg app_value counter initial X app_after counter_after hook_state
    [observed [Hobserved Hsafe]] Hhook.
  unfold time_tick_exact_state in Hobserved; subst observed.
  apply (Hsafe tt (time_tick_serialized_after_hook sg hook_state)).
  split; [reflexivity|]. exists app_after, counter_after, hook_state; split; [exact Hhook|reflexivity].
Qed.

Lemma time_tick_process_byte_unsigned__traversal_and_return : forall s,
  unsigned_last_nbits (time_tick_process_byte s) 32 = time_tick_process_byte s.
Proof. intro s; unfold time_tick_process_byte; destruct (time_tick_process_tasks s); reflexivity. Qed.
Lemma time_tick_running_unsigned__traversal_and_return : forall s,
  unsigned_last_nbits (time_tick_running s) 32 = time_tick_running s.
Proof. intro s; unfold time_tick_running; destruct s.(SchedState).(isRunning); reflexivity. Qed.
Lemma time_tick_owned_entails_post__traversal_and_return : forall platform critical application sg
  invocation origin region_entry initial app_value counter_address counter X
  app_after counter_after hook_state,
  time_tick_hook_result application sg app_value counter initial app_after counter_after hook_state ->
  time_tick_continuation application sg app_value counter initial X ->
  UCOS2_inv sg (time_tick_serialized_after_hook sg hook_state) **
  interrupt_platform_running platform invocation origin 192 **
  time_tick_client_frame critical application sg invocation region_entry
    app_after counter_address counter_after |--
  time_tick_post platform critical application sg invocation origin region_entry initial
    app_value counter_address counter X.
Proof.
  intros platform critical application sg invocation origin region_entry initial app_value
    counter_address counter X app_after counter_after hook_state Hhook Hcontinuation.
  pose proof (time_tick_return_continuation application sg app_value counter initial X
    app_after counter_after hook_state Hcontinuation Hhook) as HX.
  unfold time_tick_post.
  Exists app_after counter_after hook_state.
  unfold time_tick_owned, time_tick_client_frame; entailer!.
Qed.
Lemma time_tick_running_merge__traversal_and_return : forall sg s,
  UCOS2_state_inv sg s ->
  sg.(g_OSRunning) # UChar |-> time_tick_running s **
  time_tick_sched_without_running sg s |-- UCOS2_inv sg s.
Proof.
  intros sg s Hvalid; rewrite (time_tick_running_resources sg s); entailer!.
Qed.
Lemma time_tick_cursor_split_priority__traversal_and_return : forall sg s tid node,
  s.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_inv sg s |--
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> time_tick_priority node **
  time_tick_cursor_residual sg s tid node.
Proof.
  intros sg s tid node Hlookup.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg s).
  Intros.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid node
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ _)).
  unfold time_tick_cursor_residual.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
  unfold time_tick_priority; entailer!.
Qed.
Lemma time_tick_cursor_merge_priority__traversal_and_return : forall sg s tid node,
  UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some node ->
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> time_tick_priority node **
  time_tick_cursor_residual sg s tid node |-- UCOS2_inv sg s.
Proof.
  intros sg s tid node Hvalid Hlookup.
  unfold time_tick_cursor_residual.
  pose proof (task_public_storage_merge_field sg s.(TskState) tid node
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hmerge.
  unfold time_tick_priority.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_task_storage_sched sg s s Hvalid eq_refl).
  entailer!.
Qed.
Lemma time_tick_cursor_initialize__traversal_and_return : forall sg s,
  UCOS2_state_inv sg (time_tick_clock_step_state s) ->
  time_tick_process_tasks s = true ->
  exists remaining tid node,
    time_tick_cursor sg s [] remaining (time_tick_clock_step_state s) tid node /\
    time_tick_list_head sg s = task_slot_addr sg tid.
Proof.
  intros sg s Hvalid Hprocess.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  destruct (proj1 (proj2 Htasks)) as [Hnodup [Hhead [Hcount [Hlive Hlinks]]]].
  assert (Hrunning : (time_tick_clock_step_state s).(SchedState).(isRunning) = true).
  { change (s.(SchedState).(isRunning) = true); apply time_tick_process_running; exact Hprocess. }
  assert (Hidle : task_idle_tail sg (time_tick_clock_step_state s).(TskState)).
  { destruct Hvalid as [_ [_ [_ [_ [_ [Hidle _]]]]]]; apply Hidle; exact Hrunning. }
  destruct Hidle as [prefix [idle [idle_node [Htail _]]]].
  assert (Hnonempty : (time_tick_clock_step_state s).(TskState).(taskLifecycle).(taskActiveOrder) <> []).
  { intro Hnil; rewrite Hnil in Htail; exact (app_cons_not_nil prefix [] idle Htail). }
  destruct ((time_tick_clock_step_state s).(TskState).(taskLifecycle).(taskActiveOrder))
    as [|tid remaining] eqn:Horder; [contradiction|].
  assert (Hin : In tid (tid :: remaining)) by (simpl; auto).
  destruct (proj1 (Hlive tid) Hin) as [node Hlookup].
  exists remaining, tid, node; split.
  - unfold time_tick_cursor; split.
    + change ((time_tick_clock_step_state s).(TskState).(taskLifecycle).(taskActiveOrder) =
        tid :: remaining); exact Horder.
    + split; [reflexivity|exact Hlookup].
  - unfold time_tick_list_head.
    change (encode_task_link sg (time_tick_clock_step_state s).(TskState).(tcbListHead) =
      task_slot_addr sg tid).
    rewrite Hhead; reflexivity.
Qed.
Lemma list_last_marker_split__traversal_and_return : forall (A : Type) (prefix visited : list A)
  (mark : A) remaining,
  ~ In mark prefix ->
  prefix ++ [mark] = visited ++ mark :: remaining ->
  prefix = visited /\ remaining = [].
Proof.
  intros A prefix; induction prefix as [|head prefix IH];
    intros visited mark remaining Hnot Heq; destruct visited as [|first visited].
  - cbn in Heq; injection Heq as Hremaining; split; [reflexivity|symmetry; exact Hremaining].
  - cbn in Heq; injection Heq as Hfirst Htail.
    exfalso; exact (app_cons_not_nil visited remaining mark Htail).
  - cbn in Heq; injection Heq as Hhead Htail.
    subst head; exfalso; apply Hnot; simpl; auto.
  - cbn in Heq; injection Heq as Hhead Htail; subst first.
    destruct (IH visited mark remaining) as [Hprefix Hremaining].
    + intro Hin; apply Hnot; simpl; auto.
    + exact Htail.
    + subst; split; reflexivity.
Qed.
Lemma time_tick_cursor_idle_endpoint__traversal_and_return : forall sg initial visited remaining
  current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  time_tick_process_tasks initial = true ->
  UCOS2_state_inv sg current ->
  time_tick_priority node = sg.(osLowestPrio) ->
  current = time_tick_serialized_after_hook sg initial.
Proof.
  intros sg initial visited remaining current tid node Hcursor Hprocess Hvalid Hpriority.
  pose proof (time_tick_cursor_active_order sg initial visited remaining current tid node Hcursor)
    as Horder.
  pose proof (time_tick_cursor_idle_tail sg initial visited remaining current tid node
    Hcursor Hprocess Hvalid) as Hidle.
  destruct Hidle as [prefix [idle [idle_node [Hids [Hidle_lookup [Hidle_priority Hother]]]]]].
  pose proof (proj2 (proj2 Hcursor)) as Hlookup.
  change (node.(curPrio) = sg.(osLowestPrio)) in Hpriority.
  assert (Hin : In tid (prefix ++ [idle])).
  { rewrite <- Hids, Horder; apply in_or_app; right; simpl; auto. }
  assert (Htid : tid = idle).
  { apply in_app_or in Hin; destruct Hin as [Hin|Hin].
    - exfalso; apply (Hother tid node Hin Hlookup); exact Hpriority.
    - simpl in Hin; destruct Hin as [Heq|[]]; symmetry; exact Heq. }
  subst idle.
  assert (Hnot : ~ In tid prefix).
  { intro Hprefix_member; apply (Hother tid node Hprefix_member Hlookup); exact Hpriority. }
  assert (Hsplit : prefix ++ [tid] = visited ++ tid :: remaining).
  { rewrite <- Hids; exact Horder. }
  destruct (list_last_marker_split__traversal_and_return TaskID prefix visited tid
    remaining Hnot Hsplit) as [_ Hremaining].
  subst remaining.
  unfold time_tick_serialized_after_hook; rewrite Hprocess, (proj1 Hcursor).
  rewrite removelast_last; exact (proj1 (proj2 Hcursor)).
Qed.
Lemma time_tick_configuration_no_multi__task_update_backedges : forall sg s,
  UCOS2_state_inv sg s -> sg.(osKernelConfig).(cfgEventMultiEnabled) = false.
Proof.
  intros sg s Hvalid.
  pose proof (proj1 Hvalid) as Hprofile.
  unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto.
Qed.
Lemma time_tick_task_priority_in_range__task_update_backedges : forall sg s tid node,
  UCOS2_state_inv sg s -> time_tick_lookup s tid node ->
  0 <= node.(curPrio) < 64.
Proof.
  intros sg s tid node Hvalid Hlookup.
  pose proof (proj1 Hvalid) as Hprofile.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  unfold task_in_range in Htasks.
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hprio _]]]]]]]].
  specialize (Hprio tid node Hlookup).
  unfold task_priority_in_range in Hprio.
  unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; intuition lia.
Qed.
Lemma time_tick_task_y_in_range__task_update_backedges : forall sg s tid node,
  UCOS2_state_inv sg s -> time_tick_lookup s tid node ->
  0 <= time_tick_y node < 8.
Proof.
  intros sg s tid node Hvalid Hlookup.
  pose proof (time_tick_task_priority_in_range__task_update_backedges sg s tid node
    Hvalid Hlookup) as Hp.
  unfold time_tick_y, tcb_y_of_prio.
  split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma time_tick_task_body_resources__task_update_backedges : forall sg tid node group rows,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  used_task_rep sg tid node **
    sg.(g_OSRdyGrp) # UChar |-> group ** UCharArray.full sg.(g_OSRdyTbl) 8 rows
  --||-- time_tick_body_cells sg tid node group rows ** time_tick_task_retained sg tid node.
Proof.
  intros sg tid node group rows Hmulti.
  unfold used_task_rep, task_slot_storage_rep, time_tick_task_retained.
  rewrite Hmulti; destruct sg.(osKernelConfig).(cfgTaskProfile);
  unfold time_tick_body_cells, tcb_configured_storage_rep,
    time_tick_retained_fields, tcb_configured_fields, tcb_profile_fields, tcb_fields;
  cbn [map firstn skipn app filter time_tick_retained_field];
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  all: rewrite !TaskFieldStorage.store_fields_nil;
    cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image];
    split; entailer!.
Qed.
Lemma time_tick_cursor_merge_inv__task_update_backedges : forall sg s tid node,
  UCOS2_state_inv sg s -> time_tick_lookup s tid node ->
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
    time_tick_cursor_residual sg s tid node |-- UCOS2_inv sg s.
Proof.
  intros sg s tid node Hvalid Hlookup.
  pose proof (task_public_storage_merge_field sg s.(TskState) tid node
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ TCBPrio)) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hmerge.
  unfold time_tick_cursor_residual.
  sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_task_storage_sched sg s s Hvalid eq_refl).
  entailer!.
Qed.
Lemma time_tick_inv_split_priority__task_update_backedges : forall sg s tid node,
  time_tick_lookup s tid node ->
  UCOS2_inv sg s |--
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
    time_tick_cursor_residual sg s tid node.
Proof.
  intros sg s tid node Hlookup.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg s).
  Intros.
  pose proof (task_public_storage_split_field sg s.(TskState) tid node
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ TCBPrio)) as Hsplit.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold time_tick_cursor_residual; entailer!.
Qed.
Lemma time_tick_inv_split_body__task_update_backedges : forall sg s tid node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  time_tick_lookup s tid node ->
  UCOS2_inv sg s |--
  time_tick_body_cells sg tid node (time_tick_ready_group s) (time_tick_ready_rows s) **
    time_tick_body_residual sg s tid node.
Proof.
  intros sg s tid node Hmulti Hlookup.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg s).
  Intros.
  sep_apply_l_atomic (task_public_storage_split_task sg s.(TskState) tid node Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  fold (time_tick_ready_group s) (time_tick_ready_rows s).
  unfold time_tick_body_residual.
  cancel (task_public_storage_without_task sg s.(TskState) tid).
  cancel (sched_physical_rep sg s.(SchedState)).
  cancel (UCOS2_raw_rep_missing_task_storage_sched sg s).
  sep_apply_r_atomic (proj1 (time_tick_task_body_resources__task_update_backedges
    sg tid node (time_tick_ready_group s) (time_tick_ready_rows s) Hmulti)).
  entailer!.
Qed.
Lemma time_tick_body_delay_range__task_update_backedges : forall sg tid node group rows,
  time_tick_body_cells sg tid node group rows |--
  coq_prop (0 <= node.(dly) < 4294967296) &&
    time_tick_body_cells sg tid node group rows.
Proof.
  intros; unfold time_tick_body_cells, store_uint; entailer!;
    change Int.max_unsigned with 4294967295 in *; lia.
Qed.
Lemma time_tick_body_merge_task_step__task_update_backedges : forall sg s tid node,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  UCOS2_state_inv sg s -> time_tick_lookup s tid node ->
  time_tick_body_cells sg tid (tick_task_update node)
    (time_tick_ready_group (tick_task_step sg tid node s))
    (time_tick_ready_rows (tick_task_step sg tid node s)) **
    time_tick_body_residual sg s tid node |--
  UCOS2_inv sg (tick_task_step sg tid node s).
Proof.
  intros sg s tid node Hmulti Hvalid Hlookup.
  unfold time_tick_body_residual.
  rewrite <- (time_tick_task_retained_eq sg tid node).
  sep_apply_l_atomic (proj2 (time_tick_task_body_resources__task_update_backedges
    sg tid (tick_task_update node)
    (time_tick_ready_group (tick_task_step sg tid node s))
    (time_tick_ready_rows (tick_task_step sg tid node s)) Hmulti)).
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg s.(TskState) tid
    (tick_task_update node)).
  rewrite <- (tick_task_step_task_state_eq sg tid node s Hlookup).
  assert (Hphysical : sched_physical_rep sg (tick_task_step sg tid node s).(SchedState) =
    sched_physical_rep sg s.(SchedState)).
  { unfold tick_task_step; destruct (Z.eqb node.(dly) 0); [reflexivity|].
    destruct (Z.eqb (tick_task_update node).(dly) 0); [|reflexivity].
    apply sched_wake_by_status_physical_rep_eq. }
  rewrite <- Hphysical.
  sep_apply_r_atomic (time_tick_task_step_merge_resources sg s tid node Hmulti Hvalid Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  unfold time_tick_ready_group, time_tick_ready_rows; entailer!.
Qed.
Lemma time_tick_cursor_advance__task_update_backedges : forall sg initial visited remaining current tid node,
  time_tick_cursor sg initial visited remaining current tid node ->
  time_tick_process_byte initial = 1 -> UCOS2_state_inv sg current ->
  node.(curPrio) <> 63 ->
  exists next rest next_node,
    remaining = next :: rest /\
    time_tick_next sg node = task_slot_addr sg next /\
    time_tick_cursor sg initial (visited ++ [tid]) rest
      (tick_task_step sg tid node current) next next_node /\
    time_tick_lookup (tick_task_step sg tid node current) next next_node.
Proof.
  intros sg initial visited remaining current tid node Hcursor Hprocess Hvalid Hnonidle.
  assert (Hprocess_true : time_tick_process_tasks initial = true).
  { unfold time_tick_process_byte in Hprocess; destruct (time_tick_process_tasks initial); congruence. }
  pose proof (time_tick_cursor_active_order sg initial visited remaining current tid node Hcursor) as Horder.
  pose proof (time_tick_cursor_idle_tail sg initial visited remaining current tid node
    Hcursor Hprocess_true Hvalid) as Hidle.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  destruct (proj1 (proj2 Htasks)) as [Hnd [_ [_ [Hcover Hlinks]]]].
  rewrite Horder in Hnd, Hcover.
  destruct remaining as [|next rest].
  - destruct Hidle as [prefix [idle [idle_node [Hidle_order [Hidle_lookup [Hidle_prio _]]]]]].
    rewrite Horder in Hidle_order.
    apply app_inj_tail in Hidle_order as [_ Hid]; subst idle.
    assert (idle_node = node) by (pose proof (proj2 (proj2 Hcursor)); congruence).
    subst idle_node.
    pose proof (proj1 Hvalid) as Hprofile.
    unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; intuition congruence.
  - assert (Hin : In next (visited ++ tid :: next :: rest)).
    { apply in_or_app; right; simpl; auto. }
    destruct (proj1 (Hcover next) Hin) as [next_node Hlookup].
    assert (Htail : NoDup (tid :: next :: rest)).
    { clear -Hnd. induction visited; simpl in *; [exact Hnd|].
      inversion Hnd; apply IHvisited; assumption. }
    assert (Hne : next <> tid).
    { intro Heq; inversion Htail as [|? ? Hnot _]; apply Hnot; left; exact Heq. }
    assert (Hnextlookup : time_tick_lookup (tick_task_step sg tid node current) next next_node).
    { unfold time_tick_lookup; rewrite tick_task_step_other_task_eq by exact Hne; exact Hlookup. }
    exists next, rest, next_node; split; [reflexivity|].
    split.
    + unfold time_tick_next; rewrite (time_tick_cursor_next_link sg initial visited
        (next :: rest) current tid node Hcursor Hvalid); reflexivity.
    + split; [|exact Hnextlookup].
      unfold time_tick_cursor; split.
      * rewrite <- app_assoc; simpl; exact (proj1 Hcursor).
      * split; [symmetry; apply (time_tick_cursor_scan_step sg initial visited
          (next :: rest) current tid node Hcursor)|exact Hnextlookup].
Qed.
Lemma time_tick_bitmap_values_in_range__task_update_backedges : forall sg s tid node,
  UCOS2_state_inv sg s -> time_tick_lookup s tid node ->
  0 <= time_tick_ready_group s < 256 /\
  0 <= Znth (time_tick_y node) (time_tick_ready_rows s) 0 < 256 /\
  0 <= time_tick_bit_x node < 256 /\ 0 <= time_tick_bit_y node < 256.
Proof.
  intros sg s tid node Hvalid Hlookup.
  pose proof (time_tick_task_y_in_range__task_update_backedges sg s tid node Hvalid Hlookup) as Hy.
  split.
  - unfold time_tick_ready_group; change 256 with (2 ^ 8).
    apply encode_ready_grp_in_range.
    intros slot other Hin Hother.
    exact (time_tick_task_y_in_range__task_update_backedges sg s slot other Hvalid Hother).
  - split.
    + unfold time_tick_ready_rows; rewrite sched_row_values_Znth by exact Hy.
      apply encode_ready_tbl_or_in_range.
    + unfold time_tick_bit_x, time_tick_bit_y, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
      change 256 with (2 ^ 8).
      split; apply bitmap_single_bit_in_range.
      * unfold tcb_x_of_prio; apply Z.mod_pos_bound; lia.
      * exact Hy.
Qed.
Lemma time_tick_task_step_ready_encoding__task_update_backedges : forall sg s tid node,
  time_tick_lookup s tid node -> 0 <= time_tick_y node < 8 ->
  let post := tick_task_step sg tid node s in
  let new := tick_task_update node in
  time_tick_ready_group post =
    (if Z.eqb node.(dly) 0 then time_tick_ready_group s else
     if Z.eqb new.(dly) 0 then
       if task_status_is_suspended (encode_task_status new.(stat))
       then time_tick_ready_group s
       else Z.lor (time_tick_ready_group s) (time_tick_bit_y node)
     else time_tick_ready_group s) /\
  time_tick_ready_rows post =
    (if Z.eqb node.(dly) 0 then time_tick_ready_rows s else
     if Z.eqb new.(dly) 0 then
       if task_status_is_suspended (encode_task_status new.(stat))
       then time_tick_ready_rows s
       else replace_Znth (time_tick_y node)
         (Z.lor (Znth (time_tick_y node) (time_tick_ready_rows s) 0)
           (time_tick_bit_x node)) (time_tick_ready_rows s)
     else time_tick_ready_rows s).
Proof.
  intros sg s tid node Hlookup Hy; cbn zeta.
  assert (Hp : (tick_task_update node).(curPrio) = node.(curPrio)).
  { unfold tick_task_update; destruct (Z.eqb node.(dly) 0); reflexivity. }
  assert (Hobs : forall slot, option_map curPrio
    ((glob_task_set_usedtask s.(TskState) tid (tick_task_update node)).(inUsedTaskStates) slot) =
      option_map curPrio (s.(TskState).(inUsedTaskStates) slot)).
  { intro slot; eapply glob_task_set_usedtask_observation; eauto. }
  assert (Hext : forall ids,
    encode_ready_grp ids (glob_task_set_usedtask s.(TskState) tid (tick_task_update node)) =
      encode_ready_grp ids s.(TskState) /\
    forall row, encode_ready_tbl_at_or ids
      (glob_task_set_usedtask s.(TskState) tid (tick_task_update node)) row =
      encode_ready_tbl_at_or ids s.(TskState) row).
  { intro ids; apply sched_encoding_priority_ext; intros; apply Hobs. }
  unfold tick_task_step at 1 2.
  destruct (Z.eqb node.(dly) 0) eqn:Hz; [split; reflexivity|].
  destruct (Z.eqb (tick_task_update node).(dly) 0) eqn:He.
  - cbn [replace_TskS replace_SchedS TskState SchedState].
    unfold time_tick_ready_group, time_tick_ready_rows.
    cbn [replace_TskS replace_SchedS TskState SchedState].
    destruct (Hext (sched_wake_by_status sg s.(TskState) s.(SchedState) tid
      (encode_task_status (tick_task_update node).(stat))).(readyList)) as [Hgrp Htbl].
    destruct (sched_wake_by_status_encoding sg s.(TskState) s.(SchedState) tid node
      (encode_task_status (tick_task_update node).(stat)) Hlookup) as [Hg Ht].
    rewrite Hgrp, Hg; split; [reflexivity|].
    unfold sched_row_values; cbn [map].
    rewrite (Htbl 0), (Htbl 1), (Htbl 2), (Htbl 3), (Htbl 4), (Htbl 5), (Htbl 6), (Htbl 7).
    rewrite (Ht 0), (Ht 1), (Ht 2), (Ht 3), (Ht 4), (Ht 5), (Ht 6), (Ht 7).
    destruct (task_status_is_suspended (encode_task_status (tick_task_update node).(stat)));
      [reflexivity|].
    unfold time_tick_y, tcb_y_of_prio in Hy |- *.
    unfold time_tick_bit_x, tcb_bit_x_of_prio, tcb_x_of_prio.
    set (y := node.(curPrio) / 8) in *.
    assert (Hcases : y = 0 \/ y = 1 \/ y = 2 \/ y = 3 \/
      y = 4 \/ y = 5 \/ y = 6 \/ y = 7) by lia.
    destruct Hcases as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
  - cbn [replace_TskS TskState SchedState].
    unfold time_tick_ready_group, time_tick_ready_rows.
    cbn [replace_TskS replace_SchedS TskState SchedState].
    destruct (Hext s.(SchedState).(readyList)) as [Hgrp Htbl].
    rewrite Hgrp; split; [reflexivity|].
    unfold sched_row_values; apply map_ext; intro row; apply Htbl.
Qed.
