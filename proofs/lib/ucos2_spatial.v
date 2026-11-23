Require Import Coq.Bool.Bool.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.kernel_resources.

Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac_scope.

(** The complete shared heap, with each owner appearing once. Sem, Mutex
    and Mbox share ECB storage with Event: they must not own a second copy.
    Queue owns only QCB/ring storage, separate from its ECB. Pure module
    validity and cross-module relations belong to UCOS2_state_inv. *)
Definition UCOS2_raw_rep (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  task_shared_rep sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  interrupt_inv sg s.(IntrState) **
  event_raw_rep sg s.(TskState) s.(EventState) **
  queue_storage_rep sg s.(EventState) **
  tick_inv sg s.(TickState) **
  flag_configured_rep sg s.(FlagState) **
  memory_configured_rep sg s.(MemoryState) **
  timer_configured_rep sg s.(TimerState) **
  statistics_rep sg s.(StatsState) **
  kernel_control_rep sg s.(ControlState) **
  store_name_bytes s.(NameState).

(** These constructors select existing spatial owners; they are not new
    abstract-state fields or ghost resources. *)
Inductive UCOS2Module : Type :=
| TaskModule | SchedModule | InterruptModule | EventModule | QueueModule
| TickModule | FlagModule | MemoryModule | TimerModule | StatisticsModule
| ControlModule | NamesModule.

Definition UCOS2_module_eq_dec : forall a b : UCOS2Module, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition UCOS2_module_rep (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (m : UCOS2Module) : Assertion :=
  match m with
  | TaskModule => task_shared_rep sg s.(TskState)
  | SchedModule => sched_raw_rep sg s.(TskState) s.(SchedState)
  | InterruptModule => interrupt_inv sg s.(IntrState)
  | EventModule => event_raw_rep sg s.(TskState) s.(EventState)
  | QueueModule => queue_storage_rep sg s.(EventState)
  | TickModule => tick_inv sg s.(TickState)
  | FlagModule => flag_configured_rep sg s.(FlagState)
  | MemoryModule => memory_configured_rep sg s.(MemoryState)
  | TimerModule => timer_configured_rep sg s.(TimerState)
  | StatisticsModule => statistics_rep sg s.(StatsState)
  | ControlModule => kernel_control_rep sg s.(ControlState)
  | NamesModule => store_name_bytes s.(NameState)
  end.

(** A structural subheap of the same module conjunction. False removes
    exactly that owner (emp); it does not discharge validity or erase the
    other owners. The split theorem below is uniform in this selection. *)
Definition UCOS2_selected_rep (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (keep : UCOS2Module -> bool) : Assertion :=
  (if keep TaskModule then UCOS2_module_rep sg s TaskModule else emp) **
  (if keep SchedModule then UCOS2_module_rep sg s SchedModule else emp) **
  (if keep InterruptModule then UCOS2_module_rep sg s InterruptModule else emp) **
  (if keep EventModule then UCOS2_module_rep sg s EventModule else emp) **
  (if keep QueueModule then UCOS2_module_rep sg s QueueModule else emp) **
  (if keep TickModule then UCOS2_module_rep sg s TickModule else emp) **
  (if keep FlagModule then UCOS2_module_rep sg s FlagModule else emp) **
  (if keep MemoryModule then UCOS2_module_rep sg s MemoryModule else emp) **
  (if keep TimerModule then UCOS2_module_rep sg s TimerModule else emp) **
  (if keep StatisticsModule then UCOS2_module_rep sg s StatisticsModule else emp) **
  (if keep ControlModule then UCOS2_module_rep sg s ControlModule else emp) **
  (if keep NamesModule then UCOS2_module_rep sg s NamesModule else emp).

Lemma UCOS2_raw_rep_all_modules_eq : forall sg s,
  UCOS2_raw_rep sg s = UCOS2_selected_rep sg s (fun _ => true).
Proof. reflexivity. Qed.

Lemma UCOS2_selected_rep_split_module : forall sg s keep m,
  keep m = true ->
  UCOS2_selected_rep sg s keep --||--
    UCOS2_module_rep sg s m **
    UCOS2_selected_rep sg s
      (fun candidate => if UCOS2_module_eq_dec candidate m then false else keep candidate).
Proof.
  intros sg s keep m Hkeep; destruct m;
    unfold UCOS2_selected_rep;
    cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect];
    rewrite Hkeep; split; entailer!.
Qed.

Definition UCOS2_raw_rep_missing_module sg s (m : UCOS2Module) : Assertion :=
  UCOS2_selected_rep sg s
    (fun candidate => if UCOS2_module_eq_dec candidate m then false else true).

Definition UCOS2_raw_rep_missing_two sg s (first second : UCOS2Module) : Assertion :=
  UCOS2_selected_rep sg s
    (fun candidate => if UCOS2_module_eq_dec candidate second then false
      else if UCOS2_module_eq_dec candidate first then false else true).

Lemma UCOS2_raw_rep_split_module : forall sg s m,
  UCOS2_raw_rep sg s --||--
    UCOS2_module_rep sg s m ** UCOS2_raw_rep_missing_module sg s m.
Proof.
  intros; rewrite UCOS2_raw_rep_all_modules_eq.
  apply UCOS2_selected_rep_split_module; reflexivity.
Qed.

Lemma UCOS2_raw_rep_missing_module_split_module : forall sg s first second,
  first <> second ->
  UCOS2_raw_rep_missing_module sg s first --||--
    UCOS2_module_rep sg s second ** UCOS2_raw_rep_missing_two sg s first second.
Proof.
  intros sg s first second Hdistinct.
  unfold UCOS2_raw_rep_missing_module, UCOS2_raw_rep_missing_two.
  apply UCOS2_selected_rep_split_module.
  destruct (UCOS2_module_eq_dec second first); congruence.
Qed.

Lemma UCOS2_raw_rep_split_two : forall sg s first second,
  first <> second ->
  UCOS2_raw_rep sg s --||--
    UCOS2_module_rep sg s first ** UCOS2_module_rep sg s second **
    UCOS2_raw_rep_missing_two sg s first second.
Proof.
  intros sg s first second Hdistinct.
  rewrite (UCOS2_raw_rep_split_module sg s first).
  rewrite (UCOS2_raw_rep_missing_module_split_module sg s first second Hdistinct).
  split; entailer!.
Qed.

Lemma UCOS2_raw_rep_missing_two_comm_eq : forall sg s first second,
  UCOS2_raw_rep_missing_two sg s first second =
    UCOS2_raw_rep_missing_two sg s second first.
Proof. intros sg s first second; destruct first, second; reflexivity. Qed.

Lemma UCOS2_raw_rep_missing_two_same_eq : forall sg s m,
  UCOS2_raw_rep_missing_two sg s m m = UCOS2_raw_rep_missing_module sg s m.
Proof. intros sg s m; destruct m; reflexivity. Qed.

(** Frame equality is established for each retained physical owner, not
    inferred merely from unchanged abstract-state projections. *)
Lemma UCOS2_selected_rep_frame : forall sg before after keep,
  (forall m, keep m = true -> UCOS2_module_rep sg before m = UCOS2_module_rep sg after m) ->
  UCOS2_selected_rep sg before keep = UCOS2_selected_rep sg after keep.
Proof.
  intros sg before after keep Hparts.
  assert (Hcell : forall m,
    (if keep m then UCOS2_module_rep sg before m else emp) =
    (if keep m then UCOS2_module_rep sg after m else emp)).
  { intros m; destruct (keep m) eqn:Hkeep;
      [apply Hparts; exact Hkeep|reflexivity]. }
  unfold UCOS2_selected_rep; rewrite !Hcell; reflexivity.
Qed.

Lemma UCOS2_raw_rep_missing_module_frame : forall sg before after focused,
  (forall m, m <> focused -> UCOS2_module_rep sg before m = UCOS2_module_rep sg after m) ->
  UCOS2_raw_rep_missing_module sg before focused = UCOS2_raw_rep_missing_module sg after focused.
Proof.
  intros sg before after focused Hparts; unfold UCOS2_raw_rep_missing_module.
  apply UCOS2_selected_rep_frame; intros m Hkeep.
  destruct (UCOS2_module_eq_dec m focused); [discriminate|apply Hparts; assumption].
Qed.

Lemma UCOS2_raw_rep_missing_two_frame : forall sg before after first second,
  (forall m, m <> first -> m <> second ->
    UCOS2_module_rep sg before m = UCOS2_module_rep sg after m) ->
  UCOS2_raw_rep_missing_two sg before first second = UCOS2_raw_rep_missing_two sg after first second.
Proof.
  intros sg before after first second Hparts; unfold UCOS2_raw_rep_missing_two.
  apply UCOS2_selected_rep_frame; intros m Hkeep.
  destruct (UCOS2_module_eq_dec m second); [discriminate|].
  destruct (UCOS2_module_eq_dec m first); [discriminate|apply Hparts; assumption].
Qed.

(** Updated merge requires an actual residual transport proof. Unchanged
    EventState/SchedState projections alone are insufficient when their
    concrete encoders read the updated Task index. *)
Lemma UCOS2_raw_rep_merge_updated_module : forall sg before after m,
  (UCOS2_raw_rep_missing_module sg before m |-- UCOS2_raw_rep_missing_module sg after m) ->
  UCOS2_module_rep sg after m ** UCOS2_raw_rep_missing_module sg before m |--
    UCOS2_raw_rep sg after.
Proof.
  intros sg before after m Hframe.
  eapply derivable1_trans; [apply derivable1_sepcon_mono; [reflexivity|exact Hframe]|].
  apply (proj2 (UCOS2_raw_rep_split_module sg after m)).
Qed.

Lemma UCOS2_raw_rep_merge_updated_two : forall sg before after first second,
  first <> second ->
  (UCOS2_raw_rep_missing_two sg before first second |--
    UCOS2_raw_rep_missing_two sg after first second) ->
  UCOS2_module_rep sg after first ** UCOS2_module_rep sg after second **
    UCOS2_raw_rep_missing_two sg before first second |-- UCOS2_raw_rep sg after.
Proof.
  intros sg before after first second Hdistinct Hframe.
  rewrite (UCOS2_raw_rep_split_two sg after first second Hdistinct).
  apply derivable1_sepcon_mono; [reflexivity|exact Hframe].
Qed.

(** Named specializations for annotations; all use the same selection and
    split/merge laws, rather than maintaining separate residual lists. *)
Definition UCOS2_raw_rep_missing_task sg s := UCOS2_raw_rep_missing_module sg s TaskModule.
Definition UCOS2_raw_rep_missing_sched sg s := UCOS2_raw_rep_missing_module sg s SchedModule.
Definition UCOS2_raw_rep_missing_interrupt sg s := UCOS2_raw_rep_missing_module sg s InterruptModule.
Definition UCOS2_raw_rep_missing_event sg s := UCOS2_raw_rep_missing_module sg s EventModule.
Definition UCOS2_raw_rep_missing_queue sg s := UCOS2_raw_rep_missing_module sg s QueueModule.
Definition UCOS2_raw_rep_missing_tick sg s := UCOS2_raw_rep_missing_module sg s TickModule.
Definition UCOS2_raw_rep_missing_flag sg s := UCOS2_raw_rep_missing_module sg s FlagModule.
Definition UCOS2_raw_rep_missing_memory sg s := UCOS2_raw_rep_missing_module sg s MemoryModule.
Definition UCOS2_raw_rep_missing_timer sg s := UCOS2_raw_rep_missing_module sg s TimerModule.
Definition UCOS2_raw_rep_missing_statistics sg s := UCOS2_raw_rep_missing_module sg s StatisticsModule.
Definition UCOS2_raw_rep_missing_control sg s := UCOS2_raw_rep_missing_module sg s ControlModule.
Definition UCOS2_raw_rep_missing_names sg s := UCOS2_raw_rep_missing_module sg s NamesModule.
Definition UCOS2_raw_rep_missing_task_sched sg s :=
  UCOS2_raw_rep_missing_two sg s TaskModule SchedModule.
Definition UCOS2_raw_rep_missing_event_queue sg s :=
  UCOS2_raw_rep_missing_two sg s EventModule QueueModule.
