Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.

Import ListNotations.
Local Open Scope Z_scope.

(** OSTaskCreate / OSTaskCreateExt, V2.93.01 Source/os_task.c:219--280,
    347--416.  These definitions cover the ordered entry checks, the first
    critical section, initialization-call prefix AFTER its Restore, and
    returning trace/schedule/rollback tail through explicit call relations.
    They do not make the whole API atomic or establish a platform contract.

    [started] is the value read at the IEC check; the critical relation uses
    the state observed after Save, not a snapshot from before Save.  The
    safety error below is a branch discriminator: the source calls
    OS_SAFETY_CRITICAL_EXCEPTION before returning that error, IF the hook
    returns.  No termination or empty-effect assertion is attached to it. *)
Definition task_create_prefix_error (sg : StableGlobVars) (started : bool)
  (priority : Priority) : option OSErrCode :=
  if (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool
  then Some OS_ERR_ILLEGAL_CREATE_RUN_TIME
  else if (sg.(osKernelConfig).(cfgArgumentChecks) &&
           Z.ltb sg.(osLowestPrio) priority)%bool
       then Some OS_ERR_PRIO_INVALID else None.

Lemma task_create_prefix_error_safety : forall sg priority,
  sg.(osKernelConfig).(cfgSafetyCriticalIEC) = true ->
  task_create_prefix_error sg true priority = Some OS_ERR_ILLEGAL_CREATE_RUN_TIME.
Proof. intros; unfold task_create_prefix_error; rewrite H; reflexivity. Qed.

Lemma task_create_prefix_error_priority : forall sg started priority,
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool = false ->
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  sg.(osLowestPrio) < priority ->
  task_create_prefix_error sg started priority = Some OS_ERR_PRIO_INVALID.
Proof.
  intros sg started priority Hs Hc Hp.
  unfold task_create_prefix_error; rewrite Hs, Hc, (proj2 (Z.ltb_lt _ _) Hp).
  reflexivity.
Qed.

Lemma task_create_prefix_error_checks_disabled : forall sg started priority,
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool = false ->
  sg.(osKernelConfig).(cfgArgumentChecks) = false ->
  task_create_prefix_error sg started priority = None.
Proof. intros; unfold task_create_prefix_error; rewrite H, H0; reflexivity. Qed.

(** The source uses [>] rather than [>=]: even the idle priority reaches the
    table test.  A free/occupied decision is not replaced with an idle guard. *)
Lemma task_create_prefix_error_lowest : forall sg started,
  (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool = false ->
  task_create_prefix_error sg started sg.(osLowestPrio) = None.
Proof.
  intros; unfold task_create_prefix_error; rewrite H, Z.ltb_irrefl,
    Bool.andb_false_r; reflexivity.
Qed.

Lemma task_create_prefix_allows_priority_index : forall sg started priority,
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  0 <= priority -> task_create_prefix_error sg started priority = None ->
  task_priority_in_range sg priority.
Proof.
  intros sg started priority Hchecks Hnonnegative Hallowed.
  unfold task_create_prefix_error in Hallowed.
  destruct (sg.(osKernelConfig).(cfgSafetyCriticalIEC) && started)%bool;
    [discriminate|].
  rewrite Hchecks in Hallowed; simpl in Hallowed.
  destruct (Z.ltb sg.(osLowestPrio) priority) eqn:Hrange; [discriminate|].
  apply Z.ltb_ge in Hrange; unfold task_priority_in_range; lia.
Qed.

(** [None] means continue to Restore and stack/TCB initialization, NOT
    successful function return.  Only [PTFree] is accepted: a creation
    reservation, a mutex PCP reservation and a live TCB all produce
    OS_ERR_PRIO_EXIST.

    The index condition belongs only to the actual table-read path.  With
    argument checking off, an out-of-range priority in ISR context still
    returns OS_ERR_TASK_CREATE_ISR without dereferencing the table.

    The invocation/origin are lifecycle bookkeeping, not extra C guards.
    Their registration and freshness are required by the separate invariant
    preservation theorem, not by this source-step relation.  Saved interrupt
    tokens and the following Restore are handled by the platform contract. *)
Definition task_create_critical (sg : StableGlobVars) (priority : Priority)
  (invocation : nat) (origin : TaskInvocationOrigin)
  : program UCOS2_Verify_State (option OSErrCode) :=
  fun before result after =>
    if Z.ltb 0 before.(IntrState).(intNesting)
    then result = Some OS_ERR_TASK_CREATE_ISR /\ after = before
    else task_priority_in_range sg priority /\
      match before.(TskState).(prioTbl) priority with
      | PTFree => result = None /\ after = replace_TskS
          (task_reserve before.(TskState) priority invocation origin) before
      | PTReserved | PTTask _ => result = Some OS_ERR_PRIO_EXIST /\ after = before
      end.

Lemma task_create_critical_isr : forall sg priority invocation origin before,
  0 < before.(IntrState).(intNesting) ->
  task_create_critical sg priority invocation origin before
    (Some OS_ERR_TASK_CREATE_ISR) before.
Proof.
  intros; unfold task_create_critical; rewrite (proj2 (Z.ltb_lt _ _) H).
  split; reflexivity.
Qed.

Lemma task_create_critical_free : forall sg priority invocation origin before,
  before.(IntrState).(intNesting) = 0 -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTFree ->
  task_create_critical sg priority invocation origin before None
    (replace_TskS (task_reserve before.(TskState) priority invocation origin) before).
Proof.
  intros sg priority invocation origin before Hnest Hp Hfree.
  unfold task_create_critical; rewrite Hnest; simpl; rewrite Hfree.
  split; [exact Hp|split; reflexivity].
Qed.

Lemma task_create_critical_occupied : forall sg priority invocation origin before,
  before.(IntrState).(intNesting) = 0 -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority <> PTFree ->
  task_create_critical sg priority invocation origin before
    (Some OS_ERR_PRIO_EXIST) before.
Proof.
  intros sg priority invocation origin before Hnest Hp Hoccupied.
  unfold task_create_critical; rewrite Hnest; simpl; split; [exact Hp|].
  destruct (before.(TskState).(prioTbl) priority); [contradiction| |];
    split; reflexivity.
Qed.

Lemma task_create_critical_error_frame : forall sg priority invocation origin before err after,
  task_create_critical sg priority invocation origin before (Some err) after ->
  after = before /\ (err = OS_ERR_TASK_CREATE_ISR \/ err = OS_ERR_PRIO_EXIST).
Proof.
  intros sg priority invocation origin before err after Hstep.
  unfold task_create_critical in Hstep.
  destruct (Z.ltb 0 before.(IntrState).(intNesting)).
  - destruct Hstep as [Hr Hs]; split; [exact Hs|left; congruence].
  - destruct Hstep as [_ Hstep].
    destruct (before.(TskState).(prioTbl) priority).
    + destruct Hstep as [Hr _]; discriminate.
    + destruct Hstep as [Hr Hs]; split; [exact Hs|right; congruence].
    + destruct Hstep as [Hr Hs]; split; [exact Hs|right; congruence].
Qed.

Lemma task_create_critical_continuation_iff : forall sg priority invocation origin before after,
  task_create_critical sg priority invocation origin before None after <->
  before.(IntrState).(intNesting) <= 0 /\ task_priority_in_range sg priority /\
  before.(TskState).(prioTbl) priority = PTFree /\
  after = replace_TskS
    (task_reserve before.(TskState) priority invocation origin) before.
Proof.
  intros; unfold task_create_critical.
  destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hnest.
  - apply Z.ltb_lt in Hnest; split.
    + intros [H _]; discriminate.
    + intros [H _]; lia.
  - apply Z.ltb_ge in Hnest.
    destruct (before.(TskState).(prioTbl) priority) eqn:Htable.
    + split.
      * intros [Hp [_ Hafter]]; split; [exact Hnest|].
        split; [exact Hp|split; [reflexivity|exact Hafter]].
      * intros [_ [Hp [_ Hafter]]]; split; [exact Hp|split; [reflexivity|exact Hafter]].
    + split; [intros [_ [H _]]|intros [_ [_ [H _]]]]; discriminate.
    + split; [intros [_ [H _]]|intros [_ [_ [H _]]]]; discriminate.
Qed.

Lemma task_create_critical_deterministic : forall sg priority invocation origin before r1 s1 r2 s2,
  task_create_critical sg priority invocation origin before r1 s1 ->
  task_create_critical sg priority invocation origin before r2 s2 ->
  r1 = r2 /\ s1 = s2.
Proof.
  intros sg priority invocation origin before r1 s1 r2 s2 H1 H2.
  unfold task_create_critical in H1, H2.
  destruct (Z.ltb 0 before.(IntrState).(intNesting)).
  - destruct H1, H2; split; congruence.
  - destruct H1 as [_ H1], H2 as [_ H2].
    destruct (before.(TskState).(prioTbl) priority);
      destruct H1, H2; split; congruence.
Qed.

Lemma task_create_critical_has_result : forall sg priority invocation origin before,
  (0 < before.(IntrState).(intNesting) \/ task_priority_in_range sg priority) ->
  exists result after, task_create_critical sg priority invocation origin before result after.
Proof.
  intros sg priority invocation origin before Hdomain.
  unfold task_create_critical.
  destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hnest.
  - exists (Some OS_ERR_TASK_CREATE_ISR), before; split; reflexivity.
  - assert (Hp : task_priority_in_range sg priority).
    { destruct Hdomain as [Hpositive|Hp]; [apply Z.ltb_ge in Hnest; lia|exact Hp]. }
    destruct (before.(TskState).(prioTbl) priority).
    + exists None, (replace_TskS
        (task_reserve before.(TskState) priority invocation origin) before).
      split; [exact Hp|split; reflexivity].
    + exists (Some OS_ERR_PRIO_EXIST), before; split; [exact Hp|split; reflexivity].
    + exists (Some OS_ERR_PRIO_EXIST), before; split; [exact Hp|split; reflexivity].
Qed.

(** Public arguments have no name field.  The name address below is the
    internal OS_TCBInit initial-name constant, whose storage/configuration
    binding is supplied separately.  The constructors distinguish the two
    compiled APIs; [TaskCreateExtended] does not add a runtime feature test. *)
Inductive TaskCreateExtension : Type :=
| TaskCreateBasic
| TaskCreateExtended (public_id : Z) (stack_bottom : addr) (stack_size : Z)
    (extension : addr) (options : Z).

Record TaskCreateArgs : Type := {
  createEntry : addr;
  createArgument : addr;
  createStackTop : addr;
  createPriority : Priority;
  createExtension : TaskCreateExtension
}.

Definition task_create_options (args : TaskCreateArgs) : Z :=
  match args.(createExtension) with
  | TaskCreateBasic => 0
  | TaskCreateExtended _ _ _ _ options => options
  end.

Definition task_create_tcb_args (args : TaskCreateArgs) (stack_pointer initial_name : addr)
  : TaskTCBInitArgs :=
  match args.(createExtension) with
  | TaskCreateBasic =>
      {| initPrio := args.(createPriority); initStkPtr := stack_pointer;
         initStkBottom := 0; initPublicId := 0; initStkSize := 0;
         initExtPtr := 0; initOpt := 0; initNamePointer := initial_name |}
  | TaskCreateExtended public_id bottom size extension options =>
      {| initPrio := args.(createPriority); initStkPtr := stack_pointer;
         initStkBottom := bottom; initPublicId := public_id; initStkSize := size;
         initExtPtr := extension; initOpt := options; initNamePointer := initial_name |}
  end.

Lemma task_create_tcb_args_common_fields : forall args stack_pointer initial_name,
  let actual := task_create_tcb_args args stack_pointer initial_name in
  actual.(initPrio) = args.(createPriority) /\
  actual.(initStkPtr) = stack_pointer /\
  actual.(initOpt) = task_create_options args /\
  actual.(initNamePointer) = initial_name.
Proof.
  intros args stack_pointer initial_name; cbv zeta.
  unfold task_create_tcb_args, task_create_options;
    destruct args.(createExtension); repeat split; reflexivity.
Qed.

Lemma task_create_tcb_args_basic_fields : forall args stack_pointer initial_name,
  args.(createExtension) = TaskCreateBasic ->
  let actual := task_create_tcb_args args stack_pointer initial_name in
  actual.(initStkBottom) = 0 /\ actual.(initPublicId) = 0 /\
  actual.(initStkSize) = 0 /\ actual.(initExtPtr) = 0 /\ actual.(initOpt) = 0.
Proof.
  intros args stack_pointer initial_name H; cbv zeta.
  unfold task_create_tcb_args; rewrite H; repeat split; reflexivity.
Qed.

Lemma task_create_tcb_args_extended_fields : forall args stack_pointer initial_name id bottom size ext opt,
  args.(createExtension) = TaskCreateExtended id bottom size ext opt ->
  let actual := task_create_tcb_args args stack_pointer initial_name in
  actual.(initStkBottom) = bottom /\ actual.(initPublicId) = id /\
  actual.(initStkSize) = size /\ actual.(initExtPtr) = ext /\ actual.(initOpt) = opt.
Proof.
  intros args stack_pointer initial_name id bottom size ext opt H; cbv zeta.
  unfold task_create_tcb_args; rewrite H; repeat split; reflexivity.
Qed.

(** This parameter binds OS_TASK_STAT_STK_CHK_EN, which is not the same
    macro as OS_TASK_STAT_EN/cfgStatisticsEnabled.  The call exists whenever
    the former is enabled, even if OS_TaskStkClr internally decides not to
    clear any cells because of [opt].  Basic creation never calls it. *)
Definition task_create_stack_clear_args (stack_check_enabled : bool) (args : TaskCreateArgs)
  : option (addr * Z * Z) :=
  match args.(createExtension) with
  | TaskCreateBasic => None
  | TaskCreateExtended _ bottom size _ options =>
      if stack_check_enabled then Some (bottom, size, options) else None
  end.

Lemma task_create_stack_clear_basic : forall enabled args,
  args.(createExtension) = TaskCreateBasic -> task_create_stack_clear_args enabled args = None.
Proof. intros; unfold task_create_stack_clear_args; rewrite H; reflexivity. Qed.

Lemma task_create_stack_clear_disabled : forall args,
  task_create_stack_clear_args false args = None.
Proof. intros; unfold task_create_stack_clear_args; destruct args.(createExtension); reflexivity. Qed.

Lemma task_create_stack_clear_extended : forall args id bottom size ext opt,
  args.(createExtension) = TaskCreateExtended id bottom size ext opt ->
  task_create_stack_clear_args true args = Some (bottom, size, opt).
Proof. intros; unfold task_create_stack_clear_args; rewrite H; reflexivity. Qed.

(** An argument observation, not a proof of these call implementations.
    The [stack_pointer] in the third call is the result of the second call,
    not the input top-of-stack.  The execution relation below binds it. *)
Inductive TaskCreateInitializationCall : Type :=
| TaskCreateClearStack (bottom : addr) (size options : Z)
| TaskCreateInitializeStack (entry argument top : addr) (options : Z)
| TaskCreateInitializeTCB (args : TaskTCBInitArgs).

Definition task_create_initialization_calls (stack_check_enabled : bool)
  (args : TaskCreateArgs) (stack_pointer initial_name : addr)
  : list TaskCreateInitializationCall :=
  (match task_create_stack_clear_args stack_check_enabled args with
   | None => []
   | Some (bottom, size, options) => [TaskCreateClearStack bottom size options]
   end) ++
  [TaskCreateInitializeStack args.(createEntry) args.(createArgument)
     args.(createStackTop) (task_create_options args);
   TaskCreateInitializeTCB (task_create_tcb_args args stack_pointer initial_name)].

Lemma task_create_initialization_calls_basic : forall enabled args stack_pointer initial_name,
  args.(createExtension) = TaskCreateBasic ->
  task_create_initialization_calls enabled args stack_pointer initial_name =
    [TaskCreateInitializeStack args.(createEntry) args.(createArgument) args.(createStackTop) 0;
     TaskCreateInitializeTCB (task_create_tcb_args args stack_pointer initial_name)].
Proof.
  intros; unfold task_create_initialization_calls.
  rewrite (task_create_stack_clear_basic enabled args H); simpl.
  unfold task_create_options; rewrite H; reflexivity.
Qed.

Lemma task_create_initialization_calls_extended : forall args stack_pointer initial_name id bottom size ext opt,
  args.(createExtension) = TaskCreateExtended id bottom size ext opt ->
  task_create_initialization_calls true args stack_pointer initial_name =
    [TaskCreateClearStack bottom size opt;
     TaskCreateInitializeStack args.(createEntry) args.(createArgument) args.(createStackTop) opt;
     TaskCreateInitializeTCB (task_create_tcb_args args stack_pointer initial_name)].
Proof.
  intros; unfold task_create_initialization_calls.
  rewrite (task_create_stack_clear_extended args id bottom size ext opt H); simpl.
  unfold task_create_options; rewrite H; reflexivity.
Qed.

(** Composition of returning call intervals.  The supplied relations must
    bind actual call implementations, their heap/resource effects and any
    allowed open-interrupt interference.  [State] can carry those resources;
    it is deliberately not restricted to the kernel's pure abstract record.
    No instance or totality of an ARM/BSP stack constructor is asserted here.

    The result is the exact OS_TCBInit return.  Tracing, its fresh OSRunning
    read, scheduling and failure rollback occur later and are NOT covered by
    this initialization prefix.  In particular no old kernel state is used
    as a rollback target and no call is assumed to preserve state by name. *)
Definition task_create_initialization {State : Type}
  (clear_stack : addr -> Z -> Z -> program State unit)
  (initialize_stack : addr -> addr -> addr -> Z -> program State addr)
  (initialize_tcb : TaskTCBInitArgs -> program State OSErrCode)
  (stack_check_enabled : bool) (args : TaskCreateArgs) (initial_name : addr)
  : program State OSErrCode :=
  fun before result after => exists before_init stack_pointer after_init,
    (match task_create_stack_clear_args stack_check_enabled args with
     | None => before_init = before
     | Some (bottom, size, options) => clear_stack bottom size options before tt before_init
     end) /\
    initialize_stack args.(createEntry) args.(createArgument) args.(createStackTop)
      (task_create_options args) before_init stack_pointer after_init /\
    initialize_tcb (task_create_tcb_args args stack_pointer initial_name) after_init result after.

Lemma task_create_initialization_without_clear :
  forall State clear_stack initialize_stack initialize_tcb enabled args initial_name before result after,
  task_create_stack_clear_args enabled args = None ->
  @task_create_initialization State clear_stack initialize_stack initialize_tcb
    enabled args initial_name before result after <->
  exists stack_pointer after_init,
    initialize_stack args.(createEntry) args.(createArgument) args.(createStackTop)
      (task_create_options args) before stack_pointer after_init /\
    initialize_tcb (task_create_tcb_args args stack_pointer initial_name) after_init result after.
Proof.
  intros State clear_stack initialize_stack initialize_tcb enabled args initial_name before result after Hclear.
  unfold task_create_initialization; rewrite Hclear; split.
  - intros [before_init [stack_pointer [after_init [Heq Hcalls]]]].
    subst before_init; exists stack_pointer, after_init; exact Hcalls.
  - intros [stack_pointer [after_init Hcalls]].
    exists before, stack_pointer, after_init; split; [reflexivity|exact Hcalls].
Qed.

Lemma task_create_initialization_with_clear :
  forall State clear_stack initialize_stack initialize_tcb enabled args initial_name
    bottom size options before result after,
  task_create_stack_clear_args enabled args = Some (bottom, size, options) ->
  @task_create_initialization State clear_stack initialize_stack initialize_tcb
    enabled args initial_name before result after <->
  exists before_init stack_pointer after_init,
    clear_stack bottom size options before tt before_init /\
    initialize_stack args.(createEntry) args.(createArgument) args.(createStackTop)
      (task_create_options args) before_init stack_pointer after_init /\
    initialize_tcb (task_create_tcb_args args stack_pointer initial_name) after_init result after.
Proof. intros; unfold task_create_initialization; rewrite H; reflexivity. Qed.

Lemma task_create_initialization_preserves :
  forall State clear_stack initialize_stack initialize_tcb (invariant : State -> Prop),
  (forall bottom size options before after,
     invariant before -> clear_stack bottom size options before tt after -> invariant after) ->
  (forall entry argument top options before pointer after,
     invariant before -> initialize_stack entry argument top options before pointer after -> invariant after) ->
  (forall actual before result after,
     invariant before -> initialize_tcb actual before result after -> invariant after) ->
  forall enabled args initial_name before result after,
    invariant before ->
    @task_create_initialization State clear_stack initialize_stack initialize_tcb
      enabled args initial_name before result after -> invariant after.
Proof.
  intros State clear_stack initialize_stack initialize_tcb invariant Hclear Hstack Htcb
    enabled args initial_name before result after Hbefore
    [before_init [stack_pointer [after_init [Hclear_call [Hstack_call Htcb_call]]]]].
  assert (Hbefore_init : invariant before_init).
  { destruct (task_create_stack_clear_args enabled args) as [[[bottom size] options]|].
    - eapply Hclear; eassumption.
    - subst before_init; exact Hbefore. }
  eapply Htcb; [eapply Hstack; eassumption|exact Htcb_call].
Qed.

(** Returning tail AFTER OS_TCBInit.

    Source/os_trace.h:77,81 defines both trace macros as empty by default;
    their arguments are then NOT evaluated.  The enabled case below covers
    a specifically bound one-evaluation call expansion, not arbitrary user
    macros (which could evaluate the argument repeatedly or transfer control).

    Observations are relations rather than entry-state projections: reads
    occur at their actual source positions, and their call-site contracts
    can include allowed open-interrupt interference.  In particular the
    OSRunning read follows the returning success trace.  It is never copied
    from function entry, before TCBInit, or before the trace.

    [rollback] is the returning Save/current-slot-NULL/Restore interval, not
    restoration of an earlier abstract snapshot.  Its native lifecycle and
    heap instance is separate.  Neither a trace, scheduler nor rollback is
    assumed to return.  These are partial execution relations: a returning
    execution contains evidence of every call required by its branch. *)
Section TaskCreateTail.

Context {State : Type}.
Variable read_priority : Priority -> program State addr.
Variable read_running : program State bool.
Variable trace_created trace_failed : addr -> program State unit.
Variable schedule : program State unit.
Variable rollback : Priority -> program State unit.
Variable created_trace_enabled failed_trace_enabled : bool.

Definition task_create_trace_call (enabled : bool)
  (trace : addr -> program State unit) (priority : Priority)
  : program State unit :=
  fun before result after => result = tt /\
    if enabled then exists pointer after_read,
      read_priority priority before pointer after_read /\
      trace pointer after_read tt after
    else after = before.

Lemma task_create_trace_call_erased : forall trace priority before result after,
  task_create_trace_call false trace priority before result after <->
  result = tt /\ after = before.
Proof. reflexivity. Qed.

Lemma task_create_trace_call_enabled : forall trace priority before result after,
  task_create_trace_call true trace priority before result after <->
  result = tt /\ exists pointer after_read,
    read_priority priority before pointer after_read /\
    trace pointer after_read tt after.
Proof. reflexivity. Qed.

Definition task_create_tail (args : TaskCreateArgs) (init_result : OSErrCode)
  : program State OSErrCode :=
  fun before result after => result = init_result /\
    match init_result with
    | OS_ERR_NONE => exists after_trace running after_read,
        task_create_trace_call created_trace_enabled trace_created args.(createPriority)
          before tt after_trace /\
        read_running after_trace running after_read /\
        if running then schedule after_read tt after else after = after_read
    | _ => exists before_rollback,
        (match args.(createExtension) with
         | TaskCreateBasic =>
             task_create_trace_call failed_trace_enabled trace_failed args.(createPriority)
               before tt before_rollback
         | TaskCreateExtended _ _ _ _ _ => before_rollback = before
         end) /\
        rollback args.(createPriority) before_rollback tt after
    end.

Lemma task_create_tail_return_eq : forall args init_result before result after,
  task_create_tail args init_result before result after -> result = init_result.
Proof. intros args init_result before result after [H _]; exact H. Qed.

Lemma task_create_tail_return_code_eq : forall args init_result before result after,
  task_create_tail args init_result before result after ->
  encode_os_err_code result = encode_os_err_code init_result.
Proof. intros; rewrite (task_create_tail_return_eq args init_result before result after H); reflexivity. Qed.

Lemma task_create_tail_success_iff : forall args before result after,
  task_create_tail args OS_ERR_NONE before result after <->
  result = OS_ERR_NONE /\ exists after_trace running after_read,
    task_create_trace_call created_trace_enabled trace_created args.(createPriority)
      before tt after_trace /\
    read_running after_trace running after_read /\
    if running then schedule after_read tt after else after = after_read.
Proof. reflexivity. Qed.

(** This branch requires no scheduler execution.  [after_read] may differ
    from [before] and from [after_trace]; it is the state of the actual
    post-trace OSRunning observation. *)
Lemma task_create_tail_success_without_schedule : forall args before after_trace after_read,
  task_create_trace_call created_trace_enabled trace_created args.(createPriority)
    before tt after_trace ->
  read_running after_trace false after_read ->
  task_create_tail args OS_ERR_NONE before OS_ERR_NONE after_read.
Proof.
  intros args before after_trace after_read Htrace Hread.
  split; [reflexivity|]; exists after_trace, false, after_read.
  split; [exact Htrace|split; [exact Hread|reflexivity]].
Qed.

Lemma task_create_tail_success_with_schedule : forall args before after_trace after_read after,
  task_create_trace_call created_trace_enabled trace_created args.(createPriority)
    before tt after_trace ->
  read_running after_trace true after_read -> schedule after_read tt after ->
  task_create_tail args OS_ERR_NONE before OS_ERR_NONE after.
Proof.
  intros args before after_trace after_read after Htrace Hread Hschedule.
  split; [reflexivity|]; exists after_trace, true, after_read.
  split; [exact Htrace|split; [exact Hread|exact Hschedule]].
Qed.

Lemma task_create_tail_failure_iff : forall args init_result before result after,
  init_result <> OS_ERR_NONE ->
  task_create_tail args init_result before result after <->
  result = init_result /\ exists before_rollback,
    (match args.(createExtension) with
     | TaskCreateBasic =>
         task_create_trace_call failed_trace_enabled trace_failed args.(createPriority)
           before tt before_rollback
     | TaskCreateExtended _ _ _ _ _ => before_rollback = before
     end) /\
    rollback args.(createPriority) before_rollback tt after.
Proof.
  intros args init_result before result after Herror.
  unfold task_create_tail; destruct init_result; try contradiction; reflexivity.
Qed.

Lemma task_create_tail_basic_failure_iff : forall args init_result before result after,
  args.(createExtension) = TaskCreateBasic -> init_result <> OS_ERR_NONE ->
  task_create_tail args init_result before result after <->
  result = init_result /\ exists before_rollback,
    task_create_trace_call failed_trace_enabled trace_failed args.(createPriority)
      before tt before_rollback /\
    rollback args.(createPriority) before_rollback tt after.
Proof.
  intros args init_result before result after Hbasic Herror.
  rewrite (task_create_tail_failure_iff args init_result before result after Herror).
  rewrite Hbasic; reflexivity.
Qed.

(** Extended creation has NO failed-create trace macro site.  Even when
    failed traces are enabled, its error branch does not read the table
    for tracing, inspect OSRunning or call OS_Sched. *)
Lemma task_create_tail_extended_failure_iff : forall args init_result before result after id bottom size ext opt,
  args.(createExtension) = TaskCreateExtended id bottom size ext opt ->
  init_result <> OS_ERR_NONE ->
  task_create_tail args init_result before result after <->
  result = init_result /\ rollback args.(createPriority) before tt after.
Proof.
  intros args init_result before result after id bottom size ext opt Hext Herror.
  rewrite (task_create_tail_failure_iff args init_result before result after Herror).
  rewrite Hext; split.
  - intros [Hr [middle [Heq Hrollback]]]; subst middle; split; assumption.
  - intros [Hr Hrollback]; split; [exact Hr|]; exists before;
      split; [reflexivity|exact Hrollback].
Qed.

Lemma task_create_tail_basic_erased_failure_iff : forall args init_result before result after,
  args.(createExtension) = TaskCreateBasic -> init_result <> OS_ERR_NONE ->
  failed_trace_enabled = false ->
  task_create_tail args init_result before result after <->
  result = init_result /\ rollback args.(createPriority) before tt after.
Proof.
  intros args init_result before result after Hbasic Herror Herased.
  rewrite (task_create_tail_basic_failure_iff args init_result before result after Hbasic Herror).
  rewrite Herased; unfold task_create_trace_call; simpl; split.
  - intros [Hr [middle [[_ Heq] Hrollback]]]; subst middle; split; assumption.
  - intros [Hr Hrollback]; split; [exact Hr|]; exists before.
    split; [split; reflexivity|exact Hrollback].
Qed.

End TaskCreateTail.
