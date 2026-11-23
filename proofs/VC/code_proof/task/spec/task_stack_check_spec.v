Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.

Import UCOS2_C_Rules ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskStkChk: V2.93.01 Source/os_task.c:916--984.
    OS_TaskStatStkChk: Source/os_core.c:1949--1976.
    Both require OS_TASK_STAT_STK_CHK_EN and OS_TASK_CREATE_EXT_EN.
    This file selects growth=1 and 32-bit unsigned OS_STK.

    Crucially, the source scans AFTER Restore and does not test nfree<size.
    The dynamic read trace below therefore has no artificial size guard.
    A finite list certificate is a sufficient readable first-nonzero
    witness, not a replacement bounded implementation or a promise that
    another task leaves its stack unchanged during an unprotected scan. *)
Record TaskStackCheckData : Type := {
  stackCheckFree : Z;
  stackCheckUsed : Z
}.

Definition task_stack_check_zero_data : TaskStackCheckData :=
  {| stackCheckFree := 0; stackCheckUsed := 0 |}.

Definition task_stack_check_data_rep (output : addr) (data : TaskStackCheckData)
  : Assertion :=
  (&(output # "os_stk_data" ->ₛ "OSFree")) # UInt |-> data.(stackCheckFree) **
  (&(output # "os_stk_data" ->ₛ "OSUsed")) # UInt |-> data.(stackCheckUsed).

(** The concrete callee footprint of [OSTaskStkChk].  The output structure is
    caller-owned: the callee initializes both INT32U fields on every
    non-null, argument-valid call, while all kernel/stack resources remain in
    [frame].  Keeping this as a separate interface lets [OS_TaskStatStkChk]
    compose the call without inventing a second stack representation. *)
Definition task_stack_check_output_uninitialized (output : addr) : Assertion :=
  UIntArray.undef_full output 2.

Definition task_stack_check_output_initialized
  (output : addr) (data : TaskStackCheckData) : Assertion :=
  task_stack_check_data_rep output data.

Definition task_stack_check_callee_pre (output : addr) (frame : Assertion) : Assertion :=
  task_stack_check_output_uninitialized output ** frame.

Definition task_stack_check_callee_post
  (output : addr) (data : TaskStackCheckData) (frame : Assertion) : Assertion :=
  task_stack_check_output_initialized output data ** frame.

Lemma task_stack_check_output_initialization : forall output data frame,
  task_stack_check_callee_post output data frame =
  task_stack_check_data_rep output data ** frame.
Proof. reflexivity. Qed.

Definition task_stack_check_argument_error (sg : StableGlobVars)
  (priority : Priority) (output : addr) : option OSErrCode :=
  if sg.(osKernelConfig).(cfgArgumentChecks) then
    if (Z.ltb sg.(osLowestPrio) priority &&
        negb (Z.eqb priority sg.(osPrioSelf)))%bool
    then Some OS_ERR_PRIO_INVALID
    else if Z.eqb output 0 then Some OS_ERR_PDATA_NULL else None
  else None.

Lemma task_stack_check_argument_error_disabled : forall sg priority output,
  sg.(osKernelConfig).(cfgArgumentChecks) = false ->
  task_stack_check_argument_error sg priority output = None.
Proof. intros; unfold task_stack_check_argument_error; rewrite H; reflexivity. Qed.

Lemma task_stack_check_argument_error_priority : forall sg priority output,
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  sg.(osLowestPrio) < priority -> priority <> sg.(osPrioSelf) ->
  task_stack_check_argument_error sg priority output = Some OS_ERR_PRIO_INVALID.
Proof.
  intros; unfold task_stack_check_argument_error.
  rewrite H, (proj2 (Z.ltb_lt _ _) H0), (proj2 (Z.eqb_neq _ _) H1); reflexivity.
Qed.

Lemma task_stack_check_argument_error_null : forall sg priority,
  sg.(osKernelConfig).(cfgArgumentChecks) = true ->
  (priority <= sg.(osLowestPrio) \/ priority = sg.(osPrioSelf)) ->
  task_stack_check_argument_error sg priority 0 = Some OS_ERR_PDATA_NULL.
Proof.
  intros sg priority Hchecks [Hrange|Hself]; unfold task_stack_check_argument_error;
    rewrite Hchecks.
  - rewrite (proj2 (Z.ltb_ge _ _) Hrange); reflexivity.
  - rewrite Hself, Z.eqb_refl, Bool.andb_false_r; reflexivity.
Qed.

Lemma task_stack_check_lowest_priority_allowed : forall sg output,
  sg.(osKernelConfig).(cfgArgumentChecks) = true -> output <> 0 ->
  task_stack_check_argument_error sg sg.(osLowestPrio) output = None.
Proof.
  intros; unfold task_stack_check_argument_error.
  rewrite H, Z.ltb_irrefl, (proj2 (Z.eqb_neq _ _) H0); reflexivity.
Qed.

Lemma task_stack_check_argument_error_codes : forall sg priority output error,
  task_stack_check_argument_error sg priority output = Some error ->
  error = OS_ERR_PRIO_INVALID \/ error = OS_ERR_PDATA_NULL.
Proof.
  intros; unfold task_stack_check_argument_error in H.
  destruct (cfgArgumentChecks (osKernelConfig sg)); [|discriminate].
  destruct (Z.ltb (osLowestPrio sg) priority && negb (Z.eqb priority (osPrioSelf sg)))%bool;
    [inversion H; auto|].
  destruct (Z.eqb output 0); inversion H; auto.
Qed.

(** Both output stores occur before Save, and in OSFree then OSUsed order.
    The prefix-error branch does not access either output field. *)
Definition task_stack_check_clear_free (data : TaskStackCheckData) : TaskStackCheckData :=
  {| stackCheckFree := 0; stackCheckUsed := data.(stackCheckUsed) |}.
Definition task_stack_check_clear_used (data : TaskStackCheckData) : TaskStackCheckData :=
  {| stackCheckFree := data.(stackCheckFree); stackCheckUsed := 0 |}.

Lemma task_stack_check_output_clear_order : forall data,
  task_stack_check_clear_used (task_stack_check_clear_free data) = task_stack_check_zero_data.
Proof. reflexivity. Qed.

Record TaskStackCheckSnapshot : Type := {
  stackCheckSlot : TaskID;
  stackCheckGeneration : nat;
  stackCheckBottom : addr;
  stackCheckSize : Z
}.

Definition task_stack_check_snapshot (slot : TaskID) (node : TaskAbstractState)
  : TaskStackCheckSnapshot :=
  {| stackCheckSlot := slot; stackCheckGeneration := node.(taskGeneration);
     stackCheckBottom := node.(tcbStkBottom);
     stackCheckSize := node.(tcbStkSize) |}.

Inductive TaskStackCheckDecision : Type :=
| TaskStackCheckError (error : OSErrCode)
| TaskStackCheckScan (snapshot : TaskStackCheckSnapshot).

(** This relation starts after Save and ends before Restore.  SELF alone
    reads OSTCBCur->OSTCBPrio; an explicit priority does not need a current
    task merely to perform its table lookup.  A PTTask entry may be an alias:
    its selected TCB is not silently replaced with a task named by [prio].
    No ISR rejection or scheduler-lock test is added: neither is in C.
    Index/lookup premises interpret actual readable memory, not extra errors. *)
Definition task_stack_check_critical (sg : StableGlobVars) (priority : Priority)
  : program UCOS2_Verify_State TaskStackCheckDecision :=
  fun before decision after =>
    after = before /\ exists selected,
      (if Z.eqb priority sg.(osPrioSelf) then
         exists current_id current,
           before.(SchedState).(curTaskID) = Some current_id /\
           before.(TskState).(inUsedTaskStates) current_id = Some current /\
           selected = current.(curPrio)
       else selected = priority) /\
      task_priority_in_range sg selected /\
      match before.(TskState).(prioTbl) selected with
      | PTFree | PTReserved => decision = TaskStackCheckError OS_ERR_TASK_NOT_EXIST
      | PTTask slot => exists node,
          before.(TskState).(inUsedTaskStates) slot = Some node /\
          if Z.eqb (Z.land node.(tcbOpt) 1) 0
          then decision = TaskStackCheckError OS_ERR_TASK_OPT
          else decision = TaskStackCheckScan (task_stack_check_snapshot slot node)
      end.

Lemma task_stack_check_critical_frame : forall sg priority before decision after,
  task_stack_check_critical sg priority before decision after -> after = before.
Proof. intros; exact (proj1 H). Qed.

Lemma task_stack_check_critical_explicit_free : forall sg priority before,
  priority <> sg.(osPrioSelf) -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTFree ->
  task_stack_check_critical sg priority before
    (TaskStackCheckError OS_ERR_TASK_NOT_EXIST) before.
Proof.
  intros sg priority before Hexplicit Hrange Htable.
  split; [reflexivity|]; exists priority.
  rewrite (proj2 (Z.eqb_neq _ _) Hexplicit), Htable.
  split; [reflexivity|]; split; [exact Hrange|reflexivity].
Qed.

Lemma task_stack_check_critical_explicit_reserved : forall sg priority before,
  priority <> sg.(osPrioSelf) -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTReserved ->
  task_stack_check_critical sg priority before
    (TaskStackCheckError OS_ERR_TASK_NOT_EXIST) before.
Proof.
  intros sg priority before Hexplicit Hrange Htable.
  split; [reflexivity|]; exists priority.
  rewrite (proj2 (Z.eqb_neq _ _) Hexplicit), Htable.
  split; [reflexivity|]; split; [exact Hrange|reflexivity].
Qed.

Lemma task_stack_check_critical_explicit_option_error : forall sg priority before slot node,
  priority <> sg.(osPrioSelf) -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTTask slot ->
  before.(TskState).(inUsedTaskStates) slot = Some node ->
  Z.land node.(tcbOpt) 1 = 0 ->
  task_stack_check_critical sg priority before (TaskStackCheckError OS_ERR_TASK_OPT) before.
Proof.
  intros; split; [reflexivity|]; exists priority.
  rewrite (proj2 (Z.eqb_neq _ _) H), H1; split; [reflexivity|].
  split; [exact H0|]; exists node; split; [exact H2|].
  rewrite H3; reflexivity.
Qed.

Lemma task_stack_check_critical_explicit_scan : forall sg priority before slot node,
  priority <> sg.(osPrioSelf) -> task_priority_in_range sg priority ->
  before.(TskState).(prioTbl) priority = PTTask slot ->
  before.(TskState).(inUsedTaskStates) slot = Some node ->
  Z.land node.(tcbOpt) 1 <> 0 ->
  task_stack_check_critical sg priority before
    (TaskStackCheckScan (task_stack_check_snapshot slot node)) before.
Proof.
  intros; split; [reflexivity|]; exists priority.
  rewrite (proj2 (Z.eqb_neq _ _) H), H1; split; [reflexivity|].
  split; [exact H0|]; exists node; split; [exact H2|].
  rewrite (proj2 (Z.eqb_neq _ _) H3); reflexivity.
Qed.

Lemma task_stack_check_critical_error_codes : forall sg priority before error after,
  task_stack_check_critical sg priority before (TaskStackCheckError error) after ->
  error = OS_ERR_TASK_NOT_EXIST \/ error = OS_ERR_TASK_OPT.
Proof.
  intros sg priority before error after [_ [selected [_ [_ Hlookup]]]].
  destruct (prioTbl (TskState before) selected); try (inversion Hlookup; auto).
  destruct Hlookup as [node [_ Hoption]].
  destruct (Z.eqb (Z.land (tcbOpt node) 1) 0); inversion Hoption; auto.
Qed.

Lemma task_stack_check_critical_scan_fields : forall sg priority before snapshot after,
  task_stack_check_critical sg priority before (TaskStackCheckScan snapshot) after ->
  exists selected slot node,
    before.(TskState).(prioTbl) selected = PTTask slot /\
    before.(TskState).(inUsedTaskStates) slot = Some node /\
    Z.land node.(tcbOpt) 1 <> 0 /\
    snapshot = task_stack_check_snapshot slot node.
Proof.
  intros sg priority before snapshot after [_ [selected [_ [_ Hlookup]]]].
  destruct (prioTbl (TskState before) selected) as [| |slot] eqn:Htable;
    try discriminate.
  destruct Hlookup as [node [Hnode Hoption]].
  destruct (Z.eqb (Z.land (tcbOpt node) 1) 0) eqn:Hbit;
    [discriminate|].
  inversion Hoption; subst snapshot; apply Z.eqb_neq in Hbit.
  exists selected, slot, node; auto.
Qed.

(** A stable-image certificate.  None denotes an uninitialized word, so it
    cannot certify a readable zero or nonzero.  At the end of the owned list
    the result is None, NOT a simulated successful bounded-loop return. *)
Fixpoint task_stack_scan_count (words : list (option Z)) : option nat :=
  match words with
  | [] | None :: _ => None
  | Some word :: rest =>
      if Z.eqb word 0 then option_map S (task_stack_scan_count rest) else Some O
  end.

Definition task_stack_scan_prefix (words : list (option Z)) (count : nat)
  (stop : Z) : Prop :=
  stop <> 0 /\ exists suffix,
    words = repeat (Some 0) count ++ Some stop :: suffix.

Lemma task_stack_scan_count_of_prefix : forall count stop suffix,
  stop <> 0 ->
  task_stack_scan_count (repeat (Some 0) count ++ Some stop :: suffix) = Some count.
Proof.
  induction count; intros stop suffix Hstop; simpl.
  - rewrite (proj2 (Z.eqb_neq _ _) Hstop); reflexivity.
  - rewrite IHcount by exact Hstop; reflexivity.
Qed.

Lemma task_stack_scan_count_has_prefix : forall words count,
  task_stack_scan_count words = Some count -> exists stop, task_stack_scan_prefix words count stop.
Proof.
  induction words as [|[value|] words IH]; intros count Hscan; simpl in Hscan;
    try discriminate.
  destruct (Z.eqb value 0) eqn:Hvalue.
  - apply Z.eqb_eq in Hvalue; subst value.
    destruct (task_stack_scan_count words) as [n|] eqn:Htail; simpl in Hscan;
      [inversion Hscan; subst count|discriminate].
    destruct (IH n eq_refl) as [stop [Hstop [suffix Hwords]]].
    exists stop; split; [exact Hstop|]; exists suffix; simpl; rewrite Hwords; reflexivity.
  - inversion Hscan; subst count; apply Z.eqb_neq in Hvalue.
    exists value; split; [exact Hvalue|]; exists words; reflexivity.
Qed.

Lemma task_stack_scan_count_prefix_iff : forall words count,
  task_stack_scan_count words = Some count <-> exists stop, task_stack_scan_prefix words count stop.
Proof.
  intros; split; [apply task_stack_scan_count_has_prefix|].
  intros [stop [Hstop [suffix ->]]]; apply task_stack_scan_count_of_prefix; exact Hstop.
Qed.

Lemma task_stack_scan_count_in_range : forall words count,
  task_stack_scan_count words = Some count -> (count < List.length words)%nat.
Proof.
  intros; apply task_stack_scan_count_has_prefix in H.
  destruct H as [stop [_ [suffix ->]]]; rewrite length_app, repeat_length; simpl; lia.
Qed.

Lemma task_stack_scan_all_zero_no_stop : forall count,
  task_stack_scan_count (repeat (Some 0) count) = None.
Proof. induction count; simpl; [reflexivity|rewrite IHcount; reflexivity]. Qed.

Lemma task_stack_scan_prefix_has_initialized_zero : forall words count stop index,
  task_stack_scan_prefix words count stop -> 0 <= index < Z.of_nat count ->
  Znth index words None = Some 0.
Proof.
  intros words count stop index [_ [suffix ->]] Hindex.
  rewrite app_Znth1.
  - apply Znth_repeat_lt; exact Hindex.
  - rewrite Zlength_correct, repeat_length; exact Hindex.
Qed.

Lemma task_stack_scan_prefix_has_initialized_stop : forall words count stop,
  task_stack_scan_prefix words count stop -> Znth (Z.of_nat count) words None = Some stop.
Proof.
  intros words count stop [_ [suffix ->]].
  rewrite app_Znth2.
  - rewrite Zlength_correct, repeat_length, Z.sub_diag; reflexivity.
  - rewrite Zlength_correct, repeat_length; lia.
Qed.

Definition task_stack_scan_data (size : Z) (count : nat) : TaskStackCheckData :=
  {| stackCheckFree := kernel_u32 (Z.of_nat count);
     stackCheckUsed := kernel_u32 (size - kernel_u32 (Z.of_nat count)) |}.

Lemma task_stack_scan_data_in_range : forall size count,
  0 <= (task_stack_scan_data size count).(stackCheckFree) < 4294967296 /\
  0 <= (task_stack_scan_data size count).(stackCheckUsed) < 4294967296.
Proof. intros; split; apply kernel_u32_in_range. Qed.

Lemma task_stack_scan_counter_increment : forall count,
  kernel_u32 (Z.of_nat (S count)) = kernel_u32 (kernel_u32 (Z.of_nat count) + 1).
Proof.
  intros; unfold kernel_u32; rewrite Z.add_mod_idemp_l by lia.
  rewrite Nat2Z.inj_succ; f_equal; lia.
Qed.

Lemma task_stack_scan_data_no_wrap : forall size count,
  0 <= Z.of_nat count <= size -> size < 4294967296 ->
  (task_stack_scan_data size count).(stackCheckFree) = Z.of_nat count /\
  (task_stack_scan_data size count).(stackCheckUsed) = size - Z.of_nat count.
Proof.
  intros; unfold task_stack_scan_data; simpl.
  rewrite kernel_u32_identity by lia; rewrite kernel_u32_identity by lia; auto.
Qed.

(** This is a concrete source-level arithmetic consequence, not a repaired
    bound: three zero words followed by a nonzero with size=2 returns
    OSUsed=UINT32_MAX, if those four reads are actually accessible. *)
Lemma task_stack_scan_can_exceed_recorded_size :
  task_stack_scan_count [Some 0; Some 0; Some 0; Some 1] = Some 3%nat /\
  task_stack_scan_data 2 3 = {| stackCheckFree := 3; stackCheckUsed := 4294967295 |}.
Proof. split; reflexivity. Qed.

Section DynamicStackReads.
  Context {State : Type}.
  Variable read_word : addr -> program State Z.

  (** Counts ZERO observations, not all reads.  The final nonzero read also
      executes pchk++, so final cursor advances count+1 words.  Each read
      sees its own state; no equality across Restore or intervening task
      execution is assumed. *)
  Inductive task_stack_scan_trace : addr -> State -> nat -> addr -> State -> Prop :=
  | task_stack_scan_trace_stop : forall cursor before value after,
      read_word cursor before value after -> value <> 0 ->
      task_stack_scan_trace cursor before O (cursor + sizeof(UINT)) after
  | task_stack_scan_trace_zero : forall cursor before middle count final_cursor after,
      read_word cursor before 0 middle ->
      task_stack_scan_trace (cursor + sizeof(UINT)) middle count final_cursor after ->
      task_stack_scan_trace cursor before (S count) final_cursor after.

  Lemma task_stack_scan_trace_cursor : forall cursor before count final_cursor after,
    task_stack_scan_trace cursor before count final_cursor after ->
    final_cursor = cursor + (Z.of_nat count + 1) * sizeof(UINT).
  Proof.
    intros cursor before count final_cursor after Htrace; induction Htrace.
    - reflexivity.
    - rewrite IHHtrace, Nat2Z.inj_succ; simpl; lia.
  Qed.

  Lemma task_stack_scan_trace_preserves : forall (property : State -> Prop),
    (forall cursor before value after,
      read_word cursor before value after -> property before -> property after) ->
    forall cursor before count final_cursor after,
      task_stack_scan_trace cursor before count final_cursor after ->
      property before -> property after.
  Proof.
    intros property Hread cursor before count final_cursor after Htrace;
      induction Htrace; intros Hbefore.
    - eapply Hread; eauto.
    - apply IHHtrace; eapply Hread; eauto.
  Qed.

  (** An existence theorem needs real read successors, not safeExec's
      partial-correctness assertion.  This one uses an explicit stable
      readable zero-prefix and final nonzero observation.  The more general
      trace above still permits changing states between individual reads. *)
  Lemma task_stack_scan_trace_exists : forall count cursor state,
    (forall index, (index < count)%nat ->
      read_word (cursor + Z.of_nat index * sizeof(UINT)) state 0 state) ->
    (exists stop, stop <> 0 /\
      read_word (cursor + Z.of_nat count * sizeof(UINT)) state stop state) ->
    task_stack_scan_trace cursor state count
      (cursor + (Z.of_nat count + 1) * sizeof(UINT)) state.
  Proof.
    induction count as [|count IH]; intros cursor state Hzero [stop [Hstop Hread]].
    - replace (cursor + (Z.of_nat O + 1) * sizeof(UINT)) with
        (cursor + sizeof(UINT)) by ring.
      replace (cursor + Z.of_nat O * sizeof(UINT)) with cursor in Hread by ring.
      apply task_stack_scan_trace_stop with stop; assumption.
    - replace (cursor + (Z.of_nat (S count) + 1) * sizeof(UINT)) with
        ((cursor + sizeof(UINT)) + (Z.of_nat count + 1) * sizeof(UINT))
        by (rewrite Nat2Z.inj_succ; ring).
      eapply task_stack_scan_trace_zero.
      + pose proof (Hzero O ltac:(lia)) as Hhead.
        replace (cursor + Z.of_nat O * sizeof(UINT)) with cursor in Hhead by ring.
        exact Hhead.
      + apply IH.
        * intros index Hindex.
          replace ((cursor + sizeof(UINT)) + Z.of_nat index * sizeof(UINT)) with
            (cursor + Z.of_nat (S index) * sizeof(UINT))
            by (rewrite Nat2Z.inj_succ; ring).
          apply Hzero; lia.
        * exists stop; split; [exact Hstop|].
          replace ((cursor + sizeof(UINT)) + Z.of_nat count * sizeof(UINT)) with
            (cursor + Z.of_nat (S count) * sizeof(UINT))
            by (rewrite Nat2Z.inj_succ; ring).
          exact Hread.
  Qed.

  Lemma task_stack_scan_prefix_trace : forall words count stop cursor state,
    task_stack_scan_prefix words count stop ->
    (forall index value,
      0 <= index < Zlength words -> Znth index words None = Some value ->
      read_word (cursor + index * sizeof(UINT)) state value state) ->
    task_stack_scan_trace cursor state count
      (cursor + (Z.of_nat count + 1) * sizeof(UINT)) state.
  Proof.
    intros words count stop cursor state Hprefix Hread.
    assert (Hcount : Z.of_nat count < Zlength words).
    { destruct Hprefix as [_ [suffix ->]].
      rewrite Zlength_correct, length_app, repeat_length; simpl; lia. }
    apply task_stack_scan_trace_exists.
    - intros index Hindex; apply Hread; [lia|].
      apply (task_stack_scan_prefix_has_initialized_zero words count stop (Z.of_nat index));
        [exact Hprefix|lia].
    - exists stop; split; [exact (proj1 Hprefix)|].
      apply Hread; [lia|].
      apply task_stack_scan_prefix_has_initialized_stop; exact Hprefix.
  Qed.
End DynamicStackReads.

(** Final API observation, separated from its call/region realization.
    The critical decision and successful read count MUST be supplied by
    task_stack_check_critical and a real read trace (or a stable-image
    refinement).  This definition alone is not a whole-function contract.
    Prefix errors leave output unchanged.  Critical errors return the
    already-zeroed output; success writes OSFree before OSUsed. *)
Definition task_stack_check_observation (sg : StableGlobVars) (priority : Priority)
  (output : addr) (initial_data : TaskStackCheckData)
  (decision : option TaskStackCheckDecision) (count : option nat)
  (error : OSErrCode) (final_data : TaskStackCheckData) : Prop :=
  match task_stack_check_argument_error sg priority output with
  | Some prefix_error => decision = None /\ count = None /\
      error = prefix_error /\ final_data = initial_data
  | None => match decision with
    | None => False
    | Some (TaskStackCheckError critical_error) => count = None /\
        error = critical_error /\ final_data = task_stack_check_zero_data
    | Some (TaskStackCheckScan snapshot) => exists n,
        count = Some n /\ error = OS_ERR_NONE /\
        final_data = task_stack_scan_data snapshot.(stackCheckSize) n
    end
  end.

Lemma task_stack_check_observation_prefix_frame : forall sg priority output data prefix_error
  decision count error final_data,
  task_stack_check_argument_error sg priority output = Some prefix_error ->
  task_stack_check_observation sg priority output data decision count error final_data ->
  error = prefix_error /\ final_data = data /\ decision = None /\ count = None.
Proof. intros; unfold task_stack_check_observation in H0; rewrite H in H0; tauto. Qed.

Lemma task_stack_check_observation_critical_error_zero : forall sg priority output data critical_error,
  task_stack_check_argument_error sg priority output = None ->
  task_stack_check_observation sg priority output data
    (Some (TaskStackCheckError critical_error)) None critical_error task_stack_check_zero_data.
Proof. intros; unfold task_stack_check_observation; rewrite H; auto. Qed.

Lemma task_stack_check_observation_scan : forall sg priority output data snapshot count,
  task_stack_check_argument_error sg priority output = None ->
  task_stack_check_observation sg priority output data (Some (TaskStackCheckScan snapshot))
    (Some count) OS_ERR_NONE (task_stack_scan_data snapshot.(stackCheckSize) count).
Proof. intros; unfold task_stack_check_observation; rewrite H; exists count; auto. Qed.

(** C-level call observation for the statistics caller.  The C function
    returns an encoded [OSErrCode], while the abstract observation uses the
    typed error constructor.  Keeping the decoding and the output-data
    relation here gives the caller one canonical post relation; it does not
    grant stack ownership or assert that the priority-table lookup remains
    stable after the call. *)
Definition task_stack_check_call_observation
  (sg : StableGlobVars) (priority output error : Z)
  (initial_data final_data : TaskStackCheckData) : Prop :=
  exists typed_error,
    decode_os_err_code error = Some typed_error /\
    exists decision count,
      task_stack_check_observation sg priority output initial_data
        decision count typed_error final_data.

Lemma task_stack_check_call_observation_error_code : forall sg priority output error
    initial_data final_data typed_error decision count,
  decode_os_err_code error = Some typed_error ->
  task_stack_check_observation sg priority output initial_data
    decision count typed_error final_data ->
  task_stack_check_call_observation sg priority output error initial_data final_data.
Proof.
  intros sg priority output error initial_data final_data typed_error decision count
    Hdecode Hobs.
  exists typed_error; split; [exact Hdecode|].
  exists decision, count; exact Hobs.
Qed.

Lemma task_stack_check_call_observation_success : forall sg priority output error
    initial_data final_data snapshot count,
  decode_os_err_code error = Some OS_ERR_NONE ->
  task_stack_check_observation sg priority output initial_data
    (Some (TaskStackCheckScan snapshot)) (Some count) OS_ERR_NONE final_data ->
  task_stack_check_call_observation sg priority output error initial_data final_data.
Proof.
  intros; eapply task_stack_check_call_observation_error_code with
    (typed_error := OS_ERR_NONE)
    (decision := Some (TaskStackCheckScan snapshot)) (count := Some count);
    eauto.
Qed.

Definition task_stack_check_write_free (data : TaskStackCheckData) (count : nat)
  : TaskStackCheckData :=
  {| stackCheckFree := kernel_u32 (Z.of_nat count); stackCheckUsed := data.(stackCheckUsed) |}.
Definition task_stack_check_write_used (data : TaskStackCheckData) (size : Z) (count : nat)
  : TaskStackCheckData :=
  {| stackCheckFree := data.(stackCheckFree);
     stackCheckUsed := kernel_u32 (size - kernel_u32 (Z.of_nat count)) |}.

Lemma task_stack_check_success_output_order : forall data size count,
  task_stack_check_write_used (task_stack_check_write_free data count) size count =
  task_stack_scan_data size count.
Proof. reflexivity. Qed.

(** Read localization uses the EXISTING stack representation.  No own
    stack array, mutable copy or artificial byte frame is introduced. *)
Lemma task_stack_scan_split_initialized_cell : forall region words index value,
  0 <= index < region.(stackRegionWords) -> Znth index words None = Some value ->
  task_stack_storage region words |--
  (region.(stackRegionBase) + index * sizeof(UINT)) # UInt |-> value **
  UIntArray.mixed_missing_i region.(stackRegionBase) index 0 region.(stackRegionWords) words.
Proof.
  intros; eapply derivable1_trans; [apply task_stack_storage_split_cell; exact H|].
  rewrite H0; reflexivity.
Qed.

Lemma task_stack_scan_merge_read_cell : forall region words index value,
  0 <= index < region.(stackRegionWords) -> Znth index words None = Some value ->
  (region.(stackRegionBase) + index * sizeof(UINT)) # UInt |-> value **
  UIntArray.mixed_missing_i region.(stackRegionBase) index 0 region.(stackRegionWords) words |--
  task_stack_storage region words.
Proof.
  intros.
  change (UIntArray.mixedstoreA region.(stackRegionBase) index (Some value) **
    UIntArray.mixed_missing_i region.(stackRegionBase) index 0 region.(stackRegionWords) words |--
    task_stack_storage region words).
  rewrite <- H0.
  apply task_stack_storage_merge_cell; exact H.
Qed.

Lemma task_stack_scan_first_stop_in_owned_extent : forall region words count stop,
  Zlength words = region.(stackRegionWords) ->
  task_stack_scan_prefix words count stop ->
  0 <= Z.of_nat count < region.(stackRegionWords).
Proof.
  intros region words count stop Hlength [_ [suffix Hwords]].
  rewrite Hwords, Zlength_correct, length_app, repeat_length in Hlength; simpl in Hlength; lia.
Qed.

Lemma task_stack_scan_split_first_stop : forall region words count stop,
  Zlength words = region.(stackRegionWords) ->
  task_stack_scan_prefix words count stop ->
  task_stack_storage region words |--
  (region.(stackRegionBase) + Z.of_nat count * sizeof(UINT)) # UInt |-> stop **
  UIntArray.mixed_missing_i region.(stackRegionBase) (Z.of_nat count) 0
    region.(stackRegionWords) words.
Proof.
  intros; apply task_stack_scan_split_initialized_cell.
  - eapply task_stack_scan_first_stop_in_owned_extent; eauto.
  - apply task_stack_scan_prefix_has_initialized_stop; exact H0.
Qed.

(** OS_TaskStatStkChk's lookup is AFTER the check has returned.  It does
    not recheck generation or the stack-check option.  In the selected
    profile cfgTaskProfile=false, it still performs the pointer lookup and
    tests, but performs neither profiling store.  These observations do not
    touch the five Statistics-owned cells in statistics.v. *)
Definition task_stat_stack_relookup (priority : Priority) (error : OSErrCode)
  (tasks : Glob_TaskAbstractState) : option PrioTblEntry :=
  match error with OS_ERR_NONE => Some (tasks.(prioTbl) priority) | _ => None end.

Record TaskStackProfileWrite : Type := {
  stackProfileSlot : TaskID;
  stackProfileGeneration : nat;
  stackProfileBase : addr;
  stackProfileUsed : Z
}.

(** The full-profile task update used by the two concrete stores in
    [OS_TaskStatStkChk].  It is the existing complete task setter: the
    profiling fields are changed in the image, while identity, wait state,
    scheduler links and all other TCB fields remain those of [old]. *)
Definition task_stat_stack_profile_updated_task
  (old : TaskAbstractState) (data : TaskStackCheckData) : TaskAbstractState :=
  task_set_profile old old.(tcbCtxSwCtr) old.(tcbCyclesTot) old.(tcbCyclesStart)
    (old.(tcbStkBottom) + old.(tcbStkSize) * sizeof(UINT))
    data.(stackCheckUsed).

(** Entry-side spatial bridge for the two profiling cells.  The caller must
    provide the live TCB lookup; this lemma does not manufacture an object
    from a priority-table entry. *)
Lemma task_stat_stack_profile_storage_split : forall sg st tid old,
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  st.(inUsedTaskStates) tid = Some old ->
  task_public_storage sg st |--
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg tid) TCBStkBase
      (task_layout_image sg old TCBStkBase) **
    tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
      (task_slot_addr sg tid) TCBStkUsed
      (task_layout_image sg old TCBStkUsed) **
    task_public_storage_without_two_fields sg st tid old TCBStkBase TCBStkUsed.
Proof.
  intros sg st tid old Hprofile Hlookup.
  apply task_public_storage_split_two_fields.
  - discriminate.
  - exact Hlookup.
  - rewrite Hprofile; apply tcb_configured_profile_field_in; simpl; tauto.
  - rewrite Hprofile; apply tcb_configured_profile_field_in; simpl; tauto.
Qed.

(** Exit-side spatial bridge for the two source stores.  The image equation
    is proved by the complete setter rather than by a record containing only
    [StkBase] and [StkUsed]. *)
Lemma task_stat_stack_profile_storage_merge : forall sg st tid old data,
  sg.(osKernelConfig).(cfgTaskProfile) = true ->
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) TCBStkBase
    (Some (old.(tcbStkBottom) + old.(tcbStkSize) * sizeof(UINT))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled)
    (task_slot_addr sg tid) TCBStkUsed (Some data.(stackCheckUsed)) **
  task_public_storage_without_two_fields sg st tid old TCBStkBase TCBStkUsed |--
  task_public_storage sg
    (glob_task_set_usedtask st tid
      (task_stat_stack_profile_updated_task old data)).
Proof.
  intros sg st tid old data Hprofile.
  unfold task_stat_stack_profile_updated_task.
  apply task_public_storage_merge_updated_two_fields.
  - discriminate.
  - rewrite Hprofile; apply tcb_configured_profile_field_in; simpl; tauto.
  - rewrite Hprofile; apply tcb_configured_profile_field_in; simpl; tauto.
  - apply task_set_profile_stack_fields_layout_image_eq.
Qed.

(** A literal write observation, not an additional task-state field.  The
    profile-enabled representation/source client must supply these two
    optional C fields and their write resources before using this effect. *)
Definition task_stat_stack_profile_effect (profile_enabled : bool) (priority : Priority)
  (error : OSErrCode) (data : TaskStackCheckData) (tasks : Glob_TaskAbstractState)
  (effect : option TaskStackProfileWrite) : Prop :=
  match task_stat_stack_relookup priority error tasks with
  | None | Some PTFree | Some PTReserved => effect = None
  | Some (PTTask slot) =>
      if profile_enabled then exists node,
        tasks.(inUsedTaskStates) slot = Some node /\
        effect = Some {| stackProfileSlot := slot;
          stackProfileGeneration := node.(taskGeneration);
          stackProfileBase := node.(tcbStkBottom) +
            node.(tcbStkSize) * sizeof(UINT);
          stackProfileUsed := data.(stackCheckUsed) |}
      else effect = None
  end.

Lemma task_stat_stack_profile_disabled : forall priority error data tasks,
  task_stat_stack_profile_effect false priority error data tasks None.
Proof.
  intros; unfold task_stat_stack_profile_effect, task_stat_stack_relookup.
  destruct error; try reflexivity; destruct (prioTbl tasks priority); reflexivity.
Qed.

Lemma task_stat_stack_profile_effect_current_lookup : forall priority data tasks slot node,
  tasks.(prioTbl) priority = PTTask slot -> tasks.(inUsedTaskStates) slot = Some node ->
  task_stat_stack_profile_effect true priority OS_ERR_NONE data tasks
    (Some {| stackProfileSlot := slot; stackProfileGeneration := node.(taskGeneration);
      stackProfileBase := node.(tcbStkBottom) +
        node.(tcbStkSize) * sizeof(UINT);
      stackProfileUsed := data.(stackCheckUsed) |}).
Proof.
  intros; unfold task_stat_stack_profile_effect, task_stat_stack_relookup; rewrite H.
  exists node; auto.
Qed.

(** No equality to the scanned task is asserted above.  Only the NEW lookup
    determines the destination; the old result determines the assigned Used.
    The loop visits the inclusive [0, OS_TASK_IDLE_PRIO] range.  Its priority
    variable is INT8U, so a terminating full traversal requires idle<255,
    as in the current profile (63); this is not a new loop guard. *)
Definition task_stat_stack_priorities (idle : Z) : list Z :=
  map Z.of_nat (seq O (Z.to_nat (idle + 1))).

Lemma task_stat_stack_next_priority_no_wrap : forall priority idle,
  0 <= priority <= idle -> idle < 255 -> kernel_u8 (priority + 1) = priority + 1.
Proof. intros; apply kernel_u8_identity; lia. Qed.

Lemma task_stat_stack_last_priority_exits : forall idle,
  0 <= idle < 255 -> idle < kernel_u8 (idle + 1).
Proof. intros; rewrite kernel_u8_identity by lia; lia. Qed.
