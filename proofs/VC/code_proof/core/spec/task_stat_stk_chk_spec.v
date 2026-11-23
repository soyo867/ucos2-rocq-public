Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.task.spec.task_stk_chk_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.
Local Notation length := List.length.

(** Canonical frontend name for the uninitialized local OS_STK_DATA object.
    The selected original declaration has exactly its two UInt fields. *)
Definition UndefStructPredos_stk_data (output : addr) : Assertion :=
  task_stk_chk_output_undef output.

(** The selected helper has profiling disabled. Its only kernel effects are
    those of the actual OSTaskStkChk calls. The successful post-call table
    observation uses the returned state, never the acquired snapshot. *)
Definition task_stat_stk_chk_configuration (sg : StableGlobVars) : Prop :=
  task_stk_chk_configuration sg /\
  sg.(osKernelConfig).(cfgTaskProfile) = false.

Record TaskStatStkChkObservation : Type := {
  stat_stack_priority : Z;
  stat_stack_error : Z;
  stat_stack_data : option TaskStackCheckData;
  stat_stack_returned : UCOS2_Verify_State
}.

Definition TaskStatStkChkHistory := list TaskStatStkChkObservation.

Definition task_stat_stk_chk_table_observation (sg : StableGlobVars)
  (observation : TaskStatStkChkObservation) : option addr :=
  if Z.eqb observation.(stat_stack_error) 0
  then Some (task_stk_chk_table_pointer sg observation.(stat_stack_returned)
    observation.(stat_stack_priority))
  else None.

(** The callee's same-X interface is instantiated with its exact source
    program relation. This is consumed after every real call below; no
    termination or initialized-stack fact is extracted from safeExec. *)
Definition task_stat_stk_chk_observe_call critical sg invocation
  before caller priority output error data after : Prop :=
  task_stk_chk_program critical sg invocation caller priority output
    before (error, data) after.

Lemma task_stat_stk_chk_call_safe : forall critical sg invocation
  before caller priority output,
  task_stk_chk_safe critical sg invocation before caller priority output
    (task_stat_stk_chk_observe_call critical sg invocation before caller priority output).
Proof.
  intros; exists before; split; [reflexivity|].
  intros [error data] after Hstep; exact Hstep.
Qed.

Definition task_stat_stk_chk_call_result critical sg invocation mask
  before caller priority output error data after : Prop :=
  task_stk_chk_post critical sg invocation mask before caller priority output
    error data after
    (task_stat_stk_chk_observe_call critical sg invocation before caller priority output).

Lemma task_stat_stk_chk_call_result_source : forall critical sg invocation mask
  before caller priority output error data after,
  task_stat_stk_chk_call_result critical sg invocation mask before caller
    priority output error data after ->
  task_stk_chk_call_post critical sg invocation mask before caller
    priority output error data after /\
  task_stat_stk_chk_observe_call critical sg invocation before caller
    priority output error data after.
Proof.
  intros critical sg invocation mask before caller priority output error data after
    [Hpost [state [Heq Hsafe]]]; subst state.
  split; [exact Hpost|].
  apply (Hsafe (error, data) after); split; reflexivity.
Qed.

(** Ordered finite composition, with all actual errors and exact outputs.
    There is no success-only guard. The list is a call history, not a second
    implementation of the C scan or its profiling calculations. *)
Inductive task_stat_stk_chk_history (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask : Z) (caller : Assertion)
  (output : addr) (before : UCOS2_Verify_State)
  : TaskStatStkChkHistory -> UCOS2_Verify_State -> Prop :=
| task_stat_stk_chk_history_nil :
    task_stat_stk_chk_history critical sg invocation mask caller output before [] before
| task_stat_stk_chk_history_snoc : forall history current error data after,
    task_stat_stk_chk_history critical sg invocation mask caller output before history current ->
    task_stk_chk_call_post critical sg invocation mask current caller
      (Zlength history) output error data after ->
    task_stat_stk_chk_observe_call critical sg invocation current caller
      (Zlength history) output error data after ->
    UCOS2_state_inv sg after ->
    task_stat_stk_chk_history critical sg invocation mask caller output before
      (history ++ [{| stat_stack_priority := Zlength history;
                     stat_stack_error := error; stat_stack_data := data;
                     stat_stack_returned := after |}]) after.

Definition task_stat_stk_chk_prefix critical sg invocation mask caller output
  before index current history : Prop :=
  Zlength history = index /\
  task_stat_stk_chk_history critical sg invocation mask caller output before history current.

(** Ordinary client read-admission protocol at each actually reachable call.
    It quantifies the fresh local output address because C allocates it inside
    this helper. Its spatial views use raw kernel storage, caller and these
    same output fields. It neither supplies an additional whole stack nor
    requires every priority to denote a live task. OS_TaskStat's concrete
    caller/resource combination remains a separate consumer obligation. *)
Definition task_stat_stk_chk_protocol critical sg invocation mask caller before : Prop :=
  forall output history current,
    output <> 0 ->
    task_stat_stk_chk_history critical sg invocation mask caller output before history current ->
    0 <= Zlength history < 64 ->
    task_stk_chk_admission critical sg invocation current caller (Zlength history) output.

Definition task_stat_stk_chk_post critical sg invocation mask caller before after : Prop :=
  exists output history,
    output <> 0 /\
    task_stat_stk_chk_prefix critical sg invocation mask caller output before 64 after history.

Lemma task_stat_stk_chk_prefix_start : forall critical sg invocation mask caller output before,
  task_stat_stk_chk_prefix critical sg invocation mask caller output before 0 before [].
Proof. intros; split; [reflexivity|constructor]. Qed.

Lemma task_stat_stk_chk_prefix_append : forall critical sg invocation mask caller
  output before index current history error data after,
  task_stat_stk_chk_prefix critical sg invocation mask caller output before index current history ->
  task_stat_stk_chk_call_result critical sg invocation mask current caller index output error data after ->
  UCOS2_state_inv sg after ->
  task_stat_stk_chk_prefix critical sg invocation mask caller output before (index + 1) after
    (history ++ [{| stat_stack_priority := index; stat_stack_error := error;
                   stat_stack_data := data; stat_stack_returned := after |}]).
Proof.
  intros critical sg invocation mask caller output before index current history error data after
    [Hlength Hhistory] Hresult Hafter.
  pose proof (task_stat_stk_chk_call_result_source _ _ _ _ _ _ _ _ _ _ _ Hresult)
    as [Hpost Hsource].
  subst index; split.
  - rewrite Zlength_app; reflexivity.
  - econstructor; eauto.
Qed.

Lemma task_stat_stk_chk_protocol_call : forall critical sg invocation mask caller
  before output index current history,
  task_stat_stk_chk_protocol critical sg invocation mask caller before ->
  task_stat_stk_chk_prefix critical sg invocation mask caller output before index current history ->
  output <> 0 -> 0 <= index < 64 ->
  task_stk_chk_admission critical sg invocation current caller index output.
Proof. intros * Hprotocol [Hlength Hhistory] Houtput Hindex; subst index; eauto. Qed.

Lemma task_stat_stk_chk_history_priorities : forall critical sg invocation mask
  caller output before history after,
  task_stat_stk_chk_history critical sg invocation mask caller output before history after ->
  map stat_stack_priority history = map Z.of_nat (seq 0 (length history)).
Proof.
  intros * Hhistory; induction Hhistory.
  - reflexivity.
  - rewrite map_app, IHHhistory, app_length; simpl length.
    rewrite seq_app, map_app; simpl.
    rewrite Zlength_correct; reflexivity.
Qed.

Lemma task_stat_stk_chk_no_argument_error : forall sg priority output,
  task_stat_stk_chk_configuration sg -> 0 <= priority < 64 -> output <> 0 ->
  task_stack_check_argument_error sg priority output = None.
Proof.
  intros sg priority output [Hconfiguration _] Hpriority Houtput.
  apply task_stk_chk_valid_arguments_no_error__lookup_and_error_paths;
    [exact Hconfiguration|].
  unfold task_stk_chk_valid_arguments; intuition lia.
Qed.

Lemma task_stat_stk_chk_result_has_data : forall critical sg invocation mask
  before caller priority output error data after,
  task_stat_stk_chk_configuration sg -> 0 <= priority < 64 -> output <> 0 ->
  task_stat_stk_chk_call_result critical sg invocation mask before caller
    priority output error data after -> exists value, data = Some value.
Proof.
  intros * Hconfiguration Hpriority Houtput [Hpost _].
  unfold task_stk_chk_call_post in Hpost.
  rewrite (task_stat_stk_chk_no_argument_error _ _ _ Hconfiguration Hpriority Houtput) in Hpost.
  destruct Hpost as (entry & saved & selected & decision & Hacquire & Hcritical & Hrelease & Hdata).
  destruct decision as [error_code|snapshot].
  - destruct Hdata as [_ ->]; eauto.
  - destruct Hdata as (region & words & count & stop & residual & Hview & Herr & ->); eauto.
Qed.

Lemma task_stat_stk_chk_output_forget : forall output data,
  task_stack_check_data_rep output data |-- task_stk_chk_output_undef output.
Proof.
  intros; unfold task_stack_check_data_rep, task_stk_chk_output_undef.
  sep_apply_l_atomic (store_uint_undef_store_uint
    (&(output # "os_stk_data" ->ₛ "OSFree")) (stackCheckFree data)).
  sep_apply_l_atomic (store_uint_undef_store_uint
    (&(output # "os_stk_data" ->ₛ "OSUsed")) (stackCheckUsed data)).
  entailer!.
Qed.

(** Outside/raw is an equality of the same owned memory. It is not an
    environment transition or a permission to retain a second table owner. *)
Lemma task_stat_stk_chk_table_split : forall critical sg invocation state priority,
  UCOS2_state_inv sg state -> 0 <= priority < 64 ->
  critical_region_outside critical sg invocation state |--
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_stk_chk_table_pointer sg state priority ** task_stk_chk_table_frame sg state priority.
Proof.
  intros * Hstate Hpriority.
  rewrite (task_stk_chk_outside_raw critical sg invocation state).
  assert (Hinv : UCOS2_raw_rep sg state |-- UCOS2_inv sg state).
  { unfold UCOS2_inv; entailer!. }
  sep_apply_l_atomic Hinv.
  sep_apply_l_atomic (task_stk_chk_table_split sg state priority Hpriority); entailer!.
Qed.

Lemma task_stat_stk_chk_table_merge : forall critical sg invocation state priority,
  0 <= priority < 64 ->
  (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_stk_chk_table_pointer sg state priority ** task_stk_chk_table_frame sg state priority |--
  critical_region_outside critical sg invocation state.
Proof.
  intros * Hpriority.
  rewrite (task_stk_chk_outside_raw critical sg invocation state).
  unfold task_stk_chk_table_pointer, task_stk_chk_table_frame.
  rewrite UCOS2_raw_rep_priority_table_equiv.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg state.(TskState).(prioTbl) priority Hpriority).
  entailer!.
Qed.
