Require Export Ucos2Verify.VC.code.task.spec.task_stk_chk_continuation_spec.
Require Export Ucos2Verify.VC.code.core.spec.task_stat_stk_chk_spec.
Require Import Ucos2Verify.lib.error_codes.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Every completed call retains its returned context.  A successful call
    is followed by the real current-table read; an error skips that read.
    Neither a snapshot pointer nor a map-stability premise supplies it. *)
Record TaskStatStkChkContinuationObservation : Type := {
  stack_observed_priority : Z;
  stack_observed_error : Z;
  stack_observed_data : option TaskStackCheckData;
  stack_observed_caller : TaskSuspendCaller;
  stack_observed_state : UCOS2_Verify_State;
  stack_observed_table : option addr
}.

Definition TaskStatStkChkContinuationHistory :=
  list TaskStatStkChkContinuationObservation.

Definition task_stat_stk_chk_continuation_table_result sg priority error state observed : Prop :=
  observed = if Z.eqb error 0
    then Some (task_stk_chk_table_pointer sg state priority) else None.

Inductive task_stat_stk_chk_continuation_history environment critical saved_local sg mask
  (caller_frame : Assertion) output (original : TaskSuspendCaller) before :
    TaskStatStkChkContinuationHistory -> TaskSuspendCaller -> UCOS2_Verify_State -> Prop :=
| task_stat_stk_chk_continuation_history_nil :
    task_stat_stk_chk_continuation_history environment critical saved_local sg mask
      caller_frame output original before [] original before
| task_stat_stk_chk_continuation_history_snoc :
    forall history caller current error data returned after observed,
    task_stat_stk_chk_continuation_history environment critical saved_local sg mask
      caller_frame output original before history caller current ->
    task_stk_chk_continuation_program environment critical saved_local sg caller mask
      caller_frame (Zlength history) output current ((error, data), returned) after ->
    task_stat_stk_chk_continuation_table_result sg (Zlength history) error after observed ->
    task_stat_stk_chk_continuation_history environment critical saved_local sg mask
      caller_frame output original before
      (history ++ [{| stack_observed_priority := Zlength history;
                     stack_observed_error := error;
                     stack_observed_data := data;
                     stack_observed_caller := returned;
                     stack_observed_state := after;
                     stack_observed_table := observed |}]) returned after.

Definition task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
  caller_frame output original before index history caller current : Prop :=
  Zlength history = index /\
  task_stat_stk_chk_continuation_history environment critical saved_local sg mask
    caller_frame output original before history caller current.

Definition task_stat_stk_chk_continuation_protocol environment critical saved_local sg original
  mask caller_frame before : Prop :=
  forall output history caller current,
    output <> 0 ->
    task_stat_stk_chk_continuation_history environment critical saved_local sg mask
      caller_frame output original before history caller current ->
    0 <= Zlength history < 64 ->
    task_stk_chk_continuation_admission environment critical saved_local sg caller mask
      caller_frame (Zlength history) output current.

Definition task_stat_stk_chk_continuation_observe_call environment critical saved_local sg caller
  mask caller_frame priority output before error data after : Prop :=
  exists returned,
    task_stk_chk_continuation_program environment critical saved_local sg caller mask
      caller_frame priority output before ((error, data), returned) after.

Definition task_stat_stk_chk_continuation_call_result environment critical saved_local sg caller
  mask caller_frame priority output before error data returned after : Prop :=
  task_stk_chk_continuation_program environment critical saved_local sg caller mask
    caller_frame priority output before ((error, data), returned) after.

(** This is the finite ordered source-call history, including the conditional
    table observations. It specifies the helper's whole completed execution. *)
Definition task_stat_stk_chk_continuation_program environment critical saved_local sg original
  mask caller_frame : program UCOS2_Verify_State TaskSuspendCaller :=
  fun before caller current =>
    exists output history, output <> 0 /\
      task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
        caller_frame output original before 64 history caller current.

Definition task_stat_stk_chk_continuation_safe environment critical saved_local sg original
  mask caller_frame before (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (task_stat_stk_chk_continuation_program environment critical saved_local sg original
      mask caller_frame) (fun _ current => X tt current).

Definition task_stat_stk_chk_continuation_post environment critical saved_local sg original
  mask caller_frame before (X : unit -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX output history caller current,
    coq_prop (output <> 0 /\
      task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
        caller_frame output original before 64 history caller current /\ X tt current) &&
    (task_suspend_closed environment critical saved_local sg caller mask current ** caller_frame).

Lemma task_stat_stk_chk_continuation_call_safe :
  forall environment critical saved_local sg caller mask caller_frame priority output before,
  task_stk_chk_continuation_safe environment critical saved_local sg caller mask
    caller_frame priority output before
    (task_stat_stk_chk_continuation_observe_call environment critical saved_local sg caller
      mask caller_frame priority output before).
Proof.
  intros; exists before; split; [reflexivity|].
  intros [[error data] returned] after Hsource; exists returned; exact Hsource.
Qed.

Lemma task_stat_stk_chk_continuation_prefix_start :
  forall environment critical saved_local sg mask caller_frame output original before,
  task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
    caller_frame output original before 0 [] original before.
Proof. intros; split; [reflexivity|constructor]. Qed.

Lemma task_stat_stk_chk_continuation_prefix_append :
  forall environment critical saved_local sg mask caller_frame output original before
    index history caller current error data returned after observed,
  task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
    caller_frame output original before index history caller current ->
  task_stat_stk_chk_continuation_call_result environment critical saved_local sg caller mask
    caller_frame index output current error data returned after ->
  task_stat_stk_chk_continuation_table_result sg index error after observed ->
  task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
    caller_frame output original before (index + 1)
    (history ++ [{| stack_observed_priority := index;
                   stack_observed_error := error;
                   stack_observed_data := data;
                   stack_observed_caller := returned;
                   stack_observed_state := after;
                   stack_observed_table := observed |}]) returned after.
Proof.
  intros * [Hindex Hhistory] Hsource Htable; subst index.
  split; [rewrite Zlength_app; reflexivity|econstructor; eassumption].
Qed.

Lemma task_stat_stk_chk_continuation_protocol_call :
  forall environment critical saved_local sg mask caller_frame output original before
    index history caller current,
  task_stat_stk_chk_continuation_protocol environment critical saved_local sg original
    mask caller_frame before ->
  task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
    caller_frame output original before index history caller current ->
  output <> 0 -> 0 <= index < 64 ->
  task_stk_chk_continuation_admission environment critical saved_local sg caller mask
    caller_frame index output current.
Proof. intros * Hprotocol [Hindex Hhistory] Houtput Hindex_range; subst index; eauto. Qed.

Lemma task_stat_stk_chk_continuation_history_priorities :
  forall environment critical saved_local sg mask caller_frame output original before history caller current,
  task_stat_stk_chk_continuation_history environment critical saved_local sg mask
    caller_frame output original before history caller current ->
  map stack_observed_priority history = map Z.of_nat (seq 0 (List.length history)).
Proof.
  intros * Hhistory; induction Hhistory.
  - reflexivity.
  - rewrite map_app, IHHhistory, app_length; simpl List.length.
    rewrite seq_app, map_app; simpl.
    rewrite Zlength_correct; reflexivity.
Qed.

Lemma task_stat_stk_chk_continuation_history_table_results :
  forall environment critical saved_local sg mask caller_frame output original before history caller current,
  task_stat_stk_chk_continuation_history environment critical saved_local sg mask
    caller_frame output original before history caller current ->
  Forall (fun observation =>
    task_stat_stk_chk_continuation_table_result sg observation.(stack_observed_priority)
      observation.(stack_observed_error) observation.(stack_observed_state)
      observation.(stack_observed_table)) history.
Proof.
  intros * Hhistory; induction Hhistory; [constructor|].
  apply Forall_app; split; [exact IHHhistory|constructor; [assumption|constructor]].
Qed.

Lemma task_stat_stk_chk_continuation_result_has_data :
  forall environment critical saved_local sg caller mask caller_frame priority output before
    error data returned current,
  task_stat_stk_chk_configuration sg -> 0 <= priority < 64 -> output <> 0 ->
  task_stat_stk_chk_continuation_call_result environment critical saved_local sg caller mask
    caller_frame priority output before error data returned current ->
  exists value, data = Some value.
Proof.
  intros * Hconfiguration Hpriority Houtput Hsource.
  unfold task_stat_stk_chk_continuation_call_result, task_stk_chk_continuation_program in Hsource.
  rewrite (task_stat_stk_chk_no_argument_error _ _ _ Hconfiguration Hpriority Houtput) in Hsource.
  destruct Hsource as (zeroed & initial & [Hzero Hinitial] & Hsource); subst zeroed initial.
  destruct Hsource as ([active saved] & acquired & Hsave & Hsource).
  destruct Hsource as (decision & protected & Hlookup & Hsource).
  destruct Hsource as (restored & state & Hrestore & Hsource).
  destruct decision as [error_code|snapshot].
  - destruct Hsource as [Heq Hstate]; inversion Heq; subst; eauto.
  - destruct Hsource as (count & final & Hscan & Heq & Hstate).
    inversion Heq; subst; eauto.
Qed.


Lemma task_stat_stk_chk_continuation_error_in_range :
  forall environment critical saved_local sg caller mask caller_frame priority output before
    error data returned current,
  task_stat_stk_chk_continuation_call_result environment critical saved_local sg caller mask
    caller_frame priority output before error data returned current ->
  0 <= error < 256.
Proof.
  intros * Hsource.
  unfold task_stat_stk_chk_continuation_call_result, task_stk_chk_continuation_program in Hsource.
  destruct (task_stack_check_argument_error sg priority output) as [argument_error|].
  - destruct Hsource as [Heq Hstate]; inversion Heq; subst.
    apply encode_os_err_code_in_range.
  - destruct Hsource as (zeroed & initial & [Hzero Hinitial] & Hsource); subst zeroed initial.
    destruct Hsource as ([active saved] & acquired & Hsave & Hsource).
    destruct Hsource as (decision & protected & Hlookup & Hsource).
    destruct Hsource as (restored & state & Hrestore & Hsource).
    destruct decision as [error_code|snapshot].
    + destruct Hsource as [Heq Hstate]; inversion Heq; subst.
      apply encode_os_err_code_in_range.
    + destruct Hsource as (count & final & Hscan & Heq & Hstate).
      inversion Heq; subst; lia.
Qed.

Lemma task_stat_stk_chk_continuation_output_forget :
  forall environment critical saved_local sg caller mask caller_frame priority output before
    error data returned current,
  task_stat_stk_chk_configuration sg -> 0 <= priority < 64 -> output <> 0 ->
  task_stat_stk_chk_continuation_call_result environment critical saved_local sg caller mask
    caller_frame priority output before error data returned current ->
  task_stk_chk_output_post output data |-- task_stk_chk_output_undef output.
Proof.
  intros * Hconfiguration Hpriority Houtput Hsource.
  destruct (task_stat_stk_chk_continuation_result_has_data _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hconfiguration Hpriority Houtput Hsource) as [value ->].
  unfold task_stk_chk_output_post; apply task_stat_stk_chk_output_forget.
Qed.

Lemma task_stat_stk_chk_continuation_closed_inv :
  forall environment critical saved_local sg caller mask state,
  task_suspend_closed environment critical saved_local sg caller mask state |--
  coq_prop (UCOS2_state_inv sg state) &&
  task_suspend_closed environment critical saved_local sg caller mask state.
Proof.
  intros; rewrite time_dly_closed_inv_equiv; unfold UCOS2_inv; entailer!.
Qed.

Definition task_stat_stk_chk_continuation_table_frame environment saved_local sg caller mask state priority :=
  task_stk_chk_table_frame sg state priority **
  time_dly_outside_resources environment saved_local sg caller mask state.

Lemma task_stat_stk_chk_continuation_table_split :
  forall environment critical saved_local sg caller mask state priority,
  0 <= priority < 64 ->
  task_suspend_closed environment critical saved_local sg caller mask state |--
  coq_prop (UCOS2_state_inv sg state) &&
  ((sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_stk_chk_table_pointer sg state priority **
    task_stat_stk_chk_continuation_table_frame environment saved_local sg caller mask state priority).
Proof.
  intros * Hpriority; rewrite time_dly_closed_inv_equiv.
  unfold task_stat_stk_chk_continuation_table_frame.
  sep_apply_l_atomic (task_stk_chk_table_split sg state priority Hpriority); entailer!.
Qed.

Lemma task_stat_stk_chk_continuation_table_merge :
  forall environment critical saved_local sg caller mask state priority,
  0 <= priority < 64 ->
  coq_prop (UCOS2_state_inv sg state) &&
  ((sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_stk_chk_table_pointer sg state priority **
    task_stat_stk_chk_continuation_table_frame environment saved_local sg caller mask state priority) |--
  task_suspend_closed environment critical saved_local sg caller mask state.
Proof.
  intros * Hpriority; rewrite time_dly_closed_inv_equiv.
  unfold task_stat_stk_chk_continuation_table_frame; Intros.
  assert (Hmerge :
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
      task_stk_chk_table_pointer sg state priority ** task_stk_chk_table_frame sg state priority
      |-- UCOS2_inv sg state).
  { intros heap Hresources.
    apply (task_stk_chk_table_merge sg state priority Hpriority heap).
    split; assumption. }
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma task_stat_stk_chk_continuation_safe_result :
  forall environment critical saved_local sg original mask caller_frame before
    output history caller current X,
  task_stat_stk_chk_continuation_safe environment critical saved_local sg original
    mask caller_frame before X ->
  output <> 0 ->
  task_stat_stk_chk_continuation_prefix environment critical saved_local sg mask
    caller_frame output original before 64 history caller current ->
  X tt current.
Proof.
  intros * [start [Hstart Hsafe]] Houtput Hprefix; subst start.
  apply (Hsafe caller current); exists output, history; split; assumption.
Qed.
