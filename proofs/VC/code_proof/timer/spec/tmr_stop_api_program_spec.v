Require Export Ucos2Verify.lib.timer.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_api_program_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_api_program_spec.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.

Import Monad MonadNotation.
Local Open Scope Z_scope.

(** Source-program candidate for the pinned OSTmrStop body, with trace and
    safety-critical extensions disabled by its existing configuration.

    This file does not establish a C callback capability or a C/heap
    correspondence.  The effects below are explicit parameters that the
    actual call/resource bridge must instantiate and prove.  In particular
    no law says that a callback keeps the stopped timer alive or stopped.

    [error] represents the one actual *perr byte.  Application is its
    remaining client state; an argument equal to perr refers to that SAME
    byte, not to a second separately owned cell.  The source bridge must
    bind this representation to the actual heap, including aliasing.  This
    candidate uses the existing domain where that output byte is disjoint
    from the kernel representation: a write to it does not modify a timer
    field.  It does not silently claim the kernel-field/output overlap case.

    Raw type/state observations are functions of the current logical
    state.  State is read AFTER Lock.  Raw STOPPED, COMPLETED, UNUSED and
    invalid-state paths are retained.  A path reaching Unlink still needs
    its actual pool-address binding and verified Unlink resources; no raw
    byte with value RUNNING manufactures those resources. *)

Record TmrStopState (Application : Type) : Type := {
  tmr_stop_kernel : UCOS2_Verify_State;
  tmr_stop_error : Z;
  tmr_stop_application : Application
}.

Arguments tmr_stop_kernel {Application} _.
Arguments tmr_stop_error {Application} _.
Arguments tmr_stop_application {Application} _.

Record TmrStopReturn : Type := {
  tmr_stop_return_value : Z;
  tmr_stop_return_error : Z;
  tmr_stop_return_context : OsSchedCallContext
}.

Definition tmr_stop_output := (Z * Z)%type.
Definition tmr_stop_return_output (returned : TmrStopReturn) : tmr_stop_output :=
  (returned.(tmr_stop_return_value), returned.(tmr_stop_return_error)).

(** These relations describe actual application observations across the
    named call.  Their kernel projection is checked separately against
    the existing kernel source relation in [*_program] below.  They may
    describe a private frame or a proved shared-cell return protocol.
    Neither field is assumed to be universally true or state preserving. *)
Record TmrStopEffects (Application : Type) : Type := {
  tmr_stop_lock_application : OsSchedCallContext ->
    TmrStopState Application -> TmrStopState Application -> Prop;
  tmr_stop_unlock_application : OsSchedCallContext ->
    TmrStopState Application -> OsSchedCallContext ->
    TmrStopState Application -> Prop;
  tmr_stop_callback : Z -> Z -> Z -> OsSchedCallContext ->
    program (TmrStopState Application) OsSchedCallContext
}.

Arguments tmr_stop_lock_application {Application} _ _ _ _.
Arguments tmr_stop_unlock_application {Application} _ _ _ _ _.
Arguments tmr_stop_callback {Application} _ _ _ _ _.

Definition tmr_stop_set_error {Application} (error : Z)
  (before : TmrStopState Application) : TmrStopState Application :=
  {| tmr_stop_kernel := before.(tmr_stop_kernel);
     tmr_stop_error := error;
     tmr_stop_application := before.(tmr_stop_application) |}.

Definition tmr_stop_set_kernel {Application} (kernel : UCOS2_Verify_State)
  (before : TmrStopState Application) : TmrStopState Application :=
  {| tmr_stop_kernel := kernel;
     tmr_stop_error := before.(tmr_stop_error);
     tmr_stop_application := before.(tmr_stop_application) |}.

Definition tmr_stop_store_error_program {Application} (error : Z)
  : program (TmrStopState Application) unit :=
  fun before result after => result = tt /\ after = tmr_stop_set_error error before.

Definition tmr_stop_finish_program {Application} (value : Z)
  (context : OsSchedCallContext) : program (TmrStopState Application) TmrStopReturn :=
  get' (fun current =>
    {| tmr_stop_return_value := value;
       tmr_stop_return_error := current.(tmr_stop_error);
       tmr_stop_return_context := context |}).

Definition tmr_stop_write_return_program {Application} (value error : Z)
  (context : OsSchedCallContext) : program (TmrStopState Application) TmrStopReturn :=
  bind (tmr_stop_store_error_program error)
    (fun _ => tmr_stop_finish_program value context).

Definition tmr_stop_nonrunning_output (status : Z) : tmr_stop_output :=
  if orb (Z.eqb status 1) (Z.eqb status 2) then
    (1, encode_os_err_code OS_ERR_TMR_STOPPED)
  else if Z.eqb status 0 then
    (0, encode_os_err_code OS_ERR_TMR_INACTIVE)
  else (0, encode_os_err_code OS_ERR_TMR_INVALID_STATE).

Section StopSourceProgram.

Context {Application : Type}.
Context (external : OsSchedExternalResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (effects : TmrStopEffects Application).
Context (pooled : bool) (pointer index opt argument : Z)
  (raw_type raw_state : TmrStopState Application -> Z).

Definition tmr_stop_image_field_program (field : TimerImage -> Z)
  : program (TmrStopState Application) Z :=
  fun before value after => after = before /\
    exists image, before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image /\
      value = field image.

Definition tmr_stop_type_program : program (TmrStopState Application) Z :=
  if pooled then tmr_stop_image_field_program timerImageType
  else get' raw_type.

Definition tmr_stop_state_program : program (TmrStopState Application) Z :=
  if pooled then tmr_stop_image_field_program timerImageState
  else get' raw_state.

Definition tmr_stop_lock_program (context : OsSchedCallContext)
  : program (TmrStopState Application) unit :=
  fun before result after =>
    os_sched_lock_program critical sg context.(os_sched_call_invocation)
      before.(tmr_stop_kernel) result after.(tmr_stop_kernel) /\
    tmr_stop_lock_application effects context before after.

Definition tmr_stop_unlock_program (context : OsSchedCallContext)
  : program (TmrStopState Application) OsSchedCallContext :=
  fun before returned after =>
    os_sched_unlock_call_relation external critical sg context
      before.(tmr_stop_kernel) returned after.(tmr_stop_kernel) /\
    tmr_stop_unlock_application effects context before returned after.

Definition tmr_stop_unlink_program : program (TmrStopState Application) unit :=
  fun before result after => result = tt /\ exists timers,
    timer_unlink sg before.(tmr_stop_kernel).(TimerState) index = Some timers /\
    after = tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before.

(** This is entered AFTER Unlink and the actual *perr=0 store.
    NONE/default perform no callback-field reads.  The stored argument is
    read only in the non-NULL CALLBACK arm; CALLBACK_ARG uses the API arg. *)
Definition tmr_stop_select_callback_program
  : program (TmrStopState Application) (option (addr * addr * addr)) :=
  if Z.eqb opt 0 then ret None else
  if orb (Z.eqb opt 3) (Z.eqb opt 4) then
    bind (tmr_stop_image_field_program timerImageCallback) (fun fn =>
      if Z.eqb fn 0 then
        bind (tmr_stop_store_error_program (encode_os_err_code OS_ERR_TMR_NO_CALLBACK))
          (fun _ => ret None)
      else if Z.eqb opt 3 then
        bind (tmr_stop_image_field_program timerImageArg)
          (fun stored => ret (Some (fn, pointer, stored)))
      else ret (Some (fn, pointer, argument)))
  else bind (tmr_stop_store_error_program (encode_os_err_code OS_ERR_TMR_INVALID_OPT))
    (fun _ => ret None).

Definition tmr_stop_optional_callback_program
  (request : option (addr * addr * addr)) (context : OsSchedCallContext)
  : program (TmrStopState Application) OsSchedCallContext :=
  match request with
  | None => ret context
  | Some (fn, self, arg) => tmr_stop_callback effects fn self arg context
  end.

Definition tmr_stop_running_program (context : OsSchedCallContext)
  : program (TmrStopState Application) TmrStopReturn :=
  bind tmr_stop_unlink_program (fun _ =>
  bind (tmr_stop_store_error_program (encode_os_err_code OS_ERR_NONE)) (fun _ =>
  bind tmr_stop_select_callback_program (fun request =>
  bind (tmr_stop_optional_callback_program request context) (fun callback_returned =>
  bind (tmr_stop_unlock_program callback_returned) (fun returned =>
    tmr_stop_finish_program 1 returned))))).

(** Unlike RUNNING, these source branches overwrite *perr AFTER Unlock. *)
Definition tmr_stop_nonrunning_program (status : Z) (context : OsSchedCallContext)
  : program (TmrStopState Application) TmrStopReturn :=
  let '(ret_value, error) := tmr_stop_nonrunning_output status in
  bind (tmr_stop_unlock_program context) (fun returned =>
    tmr_stop_write_return_program ret_value error returned).

Definition tmr_stop_locked_program (context : OsSchedCallContext)
  : program (TmrStopState Application) TmrStopReturn :=
  bind tmr_stop_state_program (fun status =>
    if Z.eqb status 3 then tmr_stop_running_program context
    else tmr_stop_nonrunning_program status context).

Definition tmr_stop_source_program (context : OsSchedCallContext)
  : program (TmrStopState Application) TmrStopReturn :=
  if Z.eqb pointer 0 then
    tmr_stop_write_return_program 0 (encode_os_err_code OS_ERR_TMR_INVALID) context
  else bind tmr_stop_type_program (fun ty =>
    if Z.eqb ty 100 then
      bind (get' (fun current => os_sched_lock_ints current.(tmr_stop_kernel))) (fun ints =>
        if Z_gt_dec ints 0 then
          tmr_stop_write_return_program 0 (encode_os_err_code OS_ERR_TMR_ISR) context
        else bind (tmr_stop_lock_program context) (fun _ => tmr_stop_locked_program context))
    else tmr_stop_write_return_program 0 (encode_os_err_code OS_ERR_TMR_INVALID_TYPE) context).

(** The public observation is exactly the C Boolean and final *perr byte.
    The source relation retains the same returned context for the spatial
    postcondition; the public result does not invent a C context return. *)
Definition tmr_stop_api_program (context : OsSchedCallContext)
  : program (TmrStopState Application) tmr_stop_output :=
  bind (tmr_stop_source_program context)
    (fun returned => ret (tmr_stop_return_output returned)).

Definition tmr_stop_call_result (context : OsSchedCallContext)
  (before : TmrStopState Application) (returned : OsSchedCallContext)
  (output : tmr_stop_output) (after : TmrStopState Application) : Prop :=
  tmr_stop_source_program context before
    {| tmr_stop_return_value := fst output;
       tmr_stop_return_error := snd output;
       tmr_stop_return_context := returned |} after.

Definition tmr_stop_api_pre (context : OsSchedCallContext)
  (before : TmrStopState Application)
  (X : tmr_stop_output -> TmrStopState Application -> Prop) : Prop :=
  safeExec (eq before) (tmr_stop_api_program context) X.

Definition tmr_stop_api_post (context : OsSchedCallContext)
  (before : TmrStopState Application) (returned : OsSchedCallContext)
  (output : tmr_stop_output) (after : TmrStopState Application)
  (X : tmr_stop_output -> TmrStopState Application -> Prop) : Prop :=
  tmr_stop_call_result context before returned output after /\
  safeExec (eq after) (ret output) X.

Lemma tmr_stop_image_field_read : forall (before : TmrStopState Application) image field,
  before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image ->
  tmr_stop_image_field_program field before (field image) before.
Proof. intros before image field Himage; split; [reflexivity|eauto]. Qed.

Lemma tmr_stop_unlink_step : forall (before : TmrStopState Application) timers,
  timer_unlink sg before.(tmr_stop_kernel).(TimerState) index = Some timers ->
  tmr_stop_unlink_program before tt
    (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before).
Proof.
  intros before timers Hunlink; split; [reflexivity|].
  exists timers; split; [exact Hunlink|reflexivity].
Qed.

Lemma tmr_stop_write_return_step : forall (before : TmrStopState Application) value error context,
  tmr_stop_write_return_program value error context before
    {| tmr_stop_return_value := value; tmr_stop_return_error := error;
       tmr_stop_return_context := context |}
    (tmr_stop_set_error error before).
Proof.
  intros; unfold tmr_stop_write_return_program.
  exists tt, (tmr_stop_set_error error before); split.
  - split; reflexivity.
  - split; reflexivity.
Qed.

Lemma tmr_stop_select_none : forall (before : TmrStopState Application),
  opt = 0 -> tmr_stop_select_callback_program before None before.
Proof.
  intros before Hoption; unfold tmr_stop_select_callback_program.
  rewrite Hoption; split; reflexivity.
Qed.

Lemma tmr_stop_select_invalid_option : forall (before : TmrStopState Application),
  opt <> 0 -> opt <> 3 -> opt <> 4 ->
  tmr_stop_select_callback_program before None
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_INVALID_OPT) before).
Proof.
  intros before Hzero Hthree Hfour; unfold tmr_stop_select_callback_program.
  rewrite (proj2 (Z.eqb_neq opt 0) Hzero),
    (proj2 (Z.eqb_neq opt 3) Hthree), (proj2 (Z.eqb_neq opt 4) Hfour).
  exists tt, (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_INVALID_OPT) before).
  split; split; reflexivity.
Qed.

Lemma tmr_stop_select_null_callback : forall (before observed : TmrStopState Application),
  (opt = 3 \/ opt = 4) ->
  tmr_stop_image_field_program timerImageCallback before 0 observed ->
  tmr_stop_select_callback_program before None
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_NO_CALLBACK) observed).
Proof.
  intros before observed Hoption Hread; unfold tmr_stop_select_callback_program.
  assert (Hzero : Z.eqb opt 0 = false).
  { apply Z.eqb_neq; destruct Hoption; lia. }
  assert (Hcallback : orb (Z.eqb opt 3) (Z.eqb opt 4) = true).
  { destruct Hoption as [-> | ->]; reflexivity. }
  rewrite Hzero, Hcallback.
  exists 0, observed; split; [exact Hread|].
  exists tt, (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_NO_CALLBACK) observed).
  split; split; reflexivity.
Qed.

Lemma tmr_stop_select_stored_argument : forall (before : TmrStopState Application) fn
  (observed : TmrStopState Application) stored (after : TmrStopState Application),
  opt = 3 -> fn <> 0 ->
  tmr_stop_image_field_program timerImageCallback before fn observed ->
  tmr_stop_image_field_program timerImageArg observed stored after ->
  tmr_stop_select_callback_program before (Some (fn, pointer, stored)) after.
Proof.
  intros before fn observed stored after Hoption Hfn Hcallback Hargument.
  unfold tmr_stop_select_callback_program; rewrite Hoption.
  exists fn, observed; split; [exact Hcallback|].
  rewrite (proj2 (Z.eqb_neq fn 0) Hfn).
  exists stored, after; split; [exact Hargument|split; reflexivity].
Qed.

Lemma tmr_stop_select_api_argument : forall (before : TmrStopState Application) fn
  (observed : TmrStopState Application),
  opt = 4 -> fn <> 0 ->
  tmr_stop_image_field_program timerImageCallback before fn observed ->
  tmr_stop_select_callback_program before (Some (fn, pointer, argument)) observed.
Proof.
  intros before fn observed Hoption Hfn Hcallback.
  unfold tmr_stop_select_callback_program; rewrite Hoption.
  exists fn, observed; split; [exact Hcallback|].
  rewrite (proj2 (Z.eqb_neq fn 0) Hfn); split; reflexivity.
Qed.

Lemma tmr_stop_optional_callback_none : forall context (before : TmrStopState Application),
  tmr_stop_optional_callback_program None context before context before.
Proof. intros; split; reflexivity. Qed.

Lemma tmr_stop_optional_callback_some : forall fn self arg context
  (before : TmrStopState Application) returned (after : TmrStopState Application),
  tmr_stop_callback effects fn self arg context before returned after ->
  tmr_stop_optional_callback_program (Some (fn, self, arg)) context before returned after.
Proof.
  intros fn self arg context before returned after Hcallback; exact Hcallback.
Qed.

Lemma tmr_stop_running_step : forall context (before stopped : TmrStopState Application)
  request (selected : TmrStopState Application) callback_returned
  (callback_after : TmrStopState Application) returned (after : TmrStopState Application),
  tmr_stop_unlink_program before tt stopped ->
  tmr_stop_select_callback_program
    (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped) request selected ->
  tmr_stop_optional_callback_program request context selected callback_returned callback_after ->
  tmr_stop_unlock_program callback_returned callback_after returned after ->
  tmr_stop_running_program context before
    {| tmr_stop_return_value := 1; tmr_stop_return_error := after.(tmr_stop_error);
       tmr_stop_return_context := returned |} after.
Proof.
  intros context before stopped request selected callback_returned callback_after returned after
    Hunlink Hselect Hcallback Hunlock.
  unfold tmr_stop_running_program.
  exists tt, stopped; split; [exact Hunlink|].
  exists tt, (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped); split.
  - split; reflexivity.
  - exists request, selected; split; [exact Hselect|].
    exists callback_returned, callback_after; split; [exact Hcallback|].
    exists returned, after; split; [exact Hunlock|split; reflexivity].
Qed.

Lemma tmr_stop_nonrunning_step : forall context status (before : TmrStopState Application)
  returned (unlocked : TmrStopState Application) value error,
  tmr_stop_nonrunning_output status = (value, error) ->
  tmr_stop_unlock_program context before returned unlocked ->
  tmr_stop_nonrunning_program status context before
    {| tmr_stop_return_value := value; tmr_stop_return_error := error;
       tmr_stop_return_context := returned |}
    (tmr_stop_set_error error unlocked).
Proof.
  intros context status before returned unlocked value error Houtput Hunlock.
  unfold tmr_stop_nonrunning_program; rewrite Houtput.
  exists returned, unlocked; split; [exact Hunlock|apply tmr_stop_write_return_step].
Qed.

Lemma tmr_stop_locked_running_step : forall context (before observed : TmrStopState Application)
  returned (after : TmrStopState Application),
  tmr_stop_state_program before 3 observed ->
  tmr_stop_running_program context observed returned after ->
  tmr_stop_locked_program context before returned after.
Proof.
  intros context before observed returned after Hstate Hrun.
  unfold tmr_stop_locked_program; exists 3, observed; split; [exact Hstate|exact Hrun].
Qed.

Lemma tmr_stop_locked_nonrunning_step : forall context (before : TmrStopState Application)
  status (observed : TmrStopState Application) returned (after : TmrStopState Application),
  status <> 3 -> tmr_stop_state_program before status observed ->
  tmr_stop_nonrunning_program status context observed returned after ->
  tmr_stop_locked_program context before returned after.
Proof.
  intros context before status observed returned after Hstatus Hstate Hrun.
  unfold tmr_stop_locked_program; exists status, observed; split; [exact Hstate|].
  rewrite (proj2 (Z.eqb_neq status 3) Hstatus); exact Hrun.
Qed.

Lemma tmr_stop_source_null_return : forall context (before : TmrStopState Application),
  pointer = 0 -> tmr_stop_source_program context before
    {| tmr_stop_return_value := 0;
       tmr_stop_return_error := encode_os_err_code OS_ERR_TMR_INVALID;
       tmr_stop_return_context := context |}
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_INVALID) before).
Proof.
  intros context before Hpointer; unfold tmr_stop_source_program.
  rewrite Hpointer; simpl; apply tmr_stop_write_return_step.
Qed.

Lemma tmr_stop_source_type_return : forall context (before : TmrStopState Application) ty
  (observed : TmrStopState Application),
  pointer <> 0 -> ty <> 100 -> tmr_stop_type_program before ty observed ->
  tmr_stop_source_program context before
    {| tmr_stop_return_value := 0;
       tmr_stop_return_error := encode_os_err_code OS_ERR_TMR_INVALID_TYPE;
       tmr_stop_return_context := context |}
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_INVALID_TYPE) observed).
Proof.
  intros context before ty observed Hpointer Htype Hread; unfold tmr_stop_source_program.
  rewrite (proj2 (Z.eqb_neq pointer 0) Hpointer).
  exists ty, observed; split; [exact Hread|].
  rewrite (proj2 (Z.eqb_neq ty 100) Htype); apply tmr_stop_write_return_step.
Qed.

Lemma tmr_stop_source_isr_return : forall context (before observed : TmrStopState Application),
  pointer <> 0 -> tmr_stop_type_program before 100 observed ->
  os_sched_lock_ints observed.(tmr_stop_kernel) > 0 ->
  tmr_stop_source_program context before
    {| tmr_stop_return_value := 0;
       tmr_stop_return_error := encode_os_err_code OS_ERR_TMR_ISR;
       tmr_stop_return_context := context |}
    (tmr_stop_set_error (encode_os_err_code OS_ERR_TMR_ISR) observed).
Proof.
  intros context before observed Hpointer Hread Hints; unfold tmr_stop_source_program.
  rewrite (proj2 (Z.eqb_neq pointer 0) Hpointer).
  exists 100, observed; split; [exact Hread|].
  exists (os_sched_lock_ints observed.(tmr_stop_kernel)), observed; split.
  - split; reflexivity.
  - destruct (Z_gt_dec (os_sched_lock_ints observed.(tmr_stop_kernel)) 0);
      [apply tmr_stop_write_return_step|lia].
Qed.

Lemma tmr_stop_source_locked_return : forall context
  (before observed locked : TmrStopState Application) returned (after : TmrStopState Application),
  pointer <> 0 -> tmr_stop_type_program before 100 observed ->
  os_sched_lock_ints observed.(tmr_stop_kernel) <= 0 ->
  tmr_stop_lock_program context observed tt locked ->
  tmr_stop_locked_program context locked returned after ->
  tmr_stop_source_program context before returned after.
Proof.
  intros context before observed locked returned after Hpointer Hread Hints Hlock Hbody.
  unfold tmr_stop_source_program; rewrite (proj2 (Z.eqb_neq pointer 0) Hpointer).
  exists 100, observed; split; [exact Hread|].
  exists (os_sched_lock_ints observed.(tmr_stop_kernel)), observed; split.
  - split; reflexivity.
  - destruct (Z_gt_dec (os_sched_lock_ints observed.(tmr_stop_kernel)) 0); [lia|].
    exists tt, locked; split; assumption.
Qed.

(** [timer_stop_dispatch] is used only at its real intermediate endpoint.
    The resulting err is NOT asserted to be the final API output. *)
Lemma tmr_stop_running_dispatch_model : forall (before : TmrStopState Application) image timers,
  before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image ->
  image.(timerImageState) = 3 ->
  timer_unlink sg before.(tmr_stop_kernel).(TimerState) index = Some timers ->
  timer_stop_dispatch sg before.(tmr_stop_kernel).(TimerState) index opt argument =
    let '(request, error) := timer_stop_request sg index image opt argument in
    Some (true, error, request, timers).
Proof. intros; eapply timer_stop_dispatch_running; eassumption. Qed.

Lemma tmr_stop_source_result_program : forall context (before : TmrStopState Application)
  returned (after : TmrStopState Application),
  tmr_stop_source_program context before returned after ->
  tmr_stop_api_program context before (tmr_stop_return_output returned) after.
Proof.
  intros context before returned after Hsource; unfold tmr_stop_api_program.
  exists returned, after; split; [exact Hsource|split; reflexivity].
Qed.

Lemma tmr_stop_call_result_program : forall context (before : TmrStopState Application)
  returned output (after : TmrStopState Application),
  tmr_stop_call_result context before returned output after ->
  tmr_stop_api_program context before output after.
Proof.
  intros context before returned [value error] after Hsource.
  exact (tmr_stop_source_result_program context before
    {| tmr_stop_return_value := value; tmr_stop_return_error := error;
       tmr_stop_return_context := returned |} after Hsource).
Qed.

(** All actual source-return branches above consume this same arbitrary X.
    None of the branch lemmas assumes callback termination or a fixed
    callback/output/scheduler poststate. *)
Lemma tmr_stop_call_safe_return : forall context (before : TmrStopState Application)
  returned output (after : TmrStopState Application) X,
  tmr_stop_api_pre context before X ->
  tmr_stop_call_result context before returned output after ->
  tmr_stop_api_post context before returned output after X.
Proof.
  intros context before returned output after X Hsafe Hsource; split; [exact Hsource|].
  unfold tmr_stop_api_pre, safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros actual final [Hactual Hfinal]; subst actual; subst final.
  apply (Hsafe output after); eapply tmr_stop_call_result_program; exact Hsource.
Qed.

End StopSourceProgram.

(** This local CPS rule is shared by the actual callback, Lock, Unlink,
    stores and Unlock cutpoints.  It advances X only with a supplied
    actual step; the C/resource bridge must produce that step. *)
Lemma tmr_stop_stage_continue : forall (Application Value Result : Type)
  (command : program (TmrStopState Application) Value)
  (next : Value -> program (TmrStopState Application) Result)
  before value after (X : Result -> TmrStopState Application -> Prop),
  command before value after ->
  safeExec (eq before) (bind command next) X ->
  safeExec (eq after) (next value) X.
Proof.
  intros Application Value Result command next before value after X Hstep Hsafe.
  unfold safeExec, safe, StateRelHoare.weakestpre in *.
  destruct Hsafe as [seen [Hseen Hsafe]]; subst seen.
  exists after; split; [reflexivity|].
  intros result final Hnext; apply (Hsafe result final).
  exists value, after; split; assumption.
Qed.

Lemma tmr_stop_nonrunning_output_stopped_completed : forall status,
  status = 1 \/ status = 2 ->
  tmr_stop_nonrunning_output status = (1, encode_os_err_code OS_ERR_TMR_STOPPED).
Proof. intros status [-> | ->]; reflexivity. Qed.

Lemma tmr_stop_nonrunning_output_unused :
  tmr_stop_nonrunning_output 0 = (0, encode_os_err_code OS_ERR_TMR_INACTIVE).
Proof. reflexivity. Qed.

Lemma tmr_stop_nonrunning_output_invalid : forall status,
  status <> 0 -> status <> 1 -> status <> 2 -> status <> 3 ->
  tmr_stop_nonrunning_output status = (0, encode_os_err_code OS_ERR_TMR_INVALID_STATE).
Proof.
  intros status Hzero Hone Htwo Hthree; unfold tmr_stop_nonrunning_output.
  rewrite (proj2 (Z.eqb_neq status 1) Hone), (proj2 (Z.eqb_neq status 2) Htwo).
  simpl; rewrite (proj2 (Z.eqb_neq status 0) Hzero); reflexivity.
Qed.
