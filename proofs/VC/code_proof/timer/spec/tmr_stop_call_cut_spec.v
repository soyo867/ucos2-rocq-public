Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_call_interface_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Coq.ZArith.ZArith Coq.Strings.String.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition tmr_stop_call_kernel_any (_ : UCOS2_Verify_State) : Prop := True.

Definition tmr_stop_call_stopped_status (status : Z) : Prop := status = 1 \/ status = 2.

(** QCP treats program as an abstract type constructor.  These Prop-valued
    views expose its actual relation without applying that abstract type
    as though it were an annotation-level function type. *)
Definition tmr_stop_call_lock_step {Application : Type} critical sg effects context
  (before after : TmrStopState Application) : Prop :=
  tmr_stop_lock_program critical sg effects context before tt after.

Definition tmr_stop_call_unlink_step {Application : Type} sg index
  (before after : TmrStopState Application) : Prop :=
  tmr_stop_unlink_program sg index before tt after.

Definition tmr_stop_call_unlock_step {Application : Type} external critical sg effects context
  (before : TmrStopState Application) returned (after : TmrStopState Application) : Prop :=
  tmr_stop_unlock_program external critical sg effects context before returned after.

(** Concrete annotation vocabulary.  The read residual is the separating
    implication back to the SAME owned state: a read must return exactly
    the borrowed typed cell.  The split VC still proves that this cell and
    residual can be obtained from the current representation.  No read,
    callback or source transition is assumed by naming a cutpoint. *)
Definition tmr_stop_call_read_cell (pointer : Z) (field : TmrStopField) (value : Z)
  : TmrStopRules.expr :=
  match field with
  | StopTypeField => TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrType") value
  | StopStateField => TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrState") value
  | StopCallbackField => TmrStopRules.store_ptr (tmr_unlink_timer_field pointer "OSTmrCallback") value
  | StopArgumentField => TmrStopRules.store_ptr (tmr_unlink_timer_field pointer "OSTmrCallbackArg") value
  end.

Definition tmr_stop_call_field_read {Application : Type} (pooled : bool) (index : Z)
  (raw_type raw_state : TmrStopState Application -> Z) (field : TmrStopField)
  (before : TmrStopState Application) (value : Z) : Prop :=
  match field with
  | StopTypeField => tmr_stop_type_program pooled index raw_type before value before
  | StopStateField => tmr_stop_state_program pooled index raw_state before value before
  | StopCallbackField => tmr_stop_image_field_program index timerImageCallback before value before
  | StopArgumentField => tmr_stop_image_field_program index timerImageArg before value before
  end.

Section StopCuts.
Context {Application : Type} (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (effects : TmrStopEffects Application) (mask perr : Z).

Definition tmr_stop_call_read_rest (initialized : bool) (context : OsSchedCallContext)
  (current : TmrStopState Application) (pointer : Z) (field : TmrStopField) (value : Z)
  : TmrStopRules.expr :=
  TmrStopRules.wand (tmr_stop_call_read_cell pointer field value)
    (if initialized then tmr_stop_owned AppRep external platform critical sg mask perr context current
     else tmr_stop_entry_owned AppRep external platform critical sg mask perr context current).

Definition tmr_stop_call_output_frame (context : OsSchedCallContext)
  (current : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (tmr_stop_context_rep external platform critical sg mask context current.(tmr_stop_kernel))
    (AppRep current.(tmr_stop_application)).

Definition tmr_stop_call_unlink_client_frame (context : OsSchedCallContext)
  (current : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.sepcon (tmr_stop_unlink_frame external platform sg mask context current)
    (tmr_stop_entry_client_rep AppRep perr current).

(** The stored-argument expression is evaluated in the original call
    statement.  Its readable cell remains exposed until argument evaluation;
    then the reversible residual supplies the same callback ownership.
    This is a precondition consequence of the full callback capability,
    not another assumed callee contract. *)
Definition tmr_stop_call_callback_argument_pre
  (domain : Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop)
  (fn self argument : Z) (context : OsSchedCallContext)
  (before : TmrStopState Application) (arguments : (Z * Z)%type) : TmrStopRules.expr :=
  TmrStopRules.andp (TmrStopRules.coq_prop (domain fn self argument context before))
    (TmrStopRules.andp (TmrStopRules.coq_prop (arguments = (self, argument)))
      (TmrStopRules.sepcon (tmr_stop_call_read_cell (fst arguments) StopArgumentField argument)
        (tmr_stop_call_read_rest true context before self StopArgumentField argument))).

Lemma tmr_stop_call_callback_argument_pre_owned : forall domain fn self argument
  context before arguments,
  TmrStopRules.derivable1
    (tmr_stop_call_callback_argument_pre domain fn self argument context before arguments)
    (tmr_stop_call_callback_instance_pre AppRep external platform critical sg mask perr
      domain fn self argument context before arguments).
Proof.
  intros domain fn self argument context before arguments heap
    [Hdomain [Hargs [field_heap [rest_heap [Hjoin [Hfield Hrest]]]]]].
  split; [exact Hdomain|]. split; [exact Hargs|].
  apply (Hrest field_heap heap).
  - exact (TmrStopRules.join_comm field_heap rest_heap heap Hjoin).
  - rewrite Hargs in Hfield. exact Hfield.
Qed.

Definition tmr_stop_call_callback_argument_specification
  (domain : Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop)
  (fn self argument : Z) : TmrStopCallback.Spec TmrStopCallback.timer_callback_signature :=
  fun body => @TmrStopRules.allp OsSchedCallContext (fun context =>
    @TmrStopRules.allp (TmrStopState Application) (fun before =>
      TmrStopCallback.HoareFun TmrStopCallback.timer_callback_signature
        (tmr_stop_call_callback_argument_pre domain fn self argument context before)
        (tmr_stop_callback_post AppRep external platform critical sg effects mask perr
          fn self argument context before) body)).

Lemma tmr_stop_call_callback_argument_consequence : forall domain fn self argument,
  TmrStopRules.derivable1
    (tmr_stop_call_callback_capability AppRep external platform critical sg effects mask perr
      domain fn self argument)
    (@TmrStopCallback.func_ptr_spec TmrStopCallback.timer_callback_signature fn
      (tmr_stop_call_callback_argument_specification domain fn self argument)).
Proof.
  intros domain fn self argument. apply TmrStopCallback.func_ptr_spec_mono.
  intros body heap Hfull context entry_state.
  eapply TmrStopCallback.HoareFun_conseq; [| |exact (Hfull context entry_state)].
  - intro arguments. apply tmr_stop_call_callback_argument_pre_owned.
  - intros arguments result current Hpost. exact Hpost.
Qed.

Context (pooled : bool) (pointer index opt argument : Z)
  (raw_type raw_state : TmrStopState Application -> Z).

Definition tmr_stop_call_source_facts (context : OsSchedCallContext)
  (before : TmrStopState Application)
  (X : tmr_stop_output -> TmrStopState Application -> Prop) : Prop :=
  tmr_stop_call_requirements external critical sg effects pooled pointer index opt argument
    raw_type raw_state context before /\
  tmr_stop_api_pre external critical sg effects pooled pointer index opt argument
    raw_type raw_state context before X.

Definition tmr_stop_call_running_prefix (context : OsSchedCallContext)
  (before : TmrStopState Application) (calling : OsSchedCallContext)
  (current : TmrStopState Application) : Prop :=
  exists state_read stopped request selected,
    tmr_stop_call_state_prefix critical sg effects pooled pointer index raw_type raw_state
      context before 3 state_read /\
    tmr_stop_unlink_program sg index state_read tt stopped /\
    tmr_stop_select_callback_program pointer index opt argument
      (tmr_stop_set_error (encode_os_err_code OS_ERR_NONE) stopped) request selected /\
    tmr_stop_optional_callback_program effects request context selected calling current.

Definition tmr_stop_call_running_ready (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  fun heap => exists calling current,
    tmr_stop_call_running_prefix context before calling current /\
    tmr_stop_unlock_ready external critical sg calling current /\
    tmr_stop_owned AppRep external platform critical sg mask perr calling current heap.
End StopCuts.
