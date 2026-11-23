Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import CNotation Mem SeparationLogic.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** These four choices select a proof view; they add no kernel state.
    All C addresses below use the existing alias-arrow interpretation.
    The layout proposition must be discharged by the selected C/ABI input,
    and is never inferred merely from numeric offsets or field spelling. *)
Inductive TmrStopField : Type :=
| StopTypeField | StopStateField | StopCallbackField | StopArgumentField.

Definition tmr_stop_field_name (field : TmrStopField) : string :=
  match field with
  | StopTypeField => "OSTmrType"
  | StopStateField => "OSTmrState"
  | StopCallbackField => "OSTmrCallback"
  | StopArgumentField => "OSTmrCallbackArg"
  end.

Definition tmr_stop_field_value (field : TmrStopField) (image : TimerImage) : Z :=
  match field with
  | StopTypeField => image.(timerImageType)
  | StopStateField => image.(timerImageState)
  | StopCallbackField => image.(timerImageCallback)
  | StopArgumentField => image.(timerImageArg)
  end.

Definition tmr_stop_fields_layout : Prop :=
  (forall p, tmr_unlink_timer_field p "OSTmrType" = p) /\
  (forall p, tmr_unlink_timer_field p "OSTmrState" = p + 37) /\
  (forall p, tmr_unlink_timer_field p "OSTmrCallback" = p + 4) /\
  (forall p, tmr_unlink_timer_field p "OSTmrCallbackArg" = p + 8).

Lemma tmr_stop_fields_layout_from_unlink :
  tmr_unlink_layout ->
  (forall p, tmr_unlink_timer_field p "OSTmrType" = p) ->
  (forall p, tmr_unlink_timer_field p "OSTmrCallback" = p + 4) ->
  (forall p, tmr_unlink_timer_field p "OSTmrCallbackArg" = p + 8) ->
  tmr_stop_fields_layout.
Proof.
  intros [_ [_ [_ [Hstate Hrest]]]] Htype Hcallback Hargument.
  repeat split; assumption.
Qed.

Module TmrStopOldFields.

Module Old := UCOS2_C_Rules.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

Definition field_cell (p : Z) (image : TimerImage) (field : TmrStopField) : Assertion :=
  match field with
  | StopTypeField | StopStateField =>
      tmr_unlink_timer_field p (tmr_stop_field_name field) # UChar |-> tmr_stop_field_value field image
  | StopCallbackField | StopArgumentField =>
      tmr_unlink_timer_field p (tmr_stop_field_name field) # Ptr |-> tmr_stop_field_value field image
  end.

Definition object_without_callback (c : KernelConfiguration) (p : Z)
  (image : TimerImage) : Assertion :=
  p # UChar |-> image.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 image.(timerImagePadding)) **
  (p + 8) # Ptr |-> image.(timerImageArg) **
  (p + 12) # Ptr |-> image.(timerImageNext) ** (p + 16) # Ptr |-> image.(timerImagePrev) **
  (p + 20) # UInt |-> image.(timerImageMatch) ** (p + 24) # UInt |-> image.(timerImageDelay) **
  (p + 28) # UInt |-> image.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> image.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> image.(timerImageOption) **
  (p + timer_option_offset c + 1) # UChar |-> image.(timerImageState) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 image.(timerImagePadding)).

Definition object_without_argument (c : KernelConfiguration) (p : Z)
  (image : TimerImage) : Assertion :=
  p # UChar |-> image.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 image.(timerImagePadding)) **
  (p + 4) # Ptr |-> image.(timerImageCallback) **
  (p + 12) # Ptr |-> image.(timerImageNext) ** (p + 16) # Ptr |-> image.(timerImagePrev) **
  (p + 20) # UInt |-> image.(timerImageMatch) ** (p + 24) # UInt |-> image.(timerImageDelay) **
  (p + 28) # UInt |-> image.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> image.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> image.(timerImageOption) **
  (p + timer_option_offset c + 1) # UChar |-> image.(timerImageState) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 image.(timerImagePadding)).

Definition object_without_field (c : KernelConfiguration) (p : Z)
  (image : TimerImage) (field : TmrStopField) : Assertion :=
  match field with
  | StopTypeField => timer_object_rep_without_type c p image
  | StopStateField => timer_object_rep_without_state c p image
  | StopCallbackField => object_without_callback c p image
  | StopArgumentField => object_without_argument c p image
  end.

Lemma object_rep_split_field : forall c p image field,
  tmr_stop_fields_layout -> c.(cfgTimerNames) = true ->
  timer_object_rep c p image |-- field_cell p image field ** object_without_field c p image field.
Proof.
  intros c p image field [Htype [Hstate [Hcallback Hargument]]] Hnames.
  destruct field; cbn [field_cell object_without_field tmr_stop_field_name tmr_stop_field_value].
  - rewrite Htype. apply timer_object_rep_split_type.
  - rewrite Hstate.
    replace (p + 37) with (p + timer_option_offset c + 1)
      by (unfold timer_option_offset; rewrite Hnames; lia).
    apply timer_object_rep_split_state.
  - rewrite Hcallback; unfold timer_object_rep, object_without_callback; entailer!.
  - rewrite Hargument; unfold timer_object_rep, object_without_argument; entailer!.
Qed.

Lemma object_rep_merge_field : forall c p image field,
  tmr_stop_fields_layout -> c.(cfgTimerNames) = true ->
  field_cell p image field ** object_without_field c p image field |-- timer_object_rep c p image.
Proof.
  intros c p image field [Htype [Hstate [Hcallback Hargument]]] Hnames.
  destruct field; cbn [field_cell object_without_field tmr_stop_field_name tmr_stop_field_value].
  - rewrite Htype. apply timer_object_rep_merge_type.
  - rewrite Hstate.
    replace (p + 37) with (p + timer_option_offset c + 1)
      by (unfold timer_option_offset; rewrite Hnames; lia).
    unfold timer_object_rep, timer_object_rep_without_state; entailer!.
  - rewrite Hcallback; unfold timer_object_rep, object_without_callback; entailer!.
  - rewrite Hargument; unfold timer_object_rep, object_without_argument; entailer!.
Qed.

Definition pool_without_field (sg : StableGlobVars) (timers : GlobTimerState)
  (index : TimerID) (image : TimerImage) (field : TmrStopField) : Assertion :=
  object_without_field sg.(osKernelConfig) (timer_pool_addr sg index) image field **
  timer_images_without sg timers index **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) timers.(timerWheel) ** timer_globals_rep sg timers.

Lemma configured_rep_split_field : forall sg timers index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized timers ->
  timers.(timerImages) index = Some image ->
  timer_configured_rep sg timers |--
    field_cell (timer_pool_addr sg index) image field ** pool_without_field sg timers index image field.
Proof.
  intros sg timers index image field Hlayout Hnames Henabled Hinit Himage.
  rewrite (timer_initialized_configured_rep_eq sg timers Henabled Hinit).
  unfold timer_raw_rep, pool_without_field.
  sep_apply_l_atomic (timer_images_split_object sg timers index image Himage).
  sep_apply_l_atomic (object_rep_split_field sg.(osKernelConfig)
    (timer_pool_addr sg index) image field Hlayout Hnames); entailer!.
Qed.

Lemma configured_rep_merge_field : forall sg timers index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized timers ->
  timers.(timerImages) index = Some image ->
  field_cell (timer_pool_addr sg index) image field ** pool_without_field sg timers index image field
    |-- timer_configured_rep sg timers.
Proof.
  intros sg timers index image field Hlayout Hnames Henabled Hinit Himage.
  rewrite (timer_initialized_configured_rep_eq sg timers Henabled Hinit).
  unfold timer_raw_rep, pool_without_field.
  sep_apply_l_atomic (object_rep_merge_field sg.(osKernelConfig)
    (timer_pool_addr sg index) image field Hlayout Hnames).
  sep_apply_l_atomic (timer_images_merge_object sg timers index image Himage); entailer!.
Qed.

Definition context_rep (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (context : OsSchedCallContext)
  (mask : Z) (kernel : UCOS2_Verify_State) : Assertion :=
  mutex_query_closed platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask kernel **
  (os_sched_context_resources external context ** unmap_table_rep sg).

Definition context_without_field (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars) (context : OsSchedCallContext)
  (mask : Z) (kernel : UCOS2_Verify_State) (index : TimerID) (image : TimerImage)
  (field : TmrStopField) : Assertion :=
  coq_prop (UCOS2_state_inv sg kernel) &&
  (interrupt_platform_running platform context.(os_sched_call_invocation)
     context.(os_sched_call_origin) mask **
   pool_without_field sg kernel.(TimerState) index image field **
   UCOS2_raw_rep_missing_timer sg kernel ** os_sched_context_resources external context ** unmap_table_rep sg).

Lemma context_rep_split_field : forall external platform critical sg context mask kernel index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized kernel.(TimerState) ->
  kernel.(TimerState).(timerImages) index = Some image ->
  context_rep external platform critical sg context mask kernel |--
    field_cell (timer_pool_addr sg index) image field **
    context_without_field external platform sg context mask kernel index image field.
Proof.
  intros external platform critical sg context mask kernel index image field
    Hlayout Hnames Henabled Hinit Himage.
  unfold context_rep, context_without_field.
  rewrite mutex_query_closed_equiv, UCOS2_inv_split_timer.
  Intros.
  sep_apply_l_atomic (configured_rep_split_field sg kernel.(TimerState) index image field
    Hlayout Hnames Henabled Hinit Himage); entailer!.
Qed.

Lemma context_rep_merge_field : forall external platform critical sg context mask kernel index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized kernel.(TimerState) ->
  kernel.(TimerState).(timerImages) index = Some image ->
  field_cell (timer_pool_addr sg index) image field **
    context_without_field external platform sg context mask kernel index image field |--
  context_rep external platform critical sg context mask kernel.
Proof.
  intros external platform critical sg context mask kernel index image field
    Hlayout Hnames Henabled Hinit Himage.
  unfold context_rep, context_without_field.
  rewrite mutex_query_closed_equiv, UCOS2_inv_split_timer.
  Intros.
  sep_apply_l_atomic (configured_rep_merge_field sg kernel.(TimerState) index image field
    Hlayout Hnames Henabled Hinit Himage); entailer!.
Qed.

(** This residual owns no Timer object, row or Timer global.  Its state
    index is the pre-Unlink snapshot and does not claim that the changed
    Timer part is still represented by that snapshot. *)
Definition context_without_timer (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (sg : StableGlobVars) (context : OsSchedCallContext)
  (mask : Z) (kernel : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg kernel) &&
  (interrupt_platform_running platform context.(os_sched_call_invocation)
     context.(os_sched_call_origin) mask ** UCOS2_raw_rep_missing_timer sg kernel **
   os_sched_context_resources external context ** unmap_table_rep sg).

Lemma state_inv_timer_configuration : forall sg kernel,
  UCOS2_state_inv sg kernel -> valid_timer_configuration sg kernel.(TimerState).
Proof.
  intros sg kernel Hvalid.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
Qed.

Lemma context_rep_split_timer : forall external platform critical sg context mask kernel,
  context_rep external platform critical sg context mask kernel |--
    timer_inv sg kernel.(TimerState) ** context_without_timer external platform sg context mask kernel.
Proof.
  intros; unfold context_rep, context_without_timer.
  rewrite mutex_query_closed_equiv, UCOS2_inv_split_timer.
  Intros.
  assert (Htimers : valid_timer_configuration sg kernel.(TimerState))
    by (apply state_inv_timer_configuration; assumption).
  unfold timer_inv; entailer!.
Qed.

Lemma unlink_post_merge_context : forall external platform critical sg context mask kernel index node,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized kernel.(TimerState) ->
  kernel.(TimerState).(timerUsed) index = Some node -> node.(timerState) = TimerRunning ->
  tmr_unlink_configured_post sg kernel.(TimerState) index **
    context_without_timer external platform sg context mask kernel |--
  EX timers, coq_prop (timer_unlink sg kernel.(TimerState) index = Some timers) &&
    context_rep external platform critical sg context mask (replace_TimerS timers kernel).
Proof.
  intros external platform critical sg context mask kernel index node Henabled Hinit Hnode Hrunning.
  unfold tmr_unlink_configured_post, context_without_timer, timer_inv.
  Intros timers.
  assert (Hstep : timer_unlink sg kernel.(TimerState) index = Some timers) by tauto.
  assert (Hvalid : UCOS2_state_inv sg kernel) by tauto.
  pose proof (UCOS2_timer_unlink_preserves_validity sg kernel index node timers
    Hvalid Henabled Hinit Hnode Hrunning Hstep) as Hupdated.
  Exists timers; unfold context_rep; rewrite mutex_query_closed_equiv.
  Intros.
  assert (Htimer_eq : timers = (replace_TimerS timers kernel).(TimerState)).
  { symmetry; apply replace_TimerS_TimerState. }
  rewrite Htimer_eq.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_timer sg kernel (replace_TimerS timers kernel)
    Hupdated (eq_sym (UCOS2_raw_rep_missing_timer_replace_eq sg kernel timers))).
  entailer!.
Qed.

End TmrStopOldFields.

(** Actual product-model cells, with the old whole-kernel ownership
    transported by lift.  Reading a stored function address does not
    establish func_ptr_spec; the separate source capability is required. *)
Definition tmr_stop_field_cell (p : Z) (image : TimerImage) (field : TmrStopField)
  : TmrStopRules.expr :=
  match field with
  | StopTypeField | StopStateField =>
      TmrStopRules.store_uchar (tmr_unlink_timer_field p (tmr_stop_field_name field))
        (tmr_stop_field_value field image)
  | StopCallbackField | StopArgumentField =>
      TmrStopRules.store_ptr (tmr_unlink_timer_field p (tmr_stop_field_name field))
        (tmr_stop_field_value field image)
  end.

Lemma tmr_stop_field_cell_lift : forall p image field,
  TmrStopRules.logic_equiv (tmr_stop_field_cell p image field)
    (TmrStopRules.lift (TmrStopOldFields.field_cell p image field)).
Proof.
  intros p image field; destruct field; cbn [tmr_stop_field_cell TmrStopOldFields.field_cell];
    apply TmrStopRules.store_uchar_lift || apply TmrStopRules.store_ptr_lift.
Qed.

Lemma tmr_stop_field_split_lift : forall P R p image field,
  UCOS2_C_Rules.derivable1 P
    (UCOS2_C_Rules.sepcon (TmrStopOldFields.field_cell p image field) R) ->
  TmrStopRules.derivable1 (TmrStopRules.lift P)
    (TmrStopRules.sepcon (tmr_stop_field_cell p image field) (TmrStopRules.lift R)).
Proof.
  intros P R p image field Hsplit heap HP.
  pose proof (TmrStopRules.lift_entailment P _ Hsplit heap HP) as Hfields.
  apply (proj1 (TmrStopRules.lift_sepcon (TmrStopOldFields.field_cell p image field) R heap)) in Hfields.
  destruct Hfields as [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
  exists field_heap, rest_heap; split; [exact Hjoin|].
  split; [exact (proj2 (tmr_stop_field_cell_lift p image field) field_heap Hfield)|exact Hrest].
Qed.

Lemma tmr_stop_field_merge_lift : forall P R p image field,
  UCOS2_C_Rules.derivable1
    (UCOS2_C_Rules.sepcon (TmrStopOldFields.field_cell p image field) R) P ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon (tmr_stop_field_cell p image field) (TmrStopRules.lift R))
    (TmrStopRules.lift P).
Proof.
  intros P R p image field Hmerge heap [field_heap [rest_heap [Hjoin [Hfield Hrest]]]].
  apply (TmrStopRules.lift_entailment _ P Hmerge heap).
  apply (proj2 (TmrStopRules.lift_sepcon (TmrStopOldFields.field_cell p image field) R heap)).
  exists field_heap, rest_heap; split; [exact Hjoin|].
  split; [exact (proj1 (tmr_stop_field_cell_lift p image field) field_heap Hfield)|exact Hrest].
Qed.

Lemma tmr_stop_configured_rep_split_field : forall sg timers index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized timers ->
  timers.(timerImages) index = Some image ->
  TmrStopRules.derivable1 (TmrStopRules.lift (timer_configured_rep sg timers))
    (TmrStopRules.sepcon (tmr_stop_field_cell (timer_pool_addr sg index) image field)
      (TmrStopRules.lift (TmrStopOldFields.pool_without_field sg timers index image field))).
Proof.
  intros; apply tmr_stop_field_split_lift.
  apply TmrStopOldFields.configured_rep_split_field; assumption.
Qed.

Lemma tmr_stop_configured_rep_merge_field : forall sg timers index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized timers ->
  timers.(timerImages) index = Some image ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon (tmr_stop_field_cell (timer_pool_addr sg index) image field)
      (TmrStopRules.lift (TmrStopOldFields.pool_without_field sg timers index image field)))
    (TmrStopRules.lift (timer_configured_rep sg timers)).
Proof.
  intros; apply tmr_stop_field_merge_lift.
  apply TmrStopOldFields.configured_rep_merge_field; assumption.
Qed.

Section StopOwnedFields.

Context {Application : Type} (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (mask perr : Z).

Definition tmr_stop_owned_field_view (context : OsSchedCallContext)
  (before : TmrStopState Application) (index : TimerID) (image : TimerImage) (field : TmrStopField)
  : TmrStopRules.expr :=
  TmrStopRules.sepcon
    (TmrStopRules.sepcon (tmr_stop_field_cell (timer_pool_addr sg index) image field)
      (TmrStopRules.lift (TmrStopOldFields.context_without_field external platform sg context mask
        before.(tmr_stop_kernel) index image field)))
    (tmr_stop_client_rep AppRep perr before).

Lemma tmr_stop_owned_split_field : forall context (before : TmrStopState Application) index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(tmr_stop_kernel).(TimerState) ->
  before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image ->
  TmrStopRules.derivable1 (tmr_stop_owned AppRep external platform critical sg mask perr context before)
    (tmr_stop_owned_field_view context before index image field).
Proof.
  intros context before index image field Hlayout Hnames Henabled Hinit Himage heap
    [context_heap [client_heap [Hjoin [Hcontext Hclient]]]].
  exists context_heap, client_heap; split; [exact Hjoin|]. split; [|exact Hclient].
  apply (tmr_stop_field_split_lift _ _ _ _ _
    (TmrStopOldFields.context_rep_split_field external platform critical sg context mask
      before.(tmr_stop_kernel) index image field Hlayout Hnames Henabled Hinit Himage) context_heap).
  exact (proj1 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask before.(tmr_stop_kernel)) context_heap Hcontext).
Qed.

Lemma tmr_stop_owned_merge_field : forall context (before : TmrStopState Application) index image field,
  tmr_stop_fields_layout -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(tmr_stop_kernel).(TimerState) ->
  before.(tmr_stop_kernel).(TimerState).(timerImages) index = Some image ->
  TmrStopRules.derivable1 (tmr_stop_owned_field_view context before index image field)
    (tmr_stop_owned AppRep external platform critical sg mask perr context before).
Proof.
  intros context before index image field Hlayout Hnames Henabled Hinit Himage heap
    [context_heap [client_heap [Hjoin [Hfields Hclient]]]].
  exists context_heap, client_heap; split; [exact Hjoin|]. split; [|exact Hclient].
  apply (proj2 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask before.(tmr_stop_kernel)) context_heap).
  exact (tmr_stop_field_merge_lift _ _ _ _ _
    (TmrStopOldFields.context_rep_merge_field external platform critical sg context mask
      before.(tmr_stop_kernel) index image field Hlayout Hnames Henabled Hinit Himage)
    context_heap Hfields).
Qed.

Definition tmr_stop_unlink_frame (context : OsSchedCallContext) (before : TmrStopState Application)
  : TmrStopRules.expr :=
  TmrStopRules.lift (TmrStopOldFields.context_without_timer external platform sg context mask
    before.(tmr_stop_kernel)).

Lemma tmr_stop_owned_split_timer : forall context (before : TmrStopState Application),
  TmrStopRules.derivable1 (tmr_stop_owned AppRep external platform critical sg mask perr context before)
    (TmrStopRules.sepcon
      (TmrStopRules.sepcon (TimerCalleeLift.timer_inv sg before.(tmr_stop_kernel).(TimerState))
        (tmr_stop_unlink_frame context before))
      (tmr_stop_client_rep AppRep perr before)).
Proof.
  intros context before heap [context_heap [client_heap [Hjoin [Hcontext Hclient]]]].
  exists context_heap, client_heap; split; [exact Hjoin|]. split; [|exact Hclient].
  apply (proj1 (TmrStopRules.lift_sepcon _ _ context_heap)).
  apply (TmrStopRules.lift_entailment _ _
    (TmrStopOldFields.context_rep_split_timer external platform critical sg context mask
      before.(tmr_stop_kernel)) context_heap).
  exact (proj1 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask before.(tmr_stop_kernel)) context_heap Hcontext).
Qed.

(** The changed Timer and its exact unlink relation come from the actual
    configured postcondition.  No old whole-Timer invariant is framed.
    The client/output frame here is disjoint; its same physical bytes are
    retained, including when a callback argument denotes the output cell. *)
Lemma tmr_stop_unlink_post_merge_owned : forall context (before : TmrStopState Application) index node,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized before.(tmr_stop_kernel).(TimerState) ->
  before.(tmr_stop_kernel).(TimerState).(timerUsed) index = Some node -> node.(timerState) = TimerRunning ->
  TmrStopRules.derivable1
    (TmrStopRules.sepcon
      (TmrStopRules.sepcon
        (TimerCalleeLift.tmr_unlink_configured_post sg before.(tmr_stop_kernel).(TimerState) index)
        (tmr_stop_unlink_frame context before))
      (tmr_stop_client_rep AppRep perr before))
    (fun heap => exists after,
      tmr_stop_unlink_program sg index before tt after /\
      tmr_stop_owned AppRep external platform critical sg mask perr context after heap).
Proof.
  intros context before index node Henabled Hinit Hnode Hrunning heap
    [context_heap [client_heap [Hjoin [Hpost Hclient]]]].
  pose proof (proj2 (TmrStopRules.lift_sepcon _ _ context_heap) Hpost) as Hlifted.
  pose proof (TmrStopRules.lift_entailment _ _
    (TmrStopOldFields.unlink_post_merge_context external platform critical sg context mask
      before.(tmr_stop_kernel) index node Henabled Hinit Hnode Hrunning)
    context_heap Hlifted) as Hmerged.
  destruct Hmerged as [timers [Hstep Hcontext]].
  exists (tmr_stop_set_kernel (replace_TimerS timers before.(tmr_stop_kernel)) before).
  split; [apply tmr_stop_unlink_step; exact Hstep|].
  exists context_heap, client_heap; split; [exact Hjoin|]. split; [|exact Hclient].
  exact (proj2 (TimerCalleeLift.os_sched_closed_resources_lift external platform critical sg
    context mask (replace_TimerS timers before.(tmr_stop_kernel))) context_heap Hcontext).
Qed.

End StopOwnedFields.

(** Raw reads are a separate client-resource view.  A final AppRep may
    contain this view and the remaining application resources; perr stays
    only in tmr_stop_client_rep.  There is no callback_arg inequality.
    A raw State=3 byte supplies a read, not Unlink's pool/wheel ownership.
    State 0, 1, 2 and every other byte are represented without exclusion.

    The nesting argument is the value actually read before Lock.  The
    State value used after Lock must come from the current raw resource
    returned by that call; no getter is asserted without its bytes. *)
Definition tmr_stop_raw_state_rep (pointer type_byte nesting status : Z) : TmrStopRules.expr :=
  if Z.eqb type_byte 100 then
    if Z_gt_dec nesting 0 then TmrStopRules.emp
    else TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrState") status
  else TmrStopRules.emp.

Definition tmr_stop_raw_rep (pointer type_byte nesting status : Z) : TmrStopRules.expr :=
  if Z.eqb pointer 0 then TmrStopRules.emp
  else TmrStopRules.sepcon
    (TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrType") type_byte)
    (tmr_stop_raw_state_rep pointer type_byte nesting status).

Lemma tmr_stop_raw_rep_null : forall type_byte nesting status,
  tmr_stop_raw_rep 0 type_byte nesting status = TmrStopRules.emp.
Proof. reflexivity. Qed.

Lemma tmr_stop_raw_rep_nonnull : forall pointer type_byte nesting status,
  pointer <> 0 ->
  tmr_stop_raw_rep pointer type_byte nesting status =
    TmrStopRules.sepcon
      (TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrType") type_byte)
      (tmr_stop_raw_state_rep pointer type_byte nesting status).
Proof.
  intros pointer type_byte nesting status Hpointer; unfold tmr_stop_raw_rep.
  rewrite (proj2 (Z.eqb_neq pointer 0) Hpointer); reflexivity.
Qed.

Lemma tmr_stop_raw_state_rep_invalid_type : forall pointer type_byte nesting status,
  type_byte <> 100 -> tmr_stop_raw_state_rep pointer type_byte nesting status = TmrStopRules.emp.
Proof.
  intros pointer type_byte nesting status Htype; unfold tmr_stop_raw_state_rep.
  rewrite (proj2 (Z.eqb_neq type_byte 100) Htype); reflexivity.
Qed.

Lemma tmr_stop_raw_state_rep_isr : forall pointer nesting status,
  nesting > 0 -> tmr_stop_raw_state_rep pointer 100 nesting status = TmrStopRules.emp.
Proof.
  intros pointer nesting status Hnesting; unfold tmr_stop_raw_state_rep; cbn.
  destruct (Z_gt_dec nesting 0); [reflexivity|lia].
Qed.

Lemma tmr_stop_raw_state_rep_enabled : forall pointer nesting status,
  nesting <= 0 ->
  tmr_stop_raw_state_rep pointer 100 nesting status =
    TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrState") status.
Proof.
  intros pointer nesting status Hnesting; unfold tmr_stop_raw_state_rep; cbn.
  destruct (Z_gt_dec nesting 0); [lia|reflexivity].
Qed.

(** The unrestricted status binder above includes STOPPED/COMPLETED.
    Their source return classification is the existing program lemma,
    independently of this read-only physical representation. *)
Lemma tmr_stop_raw_stopped_completed : forall pointer nesting status,
  nesting <= 0 -> (status = 1 \/ status = 2) ->
  tmr_stop_raw_state_rep pointer 100 nesting status =
    TmrStopRules.store_uchar (tmr_unlink_timer_field pointer "OSTmrState") status /\
  tmr_stop_nonrunning_output status = (1, encode_os_err_code OS_ERR_TMR_STOPPED).
Proof.
  intros pointer nesting status Hnesting Hstatus; split.
  - apply tmr_stop_raw_state_rep_enabled; exact Hnesting.
  - apply tmr_stop_nonrunning_output_stopped_completed; exact Hstatus.
Qed.
