Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_layout_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_heap_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_create_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_annotation_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_continuation_source_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_registry_spec.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_task_call_pend_view_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_fields_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_source_fields_spec.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Strings.String Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition tmr_task_fields_index_valid sg index : Prop :=
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers).
Definition tmr_task_fields_image_at {Application}
  (world : tmr_task_scan_world Application) index image : Prop :=
  (tmr_task_timers world).(timerImages) index = Some image.
Definition tmr_task_fields_pend_blocking_layout environment critical sg call pevent before eid : Prop :=
  pevent <> 0 ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_observed_blocking_layout (Some environment) critical sg call before eid
    sg.(g_OSTCBCur) sg.(g_OSRdyGrp) sg.(g_OSRdyTbl).

Lemma tmr_task_global_addresses_implies_scheduler_addresses : forall sg signal wheel time current
  running ints locks high priority high_tcb table counter unmap group rows,
  tmr_task_global_addresses sg signal wheel time current running ints locks high priority
    high_tcb table counter unmap group rows ->
  os_sched_lock_global_addresses sg running ints locks /\
  os_sched_unlock_global_addresses sg running ints locks high priority high_tcb table
    counter unmap group rows /\
  os_sched_global_addresses sg ints locks high priority high_tcb table counter unmap group rows.
Proof.
  intros; unfold tmr_task_global_addresses, os_sched_unlock_global_addresses in *; tauto.
Qed.

(** These lifts change only the assertion model used by the Task's
    function-pointer semantics. Each callee pre/post is the exact existing
    fields contract. local is the actual input family, not saved_local. *)
Module TmrTaskFieldsCallee.
Definition lock_pre environment critical local sg call mask before X :=
  TmrTaskFieldsRules.lift
    (os_sched_lock_fields_pre environment critical local sg call mask before X).
Definition lock_post environment critical local sg call mask before X :=
  TmrTaskFieldsRules.lift
    (os_sched_lock_fields_post environment critical local sg call mask before X).
Definition unlock_pre environment critical local sg call mask before X :=
  TmrTaskFieldsRules.lift
    (os_sched_unlock_fields_pre environment critical local sg call mask before X).
Definition unlock_post environment critical local sg call mask before X :=
  TmrTaskFieldsRules.lift
    (os_sched_unlock_fields_post environment critical local sg call mask before X).
Definition pend_pre environment local critical sg call mask pevent timeout perr before eid observed X :=
  TmrTaskFieldsRules.lift (sem_pend_source_fields_call_pre environment local critical sg call
    mask pevent timeout perr before eid observed X).
Definition pend_post environment critical sg call mask pevent timeout perr before X :=
  TmrTaskFieldsRules.lift (sem_pend_source_fields_call_post environment critical sg call
    mask pevent timeout perr before X).
Definition unlink_pre p base match_time next previous first entries frame :=
  TmrTaskFieldsRules.lift (tmr_unlink_spec.tmr_unlink_raw_pre
    p base match_time next previous first entries frame).
Definition unlink_post p base match_time next previous first entries frame :=
  TmrTaskFieldsRules.lift (tmr_unlink_spec.tmr_unlink_raw_post
    p base match_time next previous first entries frame).
Definition link_pre p base clock kind time delay period first entries frame :=
  TmrTaskFieldsRules.lift (tmr_link_spec.tmr_link_raw_pre
    p base clock kind time delay period first entries frame).
Definition link_post p base clock kind time delay period first entries frame :=
  TmrTaskFieldsRules.lift (tmr_link_spec.tmr_link_raw_post
    p base clock kind time delay period first entries frame).
End TmrTaskFieldsCallee.

Definition tmr_task_fields_kernel_any (_ : OsSchedCallContext)
  (_ : UCOS2_Verify_State) : Prop := True.

(** Source bindings are read at the actual pool pointer. This smaller
    consumer does not upgrade Create's finite index quantifier to the
    frozen tmr_task_fields_layout's all-pointer quantifier. *)
Module TmrTaskFieldsPool.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.
Lemma object_split_merge_field : forall sg pointer image field,
  tmr_unlink_timer_field pointer (tmr_task_image_name field) =
    pointer + tmr_task_image_offset sg.(osKernelConfig) field ->
  timer_object_rep sg.(osKernelConfig) pointer image --||--
    TmrTaskFieldsHeap.cell (tmr_task_image_kind field)
      (tmr_unlink_timer_field pointer (tmr_task_image_name field))
      (tmr_task_image_value field image) **
    TmrTaskFieldsHeap.object_without_field sg.(osKernelConfig) pointer image field.
Proof.
  intros sg pointer image field Haddress; rewrite Haddress.
  destruct field; unfold timer_object_rep, TmrTaskFieldsHeap.object_without_field,
    TmrTaskFieldsHeap.cell, tmr_task_image_kind, tmr_task_image_offset,
    tmr_task_image_value;
    try replace (pointer + (timer_option_offset sg.(osKernelConfig) + 1))
      with (pointer + timer_option_offset sg.(osKernelConfig) + 1) by lia;
    split; entailer!.
Qed.

Lemma timer_split_merge_field : forall sg timers index image field,
  tmr_create_c_bindings sg -> tmr_unlink_layout ->
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  timers.(timerImages) index = Some image ->
  timer_raw_rep sg timers --||--
    TmrTaskFieldsHeap.cell (tmr_task_image_kind field)
      (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
      (tmr_task_image_value field image) **
    TmrTaskFieldsHeap.timer_without_field sg timers index image field.
Proof.
  intros sg timers index image field Hbinding Hlayout Hindex Himage.
  pose proof (tmr_task_pool_field_addresses_from_create_binding
    sg index field Hbinding Hlayout Hindex) as Haddress.
  unfold timer_raw_rep, TmrTaskFieldsHeap.timer_without_field; split.
  - sep_apply_l_atomic (timer_images_split_object sg timers index image Himage).
    rewrite (object_split_merge_field sg (timer_pool_addr sg index) image field Haddress).
    entailer!.
  - assert (Hobjects : timer_images_rep sg timers --||--
      timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg index) image **
      timer_images_without sg timers index).
    { split; [apply timer_images_split_object|apply timer_images_merge_object]; exact Himage. }
    rewrite Hobjects.
    rewrite (object_split_merge_field sg (timer_pool_addr sg index) image field Haddress).
    entailer!.
Qed.

Lemma timer_split_merge_time_match : forall sg timers index image,
  tmr_create_c_bindings sg -> tmr_unlink_layout ->
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  timers.(timerImages) index = Some image ->
  timer_raw_rep sg timers --||--
    (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime) timers.(timerTime) **
     TmrTaskFieldsHeap.cell TaskUIntCell
       (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrMatch")
       image.(timerImageMatch)) **
    TmrTaskFieldsHeap.timer_without_time_field sg timers index image TaskMatchField.
Proof.
  intros sg timers index image Hbinding Hlayout Hindex Himage.
  pose proof (timer_split_merge_field sg timers index image TaskMatchField
    Hbinding Hlayout Hindex Himage) as Hfield.
  split.
  - sep_apply_l_atomic (proj1 Hfield).
    unfold TmrTaskFieldsHeap.timer_without_field,
      TmrTaskFieldsHeap.timer_without_time_field, timer_globals_rep,
      TmrTaskFieldsHeap.globals_without_time, TmrTaskFieldsHeap.cell;
      cbn [tmr_task_image_kind tmr_task_image_name tmr_task_image_value]; entailer!.
  - sep_apply_r_atomic (proj2 Hfield).
    unfold TmrTaskFieldsHeap.timer_without_field,
      TmrTaskFieldsHeap.timer_without_time_field, timer_globals_rep,
      TmrTaskFieldsHeap.globals_without_time, TmrTaskFieldsHeap.cell;
      cbn [tmr_task_image_kind tmr_task_image_name tmr_task_image_value]; entailer!.
Qed.
End TmrTaskFieldsPool.

Section TaskFieldsCallAdapters.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars) (mask perr : Z).

Definition tmr_task_fields_base_owned call (world : tmr_task_scan_world Application)
  : TmrTaskFieldsRules.expr :=
  fun heap => exists local,
    TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsRules.lift
        (TmrTaskFields.tmr_task_fields_context environment local sg call mask (fst world)))
      (AppRep (snd world)) heap.

Definition tmr_task_fields_client (world : tmr_task_scan_world Application) :=
  TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.lift (sem_pend_error_cell perr))
    (AppRep (snd world)).

Lemma tmr_task_fields_base_merge_error : forall call world,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon (tmr_task_fields_base_owned call world)
      (TmrTaskFieldsRules.undef_store_uchar perr))
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world).
Proof.
  intros call world heap [base [error [Hjoin [Hbase Herror]]]].
  destruct Hbase as [local [kernel [application [Hbase [Hkernel Happlication]]]]].
  destruct (TmrTaskFieldsRules.join_assoc kernel application error base heap Hbase Hjoin)
    as [client [Hclient Hwhole]].
  exists local, kernel, client; split; [exact Hwhole|].
  split; [exact Hkernel|]. exists error, application; split.
  - apply TmrTaskFieldsRules.join_comm; exact Hclient.
  - split; [|exact Happlication].
    destruct error as [memory callback_environment].
    exact (proj1 (TmrTaskFieldsRules.undef_store_uchar_slice
      callback_environment perr memory) Herror).
Qed.

Definition tmr_task_fields_time_rest call (world : tmr_task_scan_world Application) :=
  tmr_task_fields_cell_rest AppRep environment sg mask perr call world
    (TmrTaskFieldsHeap.timer_without_time sg (tmr_task_timers world)).
Definition tmr_task_fields_image_rest call (world : tmr_task_scan_world Application) index image field :=
  tmr_task_fields_cell_rest AppRep environment sg mask perr call world
    (TmrTaskFieldsHeap.timer_without_field sg (tmr_task_timers world) index image field).
Definition tmr_task_fields_match_rest call (world : tmr_task_scan_world Application) index image :=
  tmr_task_fields_cell_rest AppRep environment sg mask perr call world
    (TmrTaskFieldsHeap.timer_without_time_field sg (tmr_task_timers world) index image TaskMatchField).
Definition tmr_task_fields_head_rest call (world : tmr_task_scan_world Application) spoke :=
  tmr_task_fields_cell_rest AppRep environment sg mask perr call world
    (TmrTaskFieldsHeap.timer_without_head sg (tmr_task_timers world) spoke
      (nth spoke (timerWheel (tmr_task_timers world)) [])).
Definition tmr_task_fields_complete_rest call (world : tmr_task_scan_world Application) index image :=
  tmr_task_fields_cell_rest AppRep environment sg mask perr call world
    (timer_complete_rep_without_state sg (tmr_task_timers world) index image).

(** The actual spatial wand produced by raw caller localization is framed
    through the raw call. It is not an assumed predicate saying that every
    raw post entails an arbitrarily chosen final Task world. *)
Definition tmr_task_fields_unlink_rest local call (world : tmr_task_scan_world Application)
  index match_time next previous first entries frame :=
  TmrTaskFieldsRules.sepcon
    (TmrTaskFieldsRules.lift (UCOS2_C_Rules.wand
      (tmr_unlink_spec.tmr_unlink_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
        match_time next previous first entries frame)
      (TmrTaskFieldsRawHeap.unlink_return environment local sg call mask (fst world) index)))
    (tmr_task_fields_client world).
Definition tmr_task_fields_link_rest local call (world : tmr_task_scan_world Application)
  index delay period first entries frame :=
  TmrTaskFieldsRules.sepcon
    (TmrTaskFieldsRules.lift (UCOS2_C_Rules.wand
      (tmr_link_spec.tmr_link_raw_post (timer_pool_addr sg index) sg.(g_OSTmrWheelTbl)
        sg.(g_OSTmrTime) 1 (timerTime (tmr_task_timers world)) delay period first entries frame)
      (TmrTaskFieldsRawHeap.link_return environment local sg call mask (fst world) index)))
    (tmr_task_fields_client world).

Lemma tmr_task_fields_pool_image_view : forall call world index image field,
  tmr_create_c_bindings sg -> tmr_unlink_layout ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers world) ->
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  (tmr_task_timers world).(timerImages) index = Some image ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (tmr_task_fields_heap_view AppRep environment sg mask perr call world
      (TmrTaskFieldsHeap.cell (tmr_task_image_kind field)
        (tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field))
        (tmr_task_image_value field image))
      (TmrTaskFieldsHeap.timer_without_field sg (tmr_task_timers world) index image field)).
Proof.
  intros call world index image field Hbinding Hlayout Hen Hinit Hindex Himage.
  pose proof (TmrTaskFieldsPool.timer_split_merge_field sg (tmr_task_timers world)
    index image field Hbinding Hlayout Hindex Himage) as Hsplit; split.
  - apply tmr_task_current_fields_split_part; try assumption; exact (proj1 Hsplit).
  - apply tmr_task_current_fields_merge_read_part; try assumption; exact (proj2 Hsplit).
Qed.

Lemma tmr_task_fields_pool_match_view : forall call world index image,
  tmr_create_c_bindings sg -> tmr_unlink_layout ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized (tmr_task_timers world) ->
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  (tmr_task_timers world).(timerImages) index = Some image ->
  TmrTaskFieldsRules.logic_equiv
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (tmr_task_fields_heap_view AppRep environment sg mask perr call world
      (UCOS2_C_Rules.sepcon
        (TmrTaskFieldsHeap.cell TaskUIntCell sg.(g_OSTmrTime) (timerTime (tmr_task_timers world)))
        (TmrTaskFieldsHeap.cell TaskUIntCell
          (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrMatch") image.(timerImageMatch)))
      (TmrTaskFieldsHeap.timer_without_time_field sg (tmr_task_timers world) index image TaskMatchField)).
Proof.
  intros call world index image Hbinding Hlayout Hen Hinit Hindex Himage.
  pose proof (TmrTaskFieldsPool.timer_split_merge_time_match sg (tmr_task_timers world)
    index image Hbinding Hlayout Hindex Himage) as Hsplit; split.
  - apply tmr_task_current_fields_split_part; try assumption; exact (proj1 Hsplit).
  - apply tmr_task_current_fields_merge_read_part; try assumption; exact (proj2 Hsplit).
Qed.
End TaskFieldsCallAdapters.

Definition tmr_task_fields_pend_argument_rest environment local critical sg call mask
  signal timeout perr before eid observed X signal_address :=
  TmrTaskFieldsRules.wand (TmrTaskFieldsRules.store_ptr signal_address signal)
    (TmrTaskFieldsCallee.pend_pre environment local critical sg call mask signal timeout
      perr before eid observed X).

(** The source must read OSTmrSemSignal before entering OSSemPend. This is
    the same argument view as the existing Task callee adapter: it consumes
    one cell and its restoration wand, then invokes the actual-source
    fields precondition. It retains that callee's same-X postcondition. *)
Definition tmr_task_fields_pend_argument_pre environment local critical sg call mask
  signal timeout perr before eid observed X signal_address :=
  TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.store_ptr signal_address signal)
    (tmr_task_fields_pend_argument_rest environment local critical sg call mask
      signal timeout perr before eid observed X signal_address).

Lemma tmr_task_fields_pend_argument_pre_closed : forall environment local critical sg call mask
  signal timeout perr before eid observed X signal_address,
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_pend_argument_pre environment local critical sg call mask
      signal timeout perr before eid observed X signal_address)
    (TmrTaskFieldsCallee.pend_pre environment local critical sg call mask signal timeout
      perr before eid observed X).
Proof.
  intros environment local critical sg call mask signal timeout perr before eid observed X
    signal_address heap [cell [rest [Hjoin [Hcell Hrest]]]].
  apply (Hrest cell heap).
  - exact (TmrTaskFieldsRules.join_comm cell rest heap Hjoin).
  - exact Hcell.
Qed.

Lemma tmr_task_fields_pend_argument_pre_frame : forall environment local critical sg call mask
  signal timeout perr before eid observed X signal_address frame,
  TmrTaskFieldsRules.derivable1
    (TmrTaskFieldsRules.sepcon
      (tmr_task_fields_pend_argument_pre environment local critical sg call mask
        signal timeout perr before eid observed X signal_address) frame)
    (TmrTaskFieldsRules.sepcon
      (TmrTaskFieldsCallee.pend_pre environment local critical sg call mask signal timeout
        perr before eid observed X) frame).
Proof.
  intros environment local critical sg call mask signal timeout perr before eid observed X
    signal_address frame heap [owned [rest [Hjoin [Howned Hframe]]]].
  exists owned, rest; split; [exact Hjoin|]. split; [|exact Hframe].
  exact (tmr_task_fields_pend_argument_pre_closed environment local critical sg call mask
    signal timeout perr before eid observed X signal_address owned Howned).
Qed.

Section TaskFieldsCallbackArgumentView.
Context {Application : Type} (AppRep : Application -> TmrTaskFieldsRules.expr).
Context (environment : TaskStackCallEnvironment) (sg : StableGlobVars)
  (callback : (addr * addr * addr) -> OsSchedCallContext ->
    StateRelMonad.M (tmr_task_scan_world Application) OsSchedCallContext)
  (mask perr : Z).

(** CallbackArg is read as a call argument. The view restores the existing
    fields callback pre; it neither manufactures a body capability nor
    changes any returned state, descriptor, or preservation obligation. *)
Definition tmr_task_fields_callback_argument_rest fn self argument context
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type) argument_address :=
  TmrTaskFieldsRules.wand (TmrTaskFieldsRules.store_ptr argument_address argument)
    (tmr_task_fields_callback_pre AppRep environment sg mask perr
      fn self argument context before arguments).

Definition tmr_task_fields_callback_argument_pre fn self argument context
  (before : tmr_task_scan_world Application) (arguments : (Z * Z)%type) argument_address :=
  TmrTaskFieldsRules.sepcon (TmrTaskFieldsRules.store_ptr argument_address argument)
    (tmr_task_fields_callback_argument_rest fn self argument context before arguments argument_address).

Lemma tmr_task_fields_callback_argument_pre_closed : forall fn self argument context
  before arguments argument_address,
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_argument_pre fn self argument context before arguments argument_address)
    (tmr_task_fields_callback_pre AppRep environment sg mask perr
      fn self argument context before arguments).
Proof.
  intros fn self argument context before arguments argument_address heap
    [cell [rest [Hjoin [Hcell Hrest]]]].
  apply (Hrest cell heap).
  - exact (TmrTaskFieldsRules.join_comm cell rest heap Hjoin).
  - exact Hcell.
Qed.

(** The actual finite-pool field split produces the wand. In particular,
    this lemma does not assume an arbitrary final owner in the residual.
    The address is the existing alias-arrow interpretation at this index. *)
Lemma tmr_task_fields_callback_argument_rest_from_image : forall fn index argument context
  before image,
  tmr_create_c_bindings sg -> tmr_unlink_layout ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  tmr_task_callback_dispatch_domain sg fn (timer_pool_addr sg index) argument before ->
  tmr_task_fields_scan_ready sg before ->
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  (tmr_task_timers before).(timerImages) index = Some image ->
  argument = tmr_task_image_value TaskArgumentField image ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_image_rest AppRep environment sg mask perr context before index image TaskArgumentField)
    (tmr_task_fields_callback_argument_rest fn (timer_pool_addr sg index) argument context before
      (timer_pool_addr sg index, argument)
      (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrCallbackArg")).
Proof.
  intros fn index argument context before image Hbinding Hlayout Hen Hdomain Hready
    Hindex Himage Hargument rest Hrest cell heap Hjoin Hcell.
  split; [split; [reflexivity|split; assumption]|].
  pose proof (tmr_task_fields_pool_image_view AppRep environment sg mask perr
    context before index image TaskArgumentField Hbinding Hlayout Hen
    (proj2 Hready) Hindex Himage) as Hview.
  apply (proj2 Hview heap).
  apply (proj2 (tmr_task_fields_heap_view_cell AppRep environment sg mask perr
    context before TaskPointerCell
    (tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrCallbackArg")
    (tmr_task_image_value TaskArgumentField image)
    (TmrTaskFieldsHeap.timer_without_field sg (tmr_task_timers before)
      index image TaskArgumentField)) heap).
  exists cell, rest; split.
  - apply TmrTaskFieldsRules.join_comm; exact Hjoin.
  - split; [rewrite <- Hargument; exact Hcell|exact Hrest].
Qed.

Definition tmr_task_fields_callback_argument_specification fn self argument argument_address
  : TmrTaskFieldsCallback.Spec TmrTaskFieldsCallback.timer_callback_signature :=
  fun body => @TmrTaskFieldsRules.allp OsSchedCallContext (fun context =>
    @TmrTaskFieldsRules.allp (tmr_task_scan_world Application) (fun before =>
      TmrTaskFieldsCallback.HoareFun TmrTaskFieldsCallback.timer_callback_signature
        (fun arguments => tmr_task_fields_callback_argument_pre
          fn self argument context before arguments argument_address)
        (tmr_task_fields_callback_post AppRep environment sg callback mask perr
          fn self argument context before) body)).

Definition tmr_task_fields_callback_argument_capability fn self argument argument_address :=
  @TmrTaskFieldsCallback.func_ptr_spec TmrTaskFieldsCallback.timer_callback_signature fn
    (tmr_task_fields_callback_argument_specification fn self argument argument_address).

(** HoareFun_conseq transports BOTH all-frame safety and positive coverage
    of every source normal result. The original capability must already
    come from the concrete body's source evidence; this is no new registry
    introduction rule. The quantifiers over context/world are unchanged. *)
Lemma tmr_task_fields_callback_argument_capability_from_fields : forall fn self argument argument_address,
  TmrTaskFieldsRules.derivable1
    (tmr_task_fields_callback_capability AppRep environment sg callback mask perr fn self argument)
    (tmr_task_fields_callback_argument_capability fn self argument argument_address).
Proof.
  intros fn self argument argument_address.
  apply TmrTaskFieldsCallback.func_ptr_spec_mono.
  intros body heap Hbody context before.
  eapply TmrTaskFieldsCallback.HoareFun_conseq.
  - intro arguments; apply tmr_task_fields_callback_argument_pre_closed.
  - intros arguments result state Hpost; exact Hpost.
  - exact (Hbody context before).
Qed.

Lemma tmr_task_fields_callback_argument_specification_environment_only :
  forall fn self argument argument_address,
  TmrTaskFieldsCallback.specification_environment_only
    (tmr_task_fields_callback_argument_specification fn self argument argument_address).
Proof.
  intros fn self argument argument_address.
  apply TmrTaskFieldsCallback.allp_specification_environment_only; intro caller.
  apply TmrTaskFieldsCallback.allp_specification_environment_only; intro world.
  apply TmrTaskFieldsCallback.HoareFun_specification_environment_only.
Qed.
End TaskFieldsCallbackArgumentView.

(** Source receipts choose the same application frame and the ACTUAL
    returned descriptor. They do not identify that descriptor with entry. *)
Lemma tmr_task_fields_pend_source : forall Application environment critical sg callback
  call signal (before : tmr_task_scan_world Application) error returned current,
  sem_pend_source_fields_program environment critical sg call signal 0 (fst before) error current ->
  kernel_stack_call_same_call returned call ->
  tmr_task_continuation_pend_program environment critical sg (tmr_task_framed_effects callback)
    call signal before (error, returned) (current, snd before).
Proof. intros; split; [assumption|]. split; [assumption|reflexivity]. Qed.

Lemma tmr_task_fields_lock_source : forall Application environment critical sg mask callback
  call (before : tmr_task_scan_world Application) returned current,
  os_sched_lock_continuation_history environment critical sg call mask (fst before) returned current ->
  tmr_task_continuation_lock_program environment critical sg mask (tmr_task_framed_effects callback)
    call before returned (current, snd before).
Proof.
  intros; split; [apply os_sched_lock_continuation_program_iff; assumption|reflexivity].
Qed.

Lemma tmr_task_fields_unlock_source : forall Application environment critical sg mask callback
  call (before : tmr_task_scan_world Application) returned current,
  os_sched_unlock_continuation_history environment critical sg call mask (fst before) returned current ->
  tmr_task_continuation_unlock_program environment critical sg mask (tmr_task_framed_effects callback)
    call before returned (current, snd before).
Proof.
  intros; split; [apply os_sched_unlock_continuation_program_iff; assumption|reflexivity].
Qed.

