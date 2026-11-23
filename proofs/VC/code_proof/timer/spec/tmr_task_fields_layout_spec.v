Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem CNotation SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_alloc_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_free_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_create_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_link_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_annotation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_repaired_scan_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The actual Task input uses the alias-arrow address term below. The
    unrelated SeparationLogic.field_address parameter is not substituted
    for that term. This equality is notation/definition normalization only. *)
Lemma tmr_task_alias_field_address_eq : forall pointer field,
  tmr_unlink_timer_field pointer field = &(pointer # "os_tmr" ->ₛ field).
Proof. reflexivity. Qed.

(** The fixed source has OS_TMR_CFG_NAME_EN=1, a 32-bit pointer/function
    pointer, and the fields Type, Callback, Arg, Next, Prev, Match, Dly,
    Period, Name, Opt, State in that order. These two equations concern
    the existing numeric representation, not the opaque C evaluator. *)
Lemma tmr_task_selected_timer_sizes :
  timer_option_offset selected_kernel_configuration = 36 /\
  timer_object_size selected_kernel_configuration = 40.
Proof. split; reflexivity. Qed.

Lemma tmr_task_profile_timer_names : forall sg,
  tmr_task_profile sg -> sg.(osKernelConfig).(cfgTimerNames) = true.
Proof.
  intros sg Hprofile; unfold tmr_task_profile, tmr_link_profile in Hprofile; tauto.
Qed.

(** Existing Free's source binding states all object fields at the actual
    pointer. These are proved projections of that binding; they do not
    assert an unconditional interpretation of eval_addr_expr. *)
Lemma tmr_task_option_address_from_free_layout : forall pointer,
  tmr_free_layout pointer ->
  tmr_unlink_timer_field pointer "OSTmrOpt" = pointer + 36.
Proof.
  intros pointer Hlayout; unfold tmr_free_layout in Hlayout.
  rewrite tmr_task_alias_field_address_eq; tauto.
Qed.

Lemma tmr_task_callback_address_from_free_layout : forall pointer,
  tmr_free_layout pointer ->
  tmr_unlink_timer_field pointer "OSTmrCallback" = pointer + 4.
Proof.
  intros pointer Hlayout; unfold tmr_free_layout in Hlayout.
  rewrite tmr_task_alias_field_address_eq; tauto.
Qed.

Lemma tmr_task_argument_address_from_free_layout : forall pointer,
  tmr_free_layout pointer ->
  tmr_unlink_timer_field pointer "OSTmrCallbackArg" = pointer + 8.
Proof.
  intros pointer Hlayout; unfold tmr_free_layout in Hlayout.
  rewrite tmr_task_alias_field_address_eq; tauto.
Qed.

(** Exact minimal constructor for the frozen heap interface: its three
    missing universal field equations supplement existing Unlink layout.
    The premise belongs to fixed source/ABI binding, not callback behavior. *)
Lemma tmr_task_fields_layout_from_unlink_fields : forall sg,
  sg.(osKernelConfig).(cfgTimerNames) = true -> tmr_unlink_layout ->
  (forall pointer, tmr_unlink_timer_field pointer "OSTmrOpt" = pointer + 36) ->
  (forall pointer, tmr_unlink_timer_field pointer "OSTmrCallback" = pointer + 4) ->
  (forall pointer, tmr_unlink_timer_field pointer "OSTmrCallbackArg" = pointer + 8) ->
  tmr_task_fields_layout sg.
Proof.
  intros sg Hnames [Hmatch [Hnext [_ [Hstate Hwheel]]]] Hoption Hcallback Hargument.
  intros pointer field; destruct field;
    cbn [tmr_task_image_name tmr_task_image_offset].
  - apply Hnext.
  - apply Hmatch.
  - unfold timer_option_offset; rewrite Hnames; apply Hoption.
  - apply Hcallback.
  - apply Hargument.
  - unfold timer_option_offset; rewrite Hnames.
    replace (pointer + (36 + 1)) with (pointer + 37) by lia; apply Hstate.
Qed.

Lemma tmr_task_fields_layout_from_free_layout : forall sg,
  sg.(osKernelConfig).(cfgTimerNames) = true ->
  (forall pointer, tmr_free_layout pointer) -> tmr_task_fields_layout sg.
Proof.
  intros sg Hnames Hfree pointer field.
  pose proof (Hfree pointer) as Hlayout.
  unfold tmr_free_layout in Hlayout.
  destruct field; cbn [tmr_task_image_name tmr_task_image_offset];
    rewrite tmr_task_alias_field_address_eq.
  - tauto.
  - tauto.
  - unfold timer_option_offset; rewrite Hnames; tauto.
  - tauto.
  - tauto.
  - unfold timer_option_offset; rewrite Hnames.
    replace (pointer + (36 + 1)) with (pointer + 37) by lia; tauto.
Qed.

Lemma tmr_task_fields_layout_from_task_profile : forall sg,
  tmr_task_profile sg -> (forall pointer, tmr_free_layout pointer) ->
  tmr_task_fields_layout sg.
Proof.
  intros sg Hprofile Hfree; apply tmr_task_fields_layout_from_free_layout.
  - apply tmr_task_profile_timer_names; exact Hprofile.
  - exact Hfree.
Qed.

Lemma tmr_task_fields_layout_from_task_source_fields : forall sg,
  tmr_task_profile sg ->
  (forall pointer, tmr_unlink_timer_field pointer "OSTmrOpt" = pointer + 36) ->
  (forall pointer, tmr_unlink_timer_field pointer "OSTmrCallback" = pointer + 4) ->
  (forall pointer, tmr_unlink_timer_field pointer "OSTmrCallbackArg" = pointer + 8) ->
  tmr_task_fields_layout sg.
Proof.
  intros sg Hprofile Hoption Hcallback Hargument.
  apply tmr_task_fields_layout_from_unlink_fields.
  - apply tmr_task_profile_timer_names; exact Hprofile.
  - unfold tmr_task_profile in Hprofile; tauto.
  - exact Hoption.
  - exact Hcallback.
  - exact Hargument.
Qed.

(** Create's existing binding is narrower: only valid Timer pool slots.
    Its actual quantifier is retained in these consumers. It is not used
    to infer the frozen interface's forall-pointer layout proposition. *)
Lemma tmr_task_create_binding_timer_configuration : forall sg,
  tmr_create_c_bindings sg -> sg.(osKernelConfig) = selected_kernel_configuration.
Proof.
  intros sg [Halloc Hrest]; exact (proj1 Halloc).
Qed.

Lemma tmr_task_option_address_from_create_binding : forall sg index,
  tmr_create_c_bindings sg -> 0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrOpt" = timer_pool_addr sg index + 36.
Proof.
  intros sg index [_ [_ Hfields]] Hindex.
  specialize (Hfields index Hindex); cbn zeta in Hfields.
  rewrite tmr_task_alias_field_address_eq; tauto.
Qed.

Lemma tmr_task_callback_address_from_create_binding : forall sg index,
  tmr_create_c_bindings sg -> 0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrCallback" = timer_pool_addr sg index + 4.
Proof.
  intros sg index [_ [_ Hfields]] Hindex.
  specialize (Hfields index Hindex); cbn zeta in Hfields.
  rewrite tmr_task_alias_field_address_eq; tauto.
Qed.

Lemma tmr_task_argument_address_from_create_binding : forall sg index,
  tmr_create_c_bindings sg -> 0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  tmr_unlink_timer_field (timer_pool_addr sg index) "OSTmrCallbackArg" = timer_pool_addr sg index + 8.
Proof.
  intros sg index [_ [_ Hfields]] Hindex.
  specialize (Hfields index Hindex); cbn zeta in Hfields.
  rewrite tmr_task_alias_field_address_eq; tauto.
Qed.

Lemma tmr_task_pool_field_addresses_from_create_binding : forall sg index field,
  tmr_create_c_bindings sg -> tmr_unlink_layout ->
  0 <= index < sg.(osKernelConfig).(cfgMaxTimers) ->
  tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field) =
    timer_pool_addr sg index + tmr_task_image_offset sg.(osKernelConfig) field.
Proof.
  intros sg index field Hbinding [Hmatch [Hnext [_ [Hstate Hwheel]]]] Hindex.
  pose proof (tmr_task_create_binding_timer_configuration sg Hbinding) as Hconfiguration.
  assert (Hnames : sg.(osKernelConfig).(cfgTimerNames) = true).
  { rewrite Hconfiguration; reflexivity. }
  destruct field; cbn [tmr_task_image_name tmr_task_image_offset].
  - apply Hnext.
  - apply Hmatch.
  - unfold timer_option_offset; rewrite Hnames.
    apply tmr_task_option_address_from_create_binding; assumption.
  - apply tmr_task_callback_address_from_create_binding; assumption.
  - apply tmr_task_argument_address_from_create_binding; assumption.
  - unfold timer_option_offset; rewrite Hnames.
    replace (timer_pool_addr sg index + (36 + 1)) with (timer_pool_addr sg index + 37) by lia.
    apply Hstate.
Qed.

Lemma tmr_task_live_field_addresses_from_create_binding : forall sg timers index node field,
  tmr_create_c_bindings sg -> tmr_unlink_layout -> valid_timer_state sg timers ->
  timers.(timerUsed) index = Some node ->
  tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field) =
    timer_pool_addr sg index + tmr_task_image_offset sg.(osKernelConfig) field.
Proof.
  intros sg timers index node field Hbinding Hlayout Hvalid Hnode.
  apply tmr_task_pool_field_addresses_from_create_binding; try assumption.
  exact (timer_used_id_in_range sg timers index node Hvalid Hnode).
Qed.

(** The C ptmr points at this CURRENT scan index. This consumer obtains
    that index's range from the actual current owner and running source
    node, retains the owner, and returns all six concrete address facts.
    It therefore works after a callback restart without using an old map. *)
Lemma tmr_task_current_fields_scan_addresses : forall Application
  (AppRep : Application -> TmrTaskFieldsRules.expr)
  environment sg mask perr call (world : tmr_task_scan_world Application) scan index tail,
  tmr_create_c_bindings sg -> tmr_unlink_layout -> timer_api_initialized (tmr_task_timers world) ->
  timer_scan_continuation_valid sg (tmr_task_timers world) scan ->
  timerScanRemaining scan = index :: tail ->
  TmrTaskFieldsRules.derivable1
    (tmr_task_current_fields_owned AppRep environment sg mask perr call world)
    (fun heap =>
      0 <= index < sg.(osKernelConfig).(cfgMaxTimers) /\
      (forall field,
        tmr_unlink_timer_field (timer_pool_addr sg index) (tmr_task_image_name field) =
          timer_pool_addr sg index + tmr_task_image_offset sg.(osKernelConfig) field) /\
      tmr_task_current_fields_owned AppRep environment sg mask perr call world heap).
Proof.
  intros Application AppRep environment sg mask perr call world scan index tail
    Hbinding Hlayout Hinit Hscan Hremaining heap Howned.
  assert (Hen : sg.(osKernelConfig).(cfgTimerEnabled) = true).
  { rewrite (tmr_task_create_binding_timer_configuration sg Hbinding); reflexivity. }
  pose proof (proj1 (tmr_task_current_fields_timer_valid AppRep environment sg mask perr
    call world Hen Hinit heap Howned)) as Hvalid.
  destruct (timer_scan_continuation_remaining_running sg (tmr_task_timers world) scan index
    Hscan ltac:(rewrite Hremaining; left; reflexivity)) as [node [Hnode Hrunning]].
  pose proof (timer_used_id_in_range sg (tmr_task_timers world) index node Hvalid Hnode) as Hindex.
  split; [exact Hindex|]. split; [|exact Howned].
  intros field; apply tmr_task_pool_field_addresses_from_create_binding; assumption.
Qed.
