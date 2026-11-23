Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import CNotation.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.timer.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The source is an internal, caller-protected helper.  It neither locks
    nor unlinks a running timer.  The raw contract permits arbitrary old
    overwritten fields and both unsigned counter wrap cases. *)
Definition tmr_free_object_frame (p : Z) (old : TimerImage) : Assertion :=
  &(p # "os_tmr" ->ₛ "OSTmrType") # UChar |-> old.(timerImageType) **
  &(p # "os_tmr" ->ₛ "OSTmrDly") # UInt |-> old.(timerImageDelay) **
  store_optional_bytes (p + 1) (firstn 3 old.(timerImagePadding)) **
  store_optional_bytes (p + 38) (skipn 3 old.(timerImagePadding)).

Definition tmr_free_pre (p : Z) (old : TimerImage) (root used free : Z) : Assertion :=
  coq_prop (List.length old.(timerImagePadding) = 5%nat) &&
  (tmr_free_object_frame p old **
  &(p # "os_tmr" ->ₛ "OSTmrState") # UChar |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrOpt") # UChar |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrPeriod") # UInt |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrMatch") # UInt |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrCallback") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrCallbackArg") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrName") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrPrev") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrNext") # Ptr |->_ **
  &("OSTmrFreeList") # Ptr |-> root **
  &("OSTmrUsed") # UShort |-> used ** &("OSTmrFree") # UShort |-> free).

Definition tmr_free_object_cells (p : Z) (v : TimerImage) : Assertion :=
  tmr_free_object_frame p v **
  &(p # "os_tmr" ->ₛ "OSTmrState") # UChar |-> v.(timerImageState) **
  &(p # "os_tmr" ->ₛ "OSTmrOpt") # UChar |-> v.(timerImageOption) **
  &(p # "os_tmr" ->ₛ "OSTmrPeriod") # UInt |-> v.(timerImagePeriod) **
  &(p # "os_tmr" ->ₛ "OSTmrMatch") # UInt |-> v.(timerImageMatch) **
  &(p # "os_tmr" ->ₛ "OSTmrCallback") # Ptr |-> v.(timerImageCallback) **
  &(p # "os_tmr" ->ₛ "OSTmrCallbackArg") # Ptr |-> v.(timerImageArg) **
  &(p # "os_tmr" ->ₛ "OSTmrName") # Ptr |-> v.(timerImageName) **
  &(p # "os_tmr" ->ₛ "OSTmrPrev") # Ptr |-> v.(timerImagePrev) **
  &(p # "os_tmr" ->ₛ "OSTmrNext") # Ptr |-> v.(timerImageNext).

Definition tmr_free_post (p : Z) (old : TimerImage) (root used free name : Z) : Assertion :=
  tmr_free_object_cells p (timer_free_image old root name) **
  &("OSTmrFreeList") # Ptr |-> p **
  &("OSTmrUsed") # UShort |-> kernel_u16 (used - 1) **
  &("OSTmrFree") # UShort |-> kernel_u16 (free + 1).

(** Exact C access footprint. Type, delay and padding are not read or
    written by OSTmr_Free; the legacy object contract below is recovered
    by framing their REAL cells, not by cancelling them from a premise.
    The C implementation is checked against this smaller contract. *)
Definition tmr_free_write_pre (p root used free : Z) : Assertion :=
  &(p # "os_tmr" ->ₛ "OSTmrState") # UChar |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrOpt") # UChar |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrPeriod") # UInt |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrMatch") # UInt |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrCallback") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrCallbackArg") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrName") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrPrev") # Ptr |->_ **
  &(p # "os_tmr" ->ₛ "OSTmrNext") # Ptr |->_ **
  &("OSTmrFreeList") # Ptr |-> root **
  &("OSTmrUsed") # UShort |-> used ** &("OSTmrFree") # UShort |-> free.

Definition tmr_free_write_post (p root used free name : Z) : Assertion :=
  &(p # "os_tmr" ->ₛ "OSTmrState") # UChar |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrOpt") # UChar |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrPeriod") # UInt |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrMatch") # UInt |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrCallback") # Ptr |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrCallbackArg") # Ptr |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrName") # Ptr |-> name **
  &(p # "os_tmr" ->ₛ "OSTmrPrev") # Ptr |-> 0 **
  &(p # "os_tmr" ->ₛ "OSTmrNext") # Ptr |-> root **
  &("OSTmrFreeList") # Ptr |-> p **
  &("OSTmrUsed") # UShort |-> kernel_u16 (used - 1) **
  &("OSTmrFree") # UShort |-> kernel_u16 (free + 1).

Lemma tmr_free_raw_spec_consequence : forall p old root used free (LitMap : string -> Z),
  tmr_free_pre p old root used free ** GlobalStrings LitMap |--
  (tmr_free_write_pre p root used free ** GlobalStrings LitMap) **
  ((tmr_free_write_post p root used free (LitMap "?") ** GlobalStrings LitMap) -*
    (tmr_free_post p old root used free (LitMap "?") ** GlobalStrings LitMap)).
Proof.
  intros.
  assert (Hreturn : tmr_free_object_frame p old |--
    (tmr_free_write_post p root used free (LitMap "?") ** GlobalStrings LitMap) -*
    (tmr_free_post p old root used free (LitMap "?") ** GlobalStrings LitMap)).
  { apply_sepcon_adjoint.
    unfold tmr_free_write_post, tmr_free_post, tmr_free_object_cells,
      tmr_free_object_frame, timer_free_image; cbn; entailer!. }
  unfold tmr_free_pre, tmr_free_write_pre; Intros.
  sep_apply_l_atomic Hreturn.
  entailer!.
Qed.

(** ABI premises bind the frontend's actual arrow expressions, rather
    than equating two unrelated field-address parameters.  The selected
    source/profile fixes these layout facts; no layout axiom is added. *)
Definition tmr_free_layout (p : Z) : Prop :=
  sizeof_struct_type "os_tmr" = 40 /\
  &(p # "os_tmr" ->ₛ "OSTmrType") = p /\
  &(p # "os_tmr" ->ₛ "OSTmrCallback") = p + 4 /\
  &(p # "os_tmr" ->ₛ "OSTmrCallbackArg") = p + 8 /\
  &(p # "os_tmr" ->ₛ "OSTmrNext") = p + 12 /\
  &(p # "os_tmr" ->ₛ "OSTmrPrev") = p + 16 /\
  &(p # "os_tmr" ->ₛ "OSTmrMatch") = p + 20 /\
  &(p # "os_tmr" ->ₛ "OSTmrDly") = p + 24 /\
  &(p # "os_tmr" ->ₛ "OSTmrPeriod") = p + 28 /\
  &(p # "os_tmr" ->ₛ "OSTmrName") = p + 32 /\
  &(p # "os_tmr" ->ₛ "OSTmrOpt") = p + 36 /\
  &(p # "os_tmr" ->ₛ "OSTmrState") = p + 37.

Definition tmr_free_bindings (sg : StableGlobVars) (p : Z) : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  sg.(g_OSTmrFreeList) = &("OSTmrFreeList") /\
  sg.(g_OSTmrUsed) = &("OSTmrUsed") /\
  sg.(g_OSTmrFree) = &("OSTmrFree") /\ tmr_free_layout p.

Definition tmr_free_valid_input (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (t : TimerObjectState) (old : TimerImage) (p : Z) : Prop :=
  tmr_free_bindings sg p /\ p = timer_pool_addr sg i /\
  timer_api_initialized s /\ s.(timerUsed) i = Some t /\
  s.(timerImages) i = Some old /\ t.(timerState) <> TimerRunning.

Definition tmr_free_valid_post (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (old : TimerImage) (name : Z) : Assertion :=
  let post := timer_release sg s i old name in
  coq_prop (timer_api_initialized post /\
    post.(timerUsedCount) = s.(timerUsedCount) - 1 /\
    post.(timerFreeCount) = s.(timerFreeCount) + 1) && timer_inv sg post.

Definition tmr_free_residual (sg : StableGlobVars) (s : GlobTimerState) (i : TimerID) : Assertion :=
  timer_images_without sg s i **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  sg.(g_OSTmrTime) # UInt |-> s.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> s.(timerSem) **
  sg.(g_OSTmrSemSignal) # Ptr |-> s.(timerSignalSem).

Lemma tmr_free_object_rep_split : forall p old,
  tmr_free_layout p ->
  timer_object_rep selected_kernel_configuration p old |--
  tmr_free_object_cells p old.
Proof.
  intros p old H; unfold tmr_free_layout in H; destruct H as
    [_ [Hty [Hcb [Harg [Hnext [Hprev [Hmatch [Hdly [Hperiod [Hname [Hopt Hstate]]]]]]]]]]].
  unfold timer_object_rep, tmr_free_object_cells, tmr_free_object_frame, timer_option_offset;
    simpl; rewrite Hty, Hcb, Harg, Hnext, Hprev, Hmatch, Hdly, Hperiod, Hname, Hopt, Hstate.
  replace (p + 36 + 1) with (p + 37) by lia.
  replace (p + 36 + 2) with (p + 38) by lia.
  entailer!.
Qed.

Lemma tmr_free_object_rep_merge : forall p old,
  tmr_free_layout p ->
  tmr_free_object_cells p old |-- timer_object_rep selected_kernel_configuration p old.
Proof.
  intros p old H; unfold tmr_free_layout in H; destruct H as
    [_ [Hty [Hcb [Harg [Hnext [Hprev [Hmatch [Hdly [Hperiod [Hname [Hopt Hstate]]]]]]]]]]].
  unfold timer_object_rep, tmr_free_object_cells, tmr_free_object_frame, timer_option_offset;
    simpl; rewrite Hty, Hcb, Harg, Hnext, Hprev, Hmatch, Hdly, Hperiod, Hname, Hopt, Hstate.
  replace (p + 36 + 1) with (p + 37) by lia.
  replace (p + 36 + 2) with (p + 38) by lia.
  entailer!.
Qed.

Lemma tmr_free_counter_bounds : forall sg s i t,
  sg.(osKernelConfig).(cfgMaxTimers) = 16 -> valid_timer_state sg s ->
  s.(timerUsed) i = Some t ->
  0 < s.(timerUsedCount) <= 16 /\ 0 <= s.(timerFreeCount) < 16.
Proof.
  intros sg s i t Hcap Hvalid Hlookup.
  destruct Hvalid as [Hpool [_ [_ [Hfreecount [Hsum [Hfc [Huc Hrest]]]]]]].
  assert (Halloc : timer_allocated_slots s i = Some tt).
  { unfold timer_allocated_slots; rewrite Hlookup; reflexivity. }
  pose proof (kernel_pool_release_preserves_partition unit _ _ _ i tt Hpool Halloc) as Hreleased.
  pose proof (kernel_pool_free_count_bound unit (cfgMaxTimers (osKernelConfig sg))
    (i :: timerFree s) (kernel_map_set (timer_allocated_slots s) i None)
    ltac:(lia) Hreleased) as Hcount.
  change (0 <= Z.of_nat (S (List.length (timerFree s))) <=
    cfgMaxTimers (osKernelConfig sg)) in Hcount.
  rewrite Nat2Z.inj_succ in Hcount; lia.
Qed.

Lemma tmr_free_counters_no_wrap : forall sg s i t,
  sg.(osKernelConfig).(cfgMaxTimers) = 16 -> valid_timer_state sg s ->
  s.(timerUsed) i = Some t ->
  kernel_u16 (s.(timerUsedCount) - 1) = s.(timerUsedCount) - 1 /\
  kernel_u16 (s.(timerFreeCount) + 1) = s.(timerFreeCount) + 1.
Proof.
  intros; pose proof (tmr_free_counter_bounds sg s i t H H0 H1).
  split; apply kernel_u16_identity; lia.
Qed.

Lemma tmr_free_split_timer_rep : forall sg s i old p,
  tmr_free_bindings sg p -> p = timer_pool_addr sg i -> s.(timerImages) i = Some old ->
  List.length old.(timerImagePadding) = 5%nat ->
  timer_raw_rep sg s |--
  tmr_free_pre p old (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount) s.(timerFreeCount) **
  tmr_free_residual sg s i.
Proof.
  intros sg s i old p [Hcfg [Hroot [Hused [Hfree Hlayout]]]] Hp Hold Hpadding.
  unfold timer_raw_rep.
  sep_apply_l_atomic (timer_images_split_object sg s i old Hold).
  rewrite <- Hp, Hcfg.
  sep_apply_l_atomic (tmr_free_object_rep_split p old Hlayout).
  unfold tmr_free_pre, tmr_free_object_cells, tmr_free_residual, timer_globals_rep.
  rewrite Hroot, Hused, Hfree; entailer!.
  sep_apply_l_atomic (store_uchar_undef_store_uchar &(p # "os_tmr" ->ₛ "OSTmrState") (timerImageState old)).
  sep_apply_l_atomic (store_uchar_undef_store_uchar &(p # "os_tmr" ->ₛ "OSTmrOpt") (timerImageOption old)).
  sep_apply_l_atomic (store_uint_undef_store_uint &(p # "os_tmr" ->ₛ "OSTmrPeriod") (timerImagePeriod old)).
  sep_apply_l_atomic (store_uint_undef_store_uint &(p # "os_tmr" ->ₛ "OSTmrMatch") (timerImageMatch old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &(p # "os_tmr" ->ₛ "OSTmrCallback") (timerImageCallback old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &(p # "os_tmr" ->ₛ "OSTmrCallbackArg") (timerImageArg old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &(p # "os_tmr" ->ₛ "OSTmrName") (timerImageName old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &(p # "os_tmr" ->ₛ "OSTmrPrev") (timerImagePrev old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr &(p # "os_tmr" ->ₛ "OSTmrNext") (timerImageNext old)).
  entailer!.
Qed.

Lemma tmr_free_merge_timer_rep : forall sg s i old p name,
  tmr_free_bindings sg p -> p = timer_pool_addr sg i ->
  tmr_free_post p old (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount) s.(timerFreeCount) name **
  tmr_free_residual sg s i |-- timer_raw_rep sg (timer_release sg s i old name).
Proof.
  intros sg s i old p name [Hcfg [Hroot [Hused [Hfree Hlayout]]]] Hp.
  unfold tmr_free_post, tmr_free_residual.
  sep_apply_l_atomic (tmr_free_object_rep_merge p
    (timer_free_image old (timer_id_pointer sg (timerFree s)) name) Hlayout).
  rewrite Hp, <- Hcfg.
  sep_apply_l_atomic (timer_images_merge_updated_object sg s (timer_release sg s i old name) i
    (timer_free_image old (timer_id_pointer sg (timerFree s)) name)
    (kernel_map_set_same _ _ _ _)
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption)).
  unfold timer_raw_rep, timer_globals_rep, timer_release; simpl.
  rewrite Hroot, Hused, Hfree; entailer!.
Qed.

Lemma tmr_free_valid_release : forall sg s i t old p name,
  tmr_free_valid_input sg s i t old p -> valid_timer_configuration sg s ->
  valid_timer_configuration sg (timer_release sg s i old name) /\
  timer_api_initialized (timer_release sg s i old name) /\
  (timer_release sg s i old name).(timerUsedCount) = s.(timerUsedCount) - 1 /\
  (timer_release sg s i old name).(timerFreeCount) = s.(timerFreeCount) + 1.
Proof.
  intros sg s i t old p name [[Hcfg Hbindings] [Hp [Hinit [Ht [Hold Hst]]]]] Hv.
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  pose proof (timer_release_preserves_configuration sg s i t old name He
    ltac:(rewrite Hcfg; simpl; lia) Hv Hinit Ht Hold Hst) as [Hpost Hipost].
  pose proof (tmr_free_counters_no_wrap sg s i t ltac:(rewrite Hcfg; reflexivity)
    (proj1 (timer_initialized_configuration_iff sg s He Hinit) Hv) Ht) as [Huc Hfc].
  repeat split; assumption.
Qed.

Lemma tmr_free_residual_closes_valid_post : forall sg s i t old p (LitMap : string -> Z),
  tmr_free_valid_input sg s i t old p -> valid_timer_configuration sg s ->
  tmr_free_residual sg s i |--
  (tmr_free_post p old (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount)
     s.(timerFreeCount) (LitMap "?") ** GlobalStrings LitMap) -*
  (tmr_free_valid_post sg s i old (LitMap "?") ** GlobalStrings LitMap).
Proof.
  intros sg s i t old p LitMap Hinput Hvalid.
  pose proof (tmr_free_valid_release sg s i t old p (LitMap "?") Hinput Hvalid)
    as [Hv [Hinit [Hused Hfree]]].
  destruct Hinput as [Hbindings [Hp Hrest]].
  destruct Hbindings as [Hcfg Hbindings'].
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  apply_sepcon_adjoint.
  sep_apply_l_atomic (tmr_free_merge_timer_rep sg s i old p (LitMap "?")
    ltac:(split; assumption) Hp).
  unfold tmr_free_valid_post, timer_inv.
  rewrite timer_initialized_configured_rep_eq by assumption.
  entailer!.
Qed.

(** This is the resource consequence consumed by QCP's derived C spec.
    The wand retains the real non-target resources throughout raw writes;
    the new validity is proved from the entry state, never assumed. *)
Lemma tmr_free_valid_spec_consequence : forall sg s i t old p (LitMap : string -> Z),
  coq_prop (tmr_free_valid_input sg s i t old p) &&
  timer_inv sg s ** GlobalStrings LitMap |--
  (tmr_free_pre p old (timer_id_pointer sg s.(timerFree))
      s.(timerUsedCount) s.(timerFreeCount) ** GlobalStrings LitMap) **
  ((tmr_free_post p old (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount)
      s.(timerFreeCount) (LitMap "?") ** GlobalStrings LitMap) -*
   (tmr_free_valid_post sg s i old (LitMap "?") ** GlobalStrings LitMap)).
Proof.
  intros sg s i t old p LitMap; Intros.
  match goal with H : tmr_free_valid_input sg s i t old p |- _ => rename H into Hinput end.
  unfold timer_inv; Intros.
  match goal with H : valid_timer_configuration sg s |- _ => rename H into Hvalid end.
  pose proof Hinput as [Hbindings [Hp [Hinit [Ht [Hold Hst]]]]].
  destruct Hbindings as [Hcfg Hbindings'].
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  pose proof (proj1 (timer_initialized_configuration_iff sg s He Hinit) Hvalid) as Hstate.
  assert (Hpadding : List.length old.(timerImagePadding) = 5%nat).
  { unfold valid_timer_state in Hstate; decompose [and] Hstate.
    match goal with H : forall j v, timerImages s j = Some v -> _ |- _ =>
      exact (H i old Hold) end. }
  rewrite timer_initialized_configured_rep_eq by assumption.
  sep_apply_l_atomic (tmr_free_split_timer_rep sg s i old p
    ltac:(split; assumption) Hp Hold Hpadding).
  sep_apply_l_atomic (tmr_free_residual_closes_valid_post sg s i t old p LitMap Hinput Hvalid).
  entailer!.
Qed.

(** A caller may retain the type view outside its exclusive pool body.
    Delay and padding are real framed bytes; only the proved write_spec's
    access footprint is passed to C. No type ownership is manufactured. *)
Definition tmr_free_body_frame (p : Z) (old : TimerImage) : Assertion :=
  &(p # "os_tmr" ->ₛ "OSTmrDly") # UInt |-> old.(timerImageDelay) **
  store_optional_bytes (p + 1) (firstn 3 old.(timerImagePadding)) **
  store_optional_bytes (p + 38) (skipn 3 old.(timerImagePadding)).

Definition tmr_free_body_residual (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (old : TimerImage) (p : Z) : Assertion :=
  tmr_free_body_frame p old ** timer_images_without_types_missing_object sg s i **
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel).

Definition tmr_free_body_post (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (old : TimerImage) (name : Z) : Assertion :=
  let post := timer_release sg s i old name in
  coq_prop (valid_timer_configuration sg post /\ timer_api_initialized post /\
    post.(timerUsedCount) = s.(timerUsedCount) - 1 /\
    post.(timerFreeCount) = s.(timerFreeCount) + 1) && timer_pool_rep_without_types sg post.

Lemma tmr_free_split_pool_body : forall sg s i old p,
  tmr_free_bindings sg p -> p = timer_pool_addr sg i -> s.(timerImages) i = Some old ->
  timer_pool_rep_without_types sg s |--
  tmr_free_write_pre p (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount) s.(timerFreeCount) **
  tmr_free_body_residual sg s i old p.
Proof.
  intros sg s i old p [Hcfg [Hroot [Hused [Hfree Hlayout]]]] Hp Hold.
  destruct Hlayout as [_ [Hty [Hcb [Harg [Hnext [Hprev [Hmatch [Hdly [Hperiod [Hname [Hopt Hstate]]]]]]]]]]].
  unfold timer_pool_rep_without_types.
  sep_apply_l_atomic (timer_images_without_types_split_object sg s i old Hold).
  rewrite <- Hp, Hcfg.
  unfold tmr_free_write_pre, tmr_free_body_residual, tmr_free_body_frame,
    timer_object_rep_without_type, timer_option_offset; simpl.
  rewrite Hroot, Hused, Hfree, Hcb, Harg, Hnext, Hprev, Hmatch, Hdly, Hperiod,
    Hname, Hopt, Hstate.
  replace (p + 36 + 1) with (p + 37) by lia.
  replace (p + 36 + 2) with (p + 38) by lia.
  sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 37) (timerImageState old)).
  sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 36) (timerImageOption old)).
  sep_apply_l_atomic (store_uint_undef_store_uint (p + 28) (timerImagePeriod old)).
  sep_apply_l_atomic (store_uint_undef_store_uint (p + 20) (timerImageMatch old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 4) (timerImageCallback old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 8) (timerImageArg old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 32) (timerImageName old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 16) (timerImagePrev old)).
  sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 12) (timerImageNext old)).
  entailer!.
Qed.

Lemma tmr_free_merge_pool_body : forall sg s i old p name,
  tmr_free_bindings sg p -> p = timer_pool_addr sg i ->
  tmr_free_write_post p (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount)
    s.(timerFreeCount) name ** tmr_free_body_residual sg s i old p |--
  timer_pool_rep_without_types sg (timer_release sg s i old name).
Proof.
  intros sg s i old p name [Hcfg [Hroot [Hused [Hfree Hlayout]]]] Hp.
  assert (Hobject : tmr_free_write_post p (timer_id_pointer sg s.(timerFree))
    s.(timerUsedCount) s.(timerFreeCount) name ** tmr_free_body_frame p old |--
    timer_object_rep_without_type selected_kernel_configuration p
      (timer_free_image old (timer_id_pointer sg s.(timerFree)) name) **
    sg.(g_OSTmrFreeList) # Ptr |-> p **
    sg.(g_OSTmrUsed) # UShort |-> kernel_u16 (s.(timerUsedCount) - 1) **
    sg.(g_OSTmrFree) # UShort |-> kernel_u16 (s.(timerFreeCount) + 1)).
  { destruct Hlayout as [_ [Hty [Hcb [Harg [Hnext [Hprev [Hmatch [Hdly [Hperiod [Hname [Hopt Hstate]]]]]]]]]]].
    unfold tmr_free_write_post, tmr_free_body_frame, timer_object_rep_without_type,
      timer_free_image, timer_option_offset; simpl.
    rewrite Hroot, Hused, Hfree, Hcb, Harg, Hnext, Hprev, Hmatch, Hdly, Hperiod,
      Hname, Hopt, Hstate.
    replace (p + 36 + 1) with (p + 37) by lia.
    replace (p + 36 + 2) with (p + 38) by lia; entailer!. }
  unfold tmr_free_body_residual; sep_apply_l_atomic Hobject.
  rewrite Hp, <- Hcfg.
  sep_apply_l_atomic (timer_images_without_types_merge_updated_object sg s
    (timer_release sg s i old name) i
    (timer_free_image old (timer_id_pointer sg s.(timerFree)) name)
    (kernel_map_set_same _ _ _ _)
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption)).
  unfold timer_pool_rep_without_types, timer_release; simpl; entailer!.
Qed.

Lemma tmr_free_body_spec_consequence : forall sg s i t old p (LitMap : string -> Z),
  tmr_free_valid_input sg s i t old p -> valid_timer_configuration sg s ->
  timer_pool_rep_without_types sg s ** GlobalStrings LitMap |--
  (tmr_free_write_pre p (timer_id_pointer sg s.(timerFree))
      s.(timerUsedCount) s.(timerFreeCount) ** GlobalStrings LitMap) **
  ((tmr_free_write_post p (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount)
      s.(timerFreeCount) (LitMap "?") ** GlobalStrings LitMap) -*
   (tmr_free_body_post sg s i old (LitMap "?") ** GlobalStrings LitMap)).
Proof.
  intros sg s i t old p LitMap Hinput Hvalid.
  pose proof Hinput as [Hbindings [Hp [Hinit [Ht [Hold Hst]]]]].
  pose proof (tmr_free_valid_release sg s i t old p (LitMap "?") Hinput Hvalid)
    as [Hv [Hinitialized [Hused Hfree]]].
  assert (Hreturn : tmr_free_body_residual sg s i old p |--
    (tmr_free_write_post p (timer_id_pointer sg s.(timerFree)) s.(timerUsedCount)
      s.(timerFreeCount) (LitMap "?") ** GlobalStrings LitMap) -*
    (tmr_free_body_post sg s i old (LitMap "?") ** GlobalStrings LitMap)).
  { apply_sepcon_adjoint.
    sep_apply_l_atomic (tmr_free_merge_pool_body sg s i old p (LitMap "?") Hbindings Hp).
    unfold tmr_free_body_post; entailer!. }
  sep_apply_l_atomic (tmr_free_split_pool_body sg s i old p Hbindings Hp Hold).
  sep_apply_l_atomic Hreturn; entailer!.
Qed.
