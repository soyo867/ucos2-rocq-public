Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import CNotation Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.timer.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is an explicit selected-C/ABI interpretation boundary, not an
    equality with SeparationLogic.field_address.  These terms are the
    CNotation alias-arrow terms emitted by QCP for the selected C tags;
    plain [p # tag] and [sizeof(tag)] use the alias vocabulary even when
    the selected C declaration is a struct. *)
Definition tmr_unlink_timer_field (p : Z) (field : string) : Z :=
  eval_addr_expr (RE_addr_of
    (LE_arrow_field (RE_const p (FET_alias "os_tmr")) field)).
Definition tmr_unlink_wheel_field (p : Z) (field : string) : Z :=
  eval_addr_expr (RE_addr_of
    (LE_arrow_field (RE_const p (FET_alias "os_tmr_wheel")) field)).
Definition tmr_unlink_wheel_size : Prop :=
  sizeof_alias_type "os_tmr_wheel" = 8.
Definition tmr_unlink_layout : Prop :=
  (forall p, tmr_unlink_timer_field p "OSTmrMatch" = p + 20) /\
  (forall p, tmr_unlink_timer_field p "OSTmrNext" = p + 12) /\
  (forall p, tmr_unlink_timer_field p "OSTmrPrev" = p + 16) /\
  (forall p, tmr_unlink_timer_field p "OSTmrState" = p + 37) /\
  (forall p, tmr_unlink_wheel_field p "OSTmrFirst" = p) /\
  (forall p, tmr_unlink_wheel_field p "OSTmrEntries" = p + 4) /\
  tmr_unlink_wheel_size.

Definition tmr_unlink_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgTimerEnabled) = true /\
  sg.(osKernelConfig).(cfgTimerNames) = true /\
  sg.(osKernelConfig).(cfgMaxTimers) = 16 /\
  sg.(osKernelConfig).(cfgTimerWheelSize) = 7 /\
  kernel_region_valid (sg.(g_OSTmrTbl), 40 * 16) /\
  kernel_region_valid (sg.(g_OSTmrWheelTbl), 8 * 7).

Definition tmr_unlink_running (s : GlobTimerState) (i : Z) : Prop :=
  exists t, s.(timerUsed) i = Some t /\ t.(timerState) = TimerRunning.

Definition tmr_unlink_configured_post (sg : StableGlobVars)
  (s : GlobTimerState) (i : Z) : Assertion :=
  EX post, coq_prop (timer_unlink sg s i = Some post /\ timer_api_initialized post) &&
    timer_inv sg post.

Definition tmr_unlink_spoke_addr (base match_time : Z) : Z :=
  base + 8 * (match_time mod 7).

(** The low-level contract owns only the real read/write cells.  R retains
    every other object field, all padding, untouched objects and spokes,
    Timer globals, and any disjoint caller resource.  It does not retain an
    unmodified whole-Timer invariant across the link mutations. *)
Definition tmr_unlink_neighbor_pre (p next prev first : Z) : Assertion :=
  (if Z.eq_dec first p then emp
   else tmr_unlink_timer_field prev "OSTmrNext" # Ptr |-> p) **
  (if Z.eq_dec next 0 then emp
   else tmr_unlink_timer_field next "OSTmrPrev" # Ptr |-> p).

Definition tmr_unlink_neighbor_post (p next prev first : Z) : Assertion :=
  (if Z.eq_dec first p then emp
   else tmr_unlink_timer_field prev "OSTmrNext" # Ptr |-> next) **
  (if Z.eq_dec next 0 then emp
   else tmr_unlink_timer_field next "OSTmrPrev" # Ptr |->
     (if Z.eq_dec first p then 0 else prev)).

Definition tmr_unlink_neighbor_bounds (p next prev first : Z) : Prop :=
  (first <> p -> 0 < prev /\ prev + 40 <= 4294967296) /\
  (next <> 0 -> 0 < next /\ next + 40 <= 4294967296).

Definition tmr_unlink_raw_pre
  (p base match_time next prev first entries : Z) (R : Assertion) : Assertion :=
  coq_prop (tmr_unlink_wheel_size /\ 0 < p /\ p + 40 <= 4294967296 /\
    0 < base /\ base + 56 <= 4294967296 /\
    0 <= match_time < 4294967296 /\ 0 <= entries < 65536 /\
    tmr_unlink_neighbor_bounds p next prev first) &&
  tmr_unlink_timer_field p "OSTmrMatch" # UInt |-> match_time **
  tmr_unlink_timer_field p "OSTmrNext" # Ptr |-> next **
  tmr_unlink_timer_field p "OSTmrPrev" # Ptr |-> prev **
  tmr_unlink_timer_field p "OSTmrState" # UChar |->_ **
  tmr_unlink_wheel_field (tmr_unlink_spoke_addr base match_time) "OSTmrFirst" # Ptr |-> first **
  tmr_unlink_wheel_field (tmr_unlink_spoke_addr base match_time) "OSTmrEntries" # UShort |-> entries **
  tmr_unlink_neighbor_pre p next prev first ** R.

Definition tmr_unlink_raw_post
  (p base match_time next prev first entries : Z) (R : Assertion) : Assertion :=
  tmr_unlink_timer_field p "OSTmrMatch" # UInt |-> match_time **
  tmr_unlink_timer_field p "OSTmrNext" # Ptr |-> 0 **
  tmr_unlink_timer_field p "OSTmrPrev" # Ptr |-> 0 **
  tmr_unlink_timer_field p "OSTmrState" # UChar |-> 1 **
  tmr_unlink_wheel_field (tmr_unlink_spoke_addr base match_time) "OSTmrFirst" # Ptr |->
    (if Z.eq_dec first p then next else first) **
  tmr_unlink_wheel_field (tmr_unlink_spoke_addr base match_time) "OSTmrEntries" # UShort |->
    kernel_u16 (entries - 1) **
  tmr_unlink_neighbor_post p next prev first ** R.

Lemma tmr_unlink_profile_object_size : forall sg,
  tmr_unlink_profile sg -> timer_object_size sg.(osKernelConfig) = 40.
Proof.
  intros sg [_ [Hnames _]]. unfold timer_object_size, timer_option_offset.
  rewrite Hnames; reflexivity.
Qed.

(** Function-local field slices.  All nonwritten fields and both padding
    regions are retained verbatim; Match is exposed and returned unchanged. *)
(** One proof covers the full object and its body without the type byte.
    include_type selects ownership, not a C branch or a weaker raw contract. *)
Definition tmr_unlink_object_view (include_type : bool) (c : KernelConfiguration)
  (p : Z) (v : TimerImage) : Assertion :=
  if include_type then timer_object_rep c p v else timer_object_rep_without_type c p v.

Section UnlinkObjectView.
Variable include_type : bool.

Definition tmr_unlink_object_frame (c : KernelConfiguration) (p : Z)
  (v : TimerImage) : Assertion :=
  (if include_type then p # UChar |-> v.(timerImageType) else emp) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) **
  (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 v.(timerImagePadding)).

Lemma tmr_unlink_object_split_fields : forall c p v,
  tmr_unlink_object_view include_type c p v |--
  (p + 12) # Ptr |-> v.(timerImageNext) **
  (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) **
  (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
  tmr_unlink_object_frame c p v.
Proof.
  intros; unfold tmr_unlink_object_view, tmr_unlink_object_frame;
    destruct include_type; unfold timer_object_rep, timer_object_rep_without_type; entailer!.
Qed.

Lemma tmr_unlink_object_merge_stopped : forall c p v,
  (p + 12) # Ptr |-> 0 ** (p + 16) # Ptr |-> 0 **
  (p + 20) # UInt |-> v.(timerImageMatch) **
  (p + timer_option_offset c + 1) # UChar |-> 1 **
  tmr_unlink_object_frame c p v |-- tmr_unlink_object_view include_type c p (timer_unlink_image v).
Proof.
  intros; unfold tmr_unlink_object_view, tmr_unlink_object_frame;
    destruct include_type; unfold timer_object_rep, timer_object_rep_without_type,
      timer_unlink_image; simpl; entailer!.
Qed.

Lemma tmr_unlink_object_merge_links : forall c p v next prev,
  (p + 12) # Ptr |-> next ** (p + 16) # Ptr |-> prev **
  (p + 20) # UInt |-> v.(timerImageMatch) **
  (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
  tmr_unlink_object_frame c p v |-- tmr_unlink_object_view include_type c p (timer_image_set_links v next prev).
Proof.
  intros; unfold tmr_unlink_object_view, tmr_unlink_object_frame;
    destruct include_type; unfold timer_object_rep, timer_object_rep_without_type,
      timer_image_set_links; simpl; entailer!.
Qed.

(** Reuse QCP's store_map split/missing/update laws; removing the focused
    key exposes a store_map on which the next distinct neighbor can focus. *)
Lemma tmr_unlink_images_split_object : forall sg images i v,
  images i = Some v ->
  store_map (fun j image => tmr_unlink_object_view include_type sg.(osKernelConfig) (timer_pool_addr sg j) image) images |--
  tmr_unlink_object_view include_type sg.(osKernelConfig) (timer_pool_addr sg i) v **
  store_map (fun j image => tmr_unlink_object_view include_type sg.(osKernelConfig) (timer_pool_addr sg j) image)
    (kernel_map_set images i None).
Proof.
  intros sg images i v H.
  sep_apply_l_atomic (store_map_split
    (fun j image => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) image) i v images H).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun j image => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) image)
    images (kernel_map_set images i None) i ltac:(intros; rewrite kernel_map_set_other by assumption; reflexivity))).
  sep_apply_l_atomic (store_map_missing_equiv_store_map
    (fun j image => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) image)
    (kernel_map_set images i None) i (kernel_map_set_same _ _ _ _)).
  entailer!.
Qed.

Lemma tmr_unlink_images_merge_updated_object : forall sg images i v,
  tmr_unlink_object_view include_type sg.(osKernelConfig) (timer_pool_addr sg i) v **
  store_map (fun j image => tmr_unlink_object_view include_type sg.(osKernelConfig) (timer_pool_addr sg j) image)
    (kernel_map_set images i None) |--
  store_map (fun j image => tmr_unlink_object_view include_type sg.(osKernelConfig) (timer_pool_addr sg j) image)
    (kernel_map_set images i (Some v)).
Proof.
  intros sg images i v.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun j image => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) image)
    (kernel_map_set images i None) i (kernel_map_set_same _ _ _ _)).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun j image => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) image)
    (kernel_map_set images i None) (kernel_map_set images i (Some v)) i
    ltac:(intros; rewrite !kernel_map_set_other by assumption; reflexivity))).
  sep_apply_l_atomic (store_map_merge
    (fun j image => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) image)
    i v (kernel_map_set images i (Some v)) (kernel_map_set_same _ _ _ _)).
  entailer!.
Qed.

Fixpoint tmr_unlink_wheel_without_spoke (sg : StableGlobVars) (p : Z)
  (wheel : list (list Z)) (n : nat) : Assertion :=
  match wheel, n with
  | [], _ => emp
  | row :: rest, O => UCharArray.undef_full (p + 6) 2 **
      timer_wheel_rep_from sg (p + 8) rest
  | row :: rest, S k => p # Ptr |-> timer_id_pointer sg row **
      (p + 4) # UShort |-> Z.of_nat (List.length row) **
      UCharArray.undef_full (p + 6) 2 **
      tmr_unlink_wheel_without_spoke sg (p + 8) rest k
  end.

Lemma tmr_unlink_wheel_split_spoke : forall sg wheel n row p,
  nth_error wheel n = Some row -> timer_wheel_rep_from sg p wheel |--
  (p + 8 * Z.of_nat n) # Ptr |-> timer_id_pointer sg row **
  (p + 8 * Z.of_nat n + 4) # UShort |-> Z.of_nat (List.length row) **
  tmr_unlink_wheel_without_spoke sg p wheel n.
Proof.
  intros sg wheel; induction wheel as [|head rest IH]; intros n row p H;
    destruct n as [|n]; simpl in H; try discriminate.
  - injection H as E; subst head; simpl.
    replace (p + 0) with p by lia; entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (p + 8 * Z.succ (Z.of_nat n)) with (p + 8 + 8 * Z.of_nat n) by lia.
    cbn [timer_wheel_rep_from tmr_unlink_wheel_without_spoke].
    sep_apply_l_atomic (IH n row (p + 8) H).
    entailer!.
Qed.

Lemma tmr_unlink_wheel_merge_updated_spoke : forall sg wheel n row new p,
  nth_error wheel n = Some row ->
  (p + 8 * Z.of_nat n) # Ptr |-> timer_id_pointer sg new **
  (p + 8 * Z.of_nat n + 4) # UShort |-> Z.of_nat (List.length new) **
  tmr_unlink_wheel_without_spoke sg p wheel n |--
  timer_wheel_rep_from sg p (timer_wheel_update wheel n new).
Proof.
  intros sg wheel; induction wheel as [|head rest IH]; intros n row new p H;
    destruct n as [|n]; simpl in H; try discriminate.
  - simpl; replace (p + 0) with p by lia; entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (p + 8 * Z.succ (Z.of_nat n)) with (p + 8 + 8 * Z.of_nat n) by lia.
    cbn [timer_wheel_rep_from timer_wheel_update tmr_unlink_wheel_without_spoke].
    sep_apply_r_atomic (IH n row new (p + 8) H); entailer!.
Qed.

Lemma tmr_unlink_profile_pool_region : forall sg,
  tmr_unlink_profile sg ->
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)).
Proof.
  intros sg H; rewrite (tmr_unlink_profile_object_size sg H).
  destruct H as [_ [_ [Hcap [_ [Hpool _]]]]]; rewrite Hcap; exact Hpool.
Qed.

Lemma tmr_unlink_spoke_in_range : forall match_time,
  0 <= match_time mod 7 < 7.
Proof. intros; apply Z.mod_pos_bound; lia. Qed.

Lemma tmr_unlink_configured_successor : forall sg s i,
  tmr_unlink_profile sg -> valid_timer_configuration sg s ->
  timer_api_initialized s -> tmr_unlink_running s i ->
  exists post, timer_unlink sg s i = Some post /\
    valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i Hprofile Hvalid Hinit [t [Ht Hrun]].
  pose proof Hprofile as [He _].
  pose proof (proj1 (timer_initialized_configuration_iff sg s He Hinit) Hvalid) as Hstate.
  pose proof Hstate as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [_ [_ [_ [v [Hv _]]]]].
  destruct (timer_unlink_result_exists sg s i t v Ht Hv) as [post Hstep].
  exists post; split; [exact Hstep|].
  eapply timer_unlink_preserves_configuration; eauto.
  apply tmr_unlink_profile_pool_region; exact Hprofile.
Qed.

Lemma tmr_unlink_row_entries_decrease : forall sg s n row i,
  tmr_unlink_profile sg -> valid_timer_state sg s ->
  nth_error s.(timerWheel) n = Some row -> In i row ->
  0 < Z.of_nat (List.length row) < 65536 /\
  kernel_u16 (Z.of_nat (List.length row) - 1) =
    Z.of_nat (List.length (remove Z.eq_dec i row)).
Proof.
  intros sg s n row i Hprofile Hvalid Hrow Hin.
  pose proof Hprofile as [_ [_ [Hcap _]]].
  pose proof (timer_wheel_row_entries_in_range sg s n row ltac:(lia) Hvalid Hrow) as Hrange.
  pose proof Hvalid as [_ [[_ [Hnd _]] _]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  apply in_split in Hin; destruct Hin as [pre [rest Heq]].
  rewrite Heq in *.
  rewrite remove_app; simpl.
  destruct (Z.eq_dec i i); [|contradiction].
  apply NoDup_remove in Hrownd; destruct Hrownd as [Hremaining_nd Hnot].
  assert (Hpre : ~ In i pre) by (intro H; apply Hnot; apply in_or_app; auto).
  assert (Hrest : ~ In i rest) by (intro H; apply Hnot; apply in_or_app; auto).
  rewrite !notin_remove by assumption.
  rewrite !app_length in *; simpl in *.
  rewrite !Nat2Z.inj_add in *; simpl in *.
  split; [lia|]. unfold kernel_u16; rewrite Z.mod_small; lia.
Qed.

(** OSTmr_Unlink itself does not lock, call OSTmr_Free, advance time,
    recycle a slot, or execute a callback.  Scan stability is conditional:
    timer_unlink_preserves_scan requires exclusion of the target and the
    non-head predecessor from the remaining scan footprint.  In particular
    timer_unlink_invalidates_remaining_scan refutes universal preservation. *)

Lemma tmr_unlink_images_merge_changed_map__configured_refinement :
  forall sg before after i v,
  after i = Some v ->
  (forall j, j <> i -> before j = after j) ->
  tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) v **
  store_map (fun j w => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) w)
    (kernel_map_set before i None) |--
  store_map (fun j w => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) w) after.
Proof.
  intros sg before after i v Hi Hframe.
  sep_apply_l_atomic (tmr_unlink_images_merge_updated_object sg before i v).
  apply (proj1 (store_map_equiv _ _ after ltac:(
    intros j; destruct (Z.eq_dec j i) as [->|Hji];
    [rewrite kernel_map_set_same; symmetry; exact Hi|
     rewrite kernel_map_set_other by exact Hji; apply Hframe; exact Hji]))).
Qed.
Lemma tmr_unlink_object_focus_stopped__configured_refinement : forall sg i v,
  (osKernelConfig sg).(cfgTimerNames) = true ->
  exists F : Assertion,
  (tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) v |--
    (timer_pool_addr sg i + 20) # UInt |-> timerImageMatch v **
    (timer_pool_addr sg i + 12) # Ptr |-> timerImageNext v **
    (timer_pool_addr sg i + 16) # Ptr |-> timerImagePrev v **
    (timer_pool_addr sg i + 37) # UChar |->_ ** F) /\
  ((timer_pool_addr sg i + 20) # UInt |-> timerImageMatch v **
    (timer_pool_addr sg i + 12) # Ptr |-> 0 **
    (timer_pool_addr sg i + 16) # Ptr |-> 0 **
    (timer_pool_addr sg i + 37) # UChar |-> 1 ** F |--
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) (timer_unlink_image v)).
Proof.
  intros sg i v Hnames.
  assert (Hoffset : timer_pool_addr sg i + timer_option_offset (osKernelConfig sg) + 1 =
      timer_pool_addr sg i + 37) by (unfold timer_option_offset; rewrite Hnames; lia).
  exists (tmr_unlink_object_frame (osKernelConfig sg) (timer_pool_addr sg i) v).
  split.
  - pose proof (tmr_unlink_object_split_fields (osKernelConfig sg) (timer_pool_addr sg i) v) as Hsplit.
    rewrite Hoffset in Hsplit; sep_apply_l_atomic Hsplit.
    sep_apply_l_atomic (store_uchar_undef_store_uchar (timer_pool_addr sg i + 37) (timerImageState v)).
    entailer!.
  - pose proof (tmr_unlink_object_merge_stopped (osKernelConfig sg) (timer_pool_addr sg i) v) as Hmerge.
    rewrite Hoffset in Hmerge; sep_apply_r_atomic Hmerge; entailer!.
Qed.
Lemma tmr_unlink_object_focus_next__configured_refinement : forall c p v,
  exists F : Assertion,
  (tmr_unlink_object_view include_type c p v |-- (p + 12) # Ptr |-> timerImageNext v ** F) /\
  (forall next, (p + 12) # Ptr |-> next ** F |--
    tmr_unlink_object_view include_type c p (timer_image_set_links v next (timerImagePrev v))).
Proof.
  intros c p v.
  exists ((p + 16) # Ptr |-> timerImagePrev v **
    (p + 20) # UInt |-> timerImageMatch v **
    (p + timer_option_offset c + 1) # UChar |-> timerImageState v **
    tmr_unlink_object_frame c p v).
  split.
  - sep_apply_l_atomic (tmr_unlink_object_split_fields c p v); entailer!.
  - intros; sep_apply_r_atomic (tmr_unlink_object_merge_links c p v next (timerImagePrev v)); entailer!.
Qed.
Lemma tmr_unlink_object_focus_prev__configured_refinement : forall c p v,
  exists F : Assertion,
  (tmr_unlink_object_view include_type c p v |-- (p + 16) # Ptr |-> timerImagePrev v ** F) /\
  (forall prev, (p + 16) # Ptr |-> prev ** F |--
    tmr_unlink_object_view include_type c p (timer_image_set_links v (timerImageNext v) prev)).
Proof.
  intros c p v.
  exists ((p + 12) # Ptr |-> timerImageNext v **
    (p + 20) # UInt |-> timerImageMatch v **
    (p + timer_option_offset c + 1) # UChar |-> timerImageState v **
    tmr_unlink_object_frame c p v).
  split.
  - sep_apply_l_atomic (tmr_unlink_object_split_fields c p v); entailer!.
  - intros; sep_apply_r_atomic (tmr_unlink_object_merge_links c p v (timerImageNext v) prev); entailer!.
Qed.
Lemma tmr_unlink_images_focus_one__configured_refinement :
  forall sg before after i vi wi,
  before i = Some vi -> after i = Some wi ->
  (forall q, q <> i -> before q = after q) ->
  exists F : Assertion,
  (store_map (fun j v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) v) before |--
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) vi ** F) /\
  (tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) wi ** F |--
    store_map (fun j v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) v) after).
Proof.
  intros sg before after i vi wi Hi Hwi Hframe.
  exists (store_map (fun j v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) v)
    (kernel_map_set before i None)).
  split.
  - apply tmr_unlink_images_split_object; exact Hi.
  - apply tmr_unlink_images_merge_changed_map__configured_refinement; assumption.
Qed.
Lemma tmr_unlink_images_focus_two__configured_refinement :
  forall sg before after i vi wi j vj wj,
  i <> j -> before i = Some vi -> before j = Some vj ->
  after i = Some wi -> after j = Some wj ->
  (forall q, q <> i -> q <> j -> before q = after q) ->
  exists F : Assertion,
  (store_map (fun k v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg k) v) before |--
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) vi **
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) vj ** F) /\
  (tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) wi **
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) wj ** F |--
    store_map (fun k v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg k) v) after).
Proof.
  intros sg before after i vi wi j vj wj Hij Hi Hj Hwi Hwj Hframe.
  exists (store_map (fun k v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg k) v)
    (kernel_map_set (kernel_map_set before i None) j None)).
  split.
  - sep_apply_l_atomic (tmr_unlink_images_split_object sg before i vi Hi).
    sep_apply_l_atomic (tmr_unlink_images_split_object sg (kernel_map_set before i None) j vj
      ltac:(rewrite kernel_map_set_other by congruence; exact Hj)).
    entailer!.
  - sep_apply_l_atomic (tmr_unlink_images_merge_changed_map__configured_refinement sg
      (kernel_map_set before i None) (kernel_map_set after i None) j wj
      ltac:(rewrite kernel_map_set_other by congruence; exact Hwj)
      ltac:(intros q Hqj; destruct (Z.eq_dec q i) as [->|Hqi];
        [rewrite !kernel_map_set_same; reflexivity|
         rewrite !kernel_map_set_other by exact Hqi; apply Hframe; assumption])).
    sep_apply_l_atomic (tmr_unlink_images_merge_changed_map__configured_refinement sg
      after after i wi Hwi ltac:(intros; reflexivity)).
    entailer!.
Qed.
Lemma tmr_unlink_images_focus_three__configured_refinement :
  forall sg before after i vi wi j vj wj k vk wk,
  i <> j -> i <> k -> j <> k ->
  before i = Some vi -> before j = Some vj -> before k = Some vk ->
  after i = Some wi -> after j = Some wj -> after k = Some wk ->
  (forall q, q <> i -> q <> j -> q <> k -> before q = after q) ->
  exists F : Assertion,
  (store_map (fun a v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg a) v) before |--
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) vi **
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) vj **
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg k) vk ** F) /\
  (tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg i) wi **
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) wj **
    tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg k) wk ** F |--
    store_map (fun a v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg a) v) after).
Proof.
  intros sg before after i vi wi j vj wj k vk wk Hij Hik Hjk Hi Hj Hk Hwi Hwj Hwk Hframe.
  destruct (tmr_unlink_images_focus_two__configured_refinement sg
    (kernel_map_set before i None) (kernel_map_set after i None) j vj wj k vk wk Hjk
    ltac:(rewrite kernel_map_set_other by congruence; exact Hj)
    ltac:(rewrite kernel_map_set_other by congruence; exact Hk)
    ltac:(rewrite kernel_map_set_other by congruence; exact Hwj)
    ltac:(rewrite kernel_map_set_other by congruence; exact Hwk)
    ltac:(intros q Hqj Hqk; destruct (Z.eq_dec q i) as [->|Hqi];
      [rewrite !kernel_map_set_same; reflexivity|
       rewrite !kernel_map_set_other by exact Hqi; apply Hframe; assumption]))
    as [F [Hsplit Hmerge]].
  exists F; split.
  - sep_apply_l_atomic (tmr_unlink_images_split_object sg before i vi Hi).
    sep_apply_l_atomic Hsplit; entailer!.
  - sep_apply_l_atomic Hmerge.
    sep_apply_l_atomic (tmr_unlink_images_merge_changed_map__configured_refinement sg
      after after i wi Hwi ltac:(intros; reflexivity)).
    entailer!.
Qed.
Lemma tmr_unlink_images_fields_split_merge__configured_refinement :
  forall sg images i old row,
  tmr_unlink_layout -> (osKernelConfig sg).(cfgTimerNames) = true ->
  images i = Some old ->
  (timer_id_pointer sg row <> timer_pool_addr sg i ->
    exists j vj, timerImagePrev old = timer_pool_addr sg j /\ j <> i /\
      images j = Some vj /\ timerImageNext vj = timer_pool_addr sg i) ->
  (timerImageNext old <> 0 ->
    exists k vk, timerImageNext old = timer_pool_addr sg k /\ k <> i /\
      images k = Some vk /\ timerImagePrev vk = timer_pool_addr sg i) ->
  (timer_id_pointer sg row <> timer_pool_addr sg i -> timerImageNext old <> 0 ->
    timerImagePrev old <> timerImageNext old) ->
  exists F : Assertion,
  (store_map (fun j v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) v) images |--
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrMatch" # UInt |-> timerImageMatch old **
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrNext" # Ptr |-> timerImageNext old **
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrPrev" # Ptr |-> timerImagePrev old **
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrState" # UChar |->_ **
    tmr_unlink_neighbor_pre (timer_pool_addr sg i) (timerImageNext old) (timerImagePrev old)
      (timer_id_pointer sg row) ** F) /\
  (tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrMatch" # UInt |-> timerImageMatch old **
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrNext" # Ptr |-> 0 **
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrPrev" # Ptr |-> 0 **
    tmr_unlink_timer_field (timer_pool_addr sg i) "OSTmrState" # UChar |-> 1 **
    tmr_unlink_neighbor_post (timer_pool_addr sg i) (timerImageNext old) (timerImagePrev old)
      (timer_id_pointer sg row) ** F |--
    store_map (fun j v => tmr_unlink_object_view include_type (osKernelConfig sg) (timer_pool_addr sg j) v)
      (timer_wheel_unlink_images sg images i old row)).
Proof.
  intros sg images i old row Hlayout Hnames Hi Hprev Hnext Hdistinct.
  destruct Hlayout as [Hmatch [Hnextaddr [Hprevaddr [Hstate _]]]].
  unfold tmr_unlink_neighbor_pre, tmr_unlink_neighbor_post.
  rewrite !Hmatch, !Hnextaddr, !Hprevaddr, !Hstate.
  destruct (tmr_unlink_object_focus_stopped__configured_refinement sg i old Hnames)
    as [Fi [Hsplit_i Hmerge_i]].
  destruct (Z.eq_dec (timer_id_pointer sg row) (timer_pool_addr sg i)) as [Ehead|Ehead];
    destruct (Z.eq_dec (timerImageNext old) 0) as [Enext|Enext].
  - assert (Eheadb : Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) = true)
      by (apply Z.eqb_eq; exact Ehead).
    assert (Enextb : Z.eqb (timerImageNext old) 0 = true) by (apply Z.eqb_eq; exact Enext).
    unfold timer_wheel_unlink_images; rewrite Eheadb, Enextb.
    destruct (tmr_unlink_images_focus_one__configured_refinement sg images
      (kernel_map_set images i (Some (timer_unlink_image old))) i old (timer_unlink_image old)
      Hi (kernel_map_set_same _ _ _ _)
      ltac:(intros; symmetry; apply kernel_map_set_other; assumption)) as [Fm [Hsplit Hmerge]].
    exists (Fi ** Fm); split.
    + sep_apply_l_atomic Hsplit; sep_apply_l_atomic Hsplit_i; entailer!.
    + sep_apply_r_atomic Hmerge; sep_apply_r_atomic Hmerge_i; entailer!.
  - destruct (Hnext Enext) as [k [vk [Eptr [Hki [Hk Hback]]]]].
    assert (Eheadb : Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) = true)
      by (apply Z.eqb_eq; exact Ehead).
    assert (Enextb : Z.eqb (timerImageNext old) 0 = false) by (apply Z.eqb_neq; exact Enext).
    unfold timer_wheel_unlink_images; rewrite Eheadb, Enextb.
    unfold timer_images_set_prev; rewrite Eptr, timer_pointer_index_addr, Hk; cbn [option_map].
    destruct (tmr_unlink_images_focus_two__configured_refinement sg images
      (kernel_map_set (kernel_map_set images k
        (Some (timer_image_set_links vk (timerImageNext vk) 0))) i (Some (timer_unlink_image old)))
      i old (timer_unlink_image old) k vk (timer_image_set_links vk (timerImageNext vk) 0)
      ltac:(congruence) Hi Hk (kernel_map_set_same _ _ _ _)
      ltac:(rewrite kernel_map_set_other by exact Hki; apply kernel_map_set_same)
      ltac:(intros; rewrite !kernel_map_set_other by assumption; reflexivity)) as [Fm [Hsplit Hmerge]].
    destruct (tmr_unlink_object_focus_prev__configured_refinement (osKernelConfig sg) (timer_pool_addr sg k) vk)
      as [Fk [Hsplit_k Hmerge_k]].
    rewrite Hback in Hsplit_k.
    exists (Fi ** Fk ** Fm); split.
    + sep_apply_l_atomic Hsplit; sep_apply_l_atomic Hsplit_i; sep_apply_l_atomic Hsplit_k;
        rewrite Eptr; entailer!.
    + sep_apply_r_atomic Hmerge; sepcon_right_assoc.
      sep_apply_r_atomic Hmerge_i; sepcon_right_assoc.
      sep_apply_r_atomic (Hmerge_k 0); entailer!.
  - destruct (Hprev Ehead) as [j [vj [Eptr [Hji [Hj Hforward]]]]].
    assert (Eheadb : Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) = false)
      by (apply Z.eqb_neq; exact Ehead).
    assert (Enextb : Z.eqb (timerImageNext old) 0 = true) by (apply Z.eqb_eq; exact Enext).
    unfold timer_wheel_unlink_images; rewrite Eheadb, Enextb.
    unfold timer_images_set_next; rewrite Eptr, timer_pointer_index_addr, Hj; cbn [option_map].
    destruct (tmr_unlink_images_focus_two__configured_refinement sg images
      (kernel_map_set (kernel_map_set images j
        (Some (timer_image_set_links vj (timerImageNext old) (timerImagePrev vj)))) i (Some (timer_unlink_image old)))
      i old (timer_unlink_image old) j vj (timer_image_set_links vj (timerImageNext old) (timerImagePrev vj))
      ltac:(congruence) Hi Hj (kernel_map_set_same _ _ _ _)
      ltac:(rewrite kernel_map_set_other by exact Hji; apply kernel_map_set_same)
      ltac:(intros; rewrite !kernel_map_set_other by assumption; reflexivity)) as [Fm [Hsplit Hmerge]].
    destruct (tmr_unlink_object_focus_next__configured_refinement (osKernelConfig sg) (timer_pool_addr sg j) vj)
      as [Fj [Hsplit_j Hmerge_j]].
    rewrite Hforward in Hsplit_j.
    exists (Fi ** Fj ** Fm); split.
    + sep_apply_l_atomic Hsplit; sep_apply_l_atomic Hsplit_i; sep_apply_l_atomic Hsplit_j;
        rewrite Eptr; entailer!.
    + sep_apply_r_atomic Hmerge; sepcon_right_assoc; sep_apply_r_atomic Hmerge_i; sepcon_right_assoc;
        sep_apply_r_atomic (Hmerge_j (timerImageNext old)); entailer!.
  - destruct (Hprev Ehead) as [j [vj [Eprev [Hji [Hj Hforward]]]]].
    destruct (Hnext Enext) as [k [vk [Enextptr [Hki [Hk Hback]]]]].
    assert (Hjk : j <> k) by (intro E; apply (Hdistinct Ehead Enext); rewrite Eprev, Enextptr, E; reflexivity).
    assert (Eheadb : Z.eqb (timer_id_pointer sg row) (timer_pool_addr sg i) = false)
      by (apply Z.eqb_neq; exact Ehead).
    assert (Enextb : Z.eqb (timerImageNext old) 0 = false) by (apply Z.eqb_neq; exact Enext).
    unfold timer_wheel_unlink_images; rewrite Eheadb, Enextb.
    unfold timer_images_set_next, timer_images_set_prev.
    rewrite Eprev, Enextptr, !timer_pointer_index_addr, Hj.
    rewrite kernel_map_set_other by congruence; rewrite Hk; cbn [option_map].
    destruct (tmr_unlink_images_focus_three__configured_refinement sg images
      (kernel_map_set (kernel_map_set (kernel_map_set images j
        (Some (timer_image_set_links vj (timer_pool_addr sg k) (timerImagePrev vj)))) k
        (Some (timer_image_set_links vk (timerImageNext vk) (timer_pool_addr sg j)))) i
        (Some (timer_unlink_image old)))
      i old (timer_unlink_image old)
      j vj (timer_image_set_links vj (timer_pool_addr sg k) (timerImagePrev vj))
      k vk (timer_image_set_links vk (timerImageNext vk) (timer_pool_addr sg j))
      ltac:(congruence) ltac:(congruence) Hjk Hi Hj Hk (kernel_map_set_same _ _ _ _)
      ltac:(rewrite !kernel_map_set_other by congruence; apply kernel_map_set_same)
      ltac:(rewrite kernel_map_set_other by exact Hki; apply kernel_map_set_same)
      ltac:(intros; rewrite !kernel_map_set_other by assumption; reflexivity)) as [Fm [Hsplit Hmerge]].
    destruct (tmr_unlink_object_focus_next__configured_refinement (osKernelConfig sg) (timer_pool_addr sg j) vj)
      as [Fj [Hsplit_j Hmerge_j]].
    destruct (tmr_unlink_object_focus_prev__configured_refinement (osKernelConfig sg) (timer_pool_addr sg k) vk)
      as [Fk [Hsplit_k Hmerge_k]].
    rewrite Hforward in Hsplit_j; rewrite Hback in Hsplit_k.
    exists (Fi ** Fj ** Fk ** Fm); split.
    + sep_apply_l_atomic Hsplit; sep_apply_l_atomic Hsplit_i;
        sep_apply_l_atomic Hsplit_j; sep_apply_l_atomic Hsplit_k;
        rewrite Eprev, Enextptr; entailer!.
    + sep_apply_r_atomic Hmerge; sepcon_right_assoc; sep_apply_r_atomic Hmerge_i; sepcon_right_assoc;
        sep_apply_r_atomic (Hmerge_j (timer_pool_addr sg k)); sepcon_right_assoc;
        sep_apply_r_atomic (Hmerge_k (timer_pool_addr sg j)); entailer!.
Qed.
End UnlinkObjectView.
Lemma kernel_list_neighbor_addresses_distinct__configured_refinement : forall ids p,
  NoDup ids -> In p ids -> kernel_list_next_addr ids p <> 0 ->
  kernel_list_previous_addr ids p <> 0 ->
  kernel_list_previous_addr ids p <> kernel_list_next_addr ids p.
Proof.
  intros ids p Hnd Hin Hnext Hprev.
  apply in_split in Hin; destruct Hin as [pre [rest E]]; subst ids.
  rewrite kernel_list_next_addr_at in * by exact Hnd.
  unfold kernel_list_previous_addr in *.
  rewrite kernel_list_previous_at in * by exact Hnd.
  destruct rest as [|k rest]; [contradiction|].
  destruct (rev pre) as [|j tail] eqn:Erev; simpl in *; [contradiction|].
  assert (Hj : In j pre) by (apply (proj2 (in_rev pre j)); rewrite Erev; left; reflexivity).
  intro Ejk; subst j.
  pose proof (proj1 (NoDup_remove pre (k :: rest) p Hnd)) as Hremaining.
  exact (kernel_list_nodup_app_disjoint Z pre (k :: rest) k Hremaining Hj (or_introl eq_refl)).
Qed.
Lemma tmr_unlink_row_member_image__configured_refinement : forall sg s n row j,
  valid_timer_state sg s -> nth_error (timerWheel s) n = Some row -> In j row ->
  exists v, timerImages s j = Some v /\
    timerImageNext v = kernel_list_next_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg j) /\
    timerImagePrev v = kernel_list_previous_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg j).
Proof.
  intros sg s n row j Hvalid Hrow Hin.
  pose proof Hvalid as [_ [Hwheel [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (timer_wheel_member_spoke sg s n row j Hwheel Hrow Hin) as [t [Ht _]].
  destruct (Hused j t Ht) as [_ [_ [_ [v [Hv _]]]]].
  exists v; split; [exact Hv|].
  eapply timer_wheel_row_node_pointers; eauto.
Qed.
Lemma tmr_unlink_row_neighbor_facts__configured_refinement : forall sg s n row i old,
  tmr_unlink_profile sg -> valid_timer_state sg s ->
  nth_error (timerWheel s) n = Some row -> In i row -> timerImages s i = Some old ->
  tmr_unlink_neighbor_bounds (timer_pool_addr sg i) (timerImageNext old) (timerImagePrev old)
    (timer_id_pointer sg row) /\
  (timer_id_pointer sg row <> timer_pool_addr sg i ->
    exists j vj, timerImagePrev old = timer_pool_addr sg j /\ j <> i /\
      timerImages s j = Some vj /\ timerImageNext vj = timer_pool_addr sg i) /\
  (timerImageNext old <> 0 ->
    exists k vk, timerImageNext old = timer_pool_addr sg k /\ k <> i /\
      timerImages s k = Some vk /\ timerImagePrev vk = timer_pool_addr sg i) /\
  (timer_id_pointer sg row <> timer_pool_addr sg i -> timerImageNext old <> 0 ->
    timerImagePrev old <> timerImageNext old).
Proof.
  intros sg s n row i old Hprofile Hvalid Hrow Hin Hi.
  pose proof Hvalid as [_ [Hwheel _]].
  pose proof Hwheel as [_ [Hnd _]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  pose proof (timer_row_addresses_nodup sg row Hrownd) as Haddrnd.
  pose proof (tmr_unlink_profile_pool_region sg Hprofile) as Hregion.
  pose proof (tmr_unlink_profile_object_size sg Hprofile) as Hsize.
  assert (Hbounds : forall j, In j row ->
    0 < timer_pool_addr sg j /\ timer_pool_addr sg j + 40 <= 4294967296).
  { intros j Hj; pose proof (timer_pool_addr_in_range sg j Hregion
      (timer_wheel_row_ids_in_range sg s n row j Hvalid Hrow Hj)) as Hb.
    rewrite Hsize in Hb; exact Hb. }
  assert (Hnonnull : forall j, In j row -> timer_pool_addr sg j <> 0)
    by (intros j Hj; pose proof (Hbounds j Hj); lia).
  assert (Hp0 : timer_pool_addr sg i <> 0) by (apply Hnonnull; exact Hin).
  destruct (timer_wheel_row_node_pointers sg s n row i old Hwheel Hrow Hin Hi) as [Hnext Hprev].
  assert (Hprev0 : timer_id_pointer sg row <> timer_pool_addr sg i -> timerImagePrev old <> 0).
  { intros Hhead Eprev.
    pose proof (timer_row_head_test_eq_previous_null sg row i Hrownd Hin Hnonnull) as Etest.
    rewrite <- Hprev, Eprev, Z.eqb_refl in Etest.
    apply Z.eqb_eq in Etest; contradiction. }
  assert (Hpf : timer_id_pointer sg row <> timer_pool_addr sg i ->
    exists j vj, timerImagePrev old = timer_pool_addr sg j /\ j <> i /\
      timerImages s j = Some vj /\ timerImageNext vj = timer_pool_addr sg i).
  { intro Hhead.
    destruct (timer_row_previous_pointer_member sg row i (timerImagePrev old) (eq_sym Hprev) (Hprev0 Hhead))
      as [j [Ej Hj]].
    assert (Hji : j <> i).
    { intro E; subst j.
      pose proof (proj1 (kernel_list_previous_addr_eq _ _ _ Hp0) ltac:(rewrite <- Hprev; exact Ej)) as Esome.
      exact (kernel_list_previous_not_self _ _ Haddrnd Esome). }
    destruct (tmr_unlink_row_member_image__configured_refinement sg s n row j Hvalid Hrow Hj)
      as [vj [Hv [Hnj Hpj]]].
    exists j, vj; repeat split; try assumption.
    rewrite Hnj; apply (proj2 (kernel_list_next_previous_addr _ _ _ Haddrnd (Hnonnull j Hj) Hp0)).
    rewrite <- Hprev; exact Ej. }
  assert (Hnf : timerImageNext old <> 0 ->
    exists k vk, timerImageNext old = timer_pool_addr sg k /\ k <> i /\
      timerImages s k = Some vk /\ timerImagePrev vk = timer_pool_addr sg i).
  { intro Hnext0.
    destruct (timer_row_next_pointer_member sg row i (timerImageNext old) (eq_sym Hnext) Hnext0)
      as [k [Ek Hk]].
    assert (Hki : k <> i).
    { intro E; subst k.
      pose proof (proj1 (kernel_list_next_addr_eq _ _ _ Hp0) ltac:(rewrite <- Hnext; exact Ek)) as Esome.
      exact (kernel_list_next_not_self _ _ Haddrnd Esome). }
    destruct (tmr_unlink_row_member_image__configured_refinement sg s n row k Hvalid Hrow Hk)
      as [vk [Hv [Hnk Hpk]]].
    exists k, vk; repeat split; try assumption.
    rewrite Hpk; apply (proj1 (kernel_list_next_previous_addr _ _ _ Haddrnd Hp0 (Hnonnull k Hk))).
    rewrite <- Hnext; exact Ek. }
  split.
  - split.
    + intro Hhead; destruct (timer_row_previous_pointer_member sg row i (timerImagePrev old)
        (eq_sym Hprev) (Hprev0 Hhead)) as [j [Ej Hj]].
      rewrite Ej; apply Hbounds; exact Hj.
    + intro Hnext0; destruct (timer_row_next_pointer_member sg row i (timerImageNext old)
        (eq_sym Hnext) Hnext0) as [k [Ek Hk]].
      rewrite Ek; apply Hbounds; exact Hk.
  - split; [exact Hpf|]. split; [exact Hnf|].
    intros Hhead Hnext0; rewrite Hprev, Hnext.
    apply kernel_list_neighbor_addresses_distinct__configured_refinement.
    + exact Haddrnd.
    + apply in_map; exact Hin.
    + rewrite <- Hnext; exact Hnext0.
    + rewrite <- Hprev; apply Hprev0; exact Hhead.
Qed.
Lemma tmr_unlink_row_first_after_remove__configured_refinement : forall sg row i next,
  NoDup row -> In i row -> (forall j, In j row -> timer_pool_addr sg j <> 0) ->
  next = kernel_list_next_addr (map (timer_pool_addr sg) row) (timer_pool_addr sg i) ->
  timer_id_pointer sg (remove Z.eq_dec i row) =
    if Z.eq_dec (timer_id_pointer sg row) (timer_pool_addr sg i) then next else timer_id_pointer sg row.
Proof.
  intros sg row i next Hnd Hin Hnonnull Hnext.
  assert (Hhead : forall ids, timer_id_pointer sg ids = hd 0 (map (timer_pool_addr sg) ids))
    by (intros [|j ids]; reflexivity).
  rewrite Hhead, timer_row_remove_addresses.
  rewrite kernel_list_head_remove.
  - rewrite <- Hnext, <- Hhead.
    rewrite <- (timer_row_head_test_eq_previous_null sg row i Hnd Hin Hnonnull).
    destruct (Z.eq_dec (timer_id_pointer sg row) (timer_pool_addr sg i)) as [E|E].
    + rewrite (proj2 (Z.eqb_eq _ _) E); reflexivity.
    + rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity.
  - apply timer_row_addresses_nodup; exact Hnd.
  - apply in_map; exact Hin.
  - intros p Hp; apply in_map_iff in Hp; destruct Hp as [j [E Hj]]; subst p; apply Hnonnull; exact Hj.
Qed.
