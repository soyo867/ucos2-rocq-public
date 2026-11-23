Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import CNotation Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.timer.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected ILP32 C/ABI interpretation. These are precisely QCP's
    alias-arrow terms, not equations with an independent field evaluator. *)
Definition tmr_link_timer_field (p : Z) (field : string) : Z :=
  eval_addr_expr (RE_addr_of
    (LE_arrow_field (RE_const p (FET_alias "os_tmr")) field)).
Definition tmr_link_wheel_field (p : Z) (field : string) : Z :=
  eval_addr_expr (RE_addr_of
    (LE_arrow_field (RE_const p (FET_alias "os_tmr_wheel")) field)).
Definition tmr_link_wheel_size : Prop := sizeof_alias_type "os_tmr_wheel" = 8.
Definition tmr_link_layout : Prop :=
  (forall p, tmr_link_timer_field p "OSTmrNext" = p + 12) /\
  (forall p, tmr_link_timer_field p "OSTmrPrev" = p + 16) /\
  (forall p, tmr_link_timer_field p "OSTmrMatch" = p + 20) /\
  (forall p, tmr_link_timer_field p "OSTmrDly" = p + 24) /\
  (forall p, tmr_link_timer_field p "OSTmrPeriod" = p + 28) /\
  (forall p, tmr_link_timer_field p "OSTmrState" = p + 37) /\
  (forall p, tmr_link_wheel_field p "OSTmrFirst" = p) /\
  (forall p, tmr_link_wheel_field p "OSTmrEntries" = p + 4) /\
  tmr_link_wheel_size.
Definition tmr_link_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgTimerEnabled) = true /\
  sg.(osKernelConfig).(cfgTimerNames) = true /\
  sg.(osKernelConfig).(cfgMaxTimers) = 16 /\
  sg.(osKernelConfig).(cfgTimerWheelSize) = 7 /\
  kernel_region_valid (sg.(g_OSTmrTbl), 40 * 16) /\
  kernel_region_valid (sg.(g_OSTmrWheelTbl), 8 * 7).

(** The source-private link tag is distinct from the timer's mode.
    Every tag other than 1 takes the actual delay/period fallback. *)
Definition tmr_link_match (kind delay period time : Z) : Z :=
  kernel_u32 ((if Z.eqb kind 1 then period
    else if Z.eqb delay 0 then period else delay) + time).
Definition tmr_link_spoke_addr (base match_time : Z) : Z :=
  base + 8 * (match_time mod 7).
Definition tmr_link_entries (first entries : Z) : Z :=
  if Z.eq_dec first 0 then 1 else kernel_u16 (entries + 1).
Definition tmr_link_neighbor_pre (first : Z) : Assertion :=
  if Z.eq_dec first 0 then emp
  else tmr_link_timer_field first "OSTmrPrev" # Ptr |->_.
Definition tmr_link_neighbor_post (p first : Z) : Assertion :=
  if Z.eq_dec first 0 then emp
  else tmr_link_timer_field first "OSTmrPrev" # Ptr |-> p.
Definition tmr_link_neighbor_bounds (first : Z) : Prop :=
  first <> 0 -> 0 < first /\ first + 40 <= 4294967296.

(** Raw ownership exposes only the real reads/writes. R keeps all
    remaining object fields/padding, other objects/spokes and caller data.
    Time, Delay and Period are explicitly returned unchanged. *)
Definition tmr_link_raw_pre
  (p base clock kind time delay period first entries : Z) (R : Assertion) : Assertion :=
  coq_prop (tmr_link_wheel_size /\ 0 < p /\ p + 40 <= 4294967296 /\
    0 < base /\ base + 56 <= 4294967296 /\
    0 <= kind < 256 /\ 0 <= time < 4294967296 /\
    0 <= delay < 4294967296 /\ 0 <= period < 4294967296 /\
    0 <= entries < 65536 /\ tmr_link_neighbor_bounds first) &&
  tmr_link_timer_field p "OSTmrState" # UChar |->_ **
  tmr_link_timer_field p "OSTmrMatch" # UInt |->_ **
  tmr_link_timer_field p "OSTmrDly" # UInt |-> delay **
  tmr_link_timer_field p "OSTmrPeriod" # UInt |-> period **
  tmr_link_timer_field p "OSTmrNext" # Ptr |->_ **
  tmr_link_timer_field p "OSTmrPrev" # Ptr |->_ **
  clock # UInt |-> time **
  tmr_link_wheel_field (tmr_link_spoke_addr base (tmr_link_match kind delay period time))
    "OSTmrFirst" # Ptr |-> first **
  tmr_link_wheel_field (tmr_link_spoke_addr base (tmr_link_match kind delay period time))
    "OSTmrEntries" # UShort |-> entries **
  tmr_link_neighbor_pre first ** R.
Definition tmr_link_raw_post
  (p base clock kind time delay period first entries : Z) (R : Assertion) : Assertion :=
  tmr_link_timer_field p "OSTmrState" # UChar |-> 3 **
  tmr_link_timer_field p "OSTmrMatch" # UInt |-> tmr_link_match kind delay period time **
  tmr_link_timer_field p "OSTmrDly" # UInt |-> delay **
  tmr_link_timer_field p "OSTmrPeriod" # UInt |-> period **
  tmr_link_timer_field p "OSTmrNext" # Ptr |-> first **
  tmr_link_timer_field p "OSTmrPrev" # Ptr |-> 0 **
  clock # UInt |-> time **
  tmr_link_wheel_field (tmr_link_spoke_addr base (tmr_link_match kind delay period time))
    "OSTmrFirst" # Ptr |-> p **
  tmr_link_wheel_field (tmr_link_spoke_addr base (tmr_link_match kind delay period time))
    "OSTmrEntries" # UShort |-> tmr_link_entries first entries **
  tmr_link_neighbor_post p first ** R.

Definition tmr_link_eligible (s : GlobTimerState) (i : Z) : Prop :=
  exists t, s.(timerUsed) i = Some t /\ t.(timerState) <> TimerRunning.
Definition tmr_link_configured_post (sg : StableGlobVars)
  (s : GlobTimerState) (i kind : Z) : Assertion :=
  EX post, coq_prop (timer_link sg s i (Z.eqb kind 1) = Some post /\
    timer_api_initialized post) && timer_inv sg post.

Lemma tmr_link_profile_object_size : forall sg,
  tmr_link_profile sg -> timer_object_size sg.(osKernelConfig) = 40.
Proof.
  intros sg [_ [Hnames _]]. unfold timer_object_size, timer_option_offset.
  rewrite Hnames; reflexivity.
Qed.
Lemma tmr_link_profile_pool_region : forall sg,
  tmr_link_profile sg -> kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)).
Proof.
  intros sg H; rewrite (tmr_link_profile_object_size sg H).
  destruct H as [_ [_ [Hcap [_ [Hpool _]]]]]; rewrite Hcap; exact Hpool.
Qed.
Lemma tmr_link_match_in_range : forall kind delay period time,
  0 <= tmr_link_match kind delay period time < 4294967296.
Proof. intros; apply kernel_u32_in_range. Qed.
Lemma tmr_link_match_object_eq : forall kind t time,
  tmr_link_match kind t.(timerDelay) t.(timerPeriod) time =
  (timer_link_object time (Z.eqb kind 1) t).(timerMatch).
Proof. reflexivity. Qed.
Lemma tmr_link_configured_successor : forall sg s i kind,
  tmr_link_profile sg -> valid_timer_configuration sg s ->
  timer_api_initialized s -> tmr_link_eligible s i ->
  exists post, timer_link sg s i (Z.eqb kind 1) = Some post /\
    valid_timer_configuration sg post /\ timer_api_initialized post.
Proof.
  intros sg s i kind Hprofile Hvalid Hinit [t [Ht Hstate]].
  pose proof Hprofile as [He [_ [_ [Hsize _]]]].
  pose proof (proj1 (timer_initialized_configuration_iff sg s He Hinit) Hvalid) as Hv.
  pose proof Hv as [_ [_ [_ [_ [_ [_ [_ [Hused _]]]]]]]].
  destruct (Hused i t Ht) as [_ [_ [_ [v [Himage _]]]]].
  destruct (timer_link_result_exists sg s i t v (Z.eqb kind 1) Ht Himage) as [post Hstep].
  exists post; split; [exact Hstep|].
  eapply timer_link_preserves_configuration; eauto; lia.
Qed.

(** Target residual omits exactly Next/Prev/Match/Delay/Period/State;
    each remaining field and both padding areas retain its original image. *)
Definition tmr_link_object_frame (c : KernelConfiguration) (p : Z)
  (v : TimerImage) : Assertion :=
  p # UChar |-> v.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) **
  (p + 8) # Ptr |-> v.(timerImageArg) **
  (if c.(cfgTimerNames) then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset c) # UChar |-> v.(timerImageOption) **
  store_optional_bytes (p + timer_option_offset c + 2) (skipn 3 v.(timerImagePadding)).
Lemma tmr_link_object_split_fields : forall c p v,
  timer_object_rep c p v |--
  (p + 12) # Ptr |-> v.(timerImageNext) **
  (p + 16) # Ptr |-> v.(timerImagePrev) **
  (p + 20) # UInt |-> v.(timerImageMatch) **
  (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
  tmr_link_object_frame c p v.
Proof. intros; unfold timer_object_rep, tmr_link_object_frame; entailer!. Qed.
Lemma tmr_link_object_merge_linked : forall c p v time next,
  (p + 12) # Ptr |-> next ** (p + 16) # Ptr |-> 0 **
  (p + 20) # UInt |-> time **
  (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (p + timer_option_offset c + 1) # UChar |-> 3 **
  tmr_link_object_frame c p v |-- timer_object_rep c p (timer_link_image v time next).
Proof.
  intros; unfold timer_object_rep, timer_link_image, tmr_link_object_frame; simpl; entailer!.
Qed.
Lemma tmr_link_object_focus_prev : forall c p v,
  exists F : Assertion,
  (timer_object_rep c p v |-- (p + 16) # Ptr |->_ ** F) /\
  (forall prev, (p + 16) # Ptr |-> prev ** F |--
    timer_object_rep c p (timer_image_set_links v v.(timerImageNext) prev)).
Proof.
  intros c p v.
  exists ((p + 12) # Ptr |-> v.(timerImageNext) **
    (p + 20) # UInt |-> v.(timerImageMatch) **
    (p + 24) # UInt |-> v.(timerImageDelay) **
    (p + 28) # UInt |-> v.(timerImagePeriod) **
    (p + timer_option_offset c + 1) # UChar |-> v.(timerImageState) **
    tmr_link_object_frame c p v).
  split.
  - sep_apply_l_atomic (tmr_link_object_split_fields c p v).
    sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 16) (timerImagePrev v)); entailer!.
  - intros; unfold timer_object_rep, timer_image_set_links, tmr_link_object_frame; simpl; entailer!.
Qed.

(** A selected row's padding and all other rows stay in the same residual.
    The merge accepts a changed row, not only the original value. *)
Fixpoint tmr_link_wheel_without_spoke (sg : StableGlobVars) (p : Z)
  (wheel : list (list Z)) (n : nat) : Assertion :=
  match wheel, n with
  | [], _ => emp
  | _ :: rest, O => UCharArray.undef_full (p + 6) 2 **
      timer_wheel_rep_from sg (p + 8) rest
  | row :: rest, S k => p # Ptr |-> timer_id_pointer sg row **
      (p + 4) # UShort |-> Z.of_nat (List.length row) **
      UCharArray.undef_full (p + 6) 2 **
      tmr_link_wheel_without_spoke sg (p + 8) rest k
  end.
Lemma tmr_link_wheel_split_spoke : forall sg wheel n row p,
  nth_error wheel n = Some row -> timer_wheel_rep_from sg p wheel |--
  (p + 8 * Z.of_nat n) # Ptr |-> timer_id_pointer sg row **
  (p + 8 * Z.of_nat n + 4) # UShort |-> Z.of_nat (List.length row) **
  tmr_link_wheel_without_spoke sg p wheel n.
Proof.
  intros sg wheel; induction wheel as [|head rest IH]; intros n row p H;
    destruct n as [|n]; simpl in H; try discriminate.
  - injection H as E; subst head; simpl.
    replace (p + 0) with p by lia; entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (p + 8 * Z.succ (Z.of_nat n)) with (p + 8 + 8 * Z.of_nat n) by lia.
    cbn [timer_wheel_rep_from tmr_link_wheel_without_spoke].
    sep_apply_l_atomic (IH n row (p + 8) H); entailer!.
Qed.
Lemma tmr_link_wheel_merge_updated_spoke : forall sg wheel n row new p,
  nth_error wheel n = Some row ->
  (p + 8 * Z.of_nat n) # Ptr |-> timer_id_pointer sg new **
  (p + 8 * Z.of_nat n + 4) # UShort |-> Z.of_nat (List.length new) **
  tmr_link_wheel_without_spoke sg p wheel n |--
  timer_wheel_rep_from sg p (timer_wheel_update wheel n new).
Proof.
  intros sg wheel; induction wheel as [|head rest IH]; intros n row new p H;
    destruct n as [|n]; simpl in H; try discriminate.
  - simpl; replace (p + 0) with p by lia; entailer!.
  - rewrite Nat2Z.inj_succ.
    replace (p + 8 * Z.succ (Z.of_nat n)) with (p + 8 + 8 * Z.of_nat n) by lia.
    cbn [timer_wheel_rep_from timer_wheel_update tmr_link_wheel_without_spoke].
    sep_apply_r_atomic (IH n row new (p + 8) H); entailer!.
Qed.

Lemma tmr_link_eligible_not_in_wheel : forall sg s i,
  valid_timer_state sg s -> tmr_link_eligible s i -> ~ timer_wheel_member s i.
Proof.
  intros sg s i [_ [[_ [_ [Hmember _]]] _]] [t [Ht Hnot]] Hin.
  destruct (proj1 (Hmember i) Hin) as [u [Hu Hrun]].
  rewrite Ht in Hu; injection Hu as E; subst u; contradiction.
Qed.
Lemma tmr_link_row_entries_increase : forall sg s n row i,
  tmr_link_profile sg -> valid_timer_state sg s ->
  nth_error s.(timerWheel) n = Some row ->
  tmr_link_entries (timer_id_pointer sg row) (Z.of_nat (List.length row)) =
    Z.of_nat (List.length (i :: row)).
Proof.
  intros sg s n row i Hprofile Hvalid Hrow.
  pose proof Hprofile as [_ [_ [Hcap _]]].
  pose proof (timer_wheel_row_pointer_null_iff sg s n row
    (tmr_link_profile_pool_region sg Hprofile) Hvalid Hrow) as Hnull.
  pose proof Hvalid as [_ [[_ [Hnd _]] _]].
  pose proof (timer_wheel_row_nodup _ _ _ Hnd Hrow) as Hrownd.
  assert (Hincl : incl row (Zrange 0 (cfgMaxTimers (osKernelConfig sg)))).
  { intros j Hin; apply In_Zrange; eapply timer_wheel_row_ids_in_range; eauto. }
  pose proof (NoDup_incl_length Hrownd Hincl) as Hlen.
  apply Nat2Z.inj_le in Hlen; rewrite kernel_zrange_length in Hlen.
  rewrite Z2Nat.id in Hlen by lia.
  unfold tmr_link_entries; destruct (Z.eq_dec (timer_id_pointer sg row) 0) as [Hz|Hz].
  - apply Hnull in Hz; subst row; reflexivity.
  - change (kernel_u16 (Z.of_nat (List.length row) + 1) =
      Z.of_nat (S (List.length row))).
    rewrite Nat2Z.inj_succ; unfold kernel_u16.
    rewrite Z.mod_small; lia.
Qed.

(** QCP MapLib provides the container laws. These local instances expose
    either just the target or the target plus the old head. *)
Lemma tmr_link_images_split_object : forall sg images i v,
  images i = Some v ->
  store_map (fun j image => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg j) image) images |--
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) v **
  store_map (fun j image => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg j) image)
    (kernel_map_set images i None).
Proof.
  intros sg images i v H.
  sep_apply_l_atomic (store_map_split
    (fun j image => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) image) i v images H).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun j image => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) image)
    images (kernel_map_set images i None) i
    ltac:(intros; rewrite kernel_map_set_other by assumption; reflexivity))).
  sep_apply_l_atomic (store_map_missing_equiv_store_map
    (fun j image => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) image)
    (kernel_map_set images i None) i (kernel_map_set_same _ _ _ _)); entailer!.
Qed.
Lemma tmr_link_images_merge_changed_map : forall sg before after i v,
  after i = Some v -> (forall j, j <> i -> before j = after j) ->
  timer_object_rep (osKernelConfig sg) (timer_pool_addr sg i) v **
  store_map (fun j w => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) w)
    (kernel_map_set before i None) |--
  store_map (fun j w => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) w) after.
Proof.
  intros sg before after i v Hi Hframe.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun j image => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) image)
    (kernel_map_set before i None) i (kernel_map_set_same _ _ _ _)).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun j image => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) image)
    (kernel_map_set before i None) after i
    ltac:(intros; rewrite kernel_map_set_other by assumption; apply Hframe; assumption))).
  sep_apply_l_atomic (store_map_merge
    (fun j image => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) image)
    i v after Hi); entailer!.
Qed.
Lemma tmr_link_images_focus_two : forall sg before after i vi wi j vj wj,
  i <> j -> before i = Some vi -> before j = Some vj ->
  after i = Some wi -> after j = Some wj ->
  (forall q, q <> i -> q <> j -> before q = after q) ->
  exists F : Assertion,
  (store_map (fun k v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg k) v) before |--
    timer_object_rep (osKernelConfig sg) (timer_pool_addr sg i) vi **
    timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) vj ** F) /\
  (timer_object_rep (osKernelConfig sg) (timer_pool_addr sg i) wi **
    timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) wj ** F |--
    store_map (fun k v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg k) v) after).
Proof.
  intros sg before after i vi wi j vj wj Hij Hi Hj Hwi Hwj Hframe.
  exists (store_map (fun k v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg k) v)
    (kernel_map_set (kernel_map_set before i None) j None)).
  split.
  - sep_apply_l_atomic (tmr_link_images_split_object sg before i vi Hi).
    sep_apply_l_atomic (tmr_link_images_split_object sg (kernel_map_set before i None) j vj
      ltac:(rewrite kernel_map_set_other by congruence; exact Hj)); entailer!.
  - sep_apply_l_atomic (tmr_link_images_merge_changed_map sg
      (kernel_map_set before i None) (kernel_map_set after i None) j wj
      ltac:(rewrite kernel_map_set_other by congruence; exact Hwj)
      ltac:(intros q Hqj; destruct (Z.eq_dec q i) as [->|Hqi];
        [rewrite !kernel_map_set_same; reflexivity|
         rewrite !kernel_map_set_other by exact Hqi; apply Hframe; assumption])).
    sep_apply_l_atomic (tmr_link_images_merge_changed_map sg after after i wi Hwi
      ltac:(intros; reflexivity)); entailer!.
Qed.

Lemma tmr_link_object_focus_linked : forall sg i v time first,
  (osKernelConfig sg).(cfgTimerNames) = true ->
  exists F : Assertion,
  (timer_object_rep (osKernelConfig sg) (timer_pool_addr sg i) v |--
    (timer_pool_addr sg i + 37) # UChar |->_ **
    (timer_pool_addr sg i + 20) # UInt |->_ **
    (timer_pool_addr sg i + 24) # UInt |-> timerImageDelay v **
    (timer_pool_addr sg i + 28) # UInt |-> timerImagePeriod v **
    (timer_pool_addr sg i + 12) # Ptr |->_ **
    (timer_pool_addr sg i + 16) # Ptr |->_ ** F) /\
  ((timer_pool_addr sg i + 37) # UChar |-> 3 **
    (timer_pool_addr sg i + 20) # UInt |-> time **
    (timer_pool_addr sg i + 24) # UInt |-> timerImageDelay v **
    (timer_pool_addr sg i + 28) # UInt |-> timerImagePeriod v **
    (timer_pool_addr sg i + 12) # Ptr |-> first **
    (timer_pool_addr sg i + 16) # Ptr |-> 0 ** F |--
    timer_object_rep (osKernelConfig sg) (timer_pool_addr sg i) (timer_link_image v time first)).
Proof.
  intros sg i v time first Hnames.
  assert (Hoffset : timer_pool_addr sg i + timer_option_offset (osKernelConfig sg) + 1 =
    timer_pool_addr sg i + 37) by (unfold timer_option_offset; rewrite Hnames; lia).
  exists (tmr_link_object_frame (osKernelConfig sg) (timer_pool_addr sg i) v).
  split.
  - pose proof (tmr_link_object_split_fields (osKernelConfig sg) (timer_pool_addr sg i) v) as Hsplit.
    rewrite Hoffset in Hsplit; sep_apply_l_atomic Hsplit.
    sep_apply_l_atomic (store_uchar_undef_store_uchar (timer_pool_addr sg i + 37) (timerImageState v)).
    sep_apply_l_atomic (store_uint_undef_store_uint (timer_pool_addr sg i + 20) (timerImageMatch v)).
    sep_apply_l_atomic (store_ptr_undef_store_ptr (timer_pool_addr sg i + 12) (timerImageNext v)).
    sep_apply_l_atomic (store_ptr_undef_store_ptr (timer_pool_addr sg i + 16) (timerImagePrev v)); entailer!.
  - pose proof (tmr_link_object_merge_linked (osKernelConfig sg) (timer_pool_addr sg i) v time first) as Hmerge.
    rewrite Hoffset in Hmerge; sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma tmr_link_images_fields_split_merge : forall sg images i old time row,
  tmr_link_layout -> (osKernelConfig sg).(cfgTimerNames) = true ->
  images i = Some old -> ~ In i row ->
  (timer_id_pointer sg row = 0 <-> row = []) ->
  (forall j, In j row -> exists v, images j = Some v) ->
  exists F : Assertion,
  (store_map (fun j v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) v) images |--
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrState" # UChar |->_ **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrMatch" # UInt |->_ **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrDly" # UInt |-> timerImageDelay old **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrPeriod" # UInt |-> timerImagePeriod old **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrNext" # Ptr |->_ **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrPrev" # Ptr |->_ **
    tmr_link_neighbor_pre (timer_id_pointer sg row) ** F) /\
  (tmr_link_timer_field (timer_pool_addr sg i) "OSTmrState" # UChar |-> 3 **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrMatch" # UInt |-> time **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrDly" # UInt |-> timerImageDelay old **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrPeriod" # UInt |-> timerImagePeriod old **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrNext" # Ptr |-> timer_id_pointer sg row **
    tmr_link_timer_field (timer_pool_addr sg i) "OSTmrPrev" # Ptr |-> 0 **
    tmr_link_neighbor_post (timer_pool_addr sg i) (timer_id_pointer sg row) ** F |--
    store_map (fun j v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) v)
      (timer_wheel_prepend_images sg images i
        (timer_link_image old time (timer_id_pointer sg row)) row)).
Proof.
  intros sg images i old time row Hlayout Hnames Hi Hnot Hnull Himages.
  destruct Hlayout as [Hnext [Hprev [Hmatch [Hdly [Hperiod [Hstate _]]]]]].
  unfold tmr_link_neighbor_pre, tmr_link_neighbor_post.
  rewrite !Hnext, !Hprev, !Hmatch, !Hdly, !Hperiod, !Hstate.
  destruct (tmr_link_object_focus_linked sg i old time (timer_id_pointer sg row) Hnames)
    as [Fi [Hsplit_i Hmerge_i]].
  destruct row as [|head tail].
  - cbn [timer_id_pointer] in *.
    destruct (Z.eq_dec 0 0); [|contradiction].
    exists (Fi ** store_map
      (fun j v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg j) v)
      (kernel_map_set images i None)).
    split.
    + sep_apply_l_atomic (tmr_link_images_split_object sg images i old Hi).
      sep_apply_l_atomic Hsplit_i; entailer!.
    + unfold timer_wheel_prepend_images.
      sep_apply_r_atomic (tmr_link_images_merge_changed_map sg images
        (kernel_map_set images i (Some (timer_link_image old time 0))) i
        (timer_link_image old time 0) (kernel_map_set_same _ _ _ _)
        ltac:(intros; symmetry; apply kernel_map_set_other; assumption)).
      sep_apply_r_atomic Hmerge_i; entailer!.
  - assert (Hhead_nonzero : timer_pool_addr sg head <> 0).
    { intro Hz; apply (proj1 Hnull) in Hz; discriminate. }
    assert (Hih : i <> head) by (intro E; apply Hnot; left; symmetry; exact E).
    destruct (Himages head (or_introl eq_refl)) as [vh Hhead].
    cbn [timer_id_pointer] in *.
    destruct (Z.eq_dec (timer_pool_addr sg head) 0); [contradiction|].
    unfold timer_wheel_prepend_images, timer_images_set_prev.
    rewrite Hhead; cbn [option_map].
    destruct (tmr_link_images_focus_two sg images
      (kernel_map_set (kernel_map_set images head
        (Some (timer_image_set_links vh (timerImageNext vh) (timer_pool_addr sg i))))
        i (Some (timer_link_image old time (timer_pool_addr sg head))))
      i old (timer_link_image old time (timer_pool_addr sg head))
      head vh (timer_image_set_links vh (timerImageNext vh) (timer_pool_addr sg i))
      Hih Hi Hhead (kernel_map_set_same _ _ _ _)
      ltac:(rewrite kernel_map_set_other by congruence; apply kernel_map_set_same)
      ltac:(intros; rewrite !kernel_map_set_other by assumption; reflexivity))
      as [Fm [Hsplit Hmerge]].
    destruct (tmr_link_object_focus_prev (osKernelConfig sg) (timer_pool_addr sg head) vh)
      as [Fh [Hsplit_h Hmerge_h]].
    exists (Fi ** Fh ** Fm); split.
    + sep_apply_l_atomic Hsplit; sep_apply_l_atomic Hsplit_i;
        sep_apply_l_atomic Hsplit_h; entailer!.
    + sep_apply_r_atomic Hmerge; sepcon_right_assoc.
      sep_apply_r_atomic Hmerge_i; sepcon_right_assoc.
      sep_apply_r_atomic (Hmerge_h (timer_pool_addr sg i)); entailer!.
Qed.
