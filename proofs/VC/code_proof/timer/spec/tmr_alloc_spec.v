Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.timer.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The low contract is independent of pool validity: even boundary counter
    values have the exact unsigned-short result.  Its arbitrary frame is the
    caller's exclusive protected ownership; this helper does not acquire or
    release a lock, invoke a callback, or publish a TimerObjectState. *)
Definition tmr_alloc_globals (head used free : Z) : Assertion :=
  &("OSTmrFreeList") # Ptr |-> head **
  &("OSTmrUsed") # UShort |-> used ** &("OSTmrFree") # UShort |-> free.

Definition tmr_alloc_links (head next prev : Z) : Assertion :=
  &((head) # "os_tmr" ->ₛ "OSTmrNext") # Ptr |-> next **
  &((head) # "os_tmr" ->ₛ "OSTmrPrev") # Ptr |-> prev.

Definition tmr_alloc_low_pre (head next prev used free : Z) : Assertion :=
  tmr_alloc_globals head used free **
  ((coq_prop (head = 0) && emp) ||
   (coq_prop (head <> 0) && tmr_alloc_links head next prev)).

Definition tmr_alloc_low_post (head next prev used free ret : Z) : Assertion :=
  (coq_prop (head = 0 /\ ret = 0) && tmr_alloc_globals head used free) ||
  (coq_prop (head <> 0 /\ ret = head) &&
   tmr_alloc_globals next (kernel_u16 (used + 1)) (kernel_u16 (free - 1)) **
   tmr_alloc_links head 0 0).

(** This is the selected C/ABI assumption, not an axiom about the opaque
    address evaluator.  The arrows are exactly the eval_addr_expr/LE_arrow_field
    terms emitted by canonical QCP (FET_alias "os_tmr"), not field_address.
    Only the two touched fields need address conversion; all other bytes stay
    in the original complete image.  A caller supplies this source binding. *)
Definition tmr_alloc_source_binding (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  sizeof_alias_type "os_tmr" = 40 /\
  &("OSTmrFreeList") = sg.(g_OSTmrFreeList) /\
  &("OSTmrUsed") = sg.(g_OSTmrUsed) /\
  &("OSTmrFree") = sg.(g_OSTmrFree) /\
  kernel_region_valid (sg.(g_OSTmrTbl),
    timer_object_size sg.(osKernelConfig) * sg.(osKernelConfig).(cfgMaxTimers)) /\
  (forall i, 0 <= i < sg.(osKernelConfig).(cfgMaxTimers) ->
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (timer_pool_addr sg i) (FET_alias "os_tmr")) "OSTmrNext")) =
      timer_pool_addr sg i + 12 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (timer_pool_addr sg i) (FET_alias "os_tmr")) "OSTmrPrev")) =
      timer_pool_addr sg i + 16).

Definition tmr_alloc_object_residual (sg : StableGlobVars) (i : TimerID)
  (v : TimerImage) : Assertion :=
  let p := timer_pool_addr sg i in
  p # UChar |-> v.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 v.(timerImagePadding)) **
  (p + 4) # Ptr |-> v.(timerImageCallback) **
  (p + 8) # Ptr |-> v.(timerImageArg) **
  (p + 20) # UInt |-> v.(timerImageMatch) **
  (p + 24) # UInt |-> v.(timerImageDelay) **
  (p + 28) # UInt |-> v.(timerImagePeriod) **
  (if sg.(osKernelConfig).(cfgTimerNames)
   then (p + 32) # Ptr |-> v.(timerImageName) else emp) **
  (p + timer_option_offset sg.(osKernelConfig)) # UChar |-> v.(timerImageOption) **
  (p + timer_option_offset sg.(osKernelConfig) + 1) # UChar |-> v.(timerImageState) **
  store_optional_bytes (p + timer_option_offset sg.(osKernelConfig) + 2)
    (skipn 3 v.(timerImagePadding)).

Definition tmr_alloc_pool_residual (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  timer_wheel_rep_from sg sg.(g_OSTmrWheelTbl) s.(timerWheel) **
  sg.(g_OSTmrTime) # UInt |-> s.(timerTime) **
  sg.(g_OSTmrSem) # Ptr |-> s.(timerSem) **
  sg.(g_OSTmrSemSignal) # Ptr |-> s.(timerSignalSem).

Definition tmr_alloc_empty_frame (sg : StableGlobVars) (s : GlobTimerState) : Assertion :=
  timer_images_rep sg s ** tmr_alloc_pool_residual sg s.

Definition tmr_alloc_nonempty_frame (sg : StableGlobVars) (s : GlobTimerState)
  (i : TimerID) (v : TimerImage) : Assertion :=
  tmr_alloc_object_residual sg i v ** timer_images_without sg s i **
  tmr_alloc_pool_residual sg s.

(** Empty failure is identity.  Success transfers complete private storage
    and returns exactly the detached address.  Existing other private objects
    and Task resources remain in the caller's frame. *)
Definition tmr_alloc_result (sg : StableGlobVars) (s : GlobTimerState)
  (ret : addr) : Assertion :=
  (coq_prop (s.(timerFree) = [] /\ ret = 0) && timer_raw_rep sg s) ||
  (EX i private post,
    coq_prop (timer_allocate s = Some (i, private, post) /\
      ret = timer_pool_addr sg i /\ valid_timer_state sg post) &&
    timer_raw_rep sg post ** timer_private_rep sg i private).

Definition tmr_alloc_configured_result (sg : StableGlobVars) (s : GlobTimerState)
  (ret : addr) : Assertion :=
  (coq_prop (s.(timerFree) = [] /\ ret = 0) && timer_inv sg s) ||
  (EX i private post,
    coq_prop (timer_allocate s = Some (i, private, post) /\
      ret = timer_pool_addr sg i /\ timer_api_initialized post) &&
    timer_inv sg post ** timer_private_rep sg i private).

Lemma tmr_alloc_unsigned_short_eq : forall x,
  unsigned_last_nbits x 16 = kernel_u16 x.
Proof. intros; unfold unsigned_last_nbits, kernel_u16; reflexivity. Qed.

Lemma tmr_alloc_nonempty_facts : forall sg s i rest,
  valid_timer_state sg s -> s.(timerFree) = i :: rest ->
  0 <= i < sg.(osKernelConfig).(cfgMaxTimers) /\
  exists old, s.(timerImages) i = Some old /\
    old.(timerImageNext) = timer_id_pointer sg rest /\ old.(timerImagePrev) = 0.
Proof.
  intros sg s i rest Hvalid Hfree.
  destruct Hvalid as [[Hnd [Hrange Hpartition]] [Hwheel [Htime [Hcount
    [Hsum [Hfc [Huc [Hused [Hprivate [Hdomain [Hpadding Hlinks]]]]]]]]]]].
  split; [apply Hrange; rewrite Hfree; left; reflexivity|].
  destruct (Hlinks [] i rest Hfree) as [old [Hlookup [_ [_ Hlinksold]]]].
  exists old; tauto.
Qed.

Lemma tmr_alloc_nonempty_counter_bounds : forall sg s i rest,
  sg.(osKernelConfig).(cfgMaxTimers) = 16 ->
  valid_timer_state sg s -> s.(timerFree) = i :: rest ->
  1 <= s.(timerFreeCount) <= 16 /\ 0 <= s.(timerUsedCount) <= 15 /\
  kernel_u16 (s.(timerFreeCount) - 1) = s.(timerFreeCount) - 1 /\
  kernel_u16 (s.(timerUsedCount) + 1) = s.(timerUsedCount) + 1.
Proof.
  intros sg s i rest Hcap [_ [_ [_ [Hcount [Hsum [Hfc [Huc Hother]]]]]]] Hfree.
  rewrite Hcap in Hsum; rewrite Hfree in Hcount.
  change (timerFreeCount s = Z.of_nat (S (List.length rest))) in Hcount.
  rewrite Nat2Z.inj_succ in Hcount.
  repeat split; try lia; apply kernel_u16_identity; lia.
Qed.

Lemma tmr_alloc_nonempty_result_exists : forall sg s i rest,
  valid_timer_state sg s -> s.(timerFree) = i :: rest ->
  exists old private post,
    s.(timerImages) i = Some old /\
    old.(timerImageNext) = timer_id_pointer sg rest /\ old.(timerImagePrev) = 0 /\
    timer_allocate s = Some (i, private, post).
Proof.
  intros sg s i rest Hv Hfree.
  destruct (tmr_alloc_nonempty_facts sg s i rest Hv Hfree) as
    [Hi [old [Hold [Hnext Hprev]]]].
  unfold timer_allocate; rewrite Hfree, Hold.
  eexists old; do 2 eexists; repeat split; eauto.
Qed.

Lemma tmr_alloc_allocate_effects : forall s i private post,
  timer_allocate s = Some (i, private, post) ->
  post.(timerUsed) = s.(timerUsed) /\ post.(timerWheel) = s.(timerWheel) /\
  post.(timerTime) = s.(timerTime) /\ post.(timerSem) = s.(timerSem) /\
  post.(timerSignalSem) = s.(timerSignalSem) /\ post.(timerTask) = s.(timerTask) /\
  post.(timerInitPhase) = s.(timerInitPhase) /\
  post.(timerImages) i = None /\ post.(timerPrivate) i = Some private /\
  private.(timerPrivateGeneration) = s.(timerNextGeneration) /\
  post.(timerNextGeneration) = S s.(timerNextGeneration) /\
  (forall j, j <> i -> post.(timerImages) j = s.(timerImages) j /\
    post.(timerPrivate) j = s.(timerPrivate) j).
Proof.
  intros s i private post Hstep.
  pose proof (timer_allocate_excludes_global_image _ _ _ _ Hstep) as Hexclude.
  unfold timer_allocate in Hstep.
  destruct (timerFree s) as [|j rest]; [discriminate|].
  destruct (timerImages s j) as [old|]; [|discriminate].
  inversion Hstep; subst; simpl in *.
  repeat split; try tauto; try reflexivity;
    intros; apply kernel_map_set_other; assumption.
Qed.

Lemma tmr_alloc_split_object_links : forall sg i old,
  tmr_alloc_source_binding sg -> 0 <= i < sg.(osKernelConfig).(cfgMaxTimers) ->
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) old |--
  tmr_alloc_links (timer_pool_addr sg i) old.(timerImageNext) old.(timerImagePrev) **
  tmr_alloc_object_residual sg i old.
Proof.
  intros sg i old [_ [_ [_ [_ [_ [_ Hfields]]]]]] Hi.
  destruct (Hfields i Hi) as [Hnext Hprev].
  unfold timer_object_rep, tmr_alloc_links, tmr_alloc_object_residual.
  rewrite Hnext, Hprev; entailer!.
Qed.

Lemma tmr_alloc_merge_cleared_links : forall sg i old,
  tmr_alloc_source_binding sg -> 0 <= i < sg.(osKernelConfig).(cfgMaxTimers) ->
  tmr_alloc_links (timer_pool_addr sg i) 0 0 ** tmr_alloc_object_residual sg i old |--
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i) (timer_image_set_links old 0 0).
Proof.
  intros sg i old [_ [_ [_ [_ [_ [_ Hfields]]]]]] Hi.
  destruct (Hfields i Hi) as [Hnext Hprev].
  unfold timer_object_rep, tmr_alloc_links, tmr_alloc_object_residual, timer_image_set_links; simpl.
  rewrite Hnext, Hprev; entailer!.
Qed.

Lemma tmr_alloc_prepare_empty : forall sg s,
  tmr_alloc_source_binding sg -> s.(timerFree) = [] ->
  timer_raw_rep sg s |--
  tmr_alloc_low_pre 0 0 0 s.(timerUsedCount) s.(timerFreeCount) ** tmr_alloc_empty_frame sg s.
Proof.
  intros sg s [_ [_ [Hroot [Hused [Hfree _]]]]] Hempty.
  unfold timer_raw_rep, timer_globals_rep, tmr_alloc_low_pre, tmr_alloc_globals,
    tmr_alloc_empty_frame, tmr_alloc_pool_residual.
  rewrite Hroot, Hused, Hfree, Hempty; simpl; entailer!.
  Left; entailer!.
Qed.

Lemma tmr_alloc_finish_empty : forall sg s ret,
  tmr_alloc_source_binding sg -> s.(timerFree) = [] ->
  tmr_alloc_low_post 0 0 0 s.(timerUsedCount) s.(timerFreeCount) ret **
    tmr_alloc_empty_frame sg s |-- tmr_alloc_result sg s ret.
Proof.
  intros sg s ret [_ [_ [Hroot [Hused [Hfree _]]]]] Hempty.
  unfold tmr_alloc_low_post; Split; Intros.
  - unfold tmr_alloc_result; Left.
    unfold tmr_alloc_empty_frame, tmr_alloc_pool_residual, timer_raw_rep,
      timer_globals_rep, tmr_alloc_globals.
    rewrite Hroot, Hused, Hfree, Hempty; simpl; entailer!.
  - entailer!.
Qed.

Lemma tmr_alloc_prepare_nonempty : forall sg s i rest old,
  tmr_alloc_source_binding sg -> valid_timer_state sg s ->
  s.(timerFree) = i :: rest -> s.(timerImages) i = Some old ->
  timer_raw_rep sg s |--
  tmr_alloc_low_pre (timer_pool_addr sg i) old.(timerImageNext) old.(timerImagePrev)
    s.(timerUsedCount) s.(timerFreeCount) ** tmr_alloc_nonempty_frame sg s i old.
Proof.
  intros sg s i rest old Hb Hv Hlist Hold.
  destruct (tmr_alloc_nonempty_facts sg s i rest Hv Hlist) as [Hi Himage].
  destruct Hb as [Hcfg [Hsize [Hroot [Hused [Hfree [Hregion Hfields]]]]]].
  pose proof (timer_pool_addr_in_range sg i Hregion Hi) as Haddr.
  unfold timer_raw_rep.
  sep_apply_l_atomic (timer_images_split_object sg s i old Hold).
  sep_apply_l_atomic (tmr_alloc_split_object_links sg i old
    ltac:(unfold tmr_alloc_source_binding; repeat first [assumption | split]) Hi).
  unfold tmr_alloc_low_pre, tmr_alloc_nonempty_frame, tmr_alloc_pool_residual,
    timer_globals_rep, tmr_alloc_globals.
  rewrite Hroot, Hused, Hfree, Hlist; simpl; entailer!.
  Right; entailer!.
Qed.

Lemma tmr_alloc_finish_nonempty : forall sg s i rest old private post ret,
  tmr_alloc_source_binding sg -> valid_timer_state sg s ->
  s.(timerFree) = i :: rest -> s.(timerImages) i = Some old ->
  old.(timerImageNext) = timer_id_pointer sg rest ->
  timer_allocate s = Some (i, private, post) ->
  tmr_alloc_low_post (timer_pool_addr sg i) old.(timerImageNext) old.(timerImagePrev)
    s.(timerUsedCount) s.(timerFreeCount) ret ** tmr_alloc_nonempty_frame sg s i old |--
  tmr_alloc_result sg s ret.
Proof.
  intros sg s i rest old private post ret Hb Hv Hlist Hold Hnext Hstep.
  destruct (tmr_alloc_nonempty_facts sg s i rest Hv Hlist) as [Hi Himage].
  assert (Hcap : cfgMaxTimers (osKernelConfig sg) = 16).
  { destruct Hb as [Hcfg _]; rewrite Hcfg; reflexivity. }
  destruct (tmr_alloc_nonempty_counter_bounds sg s i rest Hcap Hv Hlist) as
    [Hfreebounds [Husedbounds [Hfreemod Husedmod]]].
  pose proof (timer_allocate_preserves_validity sg s i private post ltac:(lia) Hv Hstep) as Hpostvalid.
  pose proof (tmr_alloc_allocate_effects s i private post Hstep) as Heffects.
  pose proof Hb as [_ [_ [Hroot [Hused [Hfree [Hregion Hfields]]]]]].
  pose proof (timer_pool_addr_in_range sg i Hregion Hi) as Haddr.
  unfold tmr_alloc_low_post; Split; Intros.
  - entailer!.
  - unfold tmr_alloc_result; Right; Exists i private post; entailer!.
    unfold tmr_alloc_nonempty_frame.
    assert (Hnew : post.(timerImages) i = None) by tauto.
    assert (Hothers : forall j, j <> i -> s.(timerImages) j = post.(timerImages) j).
    { intros j Hj.
      assert (Hmaps : forall k, k <> i -> post.(timerImages) k = s.(timerImages) k /\
        post.(timerPrivate) k = s.(timerPrivate) k) by tauto.
      specialize (Hmaps j Hj); symmetry; exact (proj1 Hmaps). }
    unfold timer_images_without.
    sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
      (fun k v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg k) v)
      (timerImages s) (timerImages post) i Hothers)).
    sep_apply_l_atomic (store_map_missing_equiv_store_map
      (fun k v => timer_object_rep (osKernelConfig sg) (timer_pool_addr sg k) v)
      (timerImages post) i Hnew).
    unfold timer_allocate in Hstep; rewrite Hlist, Hold in Hstep; inversion Hstep; subst.
    unfold timer_raw_rep, timer_images_rep, timer_globals_rep, timer_private_rep,
      tmr_alloc_pool_residual, tmr_alloc_globals; simpl.
    sep_apply_r_atomic (tmr_alloc_merge_cleared_links sg i old Hb Hi).
    rewrite Hroot, Hused, Hfree, Hnext, Hfreemod, Husedmod; entailer!.
Qed.

(** A standard two-sided framed consequence of the low C contract.  The
    existential contains only old Next/Prev and a real structural residual;
    it does not assume the desired successor image or successor validity. *)
Theorem tmr_alloc_contract_consequence : forall sg s,
  tmr_alloc_source_binding sg -> valid_timer_state sg s ->
  exists next prev frame,
    (timer_raw_rep sg s |-- tmr_alloc_low_pre (timer_id_pointer sg s.(timerFree))
      next prev s.(timerUsedCount) s.(timerFreeCount) ** frame) /\
    (forall ret, tmr_alloc_low_post (timer_id_pointer sg s.(timerFree)) next prev
      s.(timerUsedCount) s.(timerFreeCount) ret ** frame |-- tmr_alloc_result sg s ret).
Proof.
  intros sg s Hb Hv; destruct (timerFree s) as [|i rest] eqn:Hlist.
  - exists 0, 0, (tmr_alloc_empty_frame sg s); simpl; split.
    + apply tmr_alloc_prepare_empty; assumption.
    + intros; apply tmr_alloc_finish_empty; assumption.
  - destruct (tmr_alloc_nonempty_result_exists sg s i rest Hv Hlist) as
      [old [private [post [Hold [Hnext [Hprev Hstep]]]]]].
    exists old.(timerImageNext), old.(timerImagePrev), (tmr_alloc_nonempty_frame sg s i old).
    simpl; split.
    + eapply tmr_alloc_prepare_nonempty; eauto.
    + intros; eapply tmr_alloc_finish_nonempty; eauto.
Qed.

Lemma tmr_alloc_result_configured : forall sg s ret,
  tmr_alloc_source_binding sg -> valid_timer_configuration sg s -> timer_api_initialized s ->
  tmr_alloc_result sg s ret |-- tmr_alloc_configured_result sg s ret.
Proof.
  intros sg s ret [Hcfg Hb] Hv Hphase.
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true) by (rewrite Hcfg; reflexivity).
  assert (Hcap : cfgMaxTimers (osKernelConfig sg) < 65536) by (rewrite Hcfg; simpl; lia).
  unfold tmr_alloc_result; Split; Intros.
  - unfold tmr_alloc_configured_result; Left; unfold timer_inv.
    rewrite (timer_initialized_configured_rep_eq sg s He Hphase); entailer!.
  - Intros i private post.
    destruct H as [Hstep [Hret Hvalid]].
    destruct (timer_allocate_preserves_configuration sg s i private post He Hcap Hv Hphase Hstep)
      as [Hconfig Hinit].
    unfold tmr_alloc_configured_result; Right; Exists i private post.
    unfold timer_inv; rewrite (timer_initialized_configured_rep_eq sg post He Hinit); entailer!.
Qed.

Theorem tmr_alloc_configured_contract_consequence : forall sg s,
  tmr_alloc_source_binding sg -> valid_timer_configuration sg s -> timer_api_initialized s ->
  exists next prev frame,
    (timer_inv sg s |-- tmr_alloc_low_pre (timer_id_pointer sg s.(timerFree))
      next prev s.(timerUsedCount) s.(timerFreeCount) ** frame) /\
    (forall ret, tmr_alloc_low_post (timer_id_pointer sg s.(timerFree)) next prev
      s.(timerUsedCount) s.(timerFreeCount) ret ** frame |--
      tmr_alloc_configured_result sg s ret).
Proof.
  intros sg s Hb Hv Hphase.
  assert (He : cfgTimerEnabled (osKernelConfig sg) = true).
  { destruct Hb as [Hcfg _]; rewrite Hcfg; reflexivity. }
  pose proof (proj1 (timer_initialized_configuration_iff sg s He Hphase) Hv) as Hvalid.
  destruct (tmr_alloc_contract_consequence sg s Hb Hvalid) as
    [next [prev [frame [Hprepare Hfinish]]]].
  exists next, prev, frame; split.
  - unfold timer_inv; rewrite (timer_initialized_configured_rep_eq sg s He Hphase).
    Intros; sep_apply_l_atomic Hprepare; entailer!.
  - intro ret; sep_apply_l_atomic (Hfinish ret).
    sep_apply_l_atomic (tmr_alloc_result_configured sg s ret Hb Hv Hphase); entailer!.
Qed.
