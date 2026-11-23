(** OSFlagAccept source-order API specification and reversible field views.
    Platform calls use the existing generic acquire/mutable-Restore boundary;
    neither the type observation nor acquisition fixes a live generation. *)
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Export Ucos2Verify.VC.code.time.spec.time_get_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Export Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.error_codes.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** OSFlagAccept can acquire a free/reused pool image after the pre-Save
    type observation.  Updating that image does not allocate a group. *)
Definition flag_accept_free_image_update (s : GlobFlagState) (i : FlagID)
  (image : FlagGroupImage) (bits : Z) : GlobFlagState :=
  {| flagUsed := s.(flagUsed); flagFree := s.(flagFree);
     flagImages := kernel_map_set s.(flagImages) i
       (Some (flag_image_set_bits image bits));
     flagWaitNodes := s.(flagWaitNodes);
     flagNextGeneration := s.(flagNextGeneration) |}.

Definition flag_accept_pool_image_update (s : GlobFlagState) (i : FlagID)
  (image : FlagGroupImage) (bits : Z) : GlobFlagState :=
  match s.(flagUsed) i with
  | Some group => flag_replace_bits s i group image bits
  | None => flag_accept_free_image_update s i image bits
  end.

Lemma flag_accept_free_image_update_preserves_validity : forall sg s i image bits,
  valid_flag_state sg s -> s.(flagUsed) i = None ->
  s.(flagImages) i = Some image -> flag_word_in_range sg.(osKernelConfig) bits ->
  valid_flag_state sg (flag_accept_free_image_update s i image bits).
Proof.
  intros sg s i image bits [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]]
    Hnone Himage Hbits.
  unfold valid_flag_state, flag_accept_free_image_update; simpl.
  split; [exact Hpool|]. split.
  - intro j; destruct (Z.eq_dec j i) as [->|Hne].
    + rewrite kernel_map_set_same; split.
      * intros _; apply (proj1 (Hdomain i)); exists image; exact Himage.
      * intros _; eauto.
    + rewrite kernel_map_set_other by exact Hne; apply Hdomain.
  - split.
    + intros j found Hfound; destruct (Z.eq_dec j i) as [->|Hne].
      * rewrite kernel_map_set_same in Hfound; inversion Hfound; subst found.
        split; [exact Hbits|exact (proj2 (Himages i image Himage))].
      * rewrite kernel_map_set_other in Hfound by exact Hne; eapply Himages; eauto.
    + split.
      * intros j group Hgroup.
        assert (Hne : j <> i) by (intro Heq; subst j; congruence).
        destruct (Hused j group Hgroup) as [Hvalid [Hgen [Hwait [old [Hold Hfields]]]]].
        split; [exact Hvalid|]. split; [exact Hgen|]. split; [exact Hwait|].
        exists old; split; [rewrite kernel_map_set_other by exact Hne; exact Hold|exact Hfields].
      * split.
        -- intros pre j rest Hlist.
           destruct (Hfree pre j rest Hlist) as [old [Hold [Htype Hhead]]].
           destruct (Z.eq_dec j i) as [->|Hne].
           ++ rewrite Himage in Hold; inversion Hold; subst old.
              exists (flag_image_set_bits image bits); split; [apply kernel_map_set_same|].
              split; assumption.
           ++ exists old; split; [rewrite kernel_map_set_other by exact Hne; exact Hold|].
              split; assumption.
        -- exact Hnodes.
Qed.

Lemma flag_accept_pool_image_update_preserves_validity : forall sg s i image bits,
  valid_flag_state sg s -> s.(flagImages) i = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  valid_flag_state sg (flag_accept_pool_image_update s i image bits).
Proof.
  intros; unfold flag_accept_pool_image_update; destruct (flagUsed s i) eqn:Hused.
  - eapply flag_replace_bits_preserves_validity; eauto.
  - eapply flag_accept_free_image_update_preserves_validity; eauto.
Qed.

Lemma flag_accept_pool_image_update_image : forall s i image bits,
  (flag_accept_pool_image_update s i image bits).(flagImages) i =
    Some (flag_image_set_bits image bits).
Proof.
  intros; unfold flag_accept_pool_image_update; destruct (flagUsed s i);
    cbn; apply kernel_map_set_same.
Qed.

Lemma flag_accept_pool_image_update_other_image : forall s i image bits j,
  j <> i -> (flag_accept_pool_image_update s i image bits).(flagImages) j = s.(flagImages) j.
Proof.
  intros; unfold flag_accept_pool_image_update; destruct (flagUsed s i);
    cbn; apply kernel_map_set_other; assumption.
Qed.

Lemma flag_accept_pool_image_update_free : forall s i image bits,
  (flag_accept_pool_image_update s i image bits).(flagFree) = s.(flagFree).
Proof. intros; unfold flag_accept_pool_image_update; destruct (flagUsed s i); reflexivity. Qed.

Lemma flag_accept_pool_image_update_nodes : forall s i image bits,
  (flag_accept_pool_image_update s i image bits).(flagWaitNodes) = s.(flagWaitNodes).
Proof. intros; unfold flag_accept_pool_image_update; destruct (flagUsed s i); reflexivity. Qed.

Lemma flag_accept_pool_image_update_name_references : forall s i image bits p,
  flag_name_reference (flag_accept_pool_image_update s i image bits) p ->
  flag_name_reference s p.
Proof.
  intros s i image bits p; unfold flag_accept_pool_image_update.
  destruct (flagUsed s i) as [group|] eqn:Hgroup; [|exact (fun H => H)].
  intros [j [found [Hfound Hname]]]; cbn in Hfound.
  destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite kernel_map_set_same in Hfound; inversion Hfound; subst found.
    exists i, group; split; [exact Hgroup|exact Hname].
  - rewrite kernel_map_set_other in Hfound by exact Hne.
    exists j, found; auto.
Qed.

Lemma flag_accept_pool_image_update_preserves_state_inv : forall sg s i image bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> s.(FlagState).(flagImages) i = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg (replace_FlagS
    (flag_accept_pool_image_update s.(FlagState) i image bits) s).
Proof.
  intros sg s i image bits Henabled Hinv Himage Hbits.
  pose proof Hinv as
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hroots [Hstacks Hpending]]]]]]]]]]]]]]].
  unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags.
  assert (Hupdated : valid_flag_configuration sg
    (flag_accept_pool_image_update s.(FlagState) i image bits)).
  { unfold valid_flag_configuration; rewrite Henabled.
    eapply flag_accept_pool_image_update_preserves_validity; eauto. }
  assert (Hcross' : cross_module_consistency sg (replace_FlagS
    (flag_accept_pool_image_update s.(FlagState) i image bits) s)).
  { apply cross_module_consistency_flag_nodes_frame; [apply flag_accept_pool_image_update_nodes|exact Hcross]. }
  assert (Hroots' : kernel_names_valid sg (replace_FlagS
    (flag_accept_pool_image_update s.(FlagState) i image bits) s)).
  { eapply kernel_names_valid_frame; [exact Hroots|reflexivity|..];
      try (intros; assumption).
    intros p Hp; eapply flag_accept_pool_image_update_name_references; exact Hp. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *; cbn.
  repeat first [assumption | split].
Qed.

(** Structural residuals contain the other physical owners, not a promise
    that the old validity assertion also holds after a write. *)
Definition flag_accept_pool_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (i : FlagID) : Assertion :=
  flag_groups_without sg s.(FlagState) i ** flag_nodes_rep sg s.(FlagState) **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match s.(FlagState).(flagFree) with [] => 0 | j :: _ => flag_pool_addr sg j end) **
  UCOS2_raw_rep_missing_flag sg s.

Lemma flag_accept_pool_split : forall sg s i image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  s.(FlagState).(flagImages) i = Some image ->
  UCOS2_inv sg s |-- coq_prop (UCOS2_state_inv sg s) &&
    (flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) image **
     flag_accept_pool_frame sg s i).
Proof.
  intros sg s i image Henabled Himage; rewrite UCOS2_inv_split_flag.
  unfold flag_configured_rep; rewrite Henabled; unfold flag_raw_rep, flag_accept_pool_frame.
  Intros.
  sep_apply_l_atomic (flag_groups_split_group sg s.(FlagState) i image Himage); entailer!.
Qed.

Lemma flag_accept_pool_merge_updated : forall sg s i image bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> s.(FlagState).(flagImages) i = Some image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) (flag_image_set_bits image bits) **
    flag_accept_pool_frame sg s i |--
  UCOS2_inv sg (replace_FlagS
    (flag_accept_pool_image_update s.(FlagState) i image bits) s).
Proof.
  intros sg s i image bits Henabled Hinv Himage Hbits.
  unfold flag_accept_pool_frame.
  sep_apply_l_atomic (flag_groups_merge_updated_group sg s.(FlagState)
    (flag_accept_pool_image_update s.(FlagState) i image bits) i
    (flag_image_set_bits image bits)
    (flag_accept_pool_image_update_image _ _ _ _)
    ltac:(intros j Hne; symmetry; apply flag_accept_pool_image_update_other_image; exact Hne)).
  rewrite UCOS2_inv_split_flag; cbn [replace_FlagS].
  unfold flag_configured_rep; rewrite Henabled; unfold flag_raw_rep, flag_nodes_rep.
  cbn [replace_FlagS FlagState].
  rewrite ?flag_accept_pool_image_update_nodes, ?flag_accept_pool_image_update_free,
    ?UCOS2_raw_rep_missing_flag_replace_eq.
  pose proof (flag_accept_pool_image_update_preserves_state_inv
    sg s i image bits Henabled Hinv Himage Hbits); entailer!.
Qed.

Lemma flag_accept_pool_merge_original : forall sg s i image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> s.(FlagState).(flagImages) i = Some image ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg i) image **
    flag_accept_pool_frame sg s i |-- UCOS2_inv sg s.
Proof.
  intros sg s i image Henabled Hinv Himage; unfold flag_accept_pool_frame.
  sep_apply_l_atomic (flag_groups_merge_group sg s.(FlagState) i image Himage).
  rewrite UCOS2_inv_split_flag; unfold flag_configured_rep; rewrite Henabled.
  unfold flag_raw_rep; entailer!.
Qed.

Definition flag_accept_image_without_bits (c : KernelConfiguration) (p : addr)
  (image : FlagGroupImage) : Assertion :=
  p # UChar |-> image.(flagImageType) **
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  (p + 4) # Ptr |-> image.(flagImageHead) **
  store_optional_bytes (p + 8 + flag_word_bytes c) (skipn 3 image.(flagImagePadding)) **
  (if c.(cfgFlagNames) then (p + flag_group_name_offset c) # Ptr |-> image.(flagImageName) else emp).

Lemma flag_accept_image_split_bits : forall c p image,
  c.(cfgFlagBits) = 16 ->
  flag_group_rep c p image --||--
    (p + 8) # UShort |-> image.(flagImageBits) ** flag_accept_image_without_bits c p image.
Proof.
  intros c p image Hbits; unfold flag_group_rep, flag_accept_image_without_bits,
    flag_word_rep; rewrite Hbits; cbn; split; entailer!.
Qed.

Lemma flag_accept_image_merge_updated_bits : forall c p image bits,
  c.(cfgFlagBits) = 16 ->
  (p + 8) # UShort |-> bits ** flag_accept_image_without_bits c p image |--
    flag_group_rep c p (flag_image_set_bits image bits).
Proof.
  intros c p image bits Hbits; unfold flag_group_rep, flag_accept_image_without_bits,
    flag_word_rep, flag_image_set_bits; rewrite Hbits; cbn; entailer!.
Qed.

Inductive FlagAcceptView :=
| FlagAcceptRaw (image : FlagGroupImage)
| FlagAcceptPool (id : FlagID).

Definition flag_accept_selected (view : FlagAcceptView)
  (s : UCOS2_Verify_State) (image : FlagGroupImage) : Prop :=
  match view with
  | FlagAcceptRaw original => image = original
  | FlagAcceptPool id => s.(FlagState).(flagImages) id = Some image
  end.

Lemma flag_accept_acquired_pool_image : forall sg entry id,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg entry -> 0 <= id < sg.(osKernelConfig).(cfgMaxFlags) ->
  exists image, flag_accept_selected (FlagAcceptPool id) entry image.
Proof.
  intros sg entry id Henabled Hinv Hrange.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hinv.
  assert (Hflags : valid_flag_configuration sg entry.(FlagState)) by tauto.
  unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags.
  destruct Hflags as [_ [Hdomain _]]; exact (proj2 (Hdomain id) Hrange).
Qed.

Definition flag_accept_released (view : FlagAcceptView)
  (entry : UCOS2_Verify_State) (image : FlagGroupImage) (bits : Z) : UCOS2_Verify_State :=
  if Z.eqb bits image.(flagImageBits) then entry else
    match view with
    | FlagAcceptRaw _ => entry
    | FlagAcceptPool id => replace_FlagS
        (flag_accept_pool_image_update entry.(FlagState) id image bits) entry
    end.

Lemma flag_accept_released_unchanged : forall view entry image,
  flag_accept_released view entry image image.(flagImageBits) = entry.
Proof. intros; unfold flag_accept_released; rewrite Z.eqb_refl; reflexivity. Qed.

Lemma flag_accept_released_preserves_state_inv : forall sg view entry image bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg entry -> flag_accept_selected view entry image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  UCOS2_state_inv sg (flag_accept_released view entry image bits).
Proof.
  intros sg view entry image bits Henabled Hinv Himage Hbits.
  unfold flag_accept_released; destruct (Z.eqb bits (flagImageBits image)); [exact Hinv|].
  destruct view; [exact Hinv|].
  eapply flag_accept_pool_image_update_preserves_state_inv; eauto.
Qed.

Definition flag_accept_raw_post (sg : StableGlobVars) (pe : addr)
  (view : FlagAcceptView) (image : FlagGroupImage) (bits : Z) : Assertion :=
  match view with
  | FlagAcceptRaw _ => flag_group_rep sg.(osKernelConfig) pe (flag_image_set_bits image bits)
  | FlagAcceptPool _ => emp
  end.

Definition flag_accept_source_rep (sg : StableGlobVars) (pe : addr)
  (view : FlagAcceptView) : Assertion :=
  match view with
  | FlagAcceptRaw image => flag_group_rep sg.(osKernelConfig) pe image
  | FlagAcceptPool _ => emp
  end.

Definition flag_accept_source_frame (sg : StableGlobVars) (view : FlagAcceptView)
  (entry : UCOS2_Verify_State) : Assertion :=
  match view with
  | FlagAcceptRaw _ => UCOS2_inv sg entry
  | FlagAcceptPool id => coq_prop (UCOS2_state_inv sg entry) && flag_accept_pool_frame sg entry id
  end.

Definition flag_accept_address (sg : StableGlobVars) (pe : addr) (view : FlagAcceptView) : Prop :=
  match view with FlagAcceptRaw _ => True | FlagAcceptPool id => pe = flag_pool_addr sg id end.

Lemma flag_accept_source_split : forall sg pe view entry image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  flag_accept_address sg pe view -> flag_accept_selected view entry image ->
  UCOS2_inv sg entry ** flag_accept_source_rep sg pe view |--
    flag_group_rep sg.(osKernelConfig) pe image ** flag_accept_source_frame sg view entry.
Proof.
  intros sg pe [original|id] entry image Henabled Haddress Himage.
  - cbn [flag_accept_selected] in Himage; subst image.
    cbn [flag_accept_source_rep flag_accept_source_frame]; entailer!.
  - cbn [flag_accept_address] in Haddress; subst pe.
    cbn [flag_accept_selected] in Himage.
    cbn [flag_accept_source_rep flag_accept_source_frame].
    sep_apply_l_atomic (flag_accept_pool_split sg entry id image Henabled Himage); entailer!.
Qed.

Lemma flag_accept_source_merge_original : forall sg pe view entry image,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  flag_accept_address sg pe view -> flag_accept_selected view entry image ->
  flag_group_rep sg.(osKernelConfig) pe image ** flag_accept_source_frame sg view entry |--
    UCOS2_inv sg entry ** flag_accept_source_rep sg pe view.
Proof.
  intros sg pe [original|id] entry image Henabled Haddress Himage.
  - cbn [flag_accept_selected] in Himage; subst image.
    cbn [flag_accept_source_rep flag_accept_source_frame]; entailer!.
  - cbn [flag_accept_address] in Haddress; subst pe.
    cbn [flag_accept_selected] in Himage.
    cbn [flag_accept_source_rep flag_accept_source_frame]; Intros.
    sep_apply_l_atomic (flag_accept_pool_merge_original sg entry id image Henabled
      ltac:(assumption) Himage); entailer!.
Qed.

Lemma flag_accept_source_merge_updated : forall sg pe view entry image bits,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  flag_accept_address sg pe view -> flag_accept_selected view entry image ->
  flag_word_in_range sg.(osKernelConfig) bits ->
  flag_group_rep sg.(osKernelConfig) pe (flag_image_set_bits image bits) **
    flag_accept_source_frame sg view entry |--
  UCOS2_inv sg (flag_accept_released view entry image bits) **
    flag_accept_raw_post sg pe view image bits.
Proof.
  intros sg pe [original|id] entry image bits Henabled Haddress Himage Hbits.
  - unfold flag_accept_released; destruct (Z.eqb bits (flagImageBits image));
      cbn [flag_accept_raw_post flag_accept_source_frame]; entailer!.
  - cbn [flag_accept_address] in Haddress; subst pe.
    cbn [flag_accept_selected] in Himage.
    cbn [flag_accept_raw_post flag_accept_source_frame]; Intros.
    unfold flag_accept_released; destruct (Z.eqb bits (flagImageBits image)) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst bits.
      assert (Hsame : flag_image_set_bits image (flagImageBits image) = image)
        by (destruct image; reflexivity).
      rewrite Hsame.
      sep_apply_l_atomic (flag_accept_pool_merge_original sg entry id image Henabled
        ltac:(assumption) Himage); entailer!.
    + sep_apply_l_atomic (flag_accept_pool_merge_updated sg entry id image bits Henabled
        ltac:(assumption) Himage Hbits); entailer!.
Qed.

(** The result is (ready,error). Pre-Save type is a genuine prior
    observation; neither Save nor a fixed address equates it to the acquired
    type or generation. The protected stage uses the shared bit semantics,
    then the actual Restore interval supplies the returned current state. *)
Definition flag_accept_protected (sg : StableGlobVars) (view : FlagAcceptView)
  (mask wait_type : Z) : program UCOS2_Verify_State (Z * Z) :=
  fun entry observation released => exists image bits ready err,
    flag_accept_selected view entry image /\
    flag_accept_bits sg.(osKernelConfig) image.(flagImageBits) mask wait_type = (bits, ready, err) /\
    observation = (ready, encode_os_err_code err) /\
    released = flag_accept_released view entry image bits.

Definition flag_accept_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (view : FlagAcceptView)
  (pe observed_type mask wait_type : Z) : program UCOS2_Verify_State (Z * Z) :=
  if Z.eqb pe 0 then StateRelMonad.ret (0, 110)
  else if negb (Z.eqb observed_type 5) then StateRelMonad.ret (0, 1)
  else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (flag_accept_protected sg view mask wait_type)
      (fun observation => StateRelMonad.bind
        (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret observation))).

Definition flag_accept_safe critical sg invocation view pe observed_type mask wait_type before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (flag_accept_program critical sg invocation view pe observed_type mask wait_type)
    (fun result current => X (fst result) (snd result) current).

Lemma flag_accept_program_null : forall critical sg invocation view observed_type mask wait_type before,
  flag_accept_program critical sg invocation view 0 observed_type mask wait_type before (0,110) before.
Proof. intros; unfold flag_accept_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma flag_accept_program_type_error : forall critical sg invocation view pe observed_type mask wait_type before,
  pe <> 0 -> observed_type <> 5 ->
  flag_accept_program critical sg invocation view pe observed_type mask wait_type before (0,1) before.
Proof.
  intros; unfold flag_accept_program; rewrite (proj2 (Z.eqb_neq _ _) H),
    (proj2 (Z.eqb_neq _ _) H0); unfold StateRelMonad.ret; cbn; auto.
Qed.

Lemma flag_accept_program_observed_return :
  forall critical sg invocation view pe mask wait_type before entry image bits ready err released current,
  pe <> 0 -> critical_region_interval critical sg invocation before entry ->
  flag_accept_selected view entry image ->
  flag_accept_bits sg.(osKernelConfig) image.(flagImageBits) mask wait_type = (bits,ready,err) ->
  released = flag_accept_released view entry image bits ->
  critical_region_interval critical sg invocation released current ->
  flag_accept_program critical sg invocation view pe 5 mask wait_type before
    (ready,encode_os_err_code err) current.
Proof.
  intros critical sg invocation view pe mask wait_type before entry image bits ready err released current
    Hpe Hentry Himage Hbits Hreleased Hcurrent.
  unfold flag_accept_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe); cbn.
  unfold StateRelMonad.bind, update, StateRelMonad.ret.
  exists tt, entry; split; [exact Hentry|].
  exists (ready,encode_os_err_code err), released; split.
  - exists image, bits, ready, err; auto.
  - exists tt, current; split; [exact Hcurrent|]; split; reflexivity.
Qed.

Lemma flag_accept_safe_return : forall critical sg invocation view pe observed_type mask wait_type
  before ready err current X,
  flag_accept_program critical sg invocation view pe observed_type mask wait_type
    before (ready,err) current ->
  flag_accept_safe critical sg invocation view pe observed_type mask wait_type before X ->
  safeExec (eq current) (StateRelMonad.ret (ready,err))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation view pe observed_type mask wait_type before ready err current X Hprogram Hsafe.
  unfold flag_accept_safe in Hsafe.
  eapply (highstependret_derive
    (flag_accept_program critical sg invocation view pe observed_type mask wait_type)
    (eq before) (ready,err) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma flag_accept_protected_preserves_state_inv : forall sg view mask wait_type entry observation released,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> 0 <= sg.(osKernelConfig).(cfgFlagBits) ->
  UCOS2_state_inv sg entry ->
  (forall image, flag_accept_selected view entry image ->
    flag_word_in_range sg.(osKernelConfig) image.(flagImageBits)) ->
  flag_accept_protected sg view mask wait_type entry observation released ->
  UCOS2_state_inv sg released.
Proof.
  intros sg view mask wait_type entry observation released Henabled Hwidth Hinv Hrange
    [image [bits [ready [err [Himage [Hbits [Hobservation Hreleased]]]]]]].
  subst released; eapply flag_accept_released_preserves_state_inv; eauto.
  eapply flag_accept_bits_preserves_word_range; eauto.
Qed.

(** This is abstract non-vacuity, not eventual return of a platform call.
    The zero-environment-step path covers every admitted image and every
    mask/wait-type value, including invalid modes and zero masks. *)
Lemma flag_accept_program_has_result :
  forall critical sg invocation view pe observed_type mask wait_type before,
  (pe = 0 \/ observed_type <> 5 \/ exists image, flag_accept_selected view before image) ->
  exists observation current,
    flag_accept_program critical sg invocation view pe observed_type mask wait_type
      before observation current.
Proof.
  intros critical sg invocation view pe observed_type mask wait_type before Hdomain.
  destruct (Z.eq_dec pe 0) as [->|Hpe].
  - exists (0,110), before; apply flag_accept_program_null.
  - destruct (Z.eq_dec observed_type 5) as [->|Htype].
    + destruct Hdomain as [Hzero|[Htype|[image Himage]]]; try contradiction.
      destruct (flag_accept_bits (osKernelConfig sg) (flagImageBits image) mask wait_type)
        as [[bits ready] err] eqn:Hbits.
      exists (ready,encode_os_err_code err), (flag_accept_released view before image bits).
      eapply flag_accept_program_observed_return; try eassumption; try reflexivity; constructor.
    + exists (0,1), before; apply flag_accept_program_type_error; assumption.
Qed.

(** Selected original-header ARM32 profile. These are build/layout bindings,
    not restrictions on runtime flag masks or wait modes. *)
Definition flag_accept_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgFlagEnabled) = true /\
  sg.(osKernelConfig).(cfgFlagBits) = 16 /\
  sg.(osKernelConfig).(cfgFlagClearWait) = true /\
  sg.(osKernelConfig).(cfgFlagNames) = true /\
  (forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p) /\
  (forall p, (&(p # "os_flag_grp" ->ₛ "OSFlagFlags")) = p + 8).

Definition flag_accept_admission (sg : StableGlobVars) (pe : addr)
  (view : FlagAcceptView) (before : UCOS2_Verify_State)
  (observed : FlagGroupImage) : Prop :=
  flag_accept_address sg pe view /\ flag_accept_selected view before observed /\
  match view with
  | FlagAcceptRaw _ => True
  | FlagAcceptPool id => 0 <= id < sg.(osKernelConfig).(cfgMaxFlags)
  end.

Definition flag_accept_image_without_type (c : KernelConfiguration)
  (pe : addr) (image : FlagGroupImage) : Assertion :=
  store_optional_bytes (pe + 1) (firstn 3 image.(flagImagePadding)) **
  (pe + 4) # Ptr |-> image.(flagImageHead) **
  flag_word_rep c (pe + 8) image.(flagImageBits) **
  store_optional_bytes (pe + 8 + flag_word_bytes c) (skipn 3 image.(flagImagePadding)) **
  (if c.(cfgFlagNames) then (pe + flag_group_name_offset c) # Ptr |-> image.(flagImageName) else emp).

Lemma flag_accept_image_split_type : forall c pe image,
  flag_group_rep c pe image --||--
    pe # UChar |-> image.(flagImageType) ** flag_accept_image_without_type c pe image.
Proof. intros; unfold flag_group_rep, flag_accept_image_without_type; split; entailer!. Qed.

(** NULL needs no group memory; a wrong-type raw argument needs only its
    actual type byte. Any other owned bytes remain in the arbitrary caller
    frame. The successful type branch borrows the complete shared region or
    the separate caller-owned raw image, as appropriate. *)
Definition flag_accept_before_resource platform critical sg invocation origin mask
  (view : FlagAcceptView) (pe : addr) (before : UCOS2_Verify_State)
  (observed : FlagGroupImage) : Assertion :=
  if Z.eqb pe 0 then emp else
  if Z.eqb observed.(flagImageType) 5 then
    coq_prop (flag_accept_admission sg pe view before observed) &&
    (mutex_query_closed platform critical sg invocation origin mask before **
     flag_accept_source_rep sg pe view)
  else pe # UChar |-> observed.(flagImageType).

Definition flag_accept_type_frame platform sg invocation origin mask view pe before observed : Assertion :=
  if Z.eqb observed.(flagImageType) 5 then
    coq_prop (flag_accept_admission sg pe view before observed) &&
    (interrupt_platform_running platform invocation origin mask **
     flag_accept_image_without_type sg.(osKernelConfig) pe observed **
     flag_accept_source_frame sg view before)
  else emp.

Lemma flag_accept_before_split_type :
  forall platform critical sg invocation origin mask view pe before observed,
  flag_accept_profile sg -> pe <> 0 ->
  flag_accept_before_resource platform critical sg invocation origin mask view pe before observed |--
    pe # UChar |-> observed.(flagImageType) **
    flag_accept_type_frame platform sg invocation origin mask view pe before observed.
Proof.
  intros platform critical sg invocation origin mask view pe before observed Hprofile Hpe.
  unfold flag_accept_before_resource, flag_accept_type_frame.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe).
  destruct (Z.eqb (flagImageType observed) 5) eqn:Htype; [|entailer!].
  Intros.
  match goal with H : flag_accept_admission _ _ _ _ _ |- _ =>
    pose proof H as [Haddress [Hselected Hrange]] end.
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (flag_accept_source_split sg pe view before observed
    ltac:(unfold flag_accept_profile in Hprofile; tauto) Haddress Hselected).
  rewrite flag_accept_image_split_type; entailer!.
Qed.

Lemma flag_accept_type_merge_success :
  forall platform critical sg invocation origin mask view pe before observed,
  flag_accept_profile sg -> observed.(flagImageType) = 5 ->
  pe # UChar |-> observed.(flagImageType) **
    flag_accept_type_frame platform sg invocation origin mask view pe before observed |--
  coq_prop (flag_accept_admission sg pe view before observed) &&
    (mutex_query_closed platform critical sg invocation origin mask before **
     flag_accept_source_rep sg pe view).
Proof.
  intros platform critical sg invocation origin mask view pe before observed Hprofile Htype.
  unfold flag_accept_type_frame; rewrite Htype; cbn.
  Intros.
  match goal with H : flag_accept_admission _ _ _ _ _ |- _ =>
    pose proof H as [Haddress [Hselected Hrange]] end.
  pose proof (proj2 (flag_accept_image_split_type (osKernelConfig sg) pe observed)) as Hmerge.
  rewrite Htype in Hmerge; sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (flag_accept_source_merge_original sg pe view before observed
    ltac:(unfold flag_accept_profile in Hprofile; tauto) Haddress Hselected).
  rewrite mutex_query_closed_equiv; entailer!.
Qed.

Lemma flag_accept_admission_acquired_image : forall sg pe view before observed entry,
  flag_accept_profile sg -> flag_accept_admission sg pe view before observed ->
  UCOS2_state_inv sg entry -> exists image, flag_accept_selected view entry image.
Proof.
  intros sg pe [original|id] before observed entry Hprofile [Haddress [Hselected Hrange]] Hinv.
  - exists original; reflexivity.
  - eapply flag_accept_acquired_pool_image; eauto.
    unfold flag_accept_profile in Hprofile; tauto.
Qed.

Definition flag_accept_acquired_facts critical sg invocation mask saved view pe
  before observed entry image : Prop :=
  flag_accept_profile sg /\ pe <> 0 /\ observed.(flagImageType) = 5 /\
  flag_accept_admission sg pe view before observed /\
  time_get_acquire_facts critical sg invocation mask saved before entry /\
  flag_accept_selected view entry image /\ 0 <= image.(flagImageBits) <= 65535.

Definition flag_accept_bits_frame platform critical sg invocation origin mask saved
  view pe before observed entry image : Assertion :=
  coq_prop (flag_accept_acquired_facts critical sg invocation mask saved view pe
    before observed entry image) &&
  (critical_region_masked platform critical sg invocation origin saved entry **
   flag_accept_image_without_bits sg.(osKernelConfig) pe image **
   flag_accept_source_frame sg view entry).

Lemma flag_accept_acquired_split_bits :
  forall platform critical sg invocation origin mask saved view pe before observed entry,
  flag_accept_profile sg -> pe <> 0 -> observed.(flagImageType) = 5 ->
  flag_accept_admission sg pe view before observed ->
  time_get_acquire_facts critical sg invocation mask saved before entry ->
  critical_region_masked platform critical sg invocation origin saved entry **
    UCOS2_inv sg entry ** flag_accept_source_rep sg pe view |--
  EX image, (pe + 8) # UShort |-> image.(flagImageBits) **
    flag_accept_bits_frame platform critical sg invocation origin mask saved view pe
      before observed entry image.
Proof.
  intros platform critical sg invocation origin mask saved view pe before observed entry
    Hprofile Hpe Htype Hadmission Hacquire.
  destruct Hacquire as [Hinterval [Hvalid Hsaved]].
  destruct (flag_accept_admission_acquired_image sg pe view before observed entry
    Hprofile Hadmission Hvalid) as [image Himage].
  pose proof Hadmission as [Haddress _].
  sep_apply_l_atomic (flag_accept_source_split sg pe view entry image
    ltac:(unfold flag_accept_profile in Hprofile; tauto) Haddress Himage).
  rewrite flag_accept_image_split_bits by (unfold flag_accept_profile in Hprofile; tauto).
  prop_apply_p (store_ushort_range (pe + 8) (flagImageBits image)).
  unfold flag_accept_bits_frame, flag_accept_acquired_facts, time_get_acquire_facts.
  Exists image; entailer!.
Qed.

Definition flag_accept_effect (sg : StableGlobVars) (image : FlagGroupImage)
  (requested wait_type bits ready error : Z) : Prop :=
  exists code, flag_accept_bits sg.(osKernelConfig) image.(flagImageBits)
    requested wait_type = (bits, ready, code) /\ error = encode_os_err_code code.

Definition flag_accept_mode (wait_type : Z) : Z := Z.land wait_type 127.
Definition flag_accept_consume_bit (wait_type : Z) : Z := Z.land wait_type 128.
Definition flag_accept_consume_value (wait_type : Z) : Z :=
  if Z.testbit wait_type 7 then 1 else 0.

Definition flag_accept_checkpoint_facts critical sg invocation mask saved view pe
  before observed entry image requested wait_type bits ready error : Prop :=
  flag_accept_acquired_facts critical sg invocation mask saved view pe before observed entry image /\
  flag_accept_effect sg image requested wait_type bits ready error.

Lemma flag_accept_bits_merge_restore :
  forall platform critical sg invocation origin mask saved view pe before observed entry image bits,
  flag_word_in_range sg.(osKernelConfig) bits ->
  (pe + 8) # UShort |-> bits **
    flag_accept_bits_frame platform critical sg invocation origin mask saved view pe
      before observed entry image |--
  coq_prop (flag_accept_acquired_facts critical sg invocation mask saved view pe
    before observed entry image) &&
  (mbox_accept_cpu_restore_pre platform critical sg invocation origin mask saved entry
     (flag_accept_released view entry image bits) **
   flag_accept_raw_post sg pe view image bits).
Proof.
  intros; unfold flag_accept_bits_frame; Intros.
  match goal with Hfacts : flag_accept_acquired_facts _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof Hfacts as [Hprofile [Hpe [Htype [Hadmission [Hacquire [Himage Holdrange]]]]]] end.
  pose proof Hadmission as [Haddress _].
  destruct Hacquire as [Hinterval [Hvalid Hsaved]].
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true)
    by (unfold flag_accept_profile in Hprofile; tauto).
  sep_apply_l_atomic (flag_accept_image_merge_updated_bits (osKernelConfig sg) pe image bits
    ltac:(unfold flag_accept_profile in Hprofile; tauto)).
  sep_apply_l_atomic (flag_accept_source_merge_updated sg pe view entry image bits
    Henabled Haddress Himage H).
  pose proof (flag_accept_released_preserves_state_inv sg view entry image bits
    Henabled Hvalid Himage H).
  unfold mbox_accept_cpu_restore_pre; entailer!.
Qed.

Definition flag_accept_return_safe current ready error
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret (ready,error))
    (fun result state => X (fst result) (snd result) state).

Definition flag_accept_api_post platform critical sg invocation origin mask view pe perr
  before observed requested wait_type ready X : Assertion :=
  if orb (Z.eqb pe 0) (negb (Z.eqb observed.(flagImageType) 5)) then
    EX error, coq_prop
      (flag_accept_program critical sg invocation view pe observed.(flagImageType)
        requested wait_type before (ready,error) before /\
       flag_accept_return_safe before ready error X) &&
      (perr # UChar |-> error **
       flag_accept_before_resource platform critical sg invocation origin mask view pe before observed)
  else EX entry, EX image, EX bits, EX error, EX current,
    coq_prop
      (critical_region_interval critical sg invocation before entry /\
       flag_accept_selected view entry image /\
       flag_accept_effect sg image requested wait_type bits ready error /\
       critical_region_interval critical sg invocation
         (flag_accept_released view entry image bits) current /\
       flag_accept_program critical sg invocation view pe observed.(flagImageType)
         requested wait_type before (ready,error) current /\
       flag_accept_return_safe current ready error X) &&
    (perr # UChar |-> error **
     mutex_query_closed platform critical sg invocation origin mask current **
     flag_accept_raw_post sg pe view image bits).

Lemma flag_accept_null_api_post :
  forall platform critical sg invocation origin mask view perr before observed requested wait_type X,
  flag_accept_safe critical sg invocation view 0 observed.(flagImageType)
    requested wait_type before X ->
  perr # UChar |-> 110 **
    flag_accept_before_resource platform critical sg invocation origin mask view 0 before observed |--
  flag_accept_api_post platform critical sg invocation origin mask view 0 perr
    before observed requested wait_type 0 X.
Proof.
  intros.
  pose proof (flag_accept_program_null critical sg invocation view (flagImageType observed)
    requested wait_type before) as Hprogram.
  pose proof (flag_accept_safe_return critical sg invocation view 0 (flagImageType observed)
    requested wait_type before 0 110 before X Hprogram H) as Hreturn.
  unfold flag_accept_api_post; cbn.
  Exists 110; unfold flag_accept_return_safe; entailer!.
Qed.

Lemma flag_accept_type_error_api_post :
  forall platform critical sg invocation origin mask view pe perr before observed requested wait_type X,
  pe <> 0 -> observed.(flagImageType) <> 5 ->
  flag_accept_safe critical sg invocation view pe observed.(flagImageType)
    requested wait_type before X ->
  perr # UChar |-> 1 **
    flag_accept_before_resource platform critical sg invocation origin mask view pe before observed |--
  flag_accept_api_post platform critical sg invocation origin mask view pe perr
    before observed requested wait_type 0 X.
Proof.
  intros platform critical sg invocation origin mask view pe perr before observed requested wait_type X
    Hpe Htype Hsafe.
  pose proof (flag_accept_program_type_error critical sg invocation view pe (flagImageType observed)
    requested wait_type before Hpe Htype) as Hprogram.
  pose proof (flag_accept_safe_return critical sg invocation view pe (flagImageType observed)
    requested wait_type before 0 1 before X Hprogram Hsafe) as Hreturn.
  unfold flag_accept_api_post.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype); cbn.
  Exists 1; unfold flag_accept_return_safe; entailer!.
Qed.

Lemma flag_accept_restore_api_post :
  forall platform critical sg invocation origin mask saved view pe perr before observed entry image
    requested wait_type bits ready error X,
  flag_accept_checkpoint_facts critical sg invocation mask saved view pe
    before observed entry image requested wait_type bits ready error ->
  flag_accept_safe critical sg invocation view pe observed.(flagImageType)
    requested wait_type before X ->
  time_get_restore_post platform critical sg invocation origin saved
      (flag_accept_released view entry image bits) **
    flag_accept_raw_post sg pe view image bits ** perr # UChar |-> error |--
  flag_accept_api_post platform critical sg invocation origin mask view pe perr
    before observed requested wait_type ready X.
Proof.
  intros platform critical sg invocation origin mask saved view pe perr before observed entry image
    requested wait_type bits ready error X [Hfacts Heffect] Hsafe.
  destruct Hfacts as [Hprofile [Hpe [Htype [Hadmission [Hacquire [Himage Holdrange]]]]]].
  destruct Hacquire as [Hinterval [Hvalid [Hsaved Hmask]]].
  unfold time_get_restore_post; Intros current.
  destruct Heffect as [code [Hbits ->]].
  assert (Hprogram : flag_accept_program critical sg invocation view pe (flagImageType observed)
    requested wait_type before (ready,encode_os_err_code code) current).
  { rewrite Htype; eapply flag_accept_program_observed_return; eauto. }
  pose proof (flag_accept_safe_return critical sg invocation view pe (flagImageType observed)
    requested wait_type before ready (encode_os_err_code code) current X Hprogram Hsafe) as Hreturn.
  unfold flag_accept_api_post; rewrite (proj2 (Z.eqb_neq _ _) Hpe), Htype; cbn.
  rewrite Hmask; Exists entry image bits (encode_os_err_code code) current.
  unfold flag_accept_return_safe, flag_accept_effect; entailer!; eauto.
  rewrite <- Htype; exact Hprogram.
Qed.

Lemma byte_clear_high_bit_eq_low_mask__entry_acquire : forall value,
  0 <= value <= 255 -> Z.land value (Z.lnot 128) = Z.land value 127.
Proof.
  intros value Hrange.
  assert (Hmask : Z.land value 255 = value).
  { change (Z.land value (Z.ones 8) = value).
    rewrite Z.land_ones by lia.
    change (value mod 256 = value); apply Z.mod_small; lia. }
  rewrite <- Hmask at 1.
  rewrite <- Z.land_assoc; reflexivity.
Qed.
Lemma land_power_of_two_testbit__entry_acquire : forall value bit,
  0 <= bit ->
  Z.land value (2 ^ bit) = if Z.testbit value bit then 2 ^ bit else 0.
Proof.
  intros value bit Hbit.
  apply Z.bits_inj; intro i.
  rewrite Z.land_spec.
  destruct (Z.eq_dec bit i) as [Heq|Hneq].
  - subst i; rewrite Z.pow2_bits_true by lia.
    destruct (Z.testbit value bit); simpl.
    + symmetry; apply Z.pow2_bits_true; lia.
    + apply eq_sym; apply Z.testbit_0_l.
  - rewrite Z.pow2_bits_false by assumption.
    rewrite Bool.andb_false_r.
    destruct (Z.testbit value bit).
    + symmetry; apply Z.pow2_bits_false; assumption.
    + apply eq_sym; apply Z.testbit_0_l.
Qed.
Lemma land_mask_word16_in_range__flag_bit_effects : forall x mask,
  0 <= mask <= 65535 -> 0 <= Z.land x mask <= 65535.
Proof.
  intros x mask Hmask.
  assert (Hmod : Z.land x mask mod 2 ^ 16 = Z.land x mask).
  { rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc, Z.land_ones by lia.
    rewrite Z.mod_small by (change (0 <= mask < 65536); lia).
    reflexivity. }
  pose proof (Z.mod_pos_bound (Z.land x mask) (2 ^ 16) ltac:(lia)).
  rewrite Hmod in H; change (0 <= Z.land x mask < 65536) in H; lia.
Qed.
Lemma land_word16_truncate_right_eq__flag_bit_effects : forall x y,
  0 <= x <= 65535 ->
  Z.land x (unsigned_last_nbits y 16) = Z.land x y.
Proof.
  intros x y Hx; unfold unsigned_last_nbits.
  rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm y (Z.ones 16)), Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by (change (0 <= x < 65536); lia).
  reflexivity.
Qed.
Lemma flag_word16_eq__flag_bit_effects : forall c x,
  c.(cfgFlagBits) = 16 -> 0 <= x <= 65535 -> flag_word c x = x.
Proof.
  intros c x Hwidth Hrange; unfold flag_word; rewrite Hwidth.
  apply Z.mod_small; change (0 <= x < 65536); lia.
Qed.
