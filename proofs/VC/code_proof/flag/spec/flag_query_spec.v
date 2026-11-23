Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
Require Export Ucos2Verify.VC.code.time.spec.time_get_spec.
Require Export Ucos2Verify.lib.flag.
Require Export Ucos2Verify.lib.kernel_resources.
From SimpleC.SL Require Import Mem SeparationLogic MapLib StoreAux.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The raw view owns precisely the fields actually read: an invalid type
    needs only its byte, whereas type 5 additionally needs the flags word.
    All other caller-owned bytes remain in the arbitrary caller frame.
    A pool view borrows the complete image from the existing global owner.
    It is a fixed storage-slot view, NOT a promise that the live generation
    observed before Save survives acquisition. *)
Inductive FlagQueryView :=
| FlagQueryRaw (image : FlagGroupImage)
| FlagQueryPool (id : FlagID).

Definition flag_query_selected (view : FlagQueryView)
  (state : UCOS2_Verify_State) (image : FlagGroupImage) : Prop :=
  match view with
  | FlagQueryRaw original => image = original
  | FlagQueryPool id => state.(FlagState).(flagImages) id = Some image
  end.

Definition flag_query_address (sg : StableGlobVars) (p : addr)
  (view : FlagQueryView) : Prop :=
  match view with
  | FlagQueryRaw _ => True
  | FlagQueryPool id => p = flag_pool_addr sg id /\
      0 <= id < sg.(osKernelConfig).(cfgMaxFlags)
  end.

(** These are the actual canonical arrow terms for the selected original
    os_flag_grp declaration: UChar at offset 0, UShort at offset 8. *)
Definition flag_query_layout (p : addr) : Prop :=
  (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p /\
  (&(p # "os_flag_grp" ->ₛ "OSFlagFlags")) = p + 8.

Definition flag_query_admission (sg : StableGlobVars) (p : addr)
  (view : FlagQueryView) (before : UCOS2_Verify_State)
  (observed : FlagGroupImage) : Prop :=
  p = 0 \/ (p <> 0 /\ flag_query_layout p /\ flag_query_address sg p view /\
    flag_query_selected view before observed).

Definition flag_query_private_words (p : addr) (view : FlagQueryView) : Assertion :=
  match view with
  | FlagQueryRaw image => p # UChar |-> image.(flagImageType) **
      (p + 8) # UShort |-> image.(flagImageBits)
  | FlagQueryPool _ => emp
  end.

Definition flag_query_resources (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (p : addr) (view : FlagQueryView)
  (state : UCOS2_Verify_State) : Assertion :=
  if Z.eqb p 0 then emp else
  match view with
  | FlagQueryRaw image => p # UChar |-> image.(flagImageType) **
      (if Z.eqb image.(flagImageType) 5 then
        (p + 8) # UShort |-> image.(flagImageBits) **
        mutex_query_closed platform critical sg invocation origin mask state
       else emp)
  | FlagQueryPool _ => mutex_query_closed platform critical sg invocation origin mask state
  end.

Definition flag_query_group_without_type (sg : StableGlobVars) (p : addr)
  (image : FlagGroupImage) : Assertion :=
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  (p + 4) # Ptr |-> image.(flagImageHead) **
  flag_word_rep sg.(osKernelConfig) (p + 8) image.(flagImageBits) **
  store_optional_bytes (p + 8 + flag_word_bytes sg.(osKernelConfig))
    (skipn 3 image.(flagImagePadding)) **
  (if sg.(osKernelConfig).(cfgFlagNames) then
    (p + flag_group_name_offset sg.(osKernelConfig)) # Ptr |-> image.(flagImageName)
   else emp).

Definition flag_query_group_without_bits (sg : StableGlobVars) (p : addr)
  (image : FlagGroupImage) : Assertion :=
  p # UChar |-> image.(flagImageType) **
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  (p + 4) # Ptr |-> image.(flagImageHead) **
  store_optional_bytes (p + 8 + flag_word_bytes sg.(osKernelConfig))
    (skipn 3 image.(flagImagePadding)) **
  (if sg.(osKernelConfig).(cfgFlagNames) then
    (p + flag_group_name_offset sg.(osKernelConfig)) # Ptr |-> image.(flagImageName)
   else emp).

Definition flag_query_pool_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (id : FlagID) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (flag_groups_without sg state.(FlagState) id ** flag_nodes_rep sg state.(FlagState) **
     sg.(g_OSFlagFreeList) # Ptr |->
       (match state.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
     UCOS2_raw_rep_missing_flag sg state).

Lemma flag_query_state_configuration : forall sg state,
  UCOS2_state_inv sg state ->
  sg.(osKernelConfig).(cfgFlagEnabled) = true /\
  sg.(osKernelConfig).(cfgFlagBits) = 16 /\ valid_flag_state sg state.(FlagState).
Proof.
  intros sg state Hvalid.
  assert (Hprofile : selected_kernel_profile sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hflag : valid_flag_configuration sg state.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  unfold selected_kernel_profile, tcb64_configuration in Hprofile.
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true) by tauto.
  unfold valid_flag_configuration in Hflag; rewrite Henabled in Hflag.
  tauto.
Qed.

Lemma flag_query_pool_split : forall sg state id image,
  state.(FlagState).(flagImages) id = Some image ->
  UCOS2_inv sg state |--
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id) image **
    flag_query_pool_frame sg state id.
Proof.
  intros sg state id image Hlookup; rewrite UCOS2_inv_split_flag; Intros.
  match goal with H : UCOS2_state_inv sg state |- _ =>
    destruct (flag_query_state_configuration sg state H) as [Henabled _] end.
  unfold flag_configured_rep; rewrite Henabled; unfold flag_raw_rep.
  sep_apply_l_atomic (flag_groups_split_group sg state.(FlagState) id image Hlookup).
  unfold flag_query_pool_frame; entailer!.
Qed.

Lemma flag_query_pool_merge : forall sg state id image,
  state.(FlagState).(flagImages) id = Some image ->
  flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id) image **
    flag_query_pool_frame sg state id |-- UCOS2_inv sg state.
Proof.
  intros sg state id image Hlookup; unfold flag_query_pool_frame; Intros.
  match goal with H : UCOS2_state_inv sg state |- _ =>
    destruct (flag_query_state_configuration sg state H) as [Henabled _] end.
  sep_apply_l_atomic (flag_groups_merge_group sg state.(FlagState) id image Hlookup).
  rewrite UCOS2_inv_split_flag; unfold flag_configured_rep; rewrite Henabled.
  unfold flag_raw_rep; entailer!.
Qed.

Definition flag_query_type_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (p : addr) (view : FlagQueryView)
  (state : UCOS2_Verify_State) (image : FlagGroupImage) : Assertion :=
  match view with
  | FlagQueryRaw original =>
      if Z.eqb original.(flagImageType) 5 then
        (p + 8) # UShort |-> original.(flagImageBits) **
        mutex_query_closed platform critical sg invocation origin mask state
      else emp
  | FlagQueryPool id => interrupt_platform_running platform invocation origin mask **
      flag_query_group_without_type sg p image ** flag_query_pool_frame sg state id
  end.

(** Same-heap splits/merges are resource transformations only. They neither
    establish environmental stability nor keep a previously observed live
    generation alive. The existing contracted critical intervals supply the
    state transitions; availability at acquisition is proved separately from
    the fixed pool invariant below. *)
Lemma flag_query_type_split : forall platform critical sg invocation origin mask p view state image,
  p <> 0 -> flag_query_address sg p view -> flag_query_selected view state image ->
  flag_query_resources platform critical sg invocation origin mask p view state |--
    p # UChar |-> image.(flagImageType) **
    flag_query_type_frame platform critical sg invocation origin mask p view state image.
Proof.
  intros platform critical sg invocation origin mask p [original|id] state image Hp Haddress Hselected.
  - cbn [flag_query_selected] in Hselected; subst image.
    unfold flag_query_resources; rewrite (proj2 (Z.eqb_neq _ _) Hp); reflexivity.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Hselected.
    unfold flag_query_resources; rewrite (proj2 (Z.eqb_neq _ _) Hp).
    rewrite mutex_query_closed_equiv.
    sep_apply_l_atomic (flag_query_pool_split sg state id image Hselected).
    unfold flag_query_type_frame, flag_group_rep, flag_query_group_without_type; entailer!.
Qed.

Lemma flag_query_type_merge : forall platform critical sg invocation origin mask p view state image,
  p <> 0 -> flag_query_address sg p view -> flag_query_selected view state image ->
  p # UChar |-> image.(flagImageType) **
    flag_query_type_frame platform critical sg invocation origin mask p view state image |--
  flag_query_resources platform critical sg invocation origin mask p view state.
Proof.
  intros platform critical sg invocation origin mask p [original|id] state image Hp Haddress Hselected.
  - cbn [flag_query_selected] in Hselected; subst image.
    unfold flag_query_resources; rewrite (proj2 (Z.eqb_neq _ _) Hp); reflexivity.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Hselected.
    unfold flag_query_resources; rewrite (proj2 (Z.eqb_neq _ _) Hp).
    rewrite mutex_query_closed_equiv.
    sep_apply_r_atomic (flag_query_pool_merge sg state id image Hselected).
    unfold flag_query_type_frame, flag_group_rep, flag_query_group_without_type; entailer!.
Qed.

Lemma flag_query_success_resources_equiv : forall platform critical sg invocation origin mask p view state observed_state image,
  p <> 0 -> flag_query_selected view observed_state image -> image.(flagImageType) = 5 ->
  flag_query_resources platform critical sg invocation origin mask p view state --||--
    (mutex_query_closed platform critical sg invocation origin mask state **
     flag_query_private_words p view).
Proof.
  intros platform critical sg invocation origin mask p [original|id] state observed_state image Hp Hselected Htype;
    unfold flag_query_resources; rewrite (proj2 (Z.eqb_neq _ _) Hp).
  - cbn [flag_query_selected] in Hselected; subst image.
    rewrite Htype, Z.eqb_refl.
    cbn [flag_query_private_words]; rewrite Htype; split; entailer!.
  - cbn [flag_query_private_words]; split; entailer!.
Qed.

(** Availability is derived from the fixed pool's all-slots invariant, not
    from a new platform postcondition or a live-handle stability assumption.
    A legal delete/reuse between the two reads is deliberately admitted. *)
Lemma flag_query_acquired_image : forall sg p view entry,
  flag_query_address sg p view -> UCOS2_state_inv sg entry ->
  exists image, flag_query_selected view entry image.
Proof.
  intros sg p [original|id] entry Haddress Hvalid.
  - exists original; reflexivity.
  - destruct Haddress as [_ Hid].
    destruct (flag_query_state_configuration sg entry Hvalid) as [_ [_ Hflag]].
    destruct Hflag as [_ [Himages _]].
    apply (proj2 (Himages id)); exact Hid.
Qed.

Definition flag_query_flags_frame (sg : StableGlobVars) (p : addr)
  (view : FlagQueryView) (entry : UCOS2_Verify_State) (image : FlagGroupImage) : Assertion :=
  match view with
  | FlagQueryRaw original => p # UChar |-> original.(flagImageType) ** UCOS2_inv sg entry
  | FlagQueryPool id => flag_query_group_without_bits sg p image ** flag_query_pool_frame sg entry id
  end.

Lemma flag_query_flags_split : forall sg p view entry image,
  flag_query_address sg p view -> flag_query_selected view entry image ->
  UCOS2_inv sg entry ** flag_query_private_words p view |--
    coq_prop (0 <= image.(flagImageBits) <= 65535) &&
    ((p + 8) # UShort |-> image.(flagImageBits) ** flag_query_flags_frame sg p view entry image).
Proof.
  intros sg p [original|id] entry image Haddress Hselected.
  - cbn [flag_query_selected] in Hselected; subst image.
    cbn [flag_query_private_words flag_query_flags_frame].
    prop_apply (store_ushort_range (p + 8) original.(flagImageBits)); entailer!.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Hselected.
    cbn [flag_query_private_words].
    sep_apply_l_atomic (flag_query_pool_split sg entry id image Hselected).
    unfold flag_query_pool_frame; Intros.
    match goal with H : UCOS2_state_inv sg entry |- _ =>
      destruct (flag_query_state_configuration sg entry H) as [_ [Hbits _]] end.
    unfold flag_group_rep, flag_word_rep; rewrite Hbits; cbn [Z.eqb Pos.eqb].
    prop_apply (store_ushort_range (flag_pool_addr sg id + 8) image.(flagImageBits)).
    unfold flag_query_flags_frame, flag_query_group_without_bits, flag_query_pool_frame; entailer!.
Qed.

Lemma flag_query_flags_merge : forall sg p view entry image,
  flag_query_address sg p view -> flag_query_selected view entry image ->
  (p + 8) # UShort |-> image.(flagImageBits) ** flag_query_flags_frame sg p view entry image |--
    UCOS2_inv sg entry ** flag_query_private_words p view.
Proof.
  intros sg p [original|id] entry image Haddress Hselected.
  - cbn [flag_query_selected] in Hselected; subst image.
    cbn [flag_query_private_words flag_query_flags_frame]; entailer!.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Hselected.
    cbn [flag_query_private_words flag_query_flags_frame].
    unfold flag_query_pool_frame; Intros.
    match goal with H : UCOS2_state_inv sg entry |- _ =>
      destruct (flag_query_state_configuration sg entry H) as [_ [Hbits _]] end.
    sep_apply_r_atomic (flag_query_pool_merge sg entry id image Hselected).
    unfold flag_group_rep, flag_word_rep; rewrite Hbits; cbn [Z.eqb Pos.eqb].
    unfold flag_query_group_without_bits, flag_query_pool_frame; entailer!.
Qed.

Definition flag_query_observe (view : FlagQueryView) : program UCOS2_Verify_State FlagGroupImage :=
  fun state image after => flag_query_selected view state image /\ after = state.

Definition flag_query_program (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (p : addr) (view : FlagQueryView) : program UCOS2_Verify_State (Z * Z) :=
  if Z.eqb p 0 then StateRelMonad.ret (0, 110) else
  StateRelMonad.bind (flag_query_observe view) (fun observed =>
    if Z.eqb observed.(flagImageType) 5 then
      StateRelMonad.bind (update (critical_region_interval critical sg invocation)) (fun _ =>
        StateRelMonad.bind (flag_query_observe view) (fun acquired =>
          StateRelMonad.bind (update (critical_region_interval critical sg invocation)) (fun _ =>
            StateRelMonad.ret (acquired.(flagImageBits), 0))))
    else StateRelMonad.ret (0, 1)).

Definition flag_query_safe critical sg invocation p view before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (flag_query_program critical sg invocation p view)
    (fun result current => X (fst result) (snd result) current).

Lemma flag_query_program_null : forall critical sg invocation view before,
  flag_query_program critical sg invocation 0 view before (0, 110) before.
Proof. intros; unfold flag_query_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma flag_query_program_wrong_type : forall critical sg invocation p view before observed,
  p <> 0 -> flag_query_selected view before observed -> observed.(flagImageType) <> 5 ->
  flag_query_program critical sg invocation p view before (0, 1) before.
Proof.
  intros critical sg invocation p view before observed Hp Hselected Htype.
  unfold flag_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hp).
  exists observed, before; split; [split; assumption || reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Htype); split; reflexivity.
Qed.

Lemma flag_query_program_success : forall critical sg invocation p view before observed entry acquired current,
  p <> 0 -> flag_query_selected view before observed -> observed.(flagImageType) = 5 ->
  critical_region_interval critical sg invocation before entry ->
  flag_query_selected view entry acquired ->
  critical_region_interval critical sg invocation entry current ->
  flag_query_program critical sg invocation p view before (acquired.(flagImageBits), 0) current.
Proof.
  intros critical sg invocation p view before observed entry acquired current
    Hp Hselected Htype Hentry Hacquired Hcurrent.
  unfold flag_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hp).
  exists observed, before; split; [split; assumption || reflexivity|].
  rewrite Htype, Z.eqb_refl.
  exists tt, entry; split; [exact Hentry|].
  exists acquired, entry; split; [split; assumption || reflexivity|].
  exists tt, current; split; [exact Hcurrent|]; split; reflexivity.
Qed.

Lemma flag_query_program_has_result : forall critical sg invocation p view before observed,
  flag_query_admission sg p view before observed ->
  exists result, flag_query_program critical sg invocation p view before result before.
Proof.
  intros critical sg invocation p view before observed Hadmission.
  destruct Hadmission as [->|[Hp [Hlayout [Haddress Hselected]]]].
  - exists (0, 110); apply flag_query_program_null.
  - destruct (Z.eq_dec observed.(flagImageType) 5) as [Htype|Htype].
    + exists (observed.(flagImageBits), 0).
      eapply flag_query_program_success; eauto; constructor.
    + exists (0, 1); eapply flag_query_program_wrong_type; eauto.
Qed.

Lemma flag_query_safe_return : forall critical sg invocation p view before current flags error X,
  flag_query_program critical sg invocation p view before (flags, error) current ->
  flag_query_safe critical sg invocation p view before X ->
  safeExec (eq current) (StateRelMonad.ret (flags, error))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation p view before current flags error X Hprogram Hsafe.
  unfold flag_query_safe in Hsafe.
  eapply (highstependret_derive (flag_query_program critical sg invocation p view)
    (eq before) (flags, error) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Definition flag_query_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (p perr : addr) (view : FlagQueryView)
  (before : UCOS2_Verify_State) (flags : Z)
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error current,
    coq_prop (flag_query_program critical sg invocation p view before (flags, error) current /\
      safeExec (eq current) (StateRelMonad.ret (flags, error))
        (fun result state => X (fst result) (snd result) state)) &&
    (perr # UChar |-> error **
     flag_query_resources platform critical sg invocation origin mask p view current).

