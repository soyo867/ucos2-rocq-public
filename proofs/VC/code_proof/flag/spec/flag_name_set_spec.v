Require Export Ucos2Verify.VC.code.flag.spec.flag_query_spec.
Require Export Ucos2Verify.VC.code.memory.spec.mem_name_set_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic MapLib StoreAux.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** NameSet writes one pointer, never the pointed-to bytes. These case-local
    transformers retain bits, links, padding, generation and every other slot.
    A type-5 image is classified as live only after the actual acquisition. *)
Definition flag_name_set_group (g : FlagGroupState) (name : addr) : FlagGroupState :=
  {| flagGeneration := g.(flagGeneration); flagBits := g.(flagBits);
     flagName := name; flagWaitOrder := g.(flagWaitOrder) |}.

Definition flag_name_set_image (v : FlagGroupImage) (name : addr) : FlagGroupImage :=
  {| flagImageType := v.(flagImageType); flagImageHead := v.(flagImageHead);
     flagImageBits := v.(flagImageBits); flagImageName := name;
     flagImagePadding := v.(flagImagePadding) |}.

Definition flag_name_set_pool_update (s : GlobFlagState) id image name : GlobFlagState :=
  {| flagUsed := kernel_map_set s.(flagUsed) id
       (option_map (fun g => flag_name_set_group g name) (s.(flagUsed) id));
     flagFree := s.(flagFree);
     flagImages := kernel_map_set s.(flagImages) id (Some (flag_name_set_image image name));
     flagWaitNodes := s.(flagWaitNodes); flagNextGeneration := s.(flagNextGeneration) |}.

Definition flag_name_set_update (view : FlagQueryView) (s : UCOS2_Verify_State)
  (image : FlagGroupImage) name : UCOS2_Verify_State :=
  match view with
  | FlagQueryRaw _ => s
  | FlagQueryPool id => replace_FlagS (flag_name_set_pool_update s.(FlagState) id image name) s
  end.

Definition flag_name_set_updated_view (view : FlagQueryView) name : FlagQueryView :=
  match view with
  | FlagQueryRaw image => FlagQueryRaw (flag_name_set_image image name)
  | FlagQueryPool id => FlagQueryPool id
  end.

Lemma flag_name_set_pool_type_is_live : forall sg s id image,
  valid_flag_state sg s -> s.(flagImages) id = Some image -> image.(flagImageType) = 5 ->
  exists g, s.(flagUsed) id = Some g.
Proof.
  intros sg s id image [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Himage Htype.
  destruct Hpool as [Hnd [Hrange Hpartition]].
  apply (proj2 (Hpartition id)); split.
  - apply (proj1 (Hdomain id)); eauto.
  - intro Hin; apply in_split in Hin; destruct Hin as [pre [rest E]].
    destruct (Hfree pre id rest E) as [v [Hv [Ht Hhead]]].
    rewrite Himage in Hv; inversion Hv; subst v; lia.
Qed.

Lemma flag_name_set_pool_preserves_validity : forall sg s id g image name,
  valid_flag_state sg s -> s.(flagUsed) id = Some g -> s.(flagImages) id = Some image ->
  valid_flag_state sg (flag_name_set_pool_update s id image name).
Proof.
  intros sg s id g image name [Hpool [Hdomain [Himages [Hused [Hfree Hnodes]]]]] Hg Hv.
  assert (Hnot : ~ In id (flagFree s)).
  { destruct Hpool as [_ [_ Hdom]].
    exact (proj2 (proj1 (Hdom id) (ex_intro _ g Hg))). }
  destruct (Hused id g Hg) as [Hvalid [Hgen [Hwait [v [Him [Htype [Hhead [Hbits Hname]]]]]]]].
  rewrite Hv in Him; inversion Him; subst v.
  unfold valid_flag_state, flag_name_set_pool_update; cbn; rewrite Hg; cbn.
  split; [eapply kernel_pool_replace_preserves_partition; eauto|]. split.
  - intro j; destruct (Z.eq_dec j id) as [->|Hne].
    + rewrite kernel_map_set_same; split.
      * intros _; apply (proj1 (Hdomain id)); eauto.
      * intros _; eauto.
    + rewrite kernel_map_set_other by exact Hne; apply Hdomain.
  - split.
    + intros j v H; unfold kernel_map_set in H; destruct (Z.eq_dec j id) as [->|Hne].
      * inversion H; subst v; exact (Himages id image Hv).
      * eapply Himages; eauto.
    + split.
      * intros j group H; unfold kernel_map_set in H; destruct (Z.eq_dec j id) as [->|Hne].
        -- inversion H; subst group; split; [exact Hvalid|].
           split; [exact Hgen|]. split; [exact Hwait|].
           exists (flag_name_set_image image name); split; [apply kernel_map_set_same|].
           cbn; auto.
        -- destruct (Hused j group H) as [Hvg [Hgg [Hwg [v [Hother_image Hprops]]]]].
           split; [exact Hvg|]. split; [exact Hgg|]. split; [exact Hwg|].
           exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hother_image|exact Hprops].
      * split.
        -- intros pre j rest Hlist.
           assert (Hne : j <> id).
           { intro E; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
           destruct (Hfree pre j rest Hlist) as [v [Hfree_image Hprops]].
           exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hfree_image|exact Hprops].
        -- intros p w H; destruct (Hnodes p w H) as [Hnonzero [Hiv [group [Hgr Hin]]]].
           split; [exact Hnonzero|]. split; [exact Hiv|].
           destruct (Z.eq_dec (flagGroup w) id) as [Heq|Hne].
           ++ rewrite Heq in Hgr; rewrite Hg in Hgr; inversion Hgr; subst group.
              exists (flag_name_set_group g name); split;
                [rewrite Heq; apply kernel_map_set_same|exact Hin].
           ++ exists group; split; [rewrite kernel_map_set_other by exact Hne; exact Hgr|exact Hin].
Qed.

Lemma flag_name_set_pool_new_references : forall s id image name p,
  flag_name_reference (flag_name_set_pool_update s id image name) p ->
  flag_name_reference s p \/ p = name.
Proof.
  intros s id image name p [j [g [Hg Hp]]].
  change (kernel_map_set s.(flagUsed) id
    (option_map (fun old => flag_name_set_group old name) (s.(flagUsed) id)) j = Some g) in Hg.
  unfold kernel_map_set in Hg; destruct (Z.eq_dec j id).
  - destruct (s.(flagUsed) id) as [old|]; inversion Hg; subst g; right; exact Hp.
  - left; exists j, g; auto.
Qed.

Lemma flag_name_set_pool_new_roots : forall sg s id image name p,
  kernel_name_root sg (flag_name_set_update (FlagQueryPool id) s image name) p ->
  kernel_name_root sg s p \/ p = name.
Proof.
  intros sg s id image name p [Ht|[He|[[Hf [Hn Hr]]|[Hm|Htm]]]].
  - left; left; exact Ht.
  - left; right; left; exact He.
  - destruct (flag_name_set_pool_new_references s.(FlagState) id image name p Hr) as [Hold|E].
    + left; right; right; left; auto.
    + right; exact E.
  - left; right; right; right; left; exact Hm.
  - left; right; right; right; right; exact Htm.
Qed.

Lemma flag_name_set_pool_preserves_invariant : forall sg s id image name chars,
  UCOS2_state_inv sg s -> s.(FlagState).(flagImages) id = Some image ->
  image.(flagImageType) = 5 -> readable_name s.(NameState) name chars ->
  UCOS2_state_inv sg (flag_name_set_update (FlagQueryPool id) s image name).
Proof.
  intros sg s id image name chars Hvalid Himage Htype Hread.
  destruct (flag_query_state_configuration sg s Hvalid) as [Henabled [Hbits Hflags]].
  destruct (flag_name_set_pool_type_is_live sg s.(FlagState) id image Hflags Himage Htype) as [g Hg].
  assert (Hnames : kernel_names_valid sg (flag_name_set_update (FlagQueryPool id) s image name)).
  { eapply kernel_names_valid_add_root; [exact (UCOS2_state_inv_names_valid sg s Hvalid)|exact Hread|reflexivity|].
    intros; eapply flag_name_set_pool_new_roots; eassumption. }
  assert (Hnewflag : valid_flag_configuration sg (flag_name_set_pool_update s.(FlagState) id image name)).
  { unfold valid_flag_configuration; rewrite Henabled.
    eapply flag_name_set_pool_preserves_validity; eassumption. }
  assert (Hcross : cross_module_consistency sg (flag_name_set_update (FlagQueryPool id) s image name)).
  { apply cross_module_consistency_flag_nodes_frame; [reflexivity|].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [flag_name_set_update replace_FlagS] in *; tauto.
Qed.

Lemma flag_name_set_update_other_modules : forall view entry image name,
  let checkpoint := flag_name_set_update view entry image name in
  checkpoint.(TskState) = entry.(TskState) /\ checkpoint.(SchedState) = entry.(SchedState) /\
  checkpoint.(IntrState) = entry.(IntrState) /\ checkpoint.(EventState) = entry.(EventState) /\
  checkpoint.(TickState) = entry.(TickState) /\ checkpoint.(MemoryState) = entry.(MemoryState) /\
  checkpoint.(TimerState) = entry.(TimerState) /\ checkpoint.(StatsState) = entry.(StatsState) /\
  checkpoint.(ControlState) = entry.(ControlState) /\ checkpoint.(NameState) = entry.(NameState).
Proof. intros [old|id] entry image name; repeat split; reflexivity. Qed.

Lemma flag_name_set_pool_frame : forall s id image name,
  let updated := flag_name_set_pool_update s id image name in
  updated.(flagFree) = s.(flagFree) /\ updated.(flagWaitNodes) = s.(flagWaitNodes) /\
  updated.(flagNextGeneration) = s.(flagNextGeneration) /\
  (forall other, other <> id -> updated.(flagImages) other = s.(flagImages) other) /\
  (forall other, other <> id -> updated.(flagUsed) other = s.(flagUsed) other).
Proof.
  intros; cbn; repeat split; intros; try reflexivity; apply kernel_map_set_other; assumption.
Qed.

(** Canonical ARM32 layout: the actual arrow terms, not typed pointer addition. *)
Definition flag_name_set_layout (p : addr) : Prop :=
  (&(p # "os_flag_grp" ->ₛ "OSFlagType")) = p /\
  (&(p # "os_flag_grp" ->ₛ "OSFlagName")) = p + 12.

Definition flag_name_set_name_available (view : FlagQueryView)
  (s : UCOS2_Verify_State) name : Prop :=
  match view with
  | FlagQueryRaw _ => True
  | FlagQueryPool _ => exists chars, readable_name s.(NameState) name chars
  end.

(** The source-order admission only constrains actual shared publication.
    It does not require the pre-Save generation or type to survive. A caller
    can establish the protocol from one existing registered readable name;
    no additional byte owner is requested. Raw and early errors need no string. *)
Definition flag_name_set_admission critical sg invocation p name view before : Prop :=
  p <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  sg.(osKernelConfig).(cfgFlagNames) = true /\
  flag_name_set_layout p /\ flag_query_address sg p view /\
  (forall entry image, critical_region_interval critical sg invocation before entry ->
    flag_query_selected view entry image -> image.(flagImageType) = 5 ->
    flag_name_set_name_available view entry name).

Lemma flag_name_set_admission_early_error : forall critical sg invocation p name view before,
  p = 0 \/ name = 0 \/ task_name_set_nesting before <> 0 ->
  flag_name_set_admission critical sg invocation p name view before.
Proof. unfold flag_name_set_admission; intros; tauto. Qed.

Lemma flag_name_set_admission_from_name_source : forall critical sg invocation p name view before,
  sg.(osKernelConfig).(cfgFlagNames) = true -> flag_name_set_layout p -> flag_query_address sg p view ->
  flag_name_set_name_available view before name ->
  flag_name_set_admission critical sg invocation p name view before.
Proof.
  intros critical sg invocation p name view before Hnames Hlayout Haddress Hname Hpe Hpn Hnest.
  split; [exact Hnames|].
  split; [exact Hlayout|]. split; [exact Haddress|].
  intros entry image Hinterval Himage Htype.
  destruct view; [exact I|]. destruct Hname as [chars Hread]; exists chars.
  rewrite <- (critical_region_interval_preserves_name_state critical sg invocation before entry Hinterval).
  exact Hread.
Qed.

Definition flag_name_set_access sg p view entry image : Prop :=
  UCOS2_state_inv sg entry /\ sg.(osKernelConfig).(cfgFlagNames) = true /\ flag_name_set_layout p /\
  flag_query_address sg p view /\ flag_query_selected view entry image.

Definition flag_name_set_publication_ready view entry image name : Prop :=
  image.(flagImageType) = 5 -> flag_name_set_name_available view entry name.

Lemma flag_name_set_acquired_image : forall critical sg invocation p name view before entry,
  p <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  flag_name_set_admission critical sg invocation p name view before ->
  UCOS2_state_inv sg entry -> critical_region_interval critical sg invocation before entry ->
  exists image, flag_name_set_access sg p view entry image /\
    flag_name_set_publication_ready view entry image name.
Proof.
  intros critical sg invocation p name view before entry Hp Hname Hnest Hadmit Hvalid Hinterval.
  destruct (Hadmit Hp Hname Hnest) as [Hnames [Hlayout [Haddress Hready]]].
  destruct (flag_query_acquired_image sg p view entry Haddress Hvalid) as [image Himage].
  exists image; split.
  - unfold flag_name_set_access; auto.
  - intro Htype; eapply Hready; eassumption.
Qed.

(** Raw success only needs a writable pointer cell: its old value is never
    read. The separate result representation records the exact written value. *)
Definition flag_name_set_input_rep (p : addr) (view : FlagQueryView) : Assertion :=
  match view with
  | FlagQueryRaw image => p # UChar |-> image.(flagImageType) **
      (if Z.eqb image.(flagImageType) 5 then (p + 12) # Ptr |->_ else emp)
  | FlagQueryPool _ => emp
  end.

Definition flag_name_set_private_rep (p : addr) (view : FlagQueryView) : Assertion :=
  match view with
  | FlagQueryRaw image => p # UChar |-> image.(flagImageType) **
      (if Z.eqb image.(flagImageType) 5 then (p + 12) # Ptr |-> image.(flagImageName) else emp)
  | FlagQueryPool _ => emp
  end.

Definition flag_name_set_type_frame sg p view entry image : Assertion :=
  match view with
  | FlagQueryRaw original =>
      (if Z.eqb original.(flagImageType) 5 then (p + 12) # Ptr |->_ else emp) **
      UCOS2_inv sg entry
  | FlagQueryPool id => flag_query_group_without_type sg p image ** flag_query_pool_frame sg entry id
  end.

Lemma flag_name_set_type_split : forall sg p view entry image,
  flag_name_set_access sg p view entry image ->
  UCOS2_inv sg entry ** flag_name_set_input_rep p view |--
    p # UChar |-> image.(flagImageType) ** flag_name_set_type_frame sg p view entry image.
Proof.
  intros sg p [original|id] entry image [Hvalid [Hnames [Hlayout [Haddress Himage]]]].
  - cbn [flag_query_selected] in Himage; subst image.
    cbn [flag_name_set_input_rep flag_name_set_type_frame]; entailer!.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Himage.
    cbn [flag_name_set_input_rep flag_name_set_type_frame].
    sep_apply_l_atomic (flag_query_pool_split sg entry id image Himage).
    unfold flag_group_rep, flag_query_group_without_type; entailer!.
Qed.

Lemma flag_name_set_type_merge : forall sg p view entry image,
  flag_name_set_access sg p view entry image ->
  p # UChar |-> image.(flagImageType) ** flag_name_set_type_frame sg p view entry image |--
    UCOS2_inv sg entry ** flag_name_set_input_rep p view.
Proof.
  intros sg p [original|id] entry image [Hvalid [Hnames [Hlayout [Haddress Himage]]]].
  - cbn [flag_query_selected] in Himage; subst image.
    cbn [flag_name_set_input_rep flag_name_set_type_frame]; entailer!.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Himage.
    cbn [flag_name_set_input_rep flag_name_set_type_frame].
    sep_apply_r_atomic (flag_query_pool_merge sg entry id image Himage).
    unfold flag_group_rep, flag_query_group_without_type; entailer!.
Qed.

Lemma flag_name_set_wrong_type_rep_eq : forall p view entry image,
  flag_query_selected view entry image -> image.(flagImageType) <> 5 ->
  flag_name_set_input_rep p view = flag_name_set_private_rep p view.
Proof.
  intros p [original|id] entry image Himage Htype; [|reflexivity].
  cbn [flag_query_selected] in Himage; subst image.
  unfold flag_name_set_input_rep, flag_name_set_private_rep.
  rewrite (proj2 (Z.eqb_neq _ _) Htype); reflexivity.
Qed.

Definition flag_name_set_group_without_name sg p image : Assertion :=
  p # UChar |-> image.(flagImageType) **
  store_optional_bytes (p + 1) (firstn 3 image.(flagImagePadding)) **
  (p + 4) # Ptr |-> image.(flagImageHead) **
  flag_word_rep sg.(osKernelConfig) (p + 8) image.(flagImageBits) **
  store_optional_bytes (p + 8 + flag_word_bytes sg.(osKernelConfig)) (skipn 3 image.(flagImagePadding)).

Definition flag_name_set_name_frame sg p view entry image : Assertion :=
  match view with
  | FlagQueryRaw original => p # UChar |-> original.(flagImageType) ** UCOS2_inv sg entry
  | FlagQueryPool id => flag_name_set_group_without_name sg p image ** flag_query_pool_frame sg entry id
  end.

Lemma flag_name_set_name_configuration : forall sg entry,
  UCOS2_state_inv sg entry -> sg.(osKernelConfig).(cfgFlagNames) = true ->
    sg.(osKernelConfig).(cfgFlagNames) = true /\
    flag_group_name_offset sg.(osKernelConfig) = 12.
Proof.
  intros sg entry Hvalid Hnames.
  assert (Hprofile : selected_kernel_profile sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  unfold selected_kernel_profile, tcb64_configuration in Hprofile.
  assert (Hbits : sg.(osKernelConfig).(cfgFlagBits) = 16) by tauto.
  split; [exact Hnames|].
  unfold flag_group_name_offset, flag_word_bytes, kernel_align4; rewrite Hbits; reflexivity.
Qed.

Lemma flag_name_set_name_split : forall sg p view entry image,
  flag_name_set_access sg p view entry image -> image.(flagImageType) = 5 ->
  p # UChar |-> image.(flagImageType) ** flag_name_set_type_frame sg p view entry image |--
    (p + 12) # Ptr |->_ ** flag_name_set_name_frame sg p view entry image.
Proof.
  intros sg p [original|id] entry image [Hvalid [Hnames [Hlayout [Haddress Himage]]]] Htype.
  - cbn [flag_query_selected] in Himage; subst image.
    cbn [flag_name_set_type_frame flag_name_set_name_frame]; rewrite Htype, Z.eqb_refl; entailer!.
  - destruct (flag_name_set_name_configuration sg entry Hvalid Hnames) as [_ Hoffset].
    cbn [flag_name_set_type_frame flag_name_set_name_frame].
    unfold flag_query_group_without_type, flag_name_set_group_without_name.
    rewrite Hnames, Hoffset.
    sep_apply_l_atomic (store_ptr_undef_store_ptr (p + 12) image.(flagImageName)).
    entailer!.
Qed.

Lemma flag_name_set_name_merge_updated : forall sg p view entry image name,
  flag_name_set_access sg p view entry image -> image.(flagImageType) = 5 ->
  flag_name_set_name_available view entry name ->
  (p + 12) # Ptr |-> name ** flag_name_set_name_frame sg p view entry image |--
  UCOS2_inv sg (flag_name_set_update view entry image name) **
    flag_name_set_private_rep p (flag_name_set_updated_view view name).
Proof.
  intros sg p [original|id] entry image name [Hvalid [Hnames [Hlayout [Haddress Himage]]]] Htype Hread.
  - cbn [flag_query_selected] in Himage; subst image.
    cbn [flag_name_set_name_frame flag_name_set_update flag_name_set_private_rep
      flag_name_set_updated_view flag_name_set_image].
    rewrite Htype; cbn; entailer!.
    rewrite Htype; cbn; entailer!.
  - destruct Haddress as [-> Hid]; cbn [flag_query_selected] in Himage.
    destruct Hread as [chars Hread].
    pose proof (flag_name_set_pool_preserves_invariant sg entry id image name chars
      Hvalid Himage Htype Hread) as Hupdated.
    destruct (flag_query_state_configuration sg entry Hvalid) as [Henabled _].
    destruct (flag_name_set_name_configuration sg entry Hvalid Hnames) as [_ Hoffset].
    cbn [flag_name_set_name_frame flag_name_set_private_rep flag_name_set_updated_view].
    unfold flag_query_pool_frame; Intros.
    pose proof (UCOS2_inv_merge_updated_flag sg entry
      (flag_name_set_update (FlagQueryPool id) entry image name) Hupdated eq_refl) as Hmerge.
    cbn [flag_name_set_update replace_FlagS] in Hmerge.
    unfold flag_configured_rep in Hmerge; rewrite Henabled in Hmerge.
    sep_apply_r_atomic Hmerge.
    unfold flag_raw_rep.
    rewrite replace_FlagS_FlagState.
    pose proof (flag_groups_merge_updated_group sg entry.(FlagState)
      (flag_name_set_pool_update entry.(FlagState) id image name) id
      (flag_name_set_image image name) (kernel_map_set_same _ _ _ _)
      ltac:(intros; symmetry; apply kernel_map_set_other; assumption)) as Hgroups.
    assert (Hgroup : (flag_pool_addr sg id + 12) # Ptr |-> name **
      flag_name_set_group_without_name sg (flag_pool_addr sg id) image |--
      flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg id) (flag_name_set_image image name)).
    { unfold flag_group_rep, flag_name_set_group_without_name, flag_name_set_image.
      cbn; rewrite Hnames, Hoffset; entailer!. }
    sep_apply_l_atomic Hgroup.
    sep_apply_l_atomic Hgroups.
    unfold flag_nodes_rep, flag_name_set_pool_update; cbn; entailer!.
Qed.

(** A successful result observes the pointer that was actually stored; an
    error observes no name write. The first component is *perr, never a C
    return value. Kernel state is the actual endpoint after Restore. *)
Definition FlagNameSetResult := (Z * option addr)%type.
Definition flag_name_set_observation (err : Z) (name : addr) : FlagNameSetResult :=
  (err, if Z.eqb err 0 then Some name else None).

Definition flag_name_set_step (view : FlagQueryView) name
  (entry : UCOS2_Verify_State) : Z -> UCOS2_Verify_State -> Prop :=
  fun err checkpoint => exists image, flag_query_selected view entry image /\
    if Z.eqb image.(flagImageType) 5 then
      err = 0 /\ checkpoint = flag_name_set_update view entry image name
    else err = 1 /\ checkpoint = entry.

Definition flag_name_set_program critical sg invocation view p name
  : program UCOS2_Verify_State FlagNameSetResult :=
  if Z.eqb p 0 then StateRelMonad.ret (flag_name_set_observation 110 name)
  else if Z.eqb name 0 then StateRelMonad.ret (flag_name_set_observation 12 name)
  else StateRelMonad.bind (get' task_name_set_nesting) (fun nesting =>
    if Z.ltb 0 nesting then StateRelMonad.ret (flag_name_set_observation 18 name)
    else StateRelMonad.bind (update (critical_region_interval critical sg invocation)) (fun _ =>
      StateRelMonad.bind (flag_name_set_step view name) (fun err =>
        StateRelMonad.bind (update (critical_region_interval critical sg invocation))
          (fun _ => StateRelMonad.ret (flag_name_set_observation err name))))).

Definition flag_name_set_safe critical sg invocation view p name before
  (X : FlagNameSetResult -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (flag_name_set_program critical sg invocation view p name) X.

Lemma flag_name_set_step_wrong_type : forall view name entry image,
  flag_query_selected view entry image -> image.(flagImageType) <> 5 ->
  flag_name_set_step view name entry 1 entry.
Proof.
  intros; exists image; split; [exact H|].
  rewrite (proj2 (Z.eqb_neq _ _) H0); auto.
Qed.

Lemma flag_name_set_step_success : forall view name entry image,
  flag_query_selected view entry image -> image.(flagImageType) = 5 ->
  flag_name_set_step view name entry 0 (flag_name_set_update view entry image name).
Proof. intros; exists image; split; [exact H|]; rewrite H0, Z.eqb_refl; auto. Qed.

Lemma flag_name_set_program_null_group : forall critical sg invocation view name before,
  flag_name_set_program critical sg invocation view 0 name before
    (flag_name_set_observation 110 name) before.
Proof. intros; unfold flag_name_set_program; split; reflexivity. Qed.

Lemma flag_name_set_program_null_name : forall critical sg invocation view p before,
  p <> 0 -> flag_name_set_program critical sg invocation view p 0 before
    (flag_name_set_observation 12 0) before.
Proof.
  intros; unfold flag_name_set_program; rewrite (proj2 (Z.eqb_neq _ _) H); split; reflexivity.
Qed.

Lemma flag_name_set_program_isr : forall critical sg invocation view p name before,
  p <> 0 -> name <> 0 -> 0 < task_name_set_nesting before ->
  flag_name_set_program critical sg invocation view p name before
    (flag_name_set_observation 18 name) before.
Proof.
  intros critical sg invocation view p name before Hp Hname Hnest.
  unfold flag_name_set_program; rewrite (proj2 (Z.eqb_neq _ _) Hp), (proj2 (Z.eqb_neq _ _) Hname).
  exists (task_name_set_nesting before), before; split; [split; reflexivity|].
  rewrite (proj2 (Z.ltb_lt _ _) Hnest); split; reflexivity.
Qed.

Lemma flag_name_set_program_protected : forall critical sg invocation view p name before entry err checkpoint current,
  p <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  critical_region_interval critical sg invocation before entry ->
  flag_name_set_step view name entry err checkpoint ->
  critical_region_interval critical sg invocation checkpoint current ->
  flag_name_set_program critical sg invocation view p name before
    (flag_name_set_observation err name) current.
Proof.
  intros critical sg invocation view p name before entry err checkpoint current Hp Hname Hnest Hacquire Hstep Hrestore.
  unfold flag_name_set_program; rewrite (proj2 (Z.eqb_neq _ _) Hp), (proj2 (Z.eqb_neq _ _) Hname).
  exists (task_name_set_nesting before), before; split; [split; reflexivity|].
  rewrite Hnest; cbn.
  exists tt, entry; split; [exact Hacquire|].
  exists err, checkpoint; split; [exact Hstep|].
  exists tt, current; split; [exact Hrestore|]; split; reflexivity.
Qed.

Lemma flag_name_set_safe_return : forall critical sg invocation view p name before err current X,
  flag_name_set_program critical sg invocation view p name before
    (flag_name_set_observation err name) current ->
  flag_name_set_safe critical sg invocation view p name before X ->
  safeExec (eq current) (StateRelMonad.ret (flag_name_set_observation err name)) X.
Proof.
  intros critical sg invocation view p name before err current X Hprogram Hsafe.
  eapply (highstependret_derive (flag_name_set_program critical sg invocation view p name)
    (eq before) (flag_name_set_observation err name) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; [exact Hprogram|reflexivity].
Qed.

Lemma flag_name_set_program_result_iff : forall critical sg invocation view p name before result current,
  flag_name_set_program critical sg invocation view p name before result current <->
  if Z.eqb p 0 then result = flag_name_set_observation 110 name /\ before = current
  else if Z.eqb name 0 then result = flag_name_set_observation 12 name /\ before = current
  else if Z.ltb 0 (task_name_set_nesting before) then
    result = flag_name_set_observation 18 name /\ before = current
  else exists entry image,
    critical_region_interval critical sg invocation before entry /\
    flag_query_selected view entry image /\
    if Z.eqb image.(flagImageType) 5 then
      critical_region_interval critical sg invocation (flag_name_set_update view entry image name) current /\
      result = flag_name_set_observation 0 name
    else critical_region_interval critical sg invocation entry current /\
      result = flag_name_set_observation 1 name.
Proof.
  intros critical sg invocation view p name before result current.
  unfold flag_name_set_program; destruct (Z.eqb p 0); [reflexivity|].
  destruct (Z.eqb name 0); [reflexivity|].
  unfold StateRelMonad.bind, get', get.
  split.
  - intros [nesting [observed [[Hnest Hstate] Htail]]]; subst nesting observed.
    destruct (Z.ltb 0 (task_name_set_nesting before)) eqn:E; [exact Htail|].
    destruct Htail as [u [entry [Hacquire [code [checkpoint [Hstep
      [v [returned [Hrestore [Hresult Hcurrent]]]]]]]]]].
    subst returned.
    destruct Hstep as [image [Himage Hstep]].
    exists entry, image; split; [exact Hacquire|]. split; [exact Himage|].
    destruct (Z.eqb image.(flagImageType) 5); destruct Hstep as [Hcode Hcheckpoint];
      subst code checkpoint; auto.
  - intro H; exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    destruct (Z.ltb 0 (task_name_set_nesting before)) eqn:E; [exact H|].
    destruct H as [entry [image [Hacquire [Himage Htail]]]].
    exists tt, entry; split; [exact Hacquire|].
    destruct (Z.eqb image.(flagImageType) 5) eqn:Htype; destruct Htail as [Hrestore Hresult]; subst result.
    + exists 0, (flag_name_set_update view entry image name); split.
      * exists image; split; [exact Himage|]; rewrite Htype; auto.
      * exists tt, current; split; [exact Hrestore|split; reflexivity].
    + exists 1, entry; split.
      * exists image; split; [exact Himage|]; rewrite Htype; auto.
      * exists tt, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma flag_name_set_program_has_result : forall critical sg invocation view p name before,
  0 <= task_name_set_nesting before -> UCOS2_state_inv sg before ->
  flag_name_set_admission critical sg invocation p name view before ->
  exists result current, flag_name_set_program critical sg invocation view p name before result current.
Proof.
  intros critical sg invocation view p name before Hnest Hvalid Hadmit.
  destruct (Z.eq_dec p 0) as [->|Hp].
  - exists (flag_name_set_observation 110 name), before; apply flag_name_set_program_null_group.
  - destruct (Z.eq_dec name 0) as [->|Hname].
    + exists (flag_name_set_observation 12 0), before; apply flag_name_set_program_null_name; exact Hp.
    + destruct (Z_lt_dec 0 (task_name_set_nesting before)) as [Hisr|Htask].
      * exists (flag_name_set_observation 18 name), before; apply flag_name_set_program_isr; assumption.
      * assert (Hzero : task_name_set_nesting before = 0) by lia.
        destruct (Hadmit Hp Hname Hzero) as [Hnames [Hlayout [Haddress Hread]]].
        destruct (flag_query_acquired_image sg p view before Haddress Hvalid) as [image Himage].
        destruct (Z.eq_dec image.(flagImageType) 5) as [Htype|Htype].
        -- exists (flag_name_set_observation 0 name), (flag_name_set_update view before image name).
           eapply flag_name_set_program_protected; try eassumption; try constructor.
           apply flag_name_set_step_success; assumption.
        -- exists (flag_name_set_observation 1 name), before.
           eapply flag_name_set_program_protected; try eassumption; try constructor.
           eapply flag_name_set_step_wrong_type; eassumption.
Qed.

Definition flag_name_set_result_view view name err : FlagQueryView :=
  if Z.eqb err 0 then flag_name_set_updated_view view name else view.

Definition flag_name_set_return_resources platform critical sg invocation origin mask
  view p name before err current : Assertion :=
  if Z.eqb p 0 then emp else if Z.eqb name 0 then emp else
  mutex_query_closed platform critical sg invocation origin mask current **
  (if Z.ltb 0 (task_name_set_nesting before) then emp else
    flag_name_set_private_rep p (flag_name_set_result_view view name err)).

Definition flag_name_set_api_post platform critical sg invocation origin mask
  view p name error_addr before (X : FlagNameSetResult -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX err current,
    coq_prop (flag_name_set_program critical sg invocation view p name before
        (flag_name_set_observation err name) current /\
      safeExec (eq current) (StateRelMonad.ret (flag_name_set_observation err name)) X) &&
    (flag_name_set_return_resources platform critical sg invocation origin mask
       view p name before err current ** error_addr # UChar |-> err).

Lemma flag_name_set_isr_return : forall platform critical sg invocation origin mask
  view p name error_addr before X caller_frame,
  p <> 0 -> name <> 0 -> 0 < task_name_set_nesting before ->
  flag_name_set_safe critical sg invocation view p name before X ->
  mutex_query_closed platform critical sg invocation origin mask before **
    error_addr # UChar |-> 18 ** caller_frame |--
  flag_name_set_api_post platform critical sg invocation origin mask
    view p name error_addr before X ** caller_frame.
Proof.
  intros platform critical sg invocation origin mask view p name error_addr before X
    caller_frame Hp Hname Hnest Hsafe.
  pose proof (flag_name_set_program_isr critical sg invocation view p name before
    Hp Hname Hnest) as Hprogram.
  pose proof (flag_name_set_safe_return critical sg invocation view p name before 18 before X
    Hprogram Hsafe) as Hreturn.
  unfold flag_name_set_api_post; Exists 18 before.
  unfold flag_name_set_return_resources.
  rewrite (proj2 (Z.eqb_neq _ _) Hp), (proj2 (Z.eqb_neq _ _) Hname),
    (proj2 (Z.ltb_lt _ _) Hnest).
  entailer!.
Qed.

Lemma flag_name_set_protected_return : forall platform critical sg invocation origin mask saved
  view p name error_addr before entry err checkpoint X caller_frame,
  p <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  flag_name_set_safe critical sg invocation view p name before X ->
  mem_query_acquire_facts critical sg invocation mask saved before entry ->
  flag_name_set_step view name entry err checkpoint ->
  mem_query_restore_post platform critical sg invocation origin saved checkpoint **
    flag_name_set_private_rep p (flag_name_set_result_view view name err) **
    error_addr # UChar |-> err ** caller_frame |--
  flag_name_set_api_post platform critical sg invocation origin mask
    view p name error_addr before X ** caller_frame.
Proof.
  intros platform critical sg invocation origin mask saved view p name error_addr
    before entry err checkpoint X caller_frame Hp Hname Hnest Hsafe Hacquire Hstep.
  destruct Hacquire as [Hinterval [Hbefore [Hentry [Hsaved Hmask]]]].
  unfold mem_query_restore_post; Intros current.
  match goal with
  | Hrestore : critical_region_interval critical sg invocation checkpoint current |- _ =>
      pose proof (flag_name_set_program_protected critical sg invocation view p name before
        entry err checkpoint current Hp Hname Hnest Hinterval Hstep Hrestore) as Hprogram
  end.
  pose proof (flag_name_set_safe_return critical sg invocation view p name before err current X
    Hprogram Hsafe) as Hreturn.
  unfold flag_name_set_api_post; Exists err current.
  unfold flag_name_set_return_resources.
  rewrite (proj2 (Z.eqb_neq _ _) Hp), (proj2 (Z.eqb_neq _ _) Hname), Hnest.
  rewrite Hmask; entailer!.
Qed.
