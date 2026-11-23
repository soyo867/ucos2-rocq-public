Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This source-level contract is for the selected five-group initializer.
    Startup serialization is an external calling condition: no interrupt,
    task or other initializer accesses these exclusively owned bytes.  No
    running kernel invariant is required or established by this function. *)
Definition flag_init_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgFlagEnabled) = true /\
  sg.(osKernelConfig).(cfgFlagBits) = 16 /\
  sg.(osKernelConfig).(cfgMaxFlags) = 5 /\
  sg.(osKernelConfig).(cfgFlagNames) = true.

(** Only Flag's own configuration affects this initializer.  The selected
    and joint Multi/Names/Profile configurations have the same Flag layout;
    no old Task/Event configuration is imposed on the untouched frame. *)
Lemma flag_init_profile_of_supported_configuration : forall sg,
  sg.(osKernelConfig) = selected_kernel_configuration \/
  sg.(osKernelConfig) = full_features_kernel_configuration ->
  flag_init_profile sg.
Proof.
  intros sg [Hconfig | Hconfig]; unfold flag_init_profile;
    rewrite Hconfig; repeat split; reflexivity.
Qed.

Definition flag_init_global_addresses (sg : StableGlobVars) (pool root : Z) : Prop :=
  sg.(g_OSFlagTbl) = pool /\ sg.(g_OSFlagFreeList) = root.

(** Bind the actual CNotation arrow expressions emitted by QCP, rather
    than the unrelated standalone [field_address] symbol.  This is the
    selected OS_FLAG_GRP source/ABI layout, not a linker address or a
    premise about the incoming contents of the pool. *)
Definition flag_init_layout (sg : StableGlobVars) : Prop :=
  0 <= sg.(g_OSFlagTbl) /\ sg.(g_OSFlagTbl) + 80 <= 4294967295 /\
  sg.(g_OSFlagTbl) mod 4 = 0 /\
  sizeof ("os_flag_grp") = 16 /\
  (forall i, 0 <= i < 5 ->
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSFlagTbl) + i * 16) (FET_alias "os_flag_grp")) "OSFlagType")) =
      sg.(g_OSFlagTbl) + i * 16 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSFlagTbl) + i * 16) (FET_alias "os_flag_grp")) "OSFlagWaitList")) =
      sg.(g_OSFlagTbl) + i * 16 + 4 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSFlagTbl) + i * 16) (FET_alias "os_flag_grp")) "OSFlagFlags")) =
      sg.(g_OSFlagTbl) + i * 16 + 8 /\
    eval_addr_expr (RE_addr_of (LE_arrow_field
      (RE_const (sg.(g_OSFlagTbl) + i * 16) (FET_alias "os_flag_grp")) "OSFlagName")) =
      sg.(g_OSFlagTbl) + i * 16 + 12).

Definition flag_init_pre (sg : StableGlobVars) : Assertion :=
  mem_clr_pre sg.(g_OSFlagTbl) 80 ** sg.(g_OSFlagFreeList) # Ptr |->_ .

(** [flag_initial_image] is the mathematical endpoint, independently of
    the loop's order.  Its free links follow [Zrange 0 5], all flags and
    padding are zero, and every name is the actual question-mark literal. *)
Definition flag_init_prefix (sg : StableGlobVars) (name i : Z) : Assertion :=
  iter_sepcon (map (fun j =>
    flag_group_rep sg.(osKernelConfig) (flag_pool_addr sg j)
      (flag_initial_image sg name j)) (Zrange 0 i)).

Definition flag_init_loop_state (sg : StableGlobVars) (name i : Z) : Assertion :=
  flag_init_prefix sg name i **
  mem_clr_post (sg.(g_OSFlagTbl) + i * 16) (80 - i * 16) **
  sg.(g_OSFlagFreeList) # Ptr |->_ .

Definition flag_init_group_residual (p : Z) : Assertion :=
  store_optional_bytes (p + 1) [Some 0; Some 0; Some 0] **
  (p + 8) # UShort |-> 0 **
  store_optional_bytes (p + 10) [Some 0; Some 0].

Definition flag_init_loop_residual (sg : StableGlobVars) (name i : Z) : Assertion :=
  flag_init_prefix sg name i **
  flag_init_group_residual (sg.(g_OSFlagTbl) + i * 16) **
  mem_clr_post (sg.(g_OSFlagTbl) + (i + 1) * 16) (80 - (i + 1) * 16) **
  sg.(g_OSFlagFreeList) # Ptr |->_ .

Definition flag_init_post (sg : StableGlobVars) (name : Z) : Assertion :=
  flag_init_prefix sg name 5 ** sg.(g_OSFlagFreeList) # Ptr |-> sg.(g_OSFlagTbl).

(** No extra C writes create empty maps or an allocation generation.
    These are the abstraction chosen for the newly initialized resources. *)
Lemma flag_init_initial_valid : forall sg name,
  flag_init_profile sg -> valid_flag_state sg (flag_initial sg name).
Proof.
  intros sg name [_ [Hbits _]]; apply flag_initial_valid.
  - rewrite Hbits; lia.
  - unfold flag_group_name_offset, flag_word_bytes; rewrite Hbits; cbn; lia.
Qed.

Lemma flag_init_pre_mem_clr_equiv : forall sg,
  flag_init_pre sg --||--
    mem_clr_pre sg.(g_OSFlagTbl) 80 ** sg.(g_OSFlagFreeList) # Ptr |->_ .
Proof. intros; unfold flag_init_pre; split; entailer!. Qed.

Lemma flag_init_empty_prefix : forall sg name,
  flag_init_prefix sg name 0 --||-- emp.
Proof. intros; unfold flag_init_prefix; cbn; split; entailer!. Qed.

Lemma flag_init_mem_clr_to_loop_state : forall sg name,
  mem_clr_post sg.(g_OSFlagTbl) 80 ** sg.(g_OSFlagFreeList) # Ptr |->_ |--
  flag_init_loop_state sg name 0.
Proof.
  intros; unfold flag_init_loop_state; rewrite flag_init_empty_prefix.
  replace (g_OSFlagTbl sg + 0 * 16) with (g_OSFlagTbl sg) by lia.
  replace (80 - 0 * 16) with 80 by lia; entailer!.
Qed.

Lemma flag_init_loop_state_to_mem_clr : forall sg name,
  flag_init_loop_state sg name 0 |--
  mem_clr_post sg.(g_OSFlagTbl) 80 ** sg.(g_OSFlagFreeList) # Ptr |->_ .
Proof.
  intros; unfold flag_init_loop_state; rewrite flag_init_empty_prefix.
  replace (g_OSFlagTbl sg + 0 * 16) with (g_OSFlagTbl sg) by lia.
  replace (80 - 0 * 16) with 80 by lia; entailer!.
Qed.

(** The two source fields below use the SAME zero bytes as MemClr.
    The reverse implications retain every byte; the explicit alignments are
    required only when the byte view is folded into a typed field. *)
Lemma flag_init_zero_bits_uchar_equiv : forall p,
  p mod 2 = 0 ->
  p # UShort |-> 0 --||-- p # UChar |-> 0 ** (p + 1) # UChar |-> 0.
Proof.
  intros p Halign; unfold store_ushort, store_2byte; split.
  - Intros b0 b1.
    assert (Hbytes : b0 mod 256 = 0 /\ b1 mod 256 = 0).
    { unfold merge_short, LittleEndian.merge_short in *.
      pose proof (Z.mod_pos_bound b0 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound b1 256 ltac:(lia)).
      change (2 ^ 8) with 256 in *; change (0 mod (2 ^ 16)) with 0 in *; lia. }
    sep_apply_l_atomic (store_byte_eqm p b0 0
      ltac:(apply eqm_iff_mod_eq; change (b0 mod 256 = 0); tauto)).
    sep_apply_l_atomic (store_byte_eqm (p + 1) b1 0
      ltac:(apply eqm_iff_mod_eq; change (b1 mod 256 = 0); tauto)).
    unfold store_uchar; entailer!;
      unfold isvalidptr_short, isvalidptr_char in *; lia.
  - unfold store_uchar; Intros; Exists 0 0; entailer!.
    + unfold isvalidptr_short, aligned_2, isvalidptr_char in *; lia.
Qed.

Lemma flag_init_zero_link_uchar_equiv : forall p,
  p mod 4 = 0 ->
  p # Ptr |-> 0 --||--
  p # UChar |-> 0 ** (p + 1) # UChar |-> 0 **
  (p + 2) # UChar |-> 0 ** (p + 3) # UChar |-> 0.
Proof.
  intros p Halign; unfold store_ptr.
  change (ptr_size) with 4%nat; cbn; unfold store_4byte; split.
  - Intros b0 b1 b2 b3.
    assert (Hbytes : b0 mod 256 = 0 /\ b1 mod 256 = 0 /\
      b2 mod 256 = 0 /\ b3 mod 256 = 0).
    { unfold merge_int, LittleEndian.merge_int in *.
      pose proof (Z.mod_pos_bound b0 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound b1 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound b2 256 ltac:(lia)).
      pose proof (Z.mod_pos_bound b3 256 ltac:(lia)).
      change (2 ^ 8) with 256 in *; change (2 ^ 16) with 65536 in *;
        change (2 ^ 24) with 16777216 in *; change (0 mod (2 ^ 32)) with 0 in *; lia. }
    sep_apply_l_atomic (store_byte_eqm p b0 0
      ltac:(apply eqm_iff_mod_eq; change (b0 mod 256 = 0); tauto)).
    sep_apply_l_atomic (store_byte_eqm (p + 1) b1 0
      ltac:(apply eqm_iff_mod_eq; change (b1 mod 256 = 0); tauto)).
    sep_apply_l_atomic (store_byte_eqm (p + 2) b2 0
      ltac:(apply eqm_iff_mod_eq; change (b2 mod 256 = 0); tauto)).
    sep_apply_l_atomic (store_byte_eqm (p + 3) b3 0
      ltac:(apply eqm_iff_mod_eq; change (b3 mod 256 = 0); tauto)).
    unfold store_uchar; entailer!; unfold isvalidptr, isvalidptr_char in *;
      change ptr_size_Z with 4 in *; change Byte.max_unsigned with 255 in *; lia.
  - unfold store_uchar; Intros; Exists 0 0 0 0; entailer!;
      unfold isvalidptr, valid_ptr_value, Arch32.aligned, isvalidptr_char in *;
      change ptr_size_Z with 4 in *; change Arch32.ptr_align with 4 in *;
      change addr_max_unsigned with 4294967295 in *; try reflexivity; lia.
Qed.

Lemma flag_init_zero_group_bytes_equiv : forall p,
  p mod 4 = 0 ->
  mem_clr_post p 16 --||--
  p # UChar |-> 0 ** (p + 4) # Ptr |-> 0 ** (p + 12) # Ptr |-> 0 **
  flag_init_group_residual p.
Proof.
  intros p Halign.
  assert (Hhalf : p mod 2 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Halign; [|lia].
    destruct Halign as [k Hk]; exists (2 * k); lia. }
  unfold mem_clr_post, flag_init_group_residual, store_optional_bytes.
  rewrite flag_init_zero_link_uchar_equiv by
    (rewrite Z.add_mod by lia; rewrite Halign; reflexivity).
  rewrite flag_init_zero_link_uchar_equiv by
    (rewrite Z.add_mod by lia; rewrite Halign; reflexivity).
  rewrite flag_init_zero_bits_uchar_equiv by
    (rewrite Z.add_mod by lia; rewrite Hhalf; reflexivity).
  unfold UCharArray.full, UCharArray.mixed_full, UCharArray.seg, UCharArray.mixed_seg,
    store_array, store_array_rec, UCharArray.mixedstoreA,
    StoreUCharAsElement.storeA, repeat_Z; cbn.
  change (Pos.to_nat 16) with 16%nat; cbn.
  repeat rewrite Z.mul_1_r; repeat rewrite <- Z.add_assoc; cbn.
  repeat rewrite Z.add_0_r.
  split; entailer!.
Qed.

Lemma flag_init_post_to_flag_raw_rep : forall sg name,
  flag_init_profile sg ->
  flag_init_post sg name |-- flag_raw_rep sg (flag_initial sg name).
Proof.
  intros sg name Hprofile.
  assert (Hnodes : flag_nodes_rep sg (flag_initial sg name) --||-- emp).
  { unfold flag_nodes_rep, flag_wait_nodes_rep, flag_initial; cbn.
    apply store_map_empty.
    - exists []; split; [intros; split; [contradiction|intros [w Hw]; discriminate]|constructor].
    - intros; left; reflexivity. }
  unfold flag_raw_rep; rewrite Hnodes.
  unfold flag_init_post, flag_init_prefix, flag_groups_rep, store_map.
  Exists ([0; 1; 2; 3; 4]).
  destruct Hprofile as [_ [_ [Hcount _]]].
  unfold flag_initial; rewrite Hcount; cbn.
  entailer!.
  - simpl; replace (flag_pool_addr sg 0) with (g_OSFlagTbl sg)
      by (unfold flag_pool_addr; lia); entailer!.
  - repeat constructor; simpl; lia.
  - intros i; split.
    + intros Hi; simpl in Hi; destruct Hi as [Hi|[Hi|[Hi|[Hi|[Hi|Hbad]]]]];
        try contradiction; subst i; eexists; reflexivity.
    + intros [v Hv]. destruct ((0 <=? i) && (i <? 5))%bool eqn:Hi; [|discriminate].
      apply Bool.andb_true_iff in Hi; destruct Hi as [Hl Hh].
      apply Z.leb_le in Hl; apply Z.ltb_lt in Hh; simpl; lia.
Qed.

Lemma flag_init_post_to_flag_inv : forall sg name,
  flag_init_profile sg ->
  flag_init_post sg name |-- flag_inv sg (flag_initial sg name).
Proof.
  intros sg name Hprofile.
  pose proof (flag_init_initial_valid sg name Hprofile) as Hvalid.
  unfold flag_inv, valid_flag_configuration, flag_configured_rep.
  assert (Henabled : cfgFlagEnabled (osKernelConfig sg) = true)
    by (destruct Hprofile as [Henabled _]; exact Henabled).
  rewrite Henabled.
  sep_apply_l_atomic (flag_init_post_to_flag_raw_rep sg name Hprofile); entailer!.
Qed.

Lemma sublist_repeat_Z_eq__flag_pool_initialization : forall (A : Type)
  (a : A) lo hi n,
  0 <= lo <= hi -> hi <= n ->
  sublist lo hi (repeat_Z a n) = repeat_Z a (hi - lo).
Proof.
  intros A a lo hi n Hrange Hn.
  assert (Hfirst : forall k m,
    firstn k (repeat a m) = repeat a (Nat.min k m)).
  { induction k; intros [|m]; cbn; auto. rewrite IHk; reflexivity. }
  assert (Hskip : forall k m,
    skipn k (repeat a m) = repeat a (m - k)).
  { induction k; intros [|m]; cbn; auto. }
  unfold sublist, repeat_Z; rewrite Hfirst, Hskip.
  f_equal; lia.
Qed.
Lemma mem_clr_post_split__flag_pool_initialization : forall p n m,
  0 <= n <= m ->
  mem_clr_post p m |--
  mem_clr_post p n ** mem_clr_post (p + n) (m - n).
Proof.
  intros p n m Hrange; unfold mem_clr_post.
  sep_apply_l_atomic (UCharArray.full_split_to_full p n m
    (repeat_Z 0 m) Hrange).
  rewrite !sublist_repeat_Z_eq__flag_pool_initialization by lia.
  replace (n - 0) with n by lia.
  change StoreUCharAsElement.sizeA with 1.
  rewrite Z.mul_1_r; entailer!.
Qed.
Lemma flag_init_loop_state_split_group__flag_pool_initialization :
  forall sg name i,
  flag_init_layout sg -> 0 <= i < 5 ->
  flag_init_loop_state sg name i |--
  (g_OSFlagTbl sg + i * 16) # UChar |-> 0 **
  (g_OSFlagTbl sg + i * 16 + 4) # Ptr |-> 0 **
  (g_OSFlagTbl sg + i * 16 + 12) # Ptr |-> 0 **
  flag_init_loop_residual sg name i.
Proof.
  intros sg name i Hlayout Hi.
  destruct Hlayout as [_ [_ [Halign _]]].
  unfold flag_init_loop_state, flag_init_loop_residual.
  sep_apply_l_atomic (mem_clr_post_split__flag_pool_initialization
    (g_OSFlagTbl sg + i * 16) 16 (80 - i * 16) ltac:(lia)).
  replace (g_OSFlagTbl sg + i * 16 + 16) with
    (g_OSFlagTbl sg + (i + 1) * 16) by lia.
  replace (80 - i * 16 - 16) with (80 - (i + 1) * 16) by lia.
  rewrite flag_init_zero_group_bytes_equiv by
    (rewrite Z.add_mod, Z.mul_mod by lia; rewrite Halign;
     change ((0 + (i mod 4 * 0) mod 4) mod 4 = 0);
     rewrite Z.mul_0_r; reflexivity).
  entailer!.
Qed.
Lemma flag_init_prefix_snoc_eq__flag_pool_initialization : forall sg name i,
  0 <= i ->
  flag_init_prefix sg name (i + 1) =
  flag_init_prefix sg name i **
  flag_group_rep (osKernelConfig sg) (flag_pool_addr sg i)
    (flag_initial_image sg name i).
Proof.
  intros sg name i Hi.
  assert (Hrange : Zrange 0 (i + 1) = Zrange 0 i ++ [i]).
  { unfold Zrange.
    replace (Z.to_nat (i + 1 - 0)) with
      (Z.to_nat (i - 0) + 1)%nat by lia.
    rewrite Zrange_aux_app.
    replace (0 + Z.of_nat (Z.to_nat (i - 0))) with i by lia.
    reflexivity. }
  unfold flag_init_prefix; rewrite Hrange, map_app.
  unfold iter_sepcon; rewrite fold_left_app; reflexivity.
Qed.
Lemma flag_initial_image_rep_equiv__flag_pool_initialization : forall sg name i,
  flag_init_profile sg -> 0 <= i < 5 ->
  flag_group_rep (osKernelConfig sg) (flag_pool_addr sg i)
    (flag_initial_image sg name i) --||--
  (g_OSFlagTbl sg + i * 16) # UChar |-> 0 **
  (g_OSFlagTbl sg + i * 16 + 4) # Ptr |->
    (if i <? 4 then g_OSFlagTbl sg + (i + 1) * 16 else 0) **
  (g_OSFlagTbl sg + i * 16 + 12) # Ptr |-> name **
  flag_init_group_residual (g_OSFlagTbl sg + i * 16).
Proof.
  intros sg name i Hprofile Hi.
  assert (Hcases : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  unfold flag_group_rep, flag_initial_image, flag_initial_padding,
    flag_word_rep, flag_pool_addr, flag_init_group_residual.
  destruct Hprofile as [_ [Hbits [Hcount Hnames]]].
  unfold flag_group_size, flag_group_name_offset, flag_word_bytes.
  rewrite Hbits, Hcount, Hnames.
  destruct Hcases as [-> | [-> | [-> | [-> | ->]]]]; cbn;
    change (Pos.to_nat 5) with 5%nat; cbn;
    repeat rewrite Z.add_0_r; repeat rewrite <- Z.add_assoc;
    split; entailer!.
Qed.
Lemma flag_init_loop_residual_merge_group__flag_pool_initialization :
  forall sg name i,
  flag_init_profile sg -> 0 <= i < 5 ->
  (g_OSFlagTbl sg + i * 16) # UChar |-> 0 **
  (g_OSFlagTbl sg + i * 16 + 4) # Ptr |->
    (if i <? 4 then g_OSFlagTbl sg + (i + 1) * 16 else 0) **
  (g_OSFlagTbl sg + i * 16 + 12) # Ptr |-> name **
  flag_init_loop_residual sg name i |--
  flag_init_loop_state sg name (i + 1).
Proof.
  intros sg name i Hprofile Hi.
  unfold flag_init_loop_residual, flag_init_loop_state.
  rewrite flag_init_prefix_snoc_eq__flag_pool_initialization by lia.
  rewrite (flag_initial_image_rep_equiv__flag_pool_initialization
    sg name i Hprofile Hi).
  entailer!.
Qed.
