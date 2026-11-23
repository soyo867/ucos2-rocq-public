Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.flag.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Resource adapters for the OSFlagPend local OS_FLAG_NODE.  The three
    legal flag widths use the existing configured layout: 20/20/24 bytes.
    These adapters do not establish that C's &node denotes a particular
    task-stack interval; that address/provenance and the invocation/instance
    binding remain obligations of the actual call/frame protocol.

    While Flag owns the node, Task owns only the genuine two-part residual.
    The node cannot also occur as five/six None words in a complete stack:
    QCP's None has undefined-byte ownership, not absent ownership. *)
Definition flag_node_stack_word_count (c : KernelConfiguration) : Z :=
  flag_node_size c / sizeof(UINT).

(** Only the retained intervals enter the context map.  Empty intervals
    are omitted; the node's middle interval has no entry, including no
    placeholder None words.  This list introduces no new owner identity. *)
Definition flag_node_stack_residual_fragments (c : KernelConfiguration)
  (region : TaskStackRegion) (lower upper : list (option Z)) : TaskStackFragments :=
  (match lower with
   | [] => []
   | _ :: _ => [(0, Zlength lower, lower)]
   end) ++
  (match upper with
   | [] => []
   | _ :: _ =>
       [(Zlength lower + flag_node_stack_word_count c, region.(stackRegionWords), upper)]
   end).

Lemma flag_node_stack_residual_fragments_rep : forall c region lower upper,
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count c + Zlength upper ->
  task_stack_fragments_rep region (flag_node_stack_residual_fragments c region lower upper) --||--
  task_stack_storage_without_region region lower (flag_node_stack_word_count c) upper.
Proof.
  intros c region lower upper Hsize.
  assert (Hsegment : forall lo hi words,
    hi = lo + Zlength words ->
    task_stack_fragments_rep region
      (match words with [] => [] | _ :: _ => [(lo, hi, words)] end) --||--
    UIntArray.mixed_seg region.(stackRegionBase) lo hi words).
  { intros lo hi words Hlength; destruct words as [|word words].
    - rewrite Zlength_nil in Hlength; replace hi with lo by lia.
      unfold task_stack_fragments_rep; cbn [map].
      rewrite UIntArray.mixed_seg_empty; split.
      + eapply derivable1_trans; [apply derivable1_iter_sepcon_l|].
        cbn [fold_left]; entailer!.
      + eapply derivable1_trans; [|apply derivable1_iter_sepcon_r].
        cbn [fold_left]; entailer!.
    - unfold task_stack_fragments_rep; cbn [map]; split.
      + eapply derivable1_trans; [apply derivable1_iter_sepcon_l|].
        cbn [fold_left task_stack_fragment_rep]; entailer!.
      + eapply derivable1_trans; [|apply derivable1_iter_sepcon_r].
        cbn [fold_left task_stack_fragment_rep]; entailer!. }
  unfold flag_node_stack_residual_fragments.
  rewrite task_stack_fragments_rep_app.
  rewrite (Hsegment 0 (Zlength lower) lower ltac:(lia)).
  rewrite (Hsegment (Zlength lower + flag_node_stack_word_count c)
    region.(stackRegionWords) upper Hsize).
  unfold task_stack_storage_without_region.
  rewrite (UIntArray.mixed_seg_0_shift region.(stackRegionBase)
    (Zlength lower + flag_node_stack_word_count c) region.(stackRegionWords) upper).
  replace (region.(stackRegionWords) - (Zlength lower + flag_node_stack_word_count c))
    with (Zlength upper) by lia.
  split; reflexivity.
Qed.

Lemma flag_node_stack_residual_fragments_in_range : forall c region lower upper,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count c + Zlength upper ->
  task_stack_fragments_in_range region.(stackRegionWords) 0
    (flag_node_stack_residual_fragments c region lower upper).
Proof.
  intros c region lower upper Hbits Hsize.
  assert (Hcount : 0 < flag_node_stack_word_count c).
  { destruct Hbits as [Hbits|[Hbits|Hbits]];
      unfold flag_node_stack_word_count, flag_node_size, flag_node_mode_offset,
        flag_word_bytes, kernel_align4;
      rewrite Hbits; cbn; lia. }
  destruct lower as [|lower_head lower], upper as [|upper_head upper];
    cbn [flag_node_stack_residual_fragments app task_stack_fragments_in_range];
    rewrite ?Zlength_nil, ?Zlength_cons in *;
    try (pose proof (Zlength_nonneg lower) as Hlower);
    try (pose proof (Zlength_nonneg upper) as Hupper);
    repeat split; try exact I; lia.
Qed.

(** Exact pointer words are retained for callers that still read Next after
    unlink.  The word containing mode/padding is conservatively forgotten:
    padding may be uninitialized.  This is an ownership-preserving loss of
    value information, not a claim that the source cleared the word. *)
Definition flag_node_stack_words (c : KernelConfiguration) (v : FlagNodeImage)
  : list (option Z) :=
  [Some v.(flagNodeNext); Some v.(flagNodePrev); Some v.(flagNodeTCB);
   Some v.(flagNodeGroup)] ++
  if Z.eqb c.(cfgFlagBits) 32 then [Some v.(flagNodeMask); None] else [None].

Lemma flag_node_stack_words_length : forall c v,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  Zlength (flag_node_stack_words c v) = flag_node_stack_word_count c.
Proof.
  intros c v [Hbits|[Hbits|Hbits]];
    unfold flag_node_stack_words, flag_node_stack_word_count, flag_node_size,
      flag_node_mode_offset, flag_word_bytes, kernel_align4;
    rewrite Hbits; reflexivity.
Qed.

(** The private initialization phase owns bytes, not the final field values.
    None padding is still owned storage.  Six source stores must establish
    the initialized [flag_node_rep]; this predicate does not perform them. *)
Definition flag_node_uninit_rep (c : KernelConfiguration) (p : addr) : Assertion :=
  p # Ptr |->_ ** (p + 4) # Ptr |->_ ** (p + 8) # Ptr |->_ ** (p + 12) # Ptr |->_ **
  (if Z.eqb c.(cfgFlagBits) 8 then (p + 16) # UChar |->_ else
   if Z.eqb c.(cfgFlagBits) 16 then (p + 16) # UShort |->_ else (p + 16) # UInt |->_) **
  (p + flag_node_mode_offset c) # UChar |->_ **
  store_optional_bytes (p + flag_node_mode_offset c + 1)
    (repeat None (Z.to_nat (flag_node_size c - flag_node_mode_offset c - 1))).

Lemma flag_node_stack_words_to_uninit : forall c p middle,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  p mod 4 = 0 ->
  UIntArray.mixed_full p (flag_node_stack_word_count c) middle |--
  flag_node_uninit_rep c p.
Proof.
  intros c p middle Hbits Halign.
  eapply derivable1_trans; [apply UIntArray.mixed_full_to_undef_full|].
  eapply derivable1_trans; [apply UIntArray.undef_full_to_mixed_full|].
  destruct Hbits as [Hbits|[Hbits|Hbits]];
    unfold flag_node_stack_word_count, flag_node_uninit_rep, flag_node_size,
      flag_node_mode_offset, flag_word_bytes, kernel_align4;
    rewrite Hbits;
    cbn -[store_optional_bytes UIntArray.mixed_full UIntArray.mixed_seg];
    cbv [Pos.to_nat Pos.iter_op];
    cbn -[store_optional_bytes UIntArray.mixed_full UIntArray.mixed_seg];
    rewrite !store_optional_bytes_cons, store_optional_bytes_nil;
    UIntArray.ArraySimplify;
    unfold UIntArray.mixedstoreA, StoreUIntAsElement.undefstoreA;
    cbn; replace (p + 0) with p by lia; Intros;
    sep_apply_l_atomic (proj1 (kernel_undef_store_uint_ptr_equiv p));
    sep_apply_l_atomic (proj1 (kernel_undef_store_uint_ptr_equiv (p + 4)));
    sep_apply_l_atomic (proj1 (kernel_undef_store_uint_ptr_equiv (p + 8)));
    sep_apply_l_atomic (proj1 (kernel_undef_store_uint_ptr_equiv (p + 12))).
  - sep_apply_l_atomic (proj1 (kernel_undef_store_uint_uchar_equiv (p + 16))).
    replace (p + 16 + 1) with (p + 17) by lia.
    replace (p + 16 + 2) with (p + 18) by lia.
    replace (p + 16 + 3) with (p + 19) by lia.
    replace (p + 17 + 1) with (p + 18) by lia.
    replace (p + 18 + 1) with (p + 19) by lia.
    entailer!.
  - sep_apply_l_atomic (proj1 (kernel_undef_store_uint_uchar_equiv (p + 16))).
    rewrite (kernel_undef_store_ushort_uchar_equiv (p + 16)).
    replace (p + 16 + 2) with (p + 18) by lia.
    replace (p + 16 + 3) with (p + 19) by lia.
    replace (p + 18 + 1) with (p + 19) by lia.
    assert (Hhalf_align : (p + 16) mod 2 = 0).
    { apply Z.mod_divide; [lia|].
      apply Z.mod_divide in Halign; [|lia].
      destruct Halign as [k Hmultiple]; exists (2 * k + 8); lia. }
    entailer!.
  - sep_apply_l_atomic (proj1 (kernel_undef_store_uint_uchar_equiv (p + 20))).
    replace (p + 20 + 1) with (p + 21) by lia.
    replace (p + 20 + 2) with (p + 22) by lia.
    replace (p + 20 + 3) with (p + 23) by lia.
    replace (p + 21 + 1) with (p + 22) by lia.
    replace (p + 22 + 1) with (p + 23) by lia.
    entailer!.
Qed.

(** The actual middle array is removed from the caller's ownership.  The
    two residual arrays retain their values; no duplicate complete-stack
    assertion and no initialized node values are returned.  The explicit
    address equality must still come from the real C local-object frame. *)
Lemma flag_node_borrow_stack_region_uninit : forall c region lower middle upper p,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  p = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  p mod 4 = 0 ->
  Zlength middle = flag_node_stack_word_count c ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count c + Zlength upper ->
  task_stack_storage region (lower ++ middle ++ upper) |--
  flag_node_uninit_rep c p **
    task_stack_storage_without_region region lower (flag_node_stack_word_count c) upper.
Proof.
  intros c region lower middle upper p Hbits Haddress Halign Hmiddle Hsize.
  pose proof (task_stack_storage_split_region region lower middle upper) as Hsplit.
  assert (Hlength : region.(stackRegionWords) =
    Zlength lower + Zlength middle + Zlength upper) by (rewrite Hmiddle; exact Hsize).
  specialize (Hsplit Hlength).
  rewrite Hmiddle, <- Haddress in Hsplit.
  eapply derivable1_trans; [exact Hsplit|].
  apply derivable1_sepcon_mono; [apply flag_node_stack_words_to_uninit; assumption|reflexivity].
Qed.

(** The same borrow, with the residual in the representation directly
    consumed by generic context/park rules.  The C local-object address and
    all node-field initialization obligations remain unchanged. *)
Lemma flag_node_borrow_stack_fragments_uninit : forall c region lower middle upper p,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  p = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  p mod 4 = 0 ->
  Zlength middle = flag_node_stack_word_count c ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count c + Zlength upper ->
  task_stack_storage region (lower ++ middle ++ upper) |--
  flag_node_uninit_rep c p **
    task_stack_fragments_rep region (flag_node_stack_residual_fragments c region lower upper).
Proof.
  intros c region lower middle upper p Hbits Haddress Halign Hmiddle Hsize.
  eapply derivable1_trans.
  - exact (flag_node_borrow_stack_region_uninit c region lower middle upper p
      Hbits Haddress Halign Hmiddle Hsize).
  - apply derivable1_sepcon_mono; [reflexivity|].
    exact (proj2 (flag_node_stack_residual_fragments_rep c region lower upper Hsize)).
Qed.

Lemma flag_node_rep_to_stack_words : forall c p v,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  p mod 4 = 0 -> flag_node_image_valid c v ->
  flag_node_rep c p v |--
  UIntArray.mixed_full p (flag_node_stack_word_count c) (flag_node_stack_words c v).
Proof.
  intros c p v Hbits Halign [_ Hpadding].
  unfold flag_node_rep.
  sep_apply_l_atomic (store_ptr_store_uint p v.(flagNodeNext) eq_refl eq_refl).
  sep_apply_l_atomic (store_ptr_store_uint (p + 4) v.(flagNodePrev) eq_refl eq_refl).
  sep_apply_l_atomic (store_ptr_store_uint (p + 8) v.(flagNodeTCB) eq_refl eq_refl).
  sep_apply_l_atomic (store_ptr_store_uint (p + 12) v.(flagNodeGroup) eq_refl eq_refl).
  assert (Hforget_padding :
    store_optional_bytes (p + flag_node_mode_offset c + 1) v.(flagNodePadding) |--
    store_optional_bytes (p + flag_node_mode_offset c + 1)
      (repeat None (List.length v.(flagNodePadding)))).
  { unfold store_optional_bytes; rewrite repeat_length.
    eapply derivable1_trans; [apply UCharArray.mixed_full_to_undef_full|].
    pose proof (UCharArray.undef_full_to_mixed_full
      (p + flag_node_mode_offset c + 1) (Z.of_nat (List.length v.(flagNodePadding)))) as Hmixed.
    rewrite Nat2Z.id in Hmixed; exact Hmixed. }
  sep_apply_l_atomic Hforget_padding.
  destruct Hbits as [Hbits|[Hbits|Hbits]].
  - assert (Hlength : List.length v.(flagNodePadding) = 2%nat).
    { unfold flag_node_size, flag_node_mode_offset, flag_word_bytes, kernel_align4 in Hpadding.
      rewrite Hbits in Hpadding; simpl in Hpadding; lia. }
    unfold flag_word_rep, flag_node_stack_word_count, flag_node_size,
      flag_node_mode_offset, flag_word_bytes, kernel_align4, flag_node_stack_words.
    rewrite Hbits, Hlength; cbn -[store_optional_bytes].
    rewrite !store_optional_bytes_cons, store_optional_bytes_nil.
    replace (p + 17 + 1) with (p + 18) by lia.
    replace (p + 18 + 1) with (p + 19) by lia.
    sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 16) v.(flagNodeMask)).
    sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 17) v.(flagNodeMode)).
    assert (Hword :
      (p + 16) # UChar |->_ ** (p + 17) # UChar |->_ **
      (p + 18) # UChar |->_ ** (p + 19) # UChar |->_ |-- (p + 16) # UInt |->_).
    { assert (Hword_align : (p + 16) mod 4 = 0).
      { rewrite Z.add_mod by lia; rewrite Halign; reflexivity. }
      rewrite (kernel_undef_store_uint_uchar_equiv (p + 16)).
      replace (p + 16 + 1) with (p + 17) by lia.
      replace (p + 16 + 2) with (p + 18) by lia.
      replace (p + 16 + 3) with (p + 19) by lia.
      entailer!. }
    UIntArray.ArraySimplify.
    unfold UIntArray.mixedstoreA, StoreUIntAsElement.storeA, StoreUIntAsElement.undefstoreA.
    cbn -[store_optional_bytes]; replace (p + 0) with p by lia.
    sep_apply_l_atomic Hword; entailer!.
  - assert (Hlength : List.length v.(flagNodePadding) = 1%nat).
    { unfold flag_node_size, flag_node_mode_offset, flag_word_bytes, kernel_align4 in Hpadding.
      rewrite Hbits in Hpadding; simpl in Hpadding; lia. }
    unfold flag_word_rep, flag_node_stack_word_count, flag_node_size,
      flag_node_mode_offset, flag_word_bytes, kernel_align4, flag_node_stack_words.
    rewrite Hbits, Hlength; cbn -[store_optional_bytes].
    replace (p + 18 + 1) with (p + 19) by lia.
    assert (Hword : (p + 16) # UShort |-> v.(flagNodeMask) **
      (p + 18) # UChar |-> v.(flagNodeMode) ** store_optional_bytes (p + 19) [None] |--
      (p + 16) # UInt |->_).
    { replace (p + 18) with (p + 16 + 2) by lia.
      replace (p + 19) with (p + 16 + 3) by lia.
      apply kernel_store_ushort_uchar_padding_forget_uint; [|reflexivity].
      rewrite Z.add_mod by lia; rewrite Halign; reflexivity. }
    UIntArray.ArraySimplify.
    unfold UIntArray.mixedstoreA, StoreUIntAsElement.storeA, StoreUIntAsElement.undefstoreA.
    cbn -[store_optional_bytes]; replace (p + 0) with p by lia.
    sep_apply_l_atomic Hword; entailer!.
  - assert (Hlength : List.length v.(flagNodePadding) = 3%nat).
    { unfold flag_node_size, flag_node_mode_offset, flag_word_bytes, kernel_align4 in Hpadding.
      rewrite Hbits in Hpadding; simpl in Hpadding; lia. }
    unfold flag_word_rep, flag_node_stack_word_count, flag_node_size,
      flag_node_mode_offset, flag_word_bytes, kernel_align4, flag_node_stack_words.
    rewrite Hbits, Hlength; cbn -[store_optional_bytes].
    rewrite !store_optional_bytes_cons, store_optional_bytes_nil.
    replace (p + 20 + 1) with (p + 21) by lia.
    replace (p + 21 + 1) with (p + 22) by lia.
    replace (p + 22 + 1) with (p + 23) by lia.
    sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 20) v.(flagNodeMode)).
    assert (Hword :
      (p + 20) # UChar |->_ ** (p + 21) # UChar |->_ **
      (p + 22) # UChar |->_ ** (p + 23) # UChar |->_ |-- (p + 20) # UInt |->_).
    { assert (Hword_align : (p + 20) mod 4 = 0).
      { rewrite Z.add_mod by lia; rewrite Halign; reflexivity. }
      rewrite (kernel_undef_store_uint_uchar_equiv (p + 20)).
      replace (p + 20 + 1) with (p + 21) by lia.
      replace (p + 20 + 2) with (p + 22) by lia.
      replace (p + 20 + 3) with (p + 23) by lia.
      entailer!. }
    UIntArray.ArraySimplify.
    unfold UIntArray.mixedstoreA, StoreUIntAsElement.storeA, StoreUIntAsElement.undefstoreA.
    cbn -[store_optional_bytes]; replace (p + 0) with p by lia.
    sep_apply_l_atomic Hword; entailer!.
Qed.

(** The direct unlink caller must finish its remaining reads before handing
    this node to the original task/context.  This entailment consumes the
    returned node AND that context's residual; it does not wake, terminate,
    or authorize a task by a pure generation/invocation number. *)
Lemma flag_node_return_loan_merge_stack : forall c region lower upper waiter,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  waiter.(flagNodeAddr) = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  waiter.(flagNodeAddr) mod 4 = 0 ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count c + Zlength upper ->
  flag_node_image_valid c waiter.(flagWaitImage) ->
  flag_node_return_loan c waiter **
    task_stack_storage_without_region region lower (flag_node_stack_word_count c) upper |--
  task_stack_storage region
    (lower ++ flag_node_stack_words c waiter.(flagWaitImage) ++ upper).
Proof.
  intros c region lower upper waiter Hbits Haddress Halign Hsize Himage.
  unfold flag_node_return_loan.
  eapply derivable1_trans with (y :=
    UIntArray.mixed_full waiter.(flagNodeAddr) (flag_node_stack_word_count c)
      (flag_node_stack_words c waiter.(flagWaitImage)) **
    task_stack_storage_without_region region lower (flag_node_stack_word_count c) upper).
  - apply derivable1_sepcon_mono; [apply flag_node_rep_to_stack_words; assumption|reflexivity].
  - rewrite Haddress; apply task_stack_storage_merge_region; [exact Hsize|].
    apply flag_node_stack_words_length; exact Hbits.
Qed.

(** Return consumes the same retained fragments and the node's current
    returned bytes.  It reconstructs the updated stack image, not the old
    middle values, and establishes no invocation/provenance authority. *)
Lemma flag_node_return_loan_merge_stack_fragments : forall c region lower upper waiter,
  c.(cfgFlagBits) = 8 \/ c.(cfgFlagBits) = 16 \/ c.(cfgFlagBits) = 32 ->
  waiter.(flagNodeAddr) = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  waiter.(flagNodeAddr) mod 4 = 0 ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count c + Zlength upper ->
  flag_node_image_valid c waiter.(flagWaitImage) ->
  flag_node_return_loan c waiter **
    task_stack_fragments_rep region (flag_node_stack_residual_fragments c region lower upper) |--
  task_stack_storage region
    (lower ++ flag_node_stack_words c waiter.(flagWaitImage) ++ upper).
Proof.
  intros c region lower upper waiter Hbits Haddress Halign Hsize Himage.
  eapply derivable1_trans.
  - apply derivable1_sepcon_mono; [reflexivity|].
    exact (proj1 (flag_node_stack_residual_fragments_rep c region lower upper Hsize)).
  - exact (flag_node_return_loan_merge_stack c region lower upper waiter
      Hbits Haddress Halign Hsize Himage).
Qed.
