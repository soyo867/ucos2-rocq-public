Require Import Coq.ZArith.ZArith Coq.Strings.String Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The source default name is two actual bytes, '?' and NUL. This interface
    lends those same bytes to the QCP literal view and returns them; neither
    a second allocation nor a new ghost field is introduced. The literal
    pool's existing split/merge axioms remain a tool-library boundary.
    No equality between literals from different translation units is assumed. *)
Lemma store_string_lit_question_mark_equiv : forall p,
  store_stringLit p "?" --||--
    p # UChar |-> 63 ** (p + 1) # UChar |-> 0.
Proof.
  intro p; unfold store_stringLit.
  change (coq_prop (valid_stringLit "?") && CharArray.full p 2 [63; 0] --||--
    p # UChar |-> 63 ** (p + 1) # UChar |-> 0).
  unfold CharArray.full, store_array, store_array_rec, StoreCharAsElement.storeA.
  rewrite sizeof_char.
  replace (p + 0 * 1) with p by lia.
  replace (p + (0 + 1) * 1) with (p + 1) by lia.
  unfold store_char, store_uchar.
  assert (Hvalid : valid_stringLit "?").
  { unfold valid_stringLit, valid_string; cbn; repeat constructor; lia. }
  split; entailer!; try lia.
Qed.

Lemma store_name_bytes_missing_byte_equiv : forall bytes p,
  store_map_missing_i name_byte_rep bytes p --||--
    store_map name_byte_rep (kernel_map_set bytes p None).
Proof.
  intros bytes p.
  assert (Hsame : forall q, q <> p -> bytes q = kernel_map_set bytes p None q).
  { intros; symmetry; apply kernel_map_set_other; assumption. }
  pose proof (store_map_missing_i_equiv name_byte_rep bytes
    (kernel_map_set bytes p None) p Hsame) as [Hforward Hbackward].
  split.
  - eapply derivable1_trans; [exact Hforward|].
    apply store_map_missing_equiv_store_map; apply kernel_map_set_same.
  - eapply derivable1_trans; [|exact Hbackward].
    apply store_map_equiv_store_map_missing; apply kernel_map_set_same.
Qed.

Definition store_name_bytes_without_question_mark (names : NameResourceState)
  (p : addr) : Assertion :=
  store_map_missing_i name_byte_rep (kernel_map_set names.(nameBytes) p None) (p + 1).

Lemma store_name_bytes_split_question_mark : forall names p,
  names.(nameBytes) p = Some 63 -> names.(nameBytes) (p + 1) = Some 0 ->
  store_name_bytes names |--
    store_stringLit p "?" ** store_name_bytes_without_question_mark names p.
Proof.
  intros names p Hchar Hnul; unfold store_name_bytes.
  sep_apply (store_map_split name_byte_rep p 63 names.(nameBytes) Hchar).
  sep_apply (proj1 (store_name_bytes_missing_byte_equiv names.(nameBytes) p)).
  assert (Hnext : kernel_map_set names.(nameBytes) p None (p + 1) = Some 0).
  { rewrite kernel_map_set_other by lia; exact Hnul. }
  sep_apply (store_map_split name_byte_rep (p + 1) 0 _ Hnext).
  unfold store_name_bytes_without_question_mark, name_byte_rep.
  rewrite store_string_lit_question_mark_equiv; entailer!.
Qed.

Lemma store_name_bytes_merge_question_mark : forall names p,
  names.(nameBytes) p = Some 63 -> names.(nameBytes) (p + 1) = Some 0 ->
  store_stringLit p "?" ** store_name_bytes_without_question_mark names p |--
    store_name_bytes names.
Proof.
  intros names p Hchar Hnul; rewrite store_string_lit_question_mark_equiv.
  unfold store_name_bytes_without_question_mark, store_name_bytes.
  assert (Hnext : kernel_map_set names.(nameBytes) p None (p + 1) = Some 0).
  { rewrite kernel_map_set_other by lia; exact Hnul. }
  change (name_byte_rep p 63 ** name_byte_rep (p + 1) 0 **
    store_map_missing_i name_byte_rep (kernel_map_set names.(nameBytes) p None) (p + 1) |--
    store_map name_byte_rep names.(nameBytes)).
  sep_apply (store_map_merge name_byte_rep (p + 1) 0 _ Hnext).
  sep_apply (proj2 (store_name_bytes_missing_byte_equiv names.(nameBytes) p)).
  sep_apply (store_map_merge name_byte_rep p 63 names.(nameBytes) Hchar); entailer!.
Qed.

Definition UCOS2_raw_rep_without_question_mark (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (p : addr) : Assertion :=
  store_name_bytes_without_question_mark state.(NameState) p **
  UCOS2_raw_rep_missing_names sg state.

Lemma UCOS2_raw_rep_split_question_mark : forall sg state p,
  state.(NameState).(nameBytes) p = Some 63 ->
  state.(NameState).(nameBytes) (p + 1) = Some 0 ->
  UCOS2_raw_rep sg state --||--
    store_stringLit p "?" ** UCOS2_raw_rep_without_question_mark sg state p.
Proof.
  intros sg state p Hchar Hnul.
  rewrite (UCOS2_raw_rep_split_module sg state NamesModule).
  unfold UCOS2_module_rep, UCOS2_raw_rep_without_question_mark,
    UCOS2_raw_rep_missing_names; split.
  - sep_apply (store_name_bytes_split_question_mark state.(NameState) p Hchar Hnul); entailer!.
  - sep_apply (store_name_bytes_merge_question_mark state.(NameState) p Hchar Hnul); entailer!.
Qed.

Definition UCOS2_full_inv_without_question_mark (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (p : addr) : Assertion :=
  coq_prop (UCOS2_full_state_inv sg state) &&
  UCOS2_raw_rep_without_question_mark sg state p.

Lemma UCOS2_full_inv_split_question_mark : forall sg state p,
  state.(NameState).(nameBytes) p = Some 63 ->
  state.(NameState).(nameBytes) (p + 1) = Some 0 ->
  UCOS2_full_inv sg state --||--
    store_stringLit p "?" ** UCOS2_full_inv_without_question_mark sg state p.
Proof.
  intros sg state p Hchar Hnul; unfold UCOS2_full_inv,
    UCOS2_full_inv_without_question_mark.
  rewrite (UCOS2_raw_rep_split_question_mark sg state p Hchar Hnul); split; entailer!.
Qed.

(** Caller-side exchange: the whole literal pool is never inferred from
    one name. Its missing-pool frame is supplied by the actual program owner.
    Prefer the split literal view when QCP would otherwise insert that cell
    itself at a function entry. Both views retain exactly the same bytes. *)
Lemma UCOS2_full_inv_question_mark_pool_exchange : forall sg state LitMap,
  state.(NameState).(nameBytes) (LitMap "?") = Some 63 ->
  state.(NameState).(nameBytes) (LitMap "?" + 1) = Some 0 ->
  UCOS2_full_inv sg state ** GlobalStrings_missing LitMap ["?"] --||--
    UCOS2_full_inv_without_question_mark sg state (LitMap "?") ** GlobalStrings LitMap.
Proof.
  intros sg state LitMap Hchar Hnul.
  rewrite (UCOS2_full_inv_split_question_mark sg state (LitMap "?") Hchar Hnul).
  split.
  - sep_apply (GlobalStrings_merge LitMap "?"); entailer!.
  - sep_apply (GlobalStrings_split LitMap "?"); entailer!.
Qed.

(** Diagnostic of a forbidden interface, not a proof of any C branch. A
    registered byte and a second literal owner at that address contradict
    ordinary byte separation even before considering any pool axioms. *)
Lemma store_name_bytes_excludes_duplicate_question_mark : forall names p,
  names.(nameBytes) p = Some 63 ->
  store_name_bytes names ** store_stringLit p "?" |-- coq_prop False.
Proof.
  intros names p Hchar.
  sep_apply (store_name_bytes_split_byte names p 63 Hchar).
  rewrite store_string_lit_question_mark_equiv.
  unfold name_byte_rep, store_uchar; pureIntros.
  sep_apply_l_atomic (dup_store_byte p 63 63); entailer!.
Qed.

Lemma name_question_mark_resources_lookup : forall p q,
  (name_question_mark_resources p).(nameBytes) q = name_question_mark_bytes p q.
Proof.
  intros p q; unfold name_question_mark_resources, name_register_source.
  cbn [nameBytes name_question_mark_source nameStorageDomain].
  destruct (in_dec Z.eq_dec q [p; p + 1]) as [Hin|Hout]; [reflexivity|].
  cbn [empty_name_resources nameBytes]; unfold name_question_mark_bytes.
  destruct (Z.eq_dec q p), (Z.eq_dec q (p + 1)); subst; simpl in Hout; tauto.
Qed.

(** Reclassifying loader-provided constant bytes as the existing static Name
    source. No C store is invented, and address-only facts are insufficient.
    Integration with the rest of the program's static sources remains the
    initialization owner's responsibility. *)
Lemma store_string_lit_question_mark_register : forall p,
  store_stringLit p "?" |-- name_resources_inv (name_question_mark_resources p).
Proof.
  intro p.
  assert (Hchar : (name_question_mark_resources p).(nameBytes) p = Some 63).
  { rewrite name_question_mark_resources_lookup; unfold name_question_mark_bytes.
    destruct (Z.eq_dec p p); congruence. }
  assert (Hnul : (name_question_mark_resources p).(nameBytes) (p + 1) = Some 0).
  { rewrite name_question_mark_resources_lookup; unfold name_question_mark_bytes.
    destruct (Z.eq_dec (p + 1) p); [lia|].
    destruct (Z.eq_dec (p + 1) (p + 1)); congruence. }
  assert (Hdomain : forall q, In q [p; p + 1] <->
    exists b, (name_question_mark_resources p).(nameBytes) q = Some b).
  { intro q; split.
    - intros [Hq|[Hq|Hq]]; [subst q; eauto|subst q; eauto|contradiction].
    - intros [b Hb]; rewrite name_question_mark_resources_lookup in Hb.
      unfold name_question_mark_bytes in Hb.
      destruct (Z.eq_dec q p) as [->|Hq]; [simpl; auto|].
      destruct (Z.eq_dec q (p + 1)) as [->|Hq']; [simpl; auto|discriminate]. }
  unfold name_resources_inv, store_name_bytes, store_map.
  Exists [p; p + 1].
  cbn [map].
  rewrite Hchar, Hnul.
  rewrite store_string_lit_question_mark_equiv.
  unfold name_byte_rep; cbn [map iter_sepcon].
  entailer!.
  - rewrite <- derivable1_iter_sepcon_r; cbn; entailer!.
  - apply name_question_mark_resources_valid.
  - constructor; [simpl; lia|constructor; [simpl; tauto|constructor]].
Qed.

Lemma name_question_mark_resources_readable : forall p,
  readable_name (name_question_mark_resources p) p [63].
Proof.
  intro p.
  assert (Hchar : (name_question_mark_resources p).(nameBytes) p = Some 63).
  { rewrite name_question_mark_resources_lookup; unfold name_question_mark_bytes.
    destruct (Z.eq_dec p p); congruence. }
  assert (Hnul : (name_question_mark_resources p).(nameBytes) (p + 1) = Some 0).
  { rewrite name_question_mark_resources_lookup; unfold name_question_mark_bytes.
    destruct (Z.eq_dec (p + 1) p); [lia|].
    destruct (Z.eq_dec (p + 1) (p + 1)); congruence. }
  unfold readable_name; split.
  - repeat constructor; lia.
  - split.
    + intros i c Hi; destruct i as [|i]; cbn in Hi.
      * injection Hi as <-; rewrite Z.add_0_r; exact Hchar.
      * destruct i; discriminate.
    + exact Hnul.
Qed.

(** The existing QCP program-pool contract supplies the actual literal.
    This is only its static Name-owner component, not the whole OSInit or
    linker proof. In particular the missing pool remains owned exactly once. *)
Lemma global_strings_register_question_mark : forall LitMap,
  GlobalStrings LitMap |--
    name_resources_inv (name_question_mark_resources (LitMap "?")) **
    GlobalStrings_missing LitMap ["?"].
Proof.
  intro LitMap; sep_apply (GlobalStrings_split LitMap "?").
  sep_apply (store_string_lit_question_mark_register (LitMap "?")); entailer!.
Qed.
