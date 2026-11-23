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
Require Import Ucos2Verify.lib.task_storage.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The address vocabulary follows the actual storage owner, including the
    two padding bytes whose positions move when Multi is enabled.  The
    numeric ABI equality below is an explicit premise, never an axiom. *)
Definition tcb_layout_field_address (multi : bool) (p : addr)
  (field : TCBLayoutField) : addr :=
  match field with
  | TCBCommonField TCBPadding42 => p + (if multi then 50 else 42)
  | TCBCommonField TCBPadding43 => p + (if multi then 51 else 43)
  | TCBCommonField common => tcb_field_address p common
  | TCBEventMultiPtr => &(p # "os_tcb" ->ₛ "OSTCBEventMultiPtr")
  | TCBEventMultiRdy => &(p # "os_tcb" ->ₛ "OSTCBEventMultiRdy")
  | TCBCtxSwCtr => &(p # "os_tcb" ->ₛ "OSTCBCtxSwCtr")
  | TCBCyclesTot => &(p # "os_tcb" ->ₛ "OSTCBCyclesTot")
  | TCBCyclesStart => &(p # "os_tcb" ->ₛ "OSTCBCyclesStart")
  | TCBStkBase => &(p # "os_tcb" ->ₛ "OSTCBStkBase")
  | TCBStkUsed => &(p # "os_tcb" ->ₛ "OSTCBStkUsed")
  end.

Lemma repeat_zero_sublist_eq : forall lo hi n,
  0 <= lo <= hi -> hi <= n ->
  sublist lo hi (repeat_Z 0 n) = repeat_Z 0 (hi - lo).
Proof.
  intros lo hi n Hrange Hn.
  unfold sublist, repeat_Z.
  assert (Hfirst : forall k len : nat,
    firstn k (repeat 0 len) = repeat 0 (Nat.min k len)).
  { intro k; induction k; intros [|len]; cbn; auto; f_equal; auto. }
  assert (Hskip : forall k len : nat,
    skipn k (repeat 0 len) = repeat 0 (len - k)).
  { intro k; induction k; intros [|len]; cbn; auto. }
  rewrite Hfirst, Hskip, Nat.min_l by lia.
  f_equal; lia.
Qed.

Lemma zero_bytes_split : forall p n m,
  0 <= n <= m ->
  UCharArray.full p m (repeat_Z 0 m) |--
    UCharArray.full p n (repeat_Z 0 n) **
    UCharArray.full (p + n) (m - n) (repeat_Z 0 (m - n)).
Proof.
  intros p n m Hrange.
  sep_apply (UCharArray.full_split_to_full p n m (repeat_Z 0 m) Hrange).
  rewrite !repeat_zero_sublist_eq by lia.
  replace (n - 0) with n by lia.
  change StoreUCharAsElement.sizeA with 1.
  rewrite Z.mul_1_r; entailer!.
Qed.

Lemma zero_bytes_to_store_ushort : forall p,
  p mod 2 = 0 -> UCharArray.full p 2 [0; 0] |-- p # UShort |-> 0.
Proof.
  intros p Halign.
  unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  unfold store_uchar, store_ushort, store_2byte.
  Intros; Exists 0 0; entailer!.
  all: try reflexivity.
  all: unfold isvalidptr_short, isvalidptr_char, aligned_2 in *; lia.
Qed.

Lemma zero_bytes_to_store_uint : forall p,
  p mod 4 = 0 -> UCharArray.full p 4 [0; 0; 0; 0] |-- p # UInt |-> 0.
Proof.
  intros p Halign.
  unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  replace (p + 2 * 1) with (p + 2) by lia.
  replace (p + 3 * 1) with (p + 3) by lia.
  rewrite store_uint_store_char.
  unfold store_uchar; Intros; Exists 0 0 0 0.
  unfold store_char; entailer!.
  all: try reflexivity.
  all: change (0 >= -128); lia.
Qed.

Lemma zero_bytes_to_store_ptr : forall p,
  p mod 4 = 0 -> UCharArray.full p 4 [0; 0; 0; 0] |-- p # Ptr |-> 0.
Proof.
  intros p Halign; sep_apply (zero_bytes_to_store_uint p Halign).
  apply kernel_store_uint_store_ptr.
Qed.

Lemma zero_bytes_to_store_uchar : forall p,
  UCharArray.full p 1 [0] |-- p # UChar |-> 0.
Proof.
  intros p; unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1; replace (p + 0 * 1) with p by lia.
  entailer!.
Qed.

Lemma zero_bytes_to_tcb_full_storage : forall p image,
  p mod 4 = 0 ->
  (forall field, image field = Some 0) ->
  (forall field, tcb_layout_field_address true p field =
    p + tcb_configured_field_offset true true field) ->
  UCharArray.full p 92 (repeat_Z 0 92) |--
    tcb_configured_storage_rep true true p image.
Proof.
  intros p image Hmod Hzero Hlayout.
  assert (Hmod2 : p mod 2 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hmod; [|lia].
    destruct Hmod as [k Hk]; exists (2 * k); lia. }
  assert (Hcommon : forall field,
    field <> TCBPadding42 -> field <> TCBPadding43 ->
    tcb_field_address p field =
      p + tcb_configured_field_offset true true (TCBCommonField field)).
  { intros field H42 H43; specialize (Hlayout (TCBCommonField field)).
    destruct field; try contradiction; exact Hlayout. }
  pose proof (Hlayout TCBEventMultiPtr) as Hmulti_ptr.
  pose proof (Hlayout TCBEventMultiRdy) as Hmulti_rdy.
  pose proof (Hlayout TCBCtxSwCtr) as Hctx.
  pose proof (Hlayout TCBCyclesTot) as Hcycles.
  pose proof (Hlayout TCBCyclesStart) as Hstart.
  pose proof (Hlayout TCBStkBase) as Hstack.
  pose proof (Hlayout TCBStkUsed) as Hused.
  cbn [tcb_layout_field_address tcb_configured_field_offset
    tcb_layout_field_offset] in Hmulti_ptr, Hmulti_rdy, Hctx, Hcycles,
      Hstart, Hstack, Hused.
  unfold tcb_configured_storage_rep, tcb_configured_fields,
    tcb_profile_fields, tcb_fields.
  cbn [map firstn skipn app].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite TaskFieldStorage.store_fields_nil.
  rewrite !Hzero.
  cbn [tcb_layout_cell].
  unfold tcb_cell; rewrite !Hcommon by discriminate.
  rewrite Hmulti_ptr, Hmulti_rdy, Hctx, Hcycles, Hstart, Hstack, Hused.
  cbn [tcb_configured_field_offset tcb_layout_field_offset tcb_field_offset].
  rewrite UIntArray.full_unfold, UIntArray.seg_empty.
  unfold StoreUIntAsElement.storeA.
  change (sizeof(UINT)) with 4.
  replace (p + 88 + 0 * 4) with (p + 88) by lia.
  sep_apply (zero_bytes_split p 4 92 ltac:(lia)).
  sep_apply (zero_bytes_to_store_ptr p Hmod).
  sep_apply (zero_bytes_split (p + 4) 4 88 ltac:(lia)).
  replace (p + 4 + 4) with (p + 8) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 4) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 8) 4 84 ltac:(lia)).
  replace (p + 8 + 4) with (p + 12) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 8) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 12) 4 80 ltac:(lia)).
  replace (p + 12 + 4) with (p + 16) by lia.
  sep_apply (zero_bytes_to_store_uint (p + 12) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 16) 2 76 ltac:(lia)).
  replace (p + 16 + 2) with (p + 18) by lia.
  sep_apply (zero_bytes_to_store_ushort (p + 16) ltac:(rewrite Z.add_mod, Hmod2 by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 18) 2 74 ltac:(lia)).
  replace (p + 18 + 2) with (p + 20) by lia.
  sep_apply (zero_bytes_to_store_ushort (p + 18) ltac:(rewrite Z.add_mod, Hmod2 by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 20) 4 72 ltac:(lia)).
  replace (p + 20 + 4) with (p + 24) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 20) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 24) 4 68 ltac:(lia)).
  replace (p + 24 + 4) with (p + 28) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 24) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 28) 4 64 ltac:(lia)).
  replace (p + 28 + 4) with (p + 32) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 28) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 32) 4 60 ltac:(lia)).
  replace (p + 32 + 4) with (p + 36) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 32) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 36) 4 56 ltac:(lia)).
  replace (p + 36 + 4) with (p + 40) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 36) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 40) 4 52 ltac:(lia)).
  replace (p + 40 + 4) with (p + 44) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 40) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 44) 4 48 ltac:(lia)).
  replace (p + 44 + 4) with (p + 48) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 44) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 48) 2 44 ltac:(lia)).
  replace (p + 48 + 2) with (p + 50) by lia.
  sep_apply (zero_bytes_to_store_ushort (p + 48) ltac:(rewrite Z.add_mod, Hmod2 by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 50) 1 42 ltac:(lia)).
  replace (p + 50 + 1) with (p + 51) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 50)).
  sep_apply (zero_bytes_split (p + 51) 1 41 ltac:(lia)).
  replace (p + 51 + 1) with (p + 52) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 51)).
  sep_apply (zero_bytes_split (p + 52) 4 40 ltac:(lia)).
  replace (p + 52 + 4) with (p + 56) by lia.
  sep_apply (zero_bytes_to_store_uint (p + 52) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 56) 1 36 ltac:(lia)).
  replace (p + 56 + 1) with (p + 57) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 56)).
  sep_apply (zero_bytes_split (p + 57) 1 35 ltac:(lia)).
  replace (p + 57 + 1) with (p + 58) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 57)).
  sep_apply (zero_bytes_split (p + 58) 1 34 ltac:(lia)).
  replace (p + 58 + 1) with (p + 59) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 58)).
  sep_apply (zero_bytes_split (p + 59) 1 33 ltac:(lia)).
  replace (p + 59 + 1) with (p + 60) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 59)).
  sep_apply (zero_bytes_split (p + 60) 1 32 ltac:(lia)).
  replace (p + 60 + 1) with (p + 61) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 60)).
  sep_apply (zero_bytes_split (p + 61) 1 31 ltac:(lia)).
  replace (p + 61 + 1) with (p + 62) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 61)).
  sep_apply (zero_bytes_split (p + 62) 1 30 ltac:(lia)).
  replace (p + 62 + 1) with (p + 63) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 62)).
  sep_apply (zero_bytes_split (p + 63) 1 29 ltac:(lia)).
  replace (p + 63 + 1) with (p + 64) by lia.
  sep_apply (zero_bytes_to_store_uchar (p + 63)).
  sep_apply (zero_bytes_split (p + 64) 4 28 ltac:(lia)).
  replace (p + 64 + 4) with (p + 68) by lia.
  sep_apply (zero_bytes_to_store_uint (p + 64) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 68) 4 24 ltac:(lia)).
  replace (p + 68 + 4) with (p + 72) by lia.
  sep_apply (zero_bytes_to_store_uint (p + 68) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 72) 4 20 ltac:(lia)).
  replace (p + 72 + 4) with (p + 76) by lia.
  sep_apply (zero_bytes_to_store_uint (p + 72) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 76) 4 16 ltac:(lia)).
  replace (p + 76 + 4) with (p + 80) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 76) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 80) 4 12 ltac:(lia)).
  replace (p + 80 + 4) with (p + 84) by lia.
  sep_apply (zero_bytes_to_store_uint (p + 80) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_split (p + 84) 4 8 ltac:(lia)).
  replace (p + 84 + 4) with (p + 88) by lia.
  sep_apply (zero_bytes_to_store_ptr (p + 84) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  sep_apply (zero_bytes_to_store_uint (p + 88) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
  cbv [tcb_configured_field_offset tcb_layout_field_offset tcb_field_offset
    Z.leb Z.compare Pos.compare Pos.compare_cont andb].
  repeat rewrite Z.add_0_r.
  repeat rewrite Z.add_0_l.
  replace (32 + 8)%Z with 40 by lia.
  replace (36 + 8)%Z with 44 by lia.
  replace (40 + 8)%Z with 48 by lia.
  replace (44 + 8)%Z with 52 by lia.
  replace (48 + 8)%Z with 56 by lia.
  replace (49 + 8)%Z with 57 by lia.
  replace (50 + 8)%Z with 58 by lia.
  replace (51 + 8)%Z with 59 by lia.
  replace (52 + 8)%Z with 60 by lia.
  replace (53 + 8)%Z with 61 by lia.
  replace (54 + 8)%Z with 62 by lia.
  replace (55 + 8)%Z with 63 by lia.
  replace (56 + 20)%Z with 76 by lia.
  replace (60 + 20)%Z with 80 by lia.
  entailer!; rewrite Z.add_0_r; try reflexivity.
Qed.
