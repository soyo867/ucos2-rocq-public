Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/os_core.c: OS_StrLen reads through the terminating NUL. Most
    NameGet callers hold the interrupt critical region over these reads;
    OSTmrNameGet holds the scheduler lock, which does not exclude ISR writes.
    NameSet stores a pointer, not a copy or ownership of the pointed bytes.

    A reader entry describes a call protocol, not a C reference counter.
    Enter uses a fresh key; leave is allowed only after this caller's last
    access. Registered source ownership, not the entry, supplies each byte.
    Application/ISR writes or deallocation must obey the explicit existing
    writable/releasable conditions. This file does not prove arbitrary
    external code respects them, nor that a returned name pointer is safe
    to dereference after the API has released its protection. *)

(* Component lifting: concrete operations below establish both the byte
   resource invariant and the object-reference property independently. *)
Lemma name_replace_preserves_global_validity : forall sg s names,
  UCOS2_state_inv sg s -> valid_name_resources names ->
  kernel_names_valid sg (replace_NameS names s) ->
  UCOS2_state_inv sg (replace_NameS names s).
Proof.
  intros sg s names Hvalid Hnames Hreferences.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [replace_NameS]; tauto.
Qed.

Lemma name_register_reader_preserves_global_resources : forall sg s n r,
  s.(NameState).(nameReaders) n = None ->
  name_read_lease_valid s.(NameState) r ->
  UCOS2_inv sg s |--
    UCOS2_inv sg (replace_NameS (name_register_reader s.(NameState) n r) s).
Proof.
  intros sg s n r Hfresh Hr; unfold UCOS2_inv; Intros.
  assert (Hpost : UCOS2_state_inv sg
    (replace_NameS (name_register_reader s.(NameState) n r) s)).
  { apply name_replace_preserves_global_validity; [exact H| |].
    - apply name_register_reader_preserves_resources; [|exact Hr].
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto.
    - eapply kernel_names_valid_root_subset.
      + exact (UCOS2_state_inv_names_valid sg s H).
      + reflexivity.
      + intros; assumption. }
  change (UCOS2_raw_rep sg s |-- coq_prop
    (UCOS2_state_inv sg (replace_NameS (name_register_reader s.(NameState) n r) s)) &&
    UCOS2_raw_rep sg s).
  entailer!.
Qed.

Lemma name_release_reader_preserves_global_resources : forall sg s n r,
  s.(NameState).(nameReaders) n = Some r ->
  UCOS2_inv sg s |--
    UCOS2_inv sg (replace_NameS (name_release_reader s.(NameState) n) s).
Proof.
  intros sg s n r Hr; unfold UCOS2_inv; Intros.
  assert (Hpost : UCOS2_state_inv sg
    (replace_NameS (name_release_reader s.(NameState) n) s)).
  { apply name_replace_preserves_global_validity; [exact H| |].
    - apply name_release_reader_preserves_resources.
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in H; tauto.
    - eapply kernel_names_valid_root_subset.
      + exact (UCOS2_state_inv_names_valid sg s H).
      + reflexivity.
      + intros; assumption. }
  change (UCOS2_raw_rep sg s |-- coq_prop
    (UCOS2_state_inv sg (replace_NameS (name_release_reader s.(NameState) n) s)) &&
    UCOS2_raw_rep sg s).
  entailer!.
Qed.

Definition UCOS2_raw_rep_without_name_byte (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (p : addr) : Assertion :=
  store_name_bytes_without s.(NameState) p ** UCOS2_raw_rep_missing_names sg s.

Lemma UCOS2_inv_split_name_byte : forall sg s p b,
  s.(NameState).(nameBytes) p = Some b ->
  UCOS2_inv sg s |-- coq_prop (UCOS2_state_inv sg s) &&
    (name_byte_rep p b ** UCOS2_raw_rep_without_name_byte sg s p).
Proof.
  intros sg s p b Hb; rewrite UCOS2_inv_split_names.
  unfold UCOS2_raw_rep_without_name_byte; Intros.
  sep_apply_l_atomic (store_name_bytes_split_byte s.(NameState) p b Hb); entailer!.
Qed.

Lemma UCOS2_inv_merge_name_byte : forall sg s p b,
  UCOS2_state_inv sg s -> s.(NameState).(nameBytes) p = Some b ->
  name_byte_rep p b ** UCOS2_raw_rep_without_name_byte sg s p |-- UCOS2_inv sg s.
Proof.
  intros sg s p b Hvalid Hb; unfold UCOS2_raw_rep_without_name_byte.
  sep_apply_l_atomic (store_name_bytes_merge_byte s.(NameState) p b Hb).
  rewrite UCOS2_inv_split_names; entailer!.
Qed.

(** This update consumes the actual post-store byte. The write exclusion
    is a caller/environment obligation, not an extra guard in NameGet. *)
Lemma name_write_byte_merge_global_resources : forall sg s p old b,
  UCOS2_state_inv sg s ->
  name_byte_writable s.(NameState) (kernel_name_byte_protected sg s) p ->
  s.(NameState).(nameBytes) p = Some old -> 0 <= b < 256 ->
  name_byte_rep p b ** UCOS2_raw_rep_without_name_byte sg s p |--
    UCOS2_inv sg (replace_NameS (name_write_byte s.(NameState) p b) s).
Proof.
  intros sg s p old b Hvalid Hwrite Hold Hrange.
  assert (Hpost : UCOS2_state_inv sg (replace_NameS (name_write_byte s.(NameState) p b) s)).
  { apply name_replace_preserves_global_validity; [exact Hvalid| |].
    - eapply name_write_preserves_resources; [|exact Hwrite|exact Hold|exact Hrange].
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
    - apply kernel_name_write_preserves_validity; [|exact Hwrite].
      exact (UCOS2_state_inv_names_valid sg s Hvalid). }
  unfold UCOS2_raw_rep_without_name_byte.
  sep_apply_l_atomic (store_name_bytes_merge_updated_byte s.(NameState) p old b Hold).
  apply (UCOS2_inv_merge_updated_module sg s
    (replace_NameS (name_write_byte s.(NameState) p b) s) NamesModule Hpost).
  reflexivity.
Qed.

Lemma name_read_frame_trans : forall first middle last r,
  name_read_frame first middle r -> name_read_frame middle last r ->
  name_read_frame first last r.
Proof. intros first middle last r Hfirst Hlast p Hp; rewrite Hlast, Hfirst by exact Hp; reflexivity. Qed.

Lemma name_register_reader_lookup : forall s n r,
  (name_register_reader s n r).(nameReaders) n = Some r.
Proof. intros; unfold name_register_reader; simpl; destruct (Nat.eq_dec n n); congruence. Qed.

Lemma name_active_reader_excludes_write : forall s n r p,
  s.(nameReaders) n = Some r -> In p r.(nameReadDomain) ->
  forall protected, ~ name_byte_writable s protected p.
Proof. intros s n r p Hr Hp protected [_ Hwrite]; exact (Hwrite n r Hr Hp). Qed.

Lemma name_active_reader_excludes_source_release : forall s n r source src p,
  s.(nameReaders) n = Some r -> In p r.(nameReadDomain) -> In p src.(nameStorageDomain) ->
  forall protected, ~ name_source_releasable s source src protected.
Proof. intros s n r source src p Hr Hp Hsrc protected [_ [_ [_ Hrelease]]]; exact (Hrelease n r Hr p Hp Hsrc). Qed.

(** One loop access, including the final NUL. The theorem uses current
    resources, so byte stability alone cannot manufacture ownership. *)
Lemma name_read_character_split : forall sg s p chars i c,
  readable_name s.(NameState) p chars -> nth_error chars i = Some c ->
  UCOS2_inv sg s |-- coq_prop (UCOS2_state_inv sg s) &&
    (name_byte_rep (p + Z.of_nat i) c **
     UCOS2_raw_rep_without_name_byte sg s (p + Z.of_nat i)).
Proof.
  intros sg s p chars i c [_ [Hbytes _]] Hi.
  apply UCOS2_inv_split_name_byte; apply Hbytes; exact Hi.
Qed.

Lemma name_read_terminator_split : forall sg s p chars,
  readable_name s.(NameState) p chars ->
  UCOS2_inv sg s |-- coq_prop (UCOS2_state_inv sg s) &&
    (name_byte_rep (p + Z.of_nat (List.length chars)) 0 **
     UCOS2_raw_rep_without_name_byte sg s (p + Z.of_nat (List.length chars))).
Proof. intros sg s p chars [_ [_ Hnul]]; apply UCOS2_inv_split_name_byte; exact Hnul. Qed.

Lemma name_read_after_environment : forall before after n r p chars,
  readable_name before p chars -> name_lease_covers r p chars ->
  name_read_frame (name_register_reader before n r) after r ->
  readable_name (name_release_reader after n) p chars.
Proof.
  intros before after n r p chars Hread Hcover Hframe.
  change (readable_name after p chars).
  apply (readable_name_preserved_by_lease before after r p chars Hread Hcover).
  exact Hframe.
Qed.
