Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Shared unsigned observations.  The total operations preserve C
    wraparound; their range theorems are separate from execution guards. *)
Definition kernel_u8 (x : Z) := x mod 256.
Definition kernel_u16 (x : Z) := x mod 65536.
Definition kernel_u32 (x : Z) := x mod 4294967296.
Definition kernel_s8 (x : Z) :=
  let u := kernel_u8 x in if u <? 128 then u else u - 256.

Lemma kernel_u8_in_range : forall x, 0 <= kernel_u8 x < 256.
Proof. intros; apply Z.mod_pos_bound; lia. Qed.
Lemma kernel_u16_in_range : forall x, 0 <= kernel_u16 x < 65536.
Proof. intros; apply Z.mod_pos_bound; lia. Qed.
Lemma kernel_u32_in_range : forall x, 0 <= kernel_u32 x < 4294967296.
Proof. intros; apply Z.mod_pos_bound; lia. Qed.
Lemma kernel_u8_identity : forall x, 0 <= x < 256 -> kernel_u8 x = x.
Proof. intros; apply Z.mod_small; auto. Qed.
Lemma kernel_u16_identity : forall x, 0 <= x < 65536 -> kernel_u16 x = x.
Proof. intros; apply Z.mod_small; auto. Qed.
Lemma kernel_u32_identity : forall x,
  0 <= x < 4294967296 -> kernel_u32 x = x.
Proof. intros; apply Z.mod_small; auto. Qed.
Lemma kernel_s8_in_range : forall x, -128 <= kernel_s8 x < 128.
Proof.
  intro x; unfold kernel_s8.
  pose proof (kernel_u8_in_range x).
  destruct (kernel_u8 x <? 128) eqn:E;
    [apply Z.ltb_lt in E|apply Z.ltb_ge in E]; lia.
Qed.
Lemma kernel_s8_identity : forall x, 0 <= x < 128 -> kernel_s8 x = x.
Proof.
  intros x H; unfold kernel_s8; rewrite kernel_u8_identity by lia.
  destruct (x <? 128) eqn:E; [reflexivity|apply Z.ltb_ge in E; lia].
Qed.

(** Point updates are used by several independently owned pools.  Their
    lookup laws are pointwise and do not require a new extensionality axiom. *)
Definition kernel_map_set {A : Type} (m : Z -> option A) (i : Z) (v : option A) :=
  fun j => if Z.eq_dec j i then v else m j.
Lemma kernel_map_set_same : forall A (m : Z -> option A) i v,
  kernel_map_set m i v i = v.
Proof. intros; unfold kernel_map_set; destruct Z.eq_dec; congruence. Qed.
Lemma kernel_map_set_other : forall A (m : Z -> option A) i j v,
  j <> i -> kernel_map_set m i v j = m j.
Proof. intros; unfold kernel_map_set; destruct Z.eq_dec; congruence. Qed.

(** The common finite-pool partition does not hide any operation behind a
    post-invariant test.  Memory adds a third, privately initializing class. *)
Definition kernel_pool_partition {A : Type} (capacity : Z) (free : list Z)
  (used : Z -> option A) : Prop :=
  NoDup free /\ (forall i, In i free -> 0 <= i < capacity) /\
  forall i, (exists v, used i = Some v) <-> 0 <= i < capacity /\ ~ In i free.
Lemma kernel_pool_initial_partition : forall A capacity,
  kernel_pool_partition (A := A) capacity (Zrange 0 capacity) (fun _ => None).
Proof.
  intros; split; [apply NoDup_Zrange|]. split.
  - intros; apply In_Zrange; assumption.
  - intro i; split; [intros [v H]; discriminate|].
    intros [Hr Hnot]; exfalso; apply Hnot; apply In_Zrange; exact Hr.
Qed.
Lemma kernel_pool_allocate_preserves_partition : forall A capacity i rest used (v : A),
  kernel_pool_partition capacity (i :: rest) used ->
  kernel_pool_partition capacity rest (kernel_map_set used i (Some v)).
Proof.
  intros A capacity i rest used v [Hnd [Hr Hp]].
  inversion Hnd as [|? ? Hnot Hrest]; subst.
  split; [exact Hrest|]. split; [intros; apply Hr; right; assumption|].
  intro j; unfold kernel_map_set; destruct (Z.eq_dec j i) as [->|Hne].
  - split; [intros _; split; [apply Hr; left; reflexivity|exact Hnot]|eauto].
  - rewrite Hp; simpl; intuition congruence.
Qed.
Lemma kernel_pool_release_preserves_partition : forall A capacity free used i (v : A),
  kernel_pool_partition capacity free used -> used i = Some v ->
  kernel_pool_partition capacity (i :: free) (kernel_map_set used i None).
Proof.
  intros A capacity free used i v [Hnd [Hr Hp]] Hlookup.
  assert (Hi : 0 <= i < capacity /\ ~ In i free) by (apply (proj1 (Hp i)); eauto).
  split; [constructor; tauto|]. split.
  - intros j [->|Hin]; [tauto|apply Hr; exact Hin].
  - intro j; unfold kernel_map_set; destruct (Z.eq_dec j i) as [->|Hne].
    + split; [intros [w H]; discriminate|].
      intros [_ H]; exfalso; apply H; left; reflexivity.
    + rewrite Hp; simpl; intuition congruence.
Qed.
Lemma kernel_pool_replace_preserves_partition : forall A capacity free used i (old v : A),
  kernel_pool_partition capacity free used -> used i = Some old ->
  kernel_pool_partition capacity free (kernel_map_set used i (Some v)).
Proof.
  intros A capacity free used i old v [Hnd [Hr Hp]] Hlookup.
  split; [exact Hnd|]. split; [exact Hr|]. intro j; unfold kernel_map_set.
  destruct (Z.eq_dec j i) as [->|Hne]; [|apply Hp].
  split; [intros _; apply (proj1 (Hp i)); eauto|eauto].
Qed.

Lemma kernel_list_nodup_app_disjoint : forall A (left right : list A) x,
  NoDup (left ++ right) -> In x left -> ~ In x right.
Proof.
  intros A left; induction left as [|a rest IH]; intros right x Hnd Hin; [contradiction|].
  inversion Hnd as [|? ? Hnot Htail]; subst; destruct Hin as [->|Hin].
  - intro H; apply Hnot; apply in_or_app; right; exact H.
  - eapply IH; eauto.
Qed.

Lemma kernel_list_remove_preserves_nodup : forall ids i,
  NoDup ids -> NoDup (remove Z.eq_dec i ids).
Proof.
  intros ids i Hnd; induction Hnd as [|a rest Hnot Hnd IH]; simpl; [constructor|].
  destruct (Z.eq_dec i a); [exact IH|]. constructor; [|exact IH].
  intro Hin; apply Hnot; apply in_remove in Hin; tauto.
Qed.

Fixpoint kernel_list_next (ids : list Z) (i : Z) : option Z :=
  match ids with
  | [] => None
  | j :: rest => if Z.eq_dec i j then hd_error rest else kernel_list_next rest i
  end.
Lemma kernel_list_next_at : forall pre i rest,
  NoDup (pre ++ i :: rest) -> kernel_list_next (pre ++ i :: rest) i = hd_error rest.
Proof.
  induction pre as [|j pre IH]; intros i rest Hnd; simpl.
  - destruct (Z.eq_dec i i); congruence.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    destruct (Z.eq_dec i j) as [Heq|Hne].
    + subst; exfalso; apply Hnot; apply in_or_app; right; left; reflexivity.
    + apply IH; exact Htail.
Qed.

Lemma kernel_list_next_some_in : forall ids i j,
  kernel_list_next ids i = Some j -> In j ids.
Proof.
  induction ids as [|a rest IH]; intros i j H; simpl in H; [discriminate|].
  destruct (Z.eq_dec i a).
  - destruct rest as [|b tail]; [discriminate|]. inversion H; subst; right; left; reflexivity.
  - right; eapply IH; eauto.
Qed.
Lemma kernel_list_next_remove : forall ids removed i,
  NoDup ids -> i <> removed ->
  kernel_list_next (remove Z.eq_dec removed ids) i =
    match kernel_list_next ids i with
    | None => None
    | Some next => if Z.eq_dec next removed then kernel_list_next ids removed else Some next
    end.
Proof.
  induction ids as [|a rest IH]; intros removed i Hnd Hne; simpl; [reflexivity|].
  inversion Hnd as [|? ? Hnot Hrest]; subst.
  destruct (Z.eq_dec removed a) as [Heq|Hra].
  - subst a; destruct (Z.eq_dec i removed); [congruence|].
    rewrite notin_remove by exact Hnot.
    destruct (kernel_list_next rest i) as [next|] eqn:E; [|reflexivity].
    destruct (Z.eq_dec next removed) as [Heq|Hnr]; [|reflexivity].
    subst next; exfalso; apply Hnot; eapply kernel_list_next_some_in; eauto.
  - simpl; destruct (Z.eq_dec i a) as [Heq|Hia].
    + subst i; destruct rest as [|b tail]; simpl; [reflexivity|].
      destruct (Z.eq_dec removed b) as [Heq|Hrb].
      * subst b; destruct (Z.eq_dec removed removed); [|congruence].
        destruct (Z.eq_dec removed a); [congruence|].
        inversion Hrest; subst; rewrite notin_remove by assumption; reflexivity.
      * destruct (Z.eq_dec b removed); [congruence|reflexivity].
    + rewrite IH by assumption; destruct (kernel_list_next rest i); [|reflexivity].
      destruct (Z.eq_dec z removed); [|reflexivity].
      destruct (Z.eq_dec removed a); [congruence|reflexivity].
Qed.

Definition kernel_list_previous (ids : list Z) (i : Z) : option Z :=
  kernel_list_next (rev ids) i.

Lemma kernel_list_remove_rev : forall ids i,
  remove Z.eq_dec i (rev ids) = rev (remove Z.eq_dec i ids).
Proof.
  induction ids as [|a rest IH]; intros i; simpl; [reflexivity|].
  rewrite remove_app, IH; simpl; destruct (Z.eq_dec i a); simpl; rewrite ?app_nil_r; reflexivity.
Qed.

Lemma kernel_list_previous_remove : forall ids removed i,
  NoDup ids -> i <> removed ->
  kernel_list_previous (remove Z.eq_dec removed ids) i =
    match kernel_list_previous ids i with
    | None => None
    | Some previous => if Z.eq_dec previous removed then kernel_list_previous ids removed else Some previous
    end.
Proof.
  intros; unfold kernel_list_previous; rewrite <- kernel_list_remove_rev.
  apply kernel_list_next_remove; [apply NoDup_rev|]; assumption.
Qed.

Lemma kernel_list_next_split : forall ids i j,
  kernel_list_next ids i = Some j -> exists pre rest, ids = pre ++ i :: j :: rest.
Proof.
  induction ids as [|a rest IH]; intros i j H; simpl in H; [discriminate|].
  destruct (Z.eq_dec i a) as [->|Hne].
  - destruct rest as [|b tail]; [discriminate|]. inversion H; subst b; exists [], tail; reflexivity.
  - destruct (IH _ _ H) as [pre [tail Heq]]; exists (a :: pre), tail; simpl; rewrite Heq; reflexivity.
Qed.

Lemma kernel_list_next_not_self : forall ids i,
  NoDup ids -> kernel_list_next ids i <> Some i.
Proof.
  intros ids i Hnd H; apply kernel_list_next_split in H; destruct H as [pre [rest Hlist]].
  rewrite Hlist in Hnd; apply NoDup_app_remove_l in Hnd.
  inversion Hnd as [|? ? Hnot Htail]; subst; apply Hnot; left; reflexivity.
Qed.

Lemma kernel_list_previous_not_self : forall ids i,
  NoDup ids -> kernel_list_previous ids i <> Some i.
Proof. intros; unfold kernel_list_previous; apply kernel_list_next_not_self; apply NoDup_rev; assumption. Qed.

Lemma kernel_list_next_previous : forall ids i j,
  NoDup ids -> (kernel_list_next ids i = Some j <-> kernel_list_previous ids j = Some i).
Proof.
  intros ids i j Hnd; split.
  - intros H; apply kernel_list_next_split in H; destruct H as [pre [rest H]]; subst ids.
    unfold kernel_list_previous; rewrite rev_app_distr; simpl; rewrite <- !app_assoc; simpl.
    apply kernel_list_next_at.
    pose proof (NoDup_rev Hnd) as Hr; rewrite rev_app_distr in Hr; simpl in Hr.
    rewrite <- !app_assoc in Hr; exact Hr.
  - unfold kernel_list_previous; intros H; apply kernel_list_next_split in H.
    destruct H as [pre [rest H]].
    apply (f_equal (@rev Z)) in H; rewrite rev_involutive, rev_app_distr in H; simpl in H.
    rewrite <- !app_assoc in H; simpl in H; rewrite H.
    apply kernel_list_next_at; rewrite <- H; exact Hnd.
Qed.

Lemma kernel_list_previous_at : forall pre i rest,
  NoDup (pre ++ i :: rest) ->
  kernel_list_previous (pre ++ i :: rest) i = hd_error (rev pre).
Proof.
  intros pre i rest H; unfold kernel_list_previous.
  rewrite rev_app_distr; simpl; rewrite <- app_assoc; simpl.
  apply kernel_list_next_at.
  pose proof (NoDup_rev H) as Hr; rewrite rev_app_distr in Hr; simpl in Hr.
  rewrite <- app_assoc in Hr; exact Hr.
Qed.

Lemma kernel_last_eq_reverse_head : forall ids,
  last ids 0 = match hd_error (rev ids) with None => 0 | Some x => x end.
Proof.
  induction ids using rev_ind; [reflexivity|].
  rewrite last_last, rev_app_distr; reflexivity.
Qed.

Definition kernel_list_next_addr (ids : list Z) (i : Z) : Z :=
  match kernel_list_next ids i with None => 0 | Some j => j end.

Definition kernel_list_previous_addr (ids : list Z) (i : Z) : Z :=
  match kernel_list_previous ids i with None => 0 | Some j => j end.

Lemma kernel_list_next_addr_eq : forall ids i j,
  j <> 0 -> (kernel_list_next_addr ids i = j <-> kernel_list_next ids i = Some j).
Proof. intros; unfold kernel_list_next_addr; destruct (kernel_list_next ids i); split; congruence. Qed.

Lemma kernel_list_previous_addr_eq : forall ids i j,
  j <> 0 -> (kernel_list_previous_addr ids i = j <-> kernel_list_previous ids i = Some j).
Proof. intros; unfold kernel_list_previous_addr; destruct (kernel_list_previous ids i); split; congruence. Qed.

Lemma kernel_list_next_previous_addr : forall ids i j,
  NoDup ids -> i <> 0 -> j <> 0 ->
  (kernel_list_next_addr ids i = j <-> kernel_list_previous_addr ids j = i).
Proof.
  intros; rewrite kernel_list_next_addr_eq, kernel_list_previous_addr_eq by assumption.
  apply kernel_list_next_previous; assumption.
Qed.

Lemma kernel_list_next_addr_remove : forall ids removed i,
  NoDup ids -> i <> removed -> i <> 0 -> removed <> 0 ->
  kernel_list_next_addr (remove Z.eq_dec removed ids) i =
    if Z.eq_dec i (kernel_list_previous_addr ids removed) then kernel_list_next_addr ids removed
    else kernel_list_next_addr ids i.
Proof.
  intros ids removed i Hnd Hne Hi0 Hr0.
  unfold kernel_list_next_addr at 1; rewrite kernel_list_next_remove by assumption.
  destruct (kernel_list_next ids i) as [next|] eqn:E.
  - destruct (Z.eq_dec next removed) as [->|Hnr].
    + assert (Hp : kernel_list_previous_addr ids removed = i).
      { apply (proj1 (kernel_list_next_previous_addr ids i removed Hnd Hi0 Hr0)).
        unfold kernel_list_next_addr; rewrite E; reflexivity. }
      rewrite Hp; destruct (Z.eq_dec i i); [reflexivity|congruence].
    + assert (Hp : i <> kernel_list_previous_addr ids removed).
      { intro Heq; symmetry in Heq; apply (proj2 (kernel_list_next_previous_addr ids i removed Hnd Hi0 Hr0)) in Heq.
        unfold kernel_list_next_addr in Heq; rewrite E in Heq; contradiction. }
      destruct (Z.eq_dec i (kernel_list_previous_addr ids removed)); [contradiction|].
      unfold kernel_list_next_addr; rewrite E; reflexivity.
  - assert (Hp : i <> kernel_list_previous_addr ids removed).
    { intro Heq; symmetry in Heq; apply (proj2 (kernel_list_next_previous_addr ids i removed Hnd Hi0 Hr0)) in Heq.
      unfold kernel_list_next_addr in Heq; rewrite E in Heq; congruence. }
    destruct (Z.eq_dec i (kernel_list_previous_addr ids removed)); [contradiction|].
    unfold kernel_list_next_addr; rewrite E; reflexivity.
Qed.

Lemma kernel_list_previous_addr_remove : forall ids removed i,
  NoDup ids -> i <> removed -> i <> 0 -> removed <> 0 ->
  kernel_list_previous_addr (remove Z.eq_dec removed ids) i =
    if Z.eq_dec i (kernel_list_next_addr ids removed) then kernel_list_previous_addr ids removed
    else kernel_list_previous_addr ids i.
Proof.
  intros ids removed i Hnd Hne Hi0 Hr0.
  change (kernel_list_next_addr (rev (remove Z.eq_dec removed ids)) i =
    if Z.eq_dec i (kernel_list_next_addr ids removed) then kernel_list_previous_addr ids removed
    else kernel_list_previous_addr ids i).
  rewrite <- kernel_list_remove_rev, kernel_list_next_addr_remove by (try apply NoDup_rev; assumption).
  unfold kernel_list_previous_addr, kernel_list_previous, kernel_list_next_addr.
  rewrite rev_involutive; reflexivity.
Qed.

Lemma kernel_list_next_addr_at : forall pre i rest,
  NoDup (pre ++ i :: rest) -> kernel_list_next_addr (pre ++ i :: rest) i = hd 0 rest.
Proof.
  intros; unfold kernel_list_next_addr; rewrite kernel_list_next_at by assumption; destruct rest; reflexivity.
Qed.

Lemma kernel_list_previous_addr_at : forall pre i rest,
  NoDup (pre ++ i :: rest) -> kernel_list_previous_addr (pre ++ i :: rest) i = last pre 0.
Proof.
  intros; unfold kernel_list_previous_addr; rewrite kernel_list_previous_at by assumption.
  symmetry; apply kernel_last_eq_reverse_head.
Qed.

Lemma kernel_list_previous_some_in : forall ids i j,
  kernel_list_previous ids i = Some j -> In j ids.
Proof.
  intros ids i j H; unfold kernel_list_previous in H.
  apply kernel_list_next_some_in in H; apply (proj2 (in_rev ids j)); exact H.
Qed.

Lemma kernel_list_last_nonzero : forall ids,
  ids <> [] -> (forall i, In i ids -> i <> 0) -> last ids 0 <> 0.
Proof.
  intros ids Hnonempty Hnonzero; rewrite kernel_last_eq_reverse_head.
  destruct (rev ids) as [|i rest] eqn:E; simpl.
  - exfalso; apply Hnonempty; apply (f_equal (@rev Z)) in E; rewrite rev_involutive in E; exact E.
  - apply Hnonzero; apply (proj2 (in_rev ids i)); rewrite E; left; reflexivity.
Qed.

Lemma kernel_list_head_remove : forall ids p,
  NoDup ids -> In p ids -> (forall i, In i ids -> i <> 0) ->
  hd 0 (remove Z.eq_dec p ids) =
    if Z.eqb (kernel_list_previous_addr ids p) 0 then kernel_list_next_addr ids p else hd 0 ids.
Proof.
  intros ids p Hnd Hin Hnonzero; apply in_split in Hin; destruct Hin as [pre [rest Hlist]]; subst ids.
  rewrite kernel_list_previous_addr_at, kernel_list_next_addr_at by exact Hnd.
  pose proof (NoDup_remove _ _ _ Hnd) as [Hremoved Hnot].
  assert (Hpre : ~ In p pre) by (intro H; apply Hnot; apply in_or_app; left; exact H).
  assert (Hrest : ~ In p rest) by (intro H; apply Hnot; apply in_or_app; right; exact H).
  rewrite remove_app; simpl; destruct (Z.eq_dec p p); [|congruence].
  rewrite !notin_remove by assumption.
  destruct pre as [|a pre]; simpl; [reflexivity|].
  assert (Hlast : last (a :: pre) 0 <> 0).
  { apply kernel_list_last_nonzero; [discriminate|].
    intros i Hi; apply Hnonzero; apply in_or_app; left; exact Hi. }
  change (a = if Z.eqb (last (a :: pre) 0) 0 then hd 0 rest else a).
  destruct (Z.eqb (last (a :: pre) 0) 0) eqn:E; [apply Z.eqb_eq in E; contradiction|reflexivity].
Qed.

Lemma kernel_zrange_aux_length : forall n low,
  List.length (Zrange_aux low n) = n.
Proof. induction n; intros; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma kernel_zrange_length : forall low high,
  List.length (Zrange low high) = Z.to_nat (high - low).
Proof. intros; unfold Zrange; apply kernel_zrange_aux_length. Qed.
Lemma kernel_pool_free_count_bound : forall A capacity free (used : Z -> option A),
  0 <= capacity -> kernel_pool_partition capacity free used ->
  0 <= Z.of_nat (List.length free) <= capacity.
Proof.
  intros A capacity free used Hcap [Hnd [Hr Hp]].
  assert (Hincl : incl free (Zrange 0 capacity)).
  { intros i Hi; apply In_Zrange; apply Hr; exact Hi. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen.
  rewrite kernel_zrange_length in Hlen; apply Nat2Z.inj_le in Hlen.
  rewrite Z2Nat.id in Hlen by lia; lia.
Qed.

(** Padding uses QCP's mixed byte array; its length is the supplied image
    length.  These thin layout adapters add no parallel array algorithm.
    Typed fields retain the canonical QCP typed-cell representation. *)
Definition store_optional_bytes (p : addr) (bytes : list (option Z)) : Assertion :=
  UCharArray.mixed_full p (Z.of_nat (List.length bytes)) bytes.

Lemma store_optional_bytes_nil : forall p,
  store_optional_bytes p [] --||-- emp.
Proof. intros; unfold store_optional_bytes; rewrite UCharArray.mixed_full_empty; split; entailer!. Qed.

Lemma store_optional_bytes_cons : forall p b rest,
  store_optional_bytes p (b :: rest) --||--
  (match b with Some v => p # UChar |-> v | None => p # UChar |->_ end) **
  store_optional_bytes (p + 1) rest.
Proof.
  intros p b rest; unfold store_optional_bytes.
  rewrite UCharArray.mixed_full_unfold, UCharArray.mixed_seg_0_shift.
  unfold StoreUCharAsElement.sizeA; change (sizeof(UCHAR)) with 1.
  replace (p + 1 * 1) with (p + 1) by lia.
  replace (Z.of_nat (List.length (b :: rest)) - 1) with (Z.of_nat (List.length rest))
    by (simpl List.length; rewrite Nat2Z.inj_succ; lia).
  change (UCharArray.mixed_seg (p + 1) 0 (Z.of_nat (List.length rest)) rest)
    with (UCharArray.mixed_full (p + 1) (Z.of_nat (List.length rest)) rest).
  unfold UCharArray.mixedstoreA; destruct b;
    unfold StoreUCharAsElement.storeA, StoreUCharAsElement.undefstoreA;
    replace (p + 0 * sizeof(UCHAR)) with p by lia; split; entailer!.
Qed.

(** Typed views of the SAME bytes in the selected Arch32 instance.  These
    entailments neither allocate storage nor establish a C local object's
    address/provenance or a callable pointer.  The reverse initialized
    Ptr-to-UInt direction is already [store_ptr_store_uint] in StoreAux;
    its two Arch32 side conditions are reflexive here. *)
Lemma kernel_store_uint_store_ptr : forall p v,
  p # UInt |-> v |-- p # Ptr |-> v.
Proof.
  intros p v; unfold store_uint, store_ptr.
  change (coq_prop (isvalidptr_int p /\ v >= 0 /\ v <= Int.max_unsigned) &&
    store_4byte p v |--
    coq_prop (isvalidptr p /\ valid_ptr_value v) && store_4byte p v).
  Intros; destruct H as [Hvalid [Hlow Hhigh]].
  assert (Hpointer : isvalidptr p).
  { unfold isvalidptr_int, aligned_4 in Hvalid.
    change (p >= 0 /\ p + 4 - 1 <= addr_max_unsigned /\ p mod 4 = 0).
    lia. }
  assert (Hvalue : valid_ptr_value v).
  { change (0 <= v /\ v <= Int.max_unsigned); lia. }
  entailer!.
Qed.

Lemma kernel_undef_store_uint_ptr_equiv : forall p,
  p # UInt |->_ --||-- p # Ptr |->_ .
Proof.
  intro p.
  assert (Hvalid : isvalidptr_int p <-> isvalidptr p).
  { change ((p >= 0 /\ p + 3 <= addr_max_unsigned /\ p mod 4 = 0) <->
      (p >= 0 /\ p + 4 - 1 <= addr_max_unsigned /\ p mod 4 = 0)).
    lia. }
  unfold undef_store_uint, undef_store_ptr.
  change (coq_prop (isvalidptr_int p) && store_4byte_noninit p --||--
    coq_prop (isvalidptr p) && store_4byte_noninit p).
  split; Intros; entailer!; tauto.
Qed.

(** Undefined Char and UChar have identical byte ownership in QCP.  The
    explicit alignment is needed in the byte-to-word direction; forgetting
    values never forgets the last byte or treats undefined storage as emp. *)
Lemma kernel_undef_store_uint_uchar_equiv : forall p,
  p # UInt |->_ --||-- coq_prop (p mod 4 = 0) &&
    (p # UChar |->_ ** (p + 1) # UChar |->_ **
     (p + 2) # UChar |->_ ** (p + 3) # UChar |->_).
Proof. intro p; exact (undef_store_uint_undef_store_char p). Qed.

Lemma kernel_undef_store_ushort_uchar_equiv : forall p,
  p # UShort |->_ --||-- coq_prop (p mod 2 = 0) &&
    (p # UChar |->_ ** (p + 1) # UChar |->_).
Proof.
  intro p; unfold undef_store_ushort, undef_store_uchar,
    store_2byte_noninit, isvalidptr_short, isvalidptr_char, aligned_2.
  split; Intros; entailer!.
Qed.

Lemma kernel_undef_store_ushort_uchar_merge_uint : forall p,
  p mod 4 = 0 ->
  p # UShort |->_ ** (p + 2) # UChar |->_ ** (p + 3) # UChar |->_ |--
  p # UInt |->_ .
Proof.
  intros p Halign.
  eapply derivable1_trans with (y := coq_prop (p mod 4 = 0) &&
    (p # UChar |->_ ** (p + 1) # UChar |->_ **
     (p + 2) # UChar |->_ ** (p + 3) # UChar |->_)).
  - sep_apply_l_atomic (proj1 (kernel_undef_store_ushort_uchar_equiv p)); entailer!.
  - exact (proj2 (kernel_undef_store_uint_uchar_equiv p)).
Qed.

(** Reclaim a four-byte region after the UShort and UChar writes.  The
    optional padding is exactly ONE owned byte, whether initialized or not;
    only the four values are forgotten.  No statement is made about how a
    source-level stack object acquired this region. *)
Lemma kernel_store_ushort_uchar_padding_forget_uint : forall p half byte padding,
  p mod 4 = 0 -> List.length padding = 1%nat ->
  p # UShort |-> half ** (p + 2) # UChar |-> byte **
    store_optional_bytes (p + 3) padding |-- p # UInt |->_ .
Proof.
  intros p half byte padding Halign Hlength.
  destruct padding as [|pad rest]; [discriminate|].
  destruct rest as [|extra rest]; [|discriminate].
  sep_apply_l_atomic (store_ushort_undef_store_ushort p half).
  sep_apply_l_atomic (store_uchar_undef_store_uchar (p + 2) byte).
  sep_apply_l_atomic (proj1 (store_optional_bytes_cons (p + 3) pad [])).
  sep_apply_l_atomic (proj1 (store_optional_bytes_nil (p + 3 + 1))).
  assert (Hpadding :
    (match pad with Some pad_value => (p + 3) # UChar |-> pad_value
     | None => (p + 3) # UChar |->_ end) |-- (p + 3) # UChar |->_).
  { destruct pad; [apply store_uchar_undef_store_uchar|reflexivity]. }
  sep_apply_l_atomic Hpadding.
  eapply derivable1_trans with (y :=
    p # UShort |->_ ** (p + 2) # UChar |->_ ** (p + 3) # UChar |->_).
  - entailer!.
  - apply kernel_undef_store_ushort_uchar_merge_uint; exact Halign.
Qed.

Definition name_byte_rep (p : addr) (b : Z) : Assertion := p # UChar |-> b.
Definition store_name_bytes (s : NameResourceState) : Assertion :=
  store_map name_byte_rep s.(nameBytes).
Definition store_name_bytes_without (s : NameResourceState) (p : addr) : Assertion :=
  store_map_missing_i name_byte_rep s.(nameBytes) p.

Definition readable_name (s : NameResourceState) (p : addr) (chars : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) chars /\
  (forall i c, nth_error chars i = Some c -> s.(nameBytes) (p + Z.of_nat i) = Some c) /\
  s.(nameBytes) (p + Z.of_nat (List.length chars)) = Some 0.

Definition name_read_lease_valid (s : NameResourceState) (r : NameReadLease) : Prop :=
  NoDup r.(nameReadDomain) /\
  forall p, In p r.(nameReadDomain) -> exists b, s.(nameBytes) p = Some b.

Definition valid_name_resources (s : NameResourceState) : Prop :=
  (forall p b, s.(nameBytes) p = Some b -> 0 <= b < 256) /\
  (forall p, (exists b, s.(nameBytes) p = Some b) <->
     exists n src, s.(nameSources) n = Some src /\ In p src.(nameStorageDomain)) /\
  (forall n src, s.(nameSources) n = Some src -> NoDup src.(nameStorageDomain)) /\
  (forall n m a b p,
     s.(nameSources) n = Some a -> s.(nameSources) m = Some b ->
     In p a.(nameStorageDomain) -> In p b.(nameStorageDomain) -> n = m) /\
  (forall n r, s.(nameReaders) n = Some r -> name_read_lease_valid s r).

Definition name_resources_inv (s : NameResourceState) : Assertion :=
  coq_prop (valid_name_resources s) && store_name_bytes s.

Definition empty_name_resources : NameResourceState :=
  {| nameBytes := fun _ => None; nameSources := fun _ => None;
     nameReaders := fun _ => None |}.

Lemma empty_name_resources_valid : valid_name_resources empty_name_resources.
Proof.
  unfold valid_name_resources, empty_name_resources; simpl.
  split; [intros; discriminate|]. split.
  - intro p; split.
    + intros [b H]; discriminate.
    + intros [n [src [H _]]]; discriminate.
  - split; [intros; discriminate|]. split; intros; discriminate.
Qed.

Lemma store_name_bytes_split_byte : forall s p b,
  s.(nameBytes) p = Some b ->
  store_name_bytes s |-- name_byte_rep p b ** store_name_bytes_without s p.
Proof.
  intros s p b H; unfold store_name_bytes, store_name_bytes_without.
  sep_apply_l_atomic (store_map_split name_byte_rep p b s.(nameBytes) H); entailer!.
Qed.

Lemma store_name_bytes_merge_byte : forall s p b,
  s.(nameBytes) p = Some b ->
  name_byte_rep p b ** store_name_bytes_without s p |-- store_name_bytes s.
Proof.
  intros s p b H; unfold store_name_bytes, store_name_bytes_without.
  sep_apply_l_atomic (store_map_merge name_byte_rep p b s.(nameBytes) H); entailer!.
Qed.

(** Reader registration changes no byte or source ownership.  These
    ghosts describe a verified caller's loan, not a C reference counter. *)
Definition name_register_reader (s : NameResourceState) (n : nat) (r : NameReadLease)
  : NameResourceState :=
  {| nameBytes := s.(nameBytes); nameSources := s.(nameSources);
     nameReaders := fun k => if Nat.eq_dec k n then Some r else s.(nameReaders) k |}.
Definition name_release_reader (s : NameResourceState) (n : nat) : NameResourceState :=
  {| nameBytes := s.(nameBytes); nameSources := s.(nameSources);
     nameReaders := fun k => if Nat.eq_dec k n then None else s.(nameReaders) k |}.

Lemma name_register_reader_preserves_resources : forall s n r,
  valid_name_resources s -> name_read_lease_valid s r ->
  valid_name_resources (name_register_reader s n r).
Proof.
  intros s n r [Hb [Hs [Hnd [Hu Hr]]]] Hlease.
  unfold valid_name_resources, name_register_reader; simpl.
  split; [exact Hb|]. split; [exact Hs|]. split; [exact Hnd|].
  split; [exact Hu|]. intros k lease H; destruct (Nat.eq_dec k n).
  - inversion H; subst; exact Hlease.
  - apply Hr with k; exact H.
Qed.

Lemma name_release_reader_preserves_resources : forall s n,
  valid_name_resources s -> valid_name_resources (name_release_reader s n).
Proof.
  intros s n [Hb [Hs [Hnd [Hu Hr]]]].
  unfold valid_name_resources, name_release_reader; simpl.
  split; [exact Hb|]. split; [exact Hs|]. split; [exact Hnd|].
  split; [exact Hu|]. intros k lease H; destruct (Nat.eq_dec k n); [discriminate|].
  apply Hr with k; exact H.
Qed.

Lemma name_register_reader_bytes_eq : forall s n r,
  store_name_bytes (name_register_reader s n r) = store_name_bytes s.
Proof. reflexivity. Qed.
Lemma name_release_reader_bytes_eq : forall s n,
  store_name_bytes (name_release_reader s n) = store_name_bytes s.
Proof. reflexivity. Qed.

Definition name_length_result (chars : list Z) : Z := kernel_u8 (Z.of_nat (List.length chars)).
Lemma name_length_result_in_range : forall chars, 0 <= name_length_result chars < 256.
Proof. intros; apply kernel_u8_in_range. Qed.

(** [OS_StrLen] accumulates into an INT8U.  A readable byte sequence is
    therefore an exact-length source for the C result only while its number
    of non-NUL characters fits that byte; readability alone does not rule out
    a 256-byte wraparound. *)
Definition os_strlen_length_valid (chars : list Z) : Prop :=
  (Z.of_nat (List.length chars) < 256)%Z.

(** The upstream comment documents names shorter than 255 characters.  Keep
    that caller/API policy separate from [os_strlen_length_valid], which is
    the weaker no-wrap condition for the INT8U observation relation. *)
Definition os_strlen_documented_domain (chars : list Z) : Prop :=
  (Z.of_nat (List.length chars) < 255)%Z.

Lemma os_strlen_documented_domain_implies_length_valid : forall chars,
  os_strlen_documented_domain chars -> os_strlen_length_valid chars.
Proof. intros chars H; unfold os_strlen_documented_domain, os_strlen_length_valid in *; lia. Qed.

Lemma name_length_result_exact : forall chars,
  os_strlen_length_valid chars ->
  name_length_result chars = Z.of_nat (List.length chars).
Proof.
  intros chars Hlength; unfold name_length_result, os_strlen_length_valid in *.
  apply kernel_u8_identity; split; [lia|exact Hlength].
Qed.

Definition name_lease_covers (r : NameReadLease) (p : addr) (chars : list Z) : Prop :=
  r.(nameReadRoot) = p /\
  forall i, (i <= List.length chars)%nat -> In (p + Z.of_nat i) r.(nameReadDomain).
Definition name_read_frame (before after : NameResourceState) (r : NameReadLease) : Prop :=
  forall p, In p r.(nameReadDomain) -> after.(nameBytes) p = before.(nameBytes) p.
Lemma readable_name_preserved_by_lease : forall before after r p chars,
  readable_name before p chars -> name_lease_covers r p chars ->
  name_read_frame before after r -> readable_name after p chars.
Proof.
  intros before after r p chars [Hchars [Hbytes Hnul]] [_ Hcover] Hframe.
  split; [exact Hchars|]. split.
  - intros i c Hi; rewrite Hframe.
    + apply Hbytes; exact Hi.
    + apply Hcover.
      assert (Hsome : nth_error chars i <> None) by congruence.
      apply nth_error_Some in Hsome; lia.
  - rewrite Hframe; [exact Hnul|apply Hcover; lia].
Qed.

(** Byte sources are registered once.  Objects and suffix aliases borrow
    them; they do not each acquire another copy of the byte ownership. *)
Definition name_source_bytes_valid (src : NameStorageSource) (bytes : addr -> option Z) : Prop :=
  NoDup src.(nameStorageDomain) /\
  forall p, In p src.(nameStorageDomain) -> exists b, bytes p = Some b /\ 0 <= b < 256.
Definition name_source_disjoint (s : NameResourceState) (src : NameStorageSource) : Prop :=
  forall p, In p src.(nameStorageDomain) -> s.(nameBytes) p = None.
Definition name_register_source (s : NameResourceState) (n : nat) (src : NameStorageSource)
  (bytes : addr -> option Z) : NameResourceState :=
  {| nameBytes := fun p => if in_dec Z.eq_dec p src.(nameStorageDomain) then bytes p else s.(nameBytes) p;
     nameSources := fun k => if Nat.eq_dec k n then Some src else s.(nameSources) k;
     nameReaders := s.(nameReaders) |}.
Lemma name_source_disjoint_from_old_source : forall s src n old p,
  valid_name_resources s -> name_source_disjoint s src ->
  s.(nameSources) n = Some old -> In p old.(nameStorageDomain) -> ~ In p src.(nameStorageDomain).
Proof.
  intros s src n old p [_ [Hdomain _]] Hdis Hlookup Hin Hnew.
  destruct (proj2 (Hdomain p) ltac:(exists n, old; auto)) as [b Hb].
  rewrite Hdis in Hb by exact Hnew; discriminate.
Qed.
Lemma name_register_source_preserves_resources : forall s n src bytes,
  valid_name_resources s -> s.(nameSources) n = None ->
  name_source_bytes_valid src bytes -> name_source_disjoint s src ->
  valid_name_resources (name_register_source s n src bytes).
Proof.
  intros s n src bytes Hv Hfresh [Hnd Hnew] Hdis.
  destruct Hv as [Hb [Hd [Hnds [Hu Hrs]]]].
  unfold valid_name_resources, name_register_source; simpl.
  split.
  - intros p b H; destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hin|Hout].
    + destruct (Hnew p Hin) as [v [Hv Hr]]; rewrite H in Hv; inversion Hv; subst; exact Hr.
    + apply Hb with p; exact H.
  - split.
    + intro p; split.
      * intros [b H]; destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hin|Hout].
        -- exists n, src; split; [destruct (Nat.eq_dec n n); congruence|exact Hin].
        -- destruct (proj1 (Hd p) ltac:(exists b; exact H)) as [k [old [Hk Hin]]].
           exists k, old; split; [destruct (Nat.eq_dec k n); subst; congruence|exact Hin].
      * intros [k [old [Hk Hin]]]. destruct (Nat.eq_dec k n) as [Heq|Hne].
        -- inversion Hk; subst old; destruct (in_dec Z.eq_dec p (nameStorageDomain src)); [|contradiction].
           destruct (Hnew p Hin) as [b [H _]]; eauto.
        -- destruct (proj2 (Hd p) ltac:(exists k, old; auto)) as [b H].
           destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hyes|Hno].
           ++ rewrite Hdis in H by exact Hyes; discriminate.
           ++ eauto.
    + split.
      * intros k old Hk; destruct (Nat.eq_dec k n); [inversion Hk; subst; exact Hnd|eapply Hnds; eauto].
      * split.
        -- intros k l a b p Hk Hl Ha Hbdom.
           destruct (Nat.eq_dec k n) as [Hkn|Hkn], (Nat.eq_dec l n) as [Hln|Hln].
           ++ congruence.
           ++ inversion Hk; subst a; destruct (proj2 (Hd p) ltac:(exists l, b; auto)) as [v Hv].
              rewrite Hdis in Hv by exact Ha; discriminate.
           ++ inversion Hl; subst b; destruct (proj2 (Hd p) ltac:(exists k, a; auto)) as [v Hv].
              rewrite Hdis in Hv by exact Hbdom; discriminate.
           ++ eapply Hu; eauto.
        -- intros k r Hk; destruct (Hrs k r Hk) as [Hnr Hbr]; split; [exact Hnr|].
           intros p Hp; simpl; destruct (Hbr p Hp) as [b H].
           destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hin|Hout].
           ++ rewrite Hdis in H by exact Hin; discriminate.
           ++ eauto.
Qed.
Lemma name_register_source_frames_reader : forall s n src bytes r,
  name_source_disjoint s src -> name_read_lease_valid s r ->
  name_read_frame s (name_register_source s n src bytes) r.
Proof.
  intros s n src bytes r Hdis [_ Hr] p Hin.
  unfold name_register_source; simpl.
  destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hnew|Hnot]; [|reflexivity].
  destruct (Hr p Hin) as [b H]; rewrite Hdis in H by exact Hnew; discriminate.
Qed.

Definition name_byte_writable (s : NameResourceState) (protected : addr -> Prop) (p : addr) : Prop :=
  ~ protected p /\ forall n r, s.(nameReaders) n = Some r -> ~ In p r.(nameReadDomain).
Definition name_write_byte (s : NameResourceState) (p : addr) (b : Z) : NameResourceState :=
  {| nameBytes := kernel_map_set s.(nameBytes) p (Some b);
     nameSources := s.(nameSources); nameReaders := s.(nameReaders) |}.
Lemma name_write_frames_active_readers : forall s protected p b n r,
  name_byte_writable s protected p -> s.(nameReaders) n = Some r ->
  name_read_frame s (name_write_byte s p b) r.
Proof.
  intros s protected p b n r [_ Hread] Hlookup q Hq; unfold name_write_byte; simpl.
  apply kernel_map_set_other; intro E; subst; apply (Hread n r Hlookup); exact Hq.
Qed.
Lemma name_write_byte_domain_eq : forall s p old b q,
  s.(nameBytes) p = Some old ->
  (exists v, (name_write_byte s p b).(nameBytes) q = Some v) <->
  (exists v, s.(nameBytes) q = Some v).
Proof.
  intros s p old b q H; unfold name_write_byte; simpl; unfold kernel_map_set.
  destruct (Z.eq_dec q p); [subst; split; intros; eauto|reflexivity].
Qed.
Lemma name_write_preserves_resources : forall s protected p old b,
  valid_name_resources s -> name_byte_writable s protected p ->
  s.(nameBytes) p = Some old -> 0 <= b < 256 ->
  valid_name_resources (name_write_byte s p b).
Proof.
  intros s protected p old b [Hb [Hd [Hnd [Hu Hr]]]] Hwrite Hold Hrange.
  unfold valid_name_resources; split.
  - intros q v H; unfold name_write_byte in H; simpl in H; unfold kernel_map_set in H.
    destruct (Z.eq_dec q p); [inversion H; subst; exact Hrange|eapply Hb; eauto].
  - split.
    + intro q; rewrite (name_write_byte_domain_eq s p old b q Hold); exact (Hd q).
    + split; [exact Hnd|]. split; [exact Hu|].
      intros n r H; destruct (Hr n r H) as [Hn Hrbytes]; split; [exact Hn|].
      intros q Hq; destruct (Hrbytes q Hq) as [v Hv]; exists v.
      rewrite (name_write_frames_active_readers s protected p b n r Hwrite H q Hq); exact Hv.
Qed.
Lemma store_name_bytes_merge_updated_byte : forall s p old b,
  s.(nameBytes) p = Some old ->
  name_byte_rep p b ** store_name_bytes_without s p |-- store_name_bytes (name_write_byte s p b).
Proof.
  intros s p old b H; unfold store_name_bytes, store_name_bytes_without, name_write_byte; simpl.
  assert (Hframe : forall q, q <> p -> nameBytes s q = kernel_map_set (nameBytes s) p (Some b) q)
    by (intros; symmetry; apply kernel_map_set_other; assumption).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv name_byte_rep _ _ p Hframe)).
  sep_apply_l_atomic (store_map_merge name_byte_rep p b _
    (kernel_map_set_same _ (nameBytes s) p (Some b))); entailer!.
Qed.

Definition name_source_releasable (s : NameResourceState) (n : nat)
  (src : NameStorageSource) (protected : addr -> Prop) : Prop :=
  s.(nameSources) n = Some src /\ src.(nameStorageOrigin) = ApplicationNameStorage /\
  (forall p, protected p -> ~ In p src.(nameStorageDomain)) /\
  forall k r, s.(nameReaders) k = Some r ->
    forall p, In p r.(nameReadDomain) -> ~ In p src.(nameStorageDomain).
Definition name_unregister_source (s : NameResourceState) (n : nat) (src : NameStorageSource)
  : NameResourceState :=
  {| nameBytes := fun p => if in_dec Z.eq_dec p src.(nameStorageDomain) then None else s.(nameBytes) p;
     nameSources := fun k => if Nat.eq_dec k n then None else s.(nameSources) k;
     nameReaders := s.(nameReaders) |}.
Lemma name_unregister_source_preserves_resources : forall s n src protected,
  valid_name_resources s -> name_source_releasable s n src protected ->
  valid_name_resources (name_unregister_source s n src).
Proof.
  intros s n src protected [Hb [Hd [Hnd [Hu Hr]]]] [Hsrc [_ [Hprotected Hread]]].
  unfold valid_name_resources, name_unregister_source; simpl.
  split.
  - intros p b H; destruct (in_dec Z.eq_dec p (nameStorageDomain src)); [discriminate|eapply Hb; eauto].
  - split.
    + intro p; split.
      * intros [b H]; destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hin|Hout]; [discriminate|].
        destruct (proj1 (Hd p) ltac:(exists b; exact H)) as [k [old [Hk Hp]]].
        exists k, old; split; [|exact Hp]. destruct (Nat.eq_dec k n); [|exact Hk].
        subst; rewrite Hsrc in Hk; inversion Hk; subst; contradiction.
      * intros [k [old [Hk Hp]]]; destruct (Nat.eq_dec k n); [discriminate|].
        destruct (proj2 (Hd p) ltac:(exists k, old; auto)) as [b H].
        destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hin|Hout]; [|eauto].
        exfalso; apply n0; eapply Hu; eauto.
    + split.
      * intros k old Hk; destruct (Nat.eq_dec k n); [discriminate|eapply Hnd; eauto].
      * split.
        -- intros k l a b p Hk Hl Ha Hbdom.
           destruct (Nat.eq_dec k n), (Nat.eq_dec l n); try discriminate; eapply Hu; eauto.
        -- intros k r Hk; destruct (Hr k r Hk) as [Hnr Hbr]; split; [exact Hnr|].
           intros p Hp; simpl; destruct (in_dec Z.eq_dec p (nameStorageDomain src)) as [Hin|Hout].
           ++ exfalso; apply (Hread k r Hk p Hp); exact Hin.
           ++ apply Hbr; exact Hp.
Qed.
Lemma name_unregister_source_frames_readers : forall s n src protected k r,
  name_source_releasable s n src protected -> s.(nameReaders) k = Some r ->
  name_read_frame s (name_unregister_source s n src) r.
Proof.
  intros s n src protected k r [_ [_ [_ Hr]]] Hk p Hp.
  unfold name_unregister_source; simpl; destruct (in_dec Z.eq_dec p (nameStorageDomain src)); [|reflexivity].
  exfalso; apply (Hr k r Hk p Hp); assumption.
Qed.
Lemma name_unregister_source_removes_bytes : forall s n src p,
  In p src.(nameStorageDomain) -> (name_unregister_source s n src).(nameBytes) p = None.
Proof.
  intros s n src p H; unfold name_unregister_source; simpl.
  destruct (in_dec Z.eq_dec p (nameStorageDomain src)); [reflexivity|contradiction].
Qed.

Definition name_question_mark_source (p : addr) : NameStorageSource :=
  {| nameStorageOrigin := StaticNameStorage; nameStorageDomain := [p; p + 1] |}.
Definition name_question_mark_bytes (p : addr) : addr -> option Z :=
  fun q => if Z.eq_dec q p then Some 63 else if Z.eq_dec q (p + 1) then Some 0 else None.
Definition name_question_mark_resources (p : addr) : NameResourceState :=
  name_register_source empty_name_resources 0 (name_question_mark_source p) (name_question_mark_bytes p).
Lemma name_question_mark_source_valid : forall p,
  name_source_bytes_valid (name_question_mark_source p) (name_question_mark_bytes p).
Proof.
  intro p; unfold name_source_bytes_valid, name_question_mark_source; simpl; split.
  - constructor; [simpl; lia|]. constructor; [simpl; tauto|constructor].
  - intros q [Hq|[Hq|Hq]]; [subst q|subst q|contradiction]; unfold name_question_mark_bytes.
    + destruct (Z.eq_dec p p); [exists 63; split; [reflexivity|lia]|congruence].
    + destruct (Z.eq_dec (p + 1) p); [lia|]. destruct (Z.eq_dec (p + 1) (p + 1));
        [exists 0; split; [reflexivity|lia]|congruence].
Qed.
Lemma name_question_mark_resources_valid : forall p,
  valid_name_resources (name_question_mark_resources p).
Proof.
  intro p; apply name_register_source_preserves_resources.
  - apply empty_name_resources_valid.
  - reflexivity.
  - apply name_question_mark_source_valid.
  - intros q H; reflexivity.
Qed.

Definition kernel_control_valid (c : KernelConfiguration) (s : KernelControlState) : Prop :=
  match c.(cfgSafetyCriticalIEC), s.(safetyCriticalStarted) with
  | true, Some _ | false, None => True
  | _, _ => False
  end.
Definition kernel_control_rep (sg : StableGlobVars) (s : KernelControlState) : Assertion :=
  match s.(safetyCriticalStarted) with
  | Some b => sg.(g_OSSafetyCriticalStartFlag) # UChar |->
      (if b then 1 else 0)
  | None => emp
  end.
Definition kernel_control_inv (sg : StableGlobVars) (s : KernelControlState) : Assertion :=
  coq_prop (kernel_control_valid sg.(osKernelConfig) s) && kernel_control_rep sg s.
Definition kernel_control_initial (c : KernelConfiguration) : KernelControlState :=
  {| safetyCriticalStarted := if c.(cfgSafetyCriticalIEC) then Some false else None |}.
Definition kernel_safety_start (s : KernelControlState) : KernelControlState :=
  {| safetyCriticalStarted := option_map (fun _ => true) s.(safetyCriticalStarted) |}.
Lemma kernel_control_initial_valid : forall c,
  kernel_control_valid c (kernel_control_initial c).
Proof.
  intro c; unfold kernel_control_valid, kernel_control_initial; simpl.
  destruct (cfgSafetyCriticalIEC c); exact I.
Qed.
Lemma kernel_safety_start_preserves_validity : forall c s,
  kernel_control_valid c s -> kernel_control_valid c (kernel_safety_start s).
Proof.
  intros c [v]; unfold kernel_control_valid, kernel_safety_start; simpl.
  destruct (cfgSafetyCriticalIEC c), v; simpl; auto.
Qed.
