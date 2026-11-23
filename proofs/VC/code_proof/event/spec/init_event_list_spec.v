Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.

Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This source instance is compiled without OSEventName. The configuration
    fact connects its 20-byte images to the configuration-indexed shared
    representation; it is not a restriction on a runtime API argument. *)
Definition init_event_list_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgEventNames) = false.

Lemma init_event_list_pool_addr_eq : forall sg ix,
  init_event_list_profile sg ->
  event_pool_addr sg ix = sg.(g_OSEventTbl) + ix * 20.
Proof.
  intros sg ix Hprofile.
  unfold event_pool_addr, event_object_size.
  unfold init_event_list_profile in Hprofile; rewrite Hprofile; reflexivity.
Qed.

(** OS_InitEventList's selected boot operation owns only the ECB byte pool
    and the free-root cell.  No running-state invariant or Queue ownership
    is required.  The end-address premise is the source operation's final
    MemClr pointer increment, not merely validity of the last byte. *)
Definition init_event_list_pre (sg : StableGlobVars) : Assertion :=
  mem_clr_pre sg.(g_OSEventTbl) 200 ** sg.(g_OSEventFreeList) # Ptr |->_ .

Definition init_event_list_post (sg : StableGlobVars) : Assertion :=
  coq_prop (event_pool_partition sg (event_pool_initial sg) /\
            event_free_storage_valid sg (event_pool_initial sg) /\
            event_identity_valid (event_pool_initial sg)) &&
  (event_free_storage_rep sg (event_pool_initial sg) **
   event_free_root_rep sg (event_pool_initial sg)).

(** Each visited node is already its exact canonical boot image.  The
    remaining suffix is still the exact byte-zero image returned by MemClr.
    In particular all four padding bytes remain owned and zero. *)
Definition init_event_list_prefix (sg : StableGlobVars) (ix : Z) : Assertion :=
  iter_sepcon (map (fun eid =>
    event_storage_rep false (event_pool_addr sg eid)
      (event_boot_image sg (Zrange 0 sg.(osMaxEvents)) eid)) (Zrange 0 ix)).

Definition init_event_list_loop_state (sg : StableGlobVars) (ix : Z) : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |->_ **
  init_event_list_prefix sg ix **
  mem_clr_post (event_pool_addr sg ix) (20 * (10 - ix)).

(** This residual retains every non-written field through both source
    stores; only Type and Ptr are exposed, so the old payload, bitmap and
    padding zeros cannot silently be weakened to undefined storage. *)
Definition init_event_list_node_residual (sg : StableGlobVars) (ix : Z) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec
    (event_cell (event_pool_addr sg ix))
    (remove EventField_eq_dec EventTypeField
      (remove EventField_eq_dec EventPtrField (event_fields false)))
    (fun _ => Some 0).

Definition init_event_list_loop_residual (sg : StableGlobVars) (ix : Z) : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |->_ **
  init_event_list_prefix sg ix **
  init_event_list_node_residual sg ix **
  mem_clr_post (event_pool_addr sg (ix + 1)) (20 * (9 - ix)).

Lemma init_event_list_initial_valid : forall sg,
  event_pool_partition sg (event_pool_initial sg) /\
  event_free_storage_valid sg (event_pool_initial sg) /\
  event_identity_valid (event_pool_initial sg).
Proof.
  intro sg; split; [apply event_pool_initial_partition|].
  split; [apply event_pool_initial_free_storage|apply event_pool_initial_identity_valid].
Qed.

(** A source-local consequence of the exact generic byte-clear result.
    It does not strengthen the callee declaration or introduce an ABI axiom. *)
Lemma init_event_list_cleared_node_storage : forall p,
  0 <= p -> p + 20 <= 4294967295 -> p mod 4 = 0 ->
  mem_clr_post p 20 |-- event_storage_rep false p (fun _ => Some 0).
Proof.
  intros p Hp Hend Halign.
  unfold event_storage_rep, event_fields; simpl app.
  repeat rewrite EventFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite EventFieldStorage.store_fields_nil.
  unfold mem_clr_post, UCharArray.full, store_array.
  change (repeat_Z 0 20) with
    [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
  cbn [store_array_rec].
  unfold StoreUCharAsElement.storeA, event_cell, event_field_offset.
  change (sizeof(UCHAR)) with 1.
  unfold store_ptr, store_ushort.
  change ptr_size with 4%nat; cbn.
  unfold store_4byte, store_2byte.
  Exists 0 0 0 0 0 0.
  assert (Hptr : isvalidptr (p + 4)).
  { change (p + 4 >= 0 /\ p + 4 + 4 - 1 <= 4294967295 /\
            (p + 4) mod 4 = 0).
    repeat split; try lia.
    rewrite Z.add_mod, Halign by lia; reflexivity. }
  assert (Hshort : isvalidptr_short (p + 8)).
  { change (p + 8 >= 0 /\ p + 8 + 1 <= 4294967295 /\ (p + 8) mod 2 = 0).
    repeat split; try lia.
    apply Z.mod_divide; [lia|].
    pose proof (Z.div_mod p 4 ltac:(lia)); rewrite Halign in H.
    exists (2 * (p / 4) + 4); lia. }
  assert (Hvalue : valid_ptr_value 0) by (split; compute; congruence).
  assert (Hmerge_ptr : merge_int 0 0 0 0 0) by reflexivity.
  assert (Hmerge_cnt : merge_short 0 0 0) by reflexivity.
  replace (p + 4 + 1) with (p + 5) by lia.
  replace (p + 4 + 2) with (p + 6) by lia.
  replace (p + 4 + 3) with (p + 7) by lia.
  replace (p + 8 + 1) with (p + 9) by lia.
  unfold store_uchar.
  entailer!.
Qed.

Lemma Zrange_zero_snoc__event_boot_storage : forall ix,
  0 <= ix -> Zrange 0 (ix + 1) = Zrange 0 ix ++ [ix].
Proof.
  intros ix Hix; unfold Zrange.
  replace (Z.to_nat (ix + 1 - 0)) with (Z.to_nat (ix - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (0 + Z.of_nat (Z.to_nat (ix - 0))) with ix by lia.
  reflexivity.
Qed.
Lemma init_event_list_prefix_merge_node__event_boot_storage : forall sg ix,
  0 <= ix ->
  init_event_list_prefix sg ix **
  event_storage_rep false (event_pool_addr sg ix)
    (event_boot_image sg (Zrange 0 (osMaxEvents sg)) ix) |--
  init_event_list_prefix sg (ix + 1).
Proof.
  intros sg ix Hix; unfold init_event_list_prefix.
  rewrite Zrange_zero_snoc__event_boot_storage by exact Hix.
  rewrite map_app; cbn [map].
  rewrite <- derivable1_sepcon_iter_sepcon1.
  change (iter_sepcon [event_storage_rep false (event_pool_addr sg ix)
    (event_boot_image sg (Zrange 0 (osMaxEvents sg)) ix)]) with
    (emp ** event_storage_rep false (event_pool_addr sg ix)
      (event_boot_image sg (Zrange 0 (osMaxEvents sg)) ix)).
  entailer!.
Qed.
Lemma kernel_list_next_event_range_eq__event_boot_storage : forall ix,
  0 <= ix < 9 -> kernel_list_next (Zrange 0 10) ix = Some (ix + 1).
Proof.
  intros ix Hix.
  assert (Hcases : ix = 0 \/ ix = 1 \/ ix = 2 \/ ix = 3 \/ ix = 4 \/
    ix = 5 \/ ix = 6 \/ ix = 7 \/ ix = 8) by lia.
  repeat destruct Hcases as [Hcase|Hcases]; subst ix; reflexivity.
Qed.
Lemma init_event_list_prefix_implies_free_storage__event_boot_storage : forall sg,
  init_event_list_profile sg ->
  init_event_list_prefix sg (osMaxEvents sg) |--
  event_free_storage_rep sg (event_pool_initial sg).
Proof.
  intros sg Hprofile.
  unfold init_event_list_profile in Hprofile.
  unfold init_event_list_prefix, event_free_storage_rep, store_map.
  rewrite Hprofile.
  cbn [event_pool_initial eventLifecycle eventFreeStorage].
  Exists (Zrange 0 (osMaxEvents sg)).
  assert (Hdomain : forall a,
    In a (Zrange 0 (osMaxEvents sg)) <->
    exists b, (if in_dec Z.eq_dec a (Zrange 0 (osMaxEvents sg))
      then Some (event_boot_image sg (Zrange 0 (osMaxEvents sg)) a)
      else None) = Some b).
  { intro a; destruct in_dec as [Hin|Hnot].
    - split; [intros _; eexists; reflexivity|intros _; exact Hin].
    - split; [contradiction|intros [b Hb]; discriminate]. }
  assert (Hnd := NoDup_Zrange 0 (osMaxEvents sg)).
  entailer!.
  assert (Hmap : map (fun a =>
      match (if in_dec Z.eq_dec a (Zrange 0 (osMaxEvents sg))
        then Some (event_boot_image sg (Zrange 0 (osMaxEvents sg)) a)
        else None) with
      | Some b => event_storage_rep false (event_pool_addr sg a) b
      | None => emp end) (Zrange 0 (osMaxEvents sg)) =
    map (fun a => event_storage_rep false (event_pool_addr sg a)
      (event_boot_image sg (Zrange 0 (osMaxEvents sg)) a))
      (Zrange 0 (osMaxEvents sg))).
  { apply map_ext_in; intros a Hin; destruct in_dec; [reflexivity|contradiction]. }
  rewrite Hmap; reflexivity.
Qed.
Lemma repeat_firstn_eq__event_boot_storage : forall A (a : A) n m,
  firstn n (repeat a m) = repeat a (Nat.min n m).
Proof.
  intros A a n; induction n; intros [|m]; simpl; auto.
  rewrite IHn; reflexivity.
Qed.
Lemma repeat_skipn_eq__event_boot_storage : forall A (a : A) n m,
  skipn n (repeat a m) = repeat a (m - n).
Proof.
  intros A a n; induction n; intros [|m]; simpl; auto.
Qed.
Lemma cleared_bytes_split__event_boot_storage : forall p n m,
  0 <= n <= m ->
  mem_clr_post p m |-- mem_clr_post p n ** mem_clr_post (p + n) (m - n).
Proof.
  intros p n m Hnm; unfold mem_clr_post.
  sep_apply (UCharArray.full_split_to_full p n m (repeat_Z 0 m) Hnm).
  change (sizeof(UCHAR)) with 1.
  replace (p + n * 1) with (p + n) by lia.
  unfold sublist, repeat_Z.
  rewrite !repeat_firstn_eq__event_boot_storage, !repeat_skipn_eq__event_boot_storage.
  rewrite !Nat.min_l by lia.
  replace (Z.to_nat n - Z.to_nat 0)%nat with (Z.to_nat n) by lia.
  replace (Z.to_nat m - Z.to_nat n)%nat with (Z.to_nat (m - n)) by lia.
  entailer!.
Qed.
Lemma zero_event_storage_split_type_ptr__event_boot_storage : forall sg ix,
  event_storage_rep false (event_pool_addr sg ix) (fun _ => Some 0) |--
  event_cell (event_pool_addr sg ix) EventTypeField (Some 0) **
  event_cell (event_pool_addr sg ix) EventPtrField (Some 0) **
  init_event_list_node_residual sg ix.
Proof.
  intros sg ix.
  sep_apply (event_storage_split_field false (event_pool_addr sg ix)
    (fun _ => Some 0) EventPtrField ltac:(simpl; tauto)).
  unfold event_storage_without_field.
  sep_apply (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell (event_pool_addr sg ix))
    (remove EventField_eq_dec EventPtrField (event_fields false))
    (fun _ => Some 0) EventTypeField
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)).
  unfold init_event_list_node_residual; entailer!.
Qed.
Lemma event_storage_merge_boot_type_ptr__event_boot_storage : forall sg ix,
  event_cell (event_pool_addr sg ix) EventTypeField (Some 0) **
  event_cell (event_pool_addr sg ix) EventPtrField
    (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix))) **
  init_event_list_node_residual sg ix |--
  event_storage_rep false (event_pool_addr sg ix)
    (event_boot_image sg (Zrange 0 (osMaxEvents sg)) ix).
Proof.
  intros sg ix.
  unfold init_event_list_node_residual.
  sep_apply (EventFieldStorage.store_fields_merge_field
    EventField (option Z) EventField_eq_dec (event_cell (event_pool_addr sg ix))
    (remove EventField_eq_dec EventPtrField (event_fields false))
    (fun _ => Some 0) EventTypeField
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)).
  fold (event_storage_without_field false (event_pool_addr sg ix) (fun _ => Some 0) EventPtrField).
  sep_apply (event_storage_merge_updated_field false (event_pool_addr sg ix)
    (fun _ => Some 0) EventPtrField
    (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix)))
    ltac:(simpl; tauto)).
  rewrite (event_storage_rep_ext false (event_pool_addr sg ix) _
    (event_boot_image sg (Zrange 0 (osMaxEvents sg)) ix)).
  - entailer!.
  - intros f Hf; destruct f; reflexivity.
Qed.
Lemma init_event_list_loop_split_zero_node__event_boot_storage : forall sg ix,
  init_event_list_profile sg ->
  0 <= ix <= 9 -> 0 <= g_OSEventTbl sg ->
  g_OSEventTbl sg + 200 <= 4294967295 -> g_OSEventTbl sg mod 4 = 0 ->
  init_event_list_loop_state sg ix |--
  event_cell (event_pool_addr sg ix) EventTypeField (Some 0) **
  event_cell (event_pool_addr sg ix) EventPtrField (Some 0) **
  init_event_list_loop_residual sg ix.
Proof.
  intros sg ix Hprofile Hix Hbase Hend Halign.
  assert (Haddr : forall j, event_pool_addr sg j = g_OSEventTbl sg + j * 20).
  { intro j; apply init_event_list_pool_addr_eq; exact Hprofile. }
  unfold init_event_list_loop_state, init_event_list_loop_residual.
  sep_apply (cleared_bytes_split__event_boot_storage (event_pool_addr sg ix)
    20 (20 * (10 - ix)) ltac:(lia)).
  replace (20 * (10 - ix) - 20) with (20 * (9 - ix)) by lia.
  replace (event_pool_addr sg ix + 20) with (event_pool_addr sg (ix + 1))
    by (rewrite !Haddr; lia).
  assert (Hnode_align : event_pool_addr sg ix mod 4 = 0).
  { rewrite Haddr.
    rewrite Z.add_mod, Z.mul_mod, Halign by lia.
    replace (20 mod 4) with 0 by reflexivity.
    rewrite Z.mul_0_r; reflexivity. }
  sep_apply (init_event_list_cleared_node_storage (event_pool_addr sg ix)
    ltac:(rewrite Haddr; lia)
    ltac:(rewrite Haddr; lia) Hnode_align).
  sep_apply (zero_event_storage_split_type_ptr__event_boot_storage sg ix).
  entailer!.
Qed.
