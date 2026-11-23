Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
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
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.

Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** The named source uses one field beyond the common event layout interface.
    This is an explicit concrete/abstract layout relation, not an axiom or a
    consequence of sizeof alone. Its Name offset is checked against the
    original headers of the fixed full-features source input. *)
Definition init_event_list_named_table_layout (sg : StableGlobVars) : Prop :=
  event_table_layout_prop sg /\
  (forall eid, valid_event_id sg eid ->
    (&(((event_pool_addr (sg) (eid))) # "os_event" ->ₛ "OSEventName")) =
      event_pool_addr sg eid + 20).

Lemma init_event_list_named_table_layout_select : forall sg eid,
  init_event_list_named_table_layout sg -> valid_event_id sg eid ->
  (&(((event_pool_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) = event_pool_addr sg eid /\
  (&(((event_pool_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) = event_pool_addr sg eid + 4 /\
  (&(((event_pool_addr (sg) (eid))) # "os_event" ->ₛ "OSEventName")) = event_pool_addr sg eid + 20.
Proof.
  intros sg eid [Htable Hname] Heid.
  destruct (event_table_layout_select sg eid Htable Heid) as [[Htype [Hptr Hcnt]] Hwait].
  unfold event_addr, OSEventType_off, OSEventPtr_off in Htype, Hptr.
  replace (event_pool_addr sg eid + 0) with (event_pool_addr sg eid) in Htype by lia.
  repeat split; auto.
Qed.

Lemma init_event_list_named_profile_names : forall sg,
  full_features_kernel_profile sg -> cfgEventNames (osKernelConfig sg) = true.
Proof. intros sg Hprofile; unfold full_features_kernel_profile in Hprofile; tauto. Qed.

(**
  Names-enabled OS_InitEventList interface.

  This is the parallel endpoint for the source configuration with
  OS_EVENT_NAME_EN=1.  It is intentionally not a rewrite of the historical
  names-disabled specification: the ECB stride is 24 rather than 20 and each
  free node receives the shared static "?" pointer.  [name] denotes that
  pointer value, not a grant of read permission to the string. The initializer
  stores the pointer but never reads its bytes; the later name-reading
  protocol separately connects NameResourceState with actual byte ownership.
  These zero-image assertions describe the OS_MAX_EVENTS > 1 branch which
  calls OS_MemClr. They do not describe the single-slot branch.
*)
Definition init_event_list_named_pre (sg : StableGlobVars) : Assertion :=
  mem_clr_pre sg.(g_OSEventTbl)
    (event_object_size sg.(osKernelConfig) * sg.(osMaxEvents)) **
  sg.(g_OSEventFreeList) # Ptr |->_.

Definition init_event_list_named_prefix (sg : StableGlobVars)
  (name : addr) (ix : Z) : Assertion :=
  iter_sepcon (map (fun eid =>
    event_storage_rep true (event_pool_addr sg eid)
      (event_boot_image_named sg (Zrange 0 sg.(osMaxEvents)) eid name))
    (Zrange 0 ix)).

Definition init_event_list_named_loop_state (sg : StableGlobVars)
  (name : addr) (ix : Z) : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |->_ **
  init_event_list_named_prefix sg name ix **
  mem_clr_post (event_pool_addr sg ix)
    (event_object_size sg.(osKernelConfig) * (sg.(osMaxEvents) - ix)).

Definition init_event_list_named_post (sg : StableGlobVars) (name : addr)
  : Assertion :=
  coq_prop (sg.(osKernelConfig).(cfgEventNames) = true /\
            event_pool_partition sg (event_pool_initial_named sg name) /\
            event_free_storage_valid sg (event_pool_initial_named sg name) /\
            event_identity_valid (event_pool_initial_named sg name)) &&
  (event_free_storage_rep sg (event_pool_initial_named sg name) **
   event_free_root_rep sg (event_pool_initial_named sg name)).

Lemma init_event_list_named_range_snoc : forall ix,
  0 <= ix -> Zrange 0 (ix + 1) = Zrange 0 ix ++ [ix].
Proof.
  intros ix Hix; unfold Zrange.
  replace (Z.to_nat (ix + 1 - 0)) with (Z.to_nat (ix - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (0 + Z.of_nat (Z.to_nat (ix - 0))) with ix by lia.
  reflexivity.
Qed.

Lemma init_event_list_named_initial_valid : forall sg name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  event_pool_partition sg (event_pool_initial_named sg name) /\
  event_free_storage_valid sg (event_pool_initial_named sg name) /\
  event_identity_valid (event_pool_initial_named sg name).
Proof.
  intros sg name Hnamed; split; [apply event_pool_initial_named_partition|].
  split; [apply event_pool_initial_named_free_storage|
          apply event_pool_initial_named_identity_valid].
Qed.

Lemma init_event_list_named_range_next : forall ix,
  0 <= ix < 9 -> kernel_list_next (Zrange 0 10) ix = Some (ix + 1).
Proof.
  intros ix Hix.
  assert (Hcases : ix = 0 \/ ix = 1 \/ ix = 2 \/ ix = 3 \/ ix = 4 \/
    ix = 5 \/ ix = 6 \/ ix = 7 \/ ix = 8) by lia.
  repeat destruct Hcases as [Hcase|Hcases]; subst ix; reflexivity.
Qed.

Lemma init_event_list_named_prefix_merge_node : forall sg name ix,
  0 <= ix ->
  init_event_list_named_prefix sg name ix **
  event_storage_rep true (event_pool_addr sg ix)
    (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name) |--
  init_event_list_named_prefix sg name (ix + 1).
Proof.
  intros sg name ix Hix; unfold init_event_list_named_prefix.
  rewrite init_event_list_named_range_snoc by exact Hix.
  rewrite map_app; cbn [map].
  rewrite <- derivable1_sepcon_iter_sepcon1.
  change (iter_sepcon [event_storage_rep true (event_pool_addr sg ix)
    (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name)]) with
    (emp ** event_storage_rep true (event_pool_addr sg ix)
      (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name)).
  entailer!.
Qed.

Lemma init_event_list_named_name_cell : forall sg name ix,
  event_storage_rep true (event_pool_addr sg ix)
    (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name) |--
  (event_pool_addr sg ix + 20) # Ptr |-> name **
  event_storage_without_field true (event_pool_addr sg ix)
    (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name)
      EventNameField.
Proof.
  intros sg name ix.
  change (event_storage_rep true (event_pool_addr sg ix)
      (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name) |--
    event_cell (event_pool_addr sg ix) EventNameField (Some name) **
    event_storage_without_field true (event_pool_addr sg ix)
      (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name)
      EventNameField).
  apply event_storage_split_field.
  apply event_name_field_in_fields; reflexivity.
Qed.

Lemma init_event_list_named_root : forall sg name,
  0 < sg.(osMaxEvents) ->
  event_free_root_rep sg (event_pool_initial_named sg name) =
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg 0.
Proof.
  intros sg name Hmax; unfold event_free_root_rep, event_pool_initial_named.
  cbn [unUsedEventStates eventLifecycle event_encode_pool_link].
  unfold Zrange.
  assert (Hlen : (0 < Z.to_nat (osMaxEvents sg - 0))%nat) by lia.
  destruct (Z.to_nat (osMaxEvents sg - 0)) as [|len]; [lia|].
  reflexivity.
Qed.

(** Only the three cells actually assigned after OS_MemClr are focused.
    Count, wait table, group and all padding retain their precise zero bytes. *)
Definition init_event_list_named_node_residual (base : addr) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec EventNameField
      (remove EventField_eq_dec EventPtrField
        (remove EventField_eq_dec EventTypeField (event_fields true))))
    (fun _ => Some 0).

Lemma init_event_list_named_remove_preserves_nodup : forall fields field,
  NoDup fields ->
  NoDup (remove EventField_eq_dec field fields).
Proof.
  intros fields field Hnd; induction Hnd as [|head rest Hnot Hrest IH].
  - simpl; constructor.
  - simpl; destruct (EventField_eq_dec field head) as [->|Hneq].
    + exact IH.
    + constructor.
      * intros Hin; apply Hnot.
        apply in_remove in Hin; tauto.
      * exact IH.
Qed.

Lemma init_event_list_named_split_zero_node : forall base,
  event_storage_rep true base (fun _ => Some 0) |--
  event_cell base EventTypeField (Some 0) **
  event_cell base EventPtrField (Some 0) **
  event_cell base EventNameField (Some 0) **
  init_event_list_named_node_residual base.
Proof.
  intros base.
  sep_apply (event_storage_split_field true base (fun _ => Some 0)
    EventTypeField ltac:(simpl; tauto)).
  unfold event_storage_without_field.
  sep_apply (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec EventTypeField (event_fields true))
    (fun _ => Some 0) EventPtrField
    ltac:(apply init_event_list_named_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|simpl; tauto])).
  unfold event_storage_without_field.
  sep_apply (EventFieldStorage.store_fields_split_field
    EventField (option Z) EventField_eq_dec (event_cell base)
    (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields true)))
    (fun _ => Some 0) EventNameField
    ltac:(apply init_event_list_named_remove_preserves_nodup;
          apply init_event_list_named_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply in_in_remove;
          [discriminate|simpl; tauto]])).
  unfold init_event_list_named_node_residual; entailer!.
Qed.

Lemma init_event_list_named_merge_written_node : forall sg name ix,
  event_cell (event_pool_addr sg ix) EventTypeField (Some 0) **
  event_cell (event_pool_addr sg ix) EventPtrField
    (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix))) **
  event_cell (event_pool_addr sg ix) EventNameField (Some name) **
  init_event_list_named_node_residual (event_pool_addr sg ix) |--
  event_storage_rep true (event_pool_addr sg ix)
    (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name).
Proof.
  intros sg name ix; unfold init_event_list_named_node_residual.
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_updated_field
    EventField (option Z) EventField_eq_dec (event_cell (event_pool_addr sg ix))
    (remove EventField_eq_dec EventPtrField
      (remove EventField_eq_dec EventTypeField (event_fields true)))
    (fun _ => Some 0) EventNameField (Some name)
    ltac:(apply init_event_list_named_remove_preserves_nodup;
          apply init_event_list_named_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply in_in_remove;
          [discriminate|simpl; tauto]])).
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_updated_field
    EventField (option Z) EventField_eq_dec (event_cell (event_pool_addr sg ix))
    (remove EventField_eq_dec EventTypeField (event_fields true))
    (event_write (fun _ => Some 0) EventNameField (Some name)) EventPtrField
    (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix)))
    ltac:(apply init_event_list_named_remove_preserves_nodup;
          apply event_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|simpl; tauto])).
  fold (event_write (event_write (fun _ => Some 0) EventNameField (Some name)) EventPtrField
    (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix)))).
  sep_apply_l_atomic (EventFieldStorage.store_fields_merge_updated_field
    EventField (option Z) EventField_eq_dec (event_cell (event_pool_addr sg ix))
    (event_fields true)
    (event_write (event_write (fun _ => Some 0) EventNameField (Some name)) EventPtrField
      (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix))))
    EventTypeField (Some 0)
    ltac:(apply event_fields_nodup)
    ltac:(simpl; tauto)).
  fold (event_write
      (event_write
        (event_write (fun _ => Some 0) EventNameField (Some name))
        EventPtrField
        (Some (event_encode_pool_link sg
          (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix))))
      EventTypeField (Some 0)).
  fold (event_storage_rep true (event_pool_addr sg ix)
    (event_write
      (event_write
        (event_write (fun _ => Some 0) EventNameField (Some name))
        EventPtrField
        (Some (event_encode_pool_link sg
          (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix))))
      EventTypeField (Some 0))).
  rewrite (event_storage_rep_ext true (event_pool_addr sg ix) _
    (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) ix name)).
  - entailer!.
  - intros field Hin; destruct field; reflexivity.
Qed.

Lemma init_event_list_named_prefix_implies_free_storage : forall sg name,
  sg.(osKernelConfig).(cfgEventNames) = true ->
  init_event_list_named_prefix sg name (osMaxEvents sg) |--
  event_free_storage_rep sg (event_pool_initial_named sg name).
Proof.
  intros sg name Hnamed.
  unfold init_event_list_named_prefix, event_free_storage_rep, store_map.
  rewrite Hnamed; cbn [event_pool_initial_named eventLifecycle eventFreeStorage].
  Exists (Zrange 0 (osMaxEvents sg)).
  assert (Hdomain : forall a, In a (Zrange 0 (osMaxEvents sg)) <->
    exists b, (if in_dec Z.eq_dec a (Zrange 0 (osMaxEvents sg))
      then Some (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) a name)
      else None) = Some b).
  { intro a; destruct in_dec as [Hin|Hnot].
    - split; [intros _; eexists; reflexivity|intros _; exact Hin].
    - split; [contradiction|intros [b Hb]; discriminate]. }
  assert (Hnd := NoDup_Zrange 0 (osMaxEvents sg)).
  entailer!.
  assert (Hmap : map (fun a =>
      match (if in_dec Z.eq_dec a (Zrange 0 (osMaxEvents sg))
        then Some (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) a name)
        else None) with
      | Some b => event_storage_rep true (event_pool_addr sg a) b
      | None => emp end) (Zrange 0 (osMaxEvents sg)) =
    map (fun a => event_storage_rep true (event_pool_addr sg a)
      (event_boot_image_named sg (Zrange 0 (osMaxEvents sg)) a name))
      (Zrange 0 (osMaxEvents sg))).
  { apply map_ext_in; intros a Hin; destruct in_dec; [reflexivity|contradiction]. }
  rewrite Hmap; reflexivity.
Qed.

Lemma init_event_list_named_finish : forall sg name,
  sg.(osKernelConfig).(cfgEventNames) = true -> 0 < sg.(osMaxEvents) ->
  init_event_list_named_prefix sg name sg.(osMaxEvents) **
  sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg 0 |--
  init_event_list_named_post sg name.
Proof.
  intros sg name Hnamed Hmax.
  sep_apply (init_event_list_named_prefix_implies_free_storage sg name Hnamed).
  unfold init_event_list_named_post.
  rewrite init_event_list_named_root by exact Hmax.
  pose proof (init_event_list_named_initial_valid sg name Hnamed) as Hvalid.
  entailer!.
Qed.

(** Actual MemClr result, including all padding bytes, converted to the
    24-byte named ECB. This conversion does not initialize the "?" pointer;
    it exposes its zero cell for the subsequent C assignment. *)
Lemma init_event_list_named_cleared_node : forall p,
  0 <= p -> p + 24 <= 4294967295 -> p mod 4 = 0 ->
  mem_clr_post p 24 |-- event_storage_rep true p (fun _ => Some 0).
Proof.
  intros p Hp Hend Halign.
  unfold event_storage_rep, event_fields; simpl app.
  repeat rewrite EventFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite EventFieldStorage.store_fields_nil.
  unfold mem_clr_post, UCharArray.full, store_array.
  change (repeat_Z 0 24) with
    [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
  cbn [store_array_rec].
  unfold StoreUCharAsElement.storeA, event_cell, event_field_offset.
  change (sizeof(UCHAR)) with 1.
  unfold store_ptr, store_ushort.
  change ptr_size with 4%nat; cbn.
  unfold store_4byte, store_2byte.
  Exists 0 0 0 0 0 0 0 0 0 0.
  assert (Hptr : isvalidptr (p + 4)).
  { change (p + 4 >= 0 /\ p + 4 + 4 - 1 <= 4294967295 /\
            (p + 4) mod 4 = 0).
    repeat split; try lia.
    rewrite Z.add_mod, Halign by lia; reflexivity. }
  assert (Hname : isvalidptr (p + 20)).
  { change (p + 20 >= 0 /\ p + 20 + 4 - 1 <= 4294967295 /\
            (p + 20) mod 4 = 0).
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
  replace (p + 20 + 1) with (p + 21) by lia.
  replace (p + 20 + 2) with (p + 22) by lia.
  replace (p + 20 + 3) with (p + 23) by lia.
  unfold store_uchar.
  entailer!.
Qed.

Lemma init_event_list_named_firstn_repeat : forall A (a : A) n m,
  firstn n (repeat a m) = repeat a (Nat.min n m).
Proof.
  intros A a n; induction n; intros [|m]; simpl; auto.
  rewrite IHn; reflexivity.
Qed.

Lemma init_event_list_named_skipn_repeat : forall A (a : A) n m,
  skipn n (repeat a m) = repeat a (m - n).
Proof. intros A a n; induction n; intros [|m]; simpl; auto. Qed.

Lemma init_event_list_named_split_cleared_bytes : forall p n m,
  0 <= n <= m ->
  mem_clr_post p m |-- mem_clr_post p n ** mem_clr_post (p + n) (m - n).
Proof.
  intros p n m Hnm; unfold mem_clr_post.
  sep_apply (UCharArray.full_split_to_full p n m (repeat_Z 0 m) Hnm).
  change (sizeof(UCHAR)) with 1.
  replace (p + n * 1) with (p + n) by lia.
  unfold sublist, repeat_Z.
  rewrite !init_event_list_named_firstn_repeat, !init_event_list_named_skipn_repeat.
  rewrite !Nat.min_l by lia.
  replace (Z.to_nat n - Z.to_nat 0)%nat with (Z.to_nat n) by lia.
  replace (Z.to_nat m - Z.to_nat n)%nat with (Z.to_nat (m - n)) by lia.
  entailer!.
Qed.

Definition init_event_list_named_loop_residual (sg : StableGlobVars)
  (name : addr) (ix : Z) : Assertion :=
  sg.(g_OSEventFreeList) # Ptr |->_ **
  init_event_list_named_prefix sg name ix **
  init_event_list_named_node_residual (event_pool_addr sg ix) **
  mem_clr_post (event_pool_addr sg (ix + 1)) (24 * (sg.(osMaxEvents) - ix - 1)).

Lemma init_event_list_named_loop_split_node : forall sg name ix,
  sg.(osKernelConfig).(cfgEventNames) = true -> 0 <= ix < sg.(osMaxEvents) ->
  0 <= sg.(g_OSEventTbl) ->
  sg.(g_OSEventTbl) + 24 * sg.(osMaxEvents) <= 4294967295 ->
  sg.(g_OSEventTbl) mod 4 = 0 ->
  init_event_list_named_loop_state sg name ix |--
  event_cell (event_pool_addr sg ix) EventTypeField (Some 0) **
  event_cell (event_pool_addr sg ix) EventPtrField (Some 0) **
  event_cell (event_pool_addr sg ix) EventNameField (Some 0) **
  init_event_list_named_loop_residual sg name ix.
Proof.
  intros sg name ix Hnamed Hix Hbase Hend Halign.
  assert (Hsize : event_object_size sg.(osKernelConfig) = 24).
  { unfold event_object_size; rewrite Hnamed; reflexivity. }
  unfold init_event_list_named_loop_state, init_event_list_named_loop_residual.
  rewrite Hsize.
  sep_apply (init_event_list_named_split_cleared_bytes (event_pool_addr sg ix)
    24 (24 * (osMaxEvents sg - ix)) ltac:(lia)).
  replace (24 * (osMaxEvents sg - ix) - 24) with
    (24 * (osMaxEvents sg - ix - 1)) by lia.
  replace (event_pool_addr sg ix + 24) with (event_pool_addr sg (ix + 1))
    by (unfold event_pool_addr; rewrite Hsize; lia).
  assert (Hnode_align : event_pool_addr sg ix mod 4 = 0).
  { unfold event_pool_addr; rewrite Hsize.
    rewrite Z.add_mod, Z.mul_mod, Halign by lia.
    replace (24 mod 4) with 0 by reflexivity.
    rewrite Z.mul_0_r; reflexivity. }
  sep_apply (init_event_list_named_cleared_node (event_pool_addr sg ix)
    ltac:(unfold event_pool_addr; rewrite Hsize; lia)
    ltac:(unfold event_pool_addr; rewrite Hsize; lia) Hnode_align).
  sep_apply (init_event_list_named_split_zero_node (event_pool_addr sg ix)).
  entailer!.
Qed.

Lemma init_event_list_named_loop_merge_node : forall sg name ix,
  sg.(osKernelConfig).(cfgEventNames) = true -> 0 <= ix ->
  event_cell (event_pool_addr sg ix) EventTypeField (Some 0) **
  event_cell (event_pool_addr sg ix) EventPtrField
    (Some (event_encode_pool_link sg (kernel_list_next (Zrange 0 (osMaxEvents sg)) ix))) **
  event_cell (event_pool_addr sg ix) EventNameField (Some name) **
  init_event_list_named_loop_residual sg name ix |--
  init_event_list_named_loop_state sg name (ix + 1).
Proof.
  intros sg name ix Hnamed Hix.
  unfold init_event_list_named_loop_residual, init_event_list_named_loop_state.
  sep_apply_l_atomic (init_event_list_named_merge_written_node sg name ix).
  sep_apply_l_atomic (init_event_list_named_prefix_merge_node sg name ix Hix).
  unfold event_object_size; rewrite Hnamed.
  replace (osMaxEvents sg - (ix + 1)) with (osMaxEvents sg - ix - 1) by lia.
  entailer!.
Qed.
