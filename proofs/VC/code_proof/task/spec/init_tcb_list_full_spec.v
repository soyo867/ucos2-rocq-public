Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.task.spec.tcb_zero_full_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Full-profile OS_InitTCBList boundary.  This owner is deliberately
    separate from [init_tcb_list_spec.v], whose 64-byte contract is retained
    for the historical configuration.  It uses the configured Task storage
    owner, so Multi/profile fields are included without another native record. *)
Definition init_tcb_list_full_profile (sg : StableGlobVars) : Prop :=
  sg.(osMaxTasks) = 20 /\ sg.(osNSysTasks) = 2 /\
  sg.(osLowestPrio) = 63 /\
  sg.(osKernelConfig) = full_features_kernel_configuration.

Definition init_tcb_list_full_layout (sg : StableGlobVars) : Prop :=
  sizeof("os_tcb") = 92 /\
  task_object_size sg.(osKernelConfig) = 92 /\
  0 < sg.(g_OSTCBTbl) /\
  sg.(g_OSTCBTbl) + 92 * 22 <= 4294967295 /\
  sg.(g_OSTCBTbl) mod 4 = 0 /\
  0 < sg.(g_OSTCBPrioTbl) /\
  sg.(g_OSTCBPrioTbl) + 4 * 64 <= 4294967295 /\
  sg.(g_OSTCBPrioTbl) mod 4 = 0.

(** The named C fields are opaque to SeparationLogic.  This is the explicit
    ABI/layout bridge consumed by the byte-to-configured-TCB reconstruction;
    it is not inferred from [task_object_size]. *)
Definition init_tcb_list_full_field_layout (sg : StableGlobVars) : Prop :=
  forall tid field, 0 <= tid < 22 ->
    tcb_layout_field_address true (task_slot_addr sg tid) field =
      task_slot_addr sg tid + tcb_configured_field_offset true true field.

Definition init_tcb_list_full_zero_image : TCBLayoutImage :=
  fun _ => Some 0.

Definition init_tcb_list_full_global_addresses
  (sg : StableGlobVars) (pool prios used_root free_root : addr) : Prop :=
  pool = sg.(g_OSTCBTbl) /\ prios = sg.(g_OSTCBPrioTbl) /\
  used_root = sg.(g_OSTCBList) /\ free_root = sg.(g_OSTCBFreeList).

Definition init_tcb_list_full_pre (sg : StableGlobVars) : Assertion :=
  UCharArray.undef_full sg.(g_OSTCBTbl) (92 * 22) **
  UCharArray.undef_full sg.(g_OSTCBPrioTbl) (4 * 64) **
  sg.(g_OSTCBList) # Ptr |->_ ** sg.(g_OSTCBFreeList) # Ptr |->_.

Definition init_tcb_list_full_post
  (sg : StableGlobVars) (name : addr) : Assertion :=
  task_free_storage_rep sg
    (task_boot_storage sg name (Zrange 0 22)) (Zrange 0 22) **
  store_prio_tbl sg (fun _ => PTFree) **
  sg.(g_OSTCBList) # Ptr |-> 0 **
  sg.(g_OSTCBFreeList) # Ptr |-> sg.(g_OSTCBTbl).

Definition init_tcb_list_full_roots (sg : StableGlobVars) : Assertion :=
  sg.(g_OSTCBList) # Ptr |->_ ** sg.(g_OSTCBFreeList) # Ptr |->_.

Definition init_tcb_list_full_priority_zero (sg : StableGlobVars) : Assertion :=
  store_prio_tbl sg (fun _ => PTFree).

Definition init_tcb_list_full_prefix (sg : StableGlobVars)
  (name upto : Z) : Assertion :=
  task_free_storage_rep sg
    (task_boot_storage sg name (Zrange 0 22)) (Zrange 0 upto).

Definition init_tcb_list_full_zero_suffix (sg : StableGlobVars) (first : Z)
  : Assertion :=
  task_free_storage_rep sg
    (fun _ => Some init_tcb_list_full_zero_image) (Zrange first 22).

Definition init_tcb_list_full_loop_node_residual
  (base : addr) (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec (TCBCommonField TCBTaskName)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext)
        (tcb_configured_fields true true))) image.

Definition init_tcb_list_full_node_residual
  (sg : StableGlobVars) (ix : Z) : Assertion :=
  init_tcb_list_full_loop_node_residual
    (task_slot_addr sg ix) init_tcb_list_full_zero_image.

Lemma init_tcb_list_full_remove_preserves_nodup : forall (A : Type)
  (dec : forall x y : A, {x = y} + {x <> y}) x fields,
  NoDup fields -> NoDup (remove dec x fields).
Proof.
  intros A dec x fields Hnd.
  induction Hnd as [|head rest Hnot Hnd IH]; cbn.
  - constructor.
  - destruct (dec x head) as [Heq|Hne].
    + exact IH.
    + constructor; [|exact IH].
      intro Hin; apply Hnot.
      apply in_remove in Hin; tauto.
Qed.

(** Split the two concrete fields written by [OS_InitTCBList] from one
    configured full-profile TCB image.  Multi and profiling fields remain in
    the residual; no second TCB representation is introduced. *)
Lemma init_tcb_list_full_storage_split_next_name : forall base image,
  tcb_configured_storage_rep true true base image |--
    tcb_layout_cell true base (TCBCommonField TCBNext)
      (image (TCBCommonField TCBNext)) **
    tcb_layout_cell true base (TCBCommonField TCBTaskName)
      (image (TCBCommonField TCBTaskName)) **
    init_tcb_list_full_loop_node_residual base image.
Proof.
  intros base image.
  unfold tcb_configured_storage_rep,
    init_tcb_list_full_loop_node_residual.
  sep_apply_l_atomic
    (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true base) (tcb_configured_fields true true) image
      (TCBCommonField TCBNext)
      (tcb_configured_fields_nodup true true)
      (tcb_configured_common_field_in true true TCBNext)).
  sep_apply_l_atomic
    (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
      (tcb_layout_cell true base)
      (remove TCBLayoutField_eq_dec (TCBCommonField TCBNext)
        (tcb_configured_fields true true)) image
      (TCBCommonField TCBTaskName)
      ltac:(apply init_tcb_list_full_remove_preserves_nodup;
        apply tcb_configured_fields_nodup)
      ltac:(apply in_in_remove;
        [ discriminate | apply tcb_configured_common_field_in ] )).
  entailer!.
Qed.

Definition init_tcb_list_full_loop_state (sg : StableGlobVars)
  (name ix : Z) : Assertion :=
  init_tcb_list_full_roots sg **
  init_tcb_list_full_priority_zero sg **
  init_tcb_list_full_prefix sg name ix **
  init_tcb_list_full_zero_suffix sg ix.

Definition init_tcb_list_full_loop_residual (sg : StableGlobVars)
  (name ix : Z) : Assertion :=
  init_tcb_list_full_roots sg **
  init_tcb_list_full_priority_zero sg **
  init_tcb_list_full_prefix sg name ix **
  init_tcb_list_full_loop_node_residual
    (task_slot_addr sg ix) init_tcb_list_full_zero_image **
  init_tcb_list_full_zero_suffix sg (ix + 1).

Lemma init_tcb_list_full_zrange_head : forall lo hi,
  lo < hi -> Zrange lo hi = lo :: Zrange (lo + 1) hi.
Proof.
  intros lo hi Hlt; unfold Zrange.
  replace (Z.to_nat (hi - lo)) with
    (S (Z.to_nat (hi - (lo + 1)))) by lia.
  reflexivity.
Qed.

Lemma init_tcb_list_full_zrange_empty : forall lo hi,
  hi <= lo -> Zrange lo hi = (@nil Z).
Proof.
  intros lo hi Hle; unfold Zrange.
  replace (Z.to_nat (hi - lo)) with O by lia; reflexivity.
Qed.

Lemma init_tcb_list_full_zrange_snoc : forall lo hi,
  lo <= hi -> Zrange lo (hi + 1) = (Zrange lo hi ++ [hi])%list.
Proof.
  intros lo hi Hle.
  unfold Zrange.
  replace (Z.to_nat (hi + 1 - lo)) with
    (Z.to_nat (hi - lo) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  replace (lo + Z.of_nat (Z.to_nat (hi - lo))) with hi by lia.
  cbn; reflexivity.
Qed.

Lemma task_free_storage_rep_app_full : forall sg storage l r,
  task_free_storage_rep sg storage (l ++ r)%list --||--
    task_free_storage_rep sg storage l ** task_free_storage_rep sg storage r.
Proof.
  intros sg storage l; induction l as [|tid rest IH]; intro r;
    cbn [app task_free_storage_rep].
  - split; entailer!.
  - rewrite IH; split; Intros image; Exists image; entailer!.
Qed.

Lemma task_boot_storage_app_not_in_full : forall sg name l r tid,
  ~ In tid l ->
  task_boot_storage sg name (l ++ r)%list tid = task_boot_storage sg name r tid.
Proof.
  intros sg name l; induction l as [|head rest IH]; intros r tid Hnot; cbn.
  - reflexivity.
  - destruct (Z.eq_dec tid head); [subst; exfalso; apply Hnot; left; reflexivity|].
    apply IH; intro Hin; apply Hnot; right; exact Hin.
Qed.

Lemma task_boot_storage_range_lookup_full : forall sg name lo hi tid,
  lo <= tid < hi ->
  task_boot_storage sg name (Zrange lo hi) tid =
    Some (task_boot_image sg name (hd_error (Zrange (tid + 1) hi))).
Proof.
  intros sg name lo hi tid Hrange.
  unfold Zrange.
  replace (Z.to_nat (hi - lo)) with
    (Z.to_nat (tid - lo) + Z.to_nat (hi - tid))%nat by lia.
  rewrite Zrange_aux_app.
  replace (lo + Z.of_nat (Z.to_nat (tid - lo))) with tid by lia.
  fold (Zrange lo tid).
  fold (Zrange tid hi).
  rewrite task_boot_storage_app_not_in_full.
  - rewrite (init_tcb_list_full_zrange_head tid hi) by lia.
    cbn [task_boot_storage]; destruct (Z.eq_dec tid tid); [reflexivity|contradiction].
  - rewrite <- In_Zrange; lia.
Qed.

Lemma task_free_storage_range_extend_full : forall sg storage lo hi image,
  lo <= hi -> storage hi = Some image ->
  task_free_storage_rep sg storage (Zrange lo hi) **
    task_slot_storage_rep sg hi image |--
  task_free_storage_rep sg storage (Zrange lo (hi + 1)).
Proof.
  intros sg storage lo hi image Hle Hlookup.
  rewrite (init_tcb_list_full_zrange_snoc lo hi) by exact Hle.
  rewrite task_free_storage_rep_app_full.
  cbn [task_free_storage_rep].
  Exists image; entailer!.
Qed.

Lemma init_tcb_list_full_profile_valid : forall sg,
  init_tcb_list_full_profile sg ->
  sg.(osKernelConfig) = full_features_kernel_configuration.
Proof. intros sg [_ [_ [_ H]]]; exact H. Qed.

Lemma init_tcb_list_full_layout_size : forall sg,
  init_tcb_list_full_profile sg ->
  task_object_size sg.(osKernelConfig) = 92.
Proof.
  intros sg H; unfold init_tcb_list_full_profile in H.
  destruct H as [_ [_ [_ ->]]].
  apply full_features_task_object_size.
Qed.

Lemma init_tcb_list_full_layout_source_size : forall sg,
  init_tcb_list_full_layout sg -> sizeof("os_tcb") = 92.
Proof. intros sg [Hsize _]; exact Hsize. Qed.

Lemma init_tcb_list_full_layout_from_profile : forall sg,
  init_tcb_list_full_profile sg ->
  task_layout_configuration sg.(osKernelConfig).
Proof.
  intros sg H; unfold init_tcb_list_full_profile in H.
  destruct H as [_ [_ [_ ->]]].
  apply full_features_kernel_configuration_task_layout.
Qed.

Lemma init_tcb_list_full_profile_enables_multi_and_profile : forall sg,
  init_tcb_list_full_profile sg ->
  sg.(osKernelConfig).(cfgEventMultiEnabled) = true /\
  sg.(osKernelConfig).(cfgTaskProfile) = true /\
  sg.(osKernelConfig).(cfgEventNames) = true.
Proof.
  intros sg H; unfold init_tcb_list_full_profile in H.
  destruct H as [_ [_ [_ ->]]]; repeat split; reflexivity.
Qed.

Lemma init_tcb_list_full_slot_addr_stride : forall sg tid,
  init_tcb_list_full_profile sg ->
  task_slot_addr sg tid = sg.(g_OSTCBTbl) + tid * 92.
Proof.
  intros sg tid H.
  unfold init_tcb_list_full_profile in H.
  destruct H as [_ [_ [_ Hconfig]]].
  unfold task_slot_addr, tcb_configured_size.
  rewrite Hconfig; cbn; lia.
Qed.

Lemma init_tcb_list_full_pre_pool_lengths : forall sg,
  init_tcb_list_full_profile sg ->
  92 * 22 = 2024 /\ 4 * 64 = 256.
Proof. intros; split; lia. Qed.

Lemma task_slot_storage_full : forall sg tid image,
  init_tcb_list_full_profile sg ->
  task_slot_storage_rep sg tid image --||--
    tcb_configured_storage_rep true true (task_slot_addr sg tid) image.
Proof.
  intros sg tid image Hprofile.
  pose proof (init_tcb_list_full_profile_valid sg Hprofile) as Hconfig.
  unfold task_slot_storage_rep.
  rewrite Hconfig.
  cbn [cfgEventMultiEnabled cfgTaskProfile].
  reflexivity.
Qed.

(** Canonical clear output for the full profile.  This closes only the
    resource reconstruction from the 92-byte byte image; it does not claim
    the OS_InitTCBList control-flow or its public postcondition. *)
Lemma zero_bytes_to_full_task_storage : forall sg n first,
  init_tcb_list_full_profile sg ->
  init_tcb_list_full_layout sg ->
  init_tcb_list_full_field_layout sg ->
  0 <= first -> first + Z.of_nat n <= 22 ->
  UCharArray.full (task_slot_addr sg first) (92 * Z.of_nat n)
    (repeat_Z 0 (92 * Z.of_nat n)) |--
  task_free_storage_rep sg (fun _ => Some init_tcb_list_full_zero_image)
    (Zrange_aux first n).
Proof.
  intros sg n; induction n as [|n IH]; intros first Hprofile Hlayout Hfields Hfirst Hend.
  - change (92 * Z.of_nat 0) with 0.
    change (repeat_Z 0 0) with (@nil Z).
    cbn [Zrange_aux task_free_storage_rep].
    rewrite UCharArray.full_empty; entailer!.
  - cbn [Zrange_aux task_free_storage_rep].
    sep_apply (zero_bytes_split (task_slot_addr sg first) 92
      (92 * Z.of_nat (S n)) ltac:(lia)).
    replace (92 * Z.of_nat (S n) - 92) with (92 * Z.of_nat n) by lia.
    replace (task_slot_addr sg first + 92) with
      (task_slot_addr sg (first + 1))
      by (rewrite !init_tcb_list_full_slot_addr_stride by assumption; lia).
    sep_apply (IH (first + 1) Hprofile Hlayout Hfields ltac:(lia) ltac:(lia)).
    Exists init_tcb_list_full_zero_image.
    entailer!.
    rewrite task_slot_storage_full by exact Hprofile.
    apply zero_bytes_to_tcb_full_storage.
    + destruct Hlayout as [_ [_ [_ [_ [Hmod _]]]]].
      rewrite init_tcb_list_full_slot_addr_stride by exact Hprofile.
      unfold task_slot_addr in *; rewrite Z.add_mod, Z.mul_mod, Hmod by lia.
      replace (92 mod 4) with 0 by reflexivity.
      rewrite Z.mul_0_r; reflexivity.
    + intro field; reflexivity.
    + intros field; apply Hfields; lia.
Qed.
