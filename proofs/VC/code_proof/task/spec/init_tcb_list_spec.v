Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Initialization-only profile.  No ready/running kernel invariant is an
    input.  The complete selected ABI is an explicit representation boundary:
    named C field addresses are not definitionally numeric byte offsets. *)
Definition init_tcb_list_profile (sg : StableGlobVars) : Prop :=
  sg.(osMaxTasks) = 20 /\ sg.(osNSysTasks) = 2 /\
  sg.(osLowestPrio) = 63 /\
  sg.(osKernelConfig) = selected_kernel_configuration.

Definition init_tcb_list_global_addresses
  (sg : StableGlobVars) (pool prios used_root free_root : addr) : Prop :=
  pool = sg.(g_OSTCBTbl) /\ prios = sg.(g_OSTCBPrioTbl) /\
  used_root = sg.(g_OSTCBList) /\ free_root = sg.(g_OSTCBFreeList).

Definition init_tcb_list_layout (sg : StableGlobVars) : Prop :=
  sizeof_alias_type "os_tcb" = 64 /\
  0 < sg.(g_OSTCBTbl) /\ sg.(g_OSTCBTbl) + 1408 <= 4294967295 /\
  sg.(g_OSTCBTbl) mod 4 = 0 /\
  0 < sg.(g_OSTCBPrioTbl) /\ sg.(g_OSTCBPrioTbl) + 256 <= 4294967295 /\
  sg.(g_OSTCBPrioTbl) mod 4 = 0 /\
  (forall tid field, 0 <= tid < 22 ->
    tcb_field_address (tcb64_addr sg tid) field =
      tcb64_addr sg tid + tcb_field_offset field).

(** Exactly the writable bytes and roots.  Each MemClr end address is
    representable even after its last pointer increment.  The two lengths
    fit its existing INT16U contract; no typed-zero callee is declared. *)
Definition init_tcb_list_pre (sg : StableGlobVars) : Assertion :=
  mem_clr_pre sg.(g_OSTCBTbl) 1408 **
  mem_clr_pre sg.(g_OSTCBPrioTbl) 256 **
  sg.(g_OSTCBList) # Ptr |->_ ** sg.(g_OSTCBFreeList) # Ptr |->_.

Definition init_tcb_list_roots (sg : StableGlobVars) : Assertion :=
  sg.(g_OSTCBList) # Ptr |->_ ** sg.(g_OSTCBFreeList) # Ptr |->_.

Definition init_tcb_list_zero_image (sg : StableGlobVars) : TCBLayoutImage :=
  tcb_init_free_image sg None 0.

(** These are slices of the existing Task storage owner, not another TCB
    representation.  The processed prefix already has its final image. *)
Definition init_tcb_list_prefix (sg : StableGlobVars) (name upto : Z) : Assertion :=
  task_free_storage_rep sg (task_boot_storage sg name (Zrange 0 22))
    (Zrange 0 upto).

Definition init_tcb_list_zero_suffix (sg : StableGlobVars) (first : Z) : Assertion :=
  task_free_storage_rep sg (fun _ => Some (init_tcb_list_zero_image sg))
    (Zrange first 22).

Definition init_tcb_list_priority_zero (sg : StableGlobVars) : Assertion :=
  store_prio_tbl sg (fun _ => PTFree).

Definition init_tcb_list_loop_state (sg : StableGlobVars) (name ix : Z) : Assertion :=
  init_tcb_list_roots sg ** init_tcb_list_priority_zero sg **
  init_tcb_list_prefix sg name ix ** init_tcb_list_zero_suffix sg ix.

(** All fields except the two actual writes remain the exact clear image,
    including FlagsRdy, the register cell, and padding bytes 42 and 43. *)
Definition init_tcb_list_node_residual (sg : StableGlobVars) (ix : Z) : Assertion :=
  tcb64_fields_rep (tcb64_addr sg ix)
    (remove TCBField_eq_dec TCBTaskName
      (remove TCBField_eq_dec TCBNext tcb_fields))
    (tcb_layout_common_image (init_tcb_list_zero_image sg)).

Definition init_tcb_list_loop_residual (sg : StableGlobVars) (name ix : Z) : Assertion :=
  init_tcb_list_roots sg ** init_tcb_list_priority_zero sg **
  init_tcb_list_prefix sg name ix ** init_tcb_list_node_residual sg ix **
  init_tcb_list_zero_suffix sg (ix + 1).

Definition init_tcb_list_post (sg : StableGlobVars) (name : addr) : Assertion :=
  task_free_storage_rep sg (task_boot_storage sg name (Zrange 0 22)) (Zrange 0 22) **
  init_tcb_list_priority_zero sg **
  sg.(g_OSTCBList) # Ptr |-> 0 ** sg.(g_OSTCBFreeList) # Ptr |-> sg.(g_OSTCBTbl).

Lemma init_tcb_list_profile_no_multi : forall sg,
  init_tcb_list_profile sg -> sg.(osKernelConfig).(cfgEventMultiEnabled) = false.
Proof. intros sg [_ [_ [_ Hconfig]]]; rewrite Hconfig; reflexivity. Qed.

Lemma init_tcb_list_profile_no_profiling : forall sg,
  init_tcb_list_profile sg -> sg.(osKernelConfig).(cfgTaskProfile) = false.
Proof. intros sg [_ [_ [_ Hconfig]]]; rewrite Hconfig; reflexivity. Qed.

(** A conditional producer from the existing basic64 safe-init boundary.
    It does not establish a linked address or prove OSInit/deployment. *)
Lemma init_tcb_list_tcb_pool_initialization_endpoint : forall sg,
  init_tcb_list_profile sg -> init_tcb_list_layout sg ->
  valid_tcb_pool_initialization_endpoint sg.
Proof.
  intros sg [Happ [Hsystem [_ Hconfig]]] [_ [_ [Hendpoint _]]].
  unfold valid_tcb_pool_initialization_endpoint.
  rewrite Happ, Hsystem, Hconfig; exact Hendpoint.
Qed.

Lemma init_tcb_list_selected_kernel_profile : forall sg,
  init_tcb_list_profile sg -> init_tcb_list_layout sg ->
  valid_stable_glob_vars sg -> valid_selected_kernel_global_layout sg ->
  selected_kernel_profile sg.
Proof.
  intros sg Hprofile Hlayout Hstable Hglobal.
  pose proof (init_tcb_list_tcb_pool_initialization_endpoint sg Hprofile Hlayout)
    as Hendpoint.
  destruct Hprofile as [Happ [Hsystem [_ Hconfig]]].
  unfold selected_kernel_profile.
  split; [exact Hstable|].
  rewrite Happ, Hsystem, Hconfig.
  split; [reflexivity|]. split; [reflexivity|].
  split; [apply selected_kernel_configuration_valid|].
  split; [apply selected_kernel_configuration_tcb64|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [cbn; lia|]. split; assumption.
Qed.

Lemma init_tcb_list_zero_image_all_fields : forall sg field,
  init_tcb_list_zero_image sg field = Some 0.
Proof. intros sg [field| | | | | | |]; try destruct field; reflexivity. Qed.

Lemma init_tcb_list_profile_boot_in_range : forall sg name,
  init_tcb_list_profile sg -> task_in_range sg (task_boot sg name).
Proof.
  intros sg name [_ [_ [_ Hconfig]]].
  apply task_boot_in_range; rewrite Hconfig; cbn; lia.
Qed.

Lemma init_tcb_list_boot_free_ids : forall sg name,
  init_tcb_list_profile sg -> (task_boot sg name).(unUsedTaskStates) = Zrange 0 22.
Proof.
  intros sg name [Happ [Hsys _]].
  cbn [task_boot unUsedTaskStates]; rewrite Happ, Hsys; reflexivity.
Qed.

(** OS_InitMisc supplies these two unchanged zero cells.  Only the composed
    assertion, never InitTCBList's own postcondition, owns them. *)
Lemma init_tcb_list_post_to_task_boot : forall sg name,
  init_tcb_list_profile sg ->
  init_tcb_list_post sg name **
  sg.(g_OSTaskCtr) # UChar |-> 0 ** sg.(g_OSTaskRegNextAvailID) # UChar |-> 0 |--
  task_public_storage sg (task_boot sg name).
Proof.
  intros sg name [Happ [Hsys [_ Hconfig]]].
  unfold init_tcb_list_post, init_tcb_list_priority_zero, task_public_storage,
    task_reg_allocator_rep, task_boot.
  cbn [inUsedTaskStates unUsedTaskStates tcbListHead taskCount prioTbl
    taskLifecycle taskFreeStorage taskRegNextID].
  rewrite Happ, Hsys, Hconfig.
  change (20 + 2) with 22.
  change (Z.ltb 0 (cfgTaskRegisters selected_kernel_configuration)) with true.
  change (hd_error (Zrange 0 22)) with (Some 0).
  unfold encode_task_link, task_slot_addr, tcb_configured_size, tcb_layout_size.
  rewrite Hconfig; cbn [cfgEventMultiEnabled cfgTaskProfile].
  replace (g_OSTCBTbl sg + 0 * 64) with (g_OSTCBTbl sg) by lia.
  unfold store_used_task_map.
  rewrite store_map_empty.
  - entailer!; rewrite Z.mul_0_l, Z.add_0_r; reflexivity.
  - exists []; split; [intro tid; split; [contradiction|intros [t H]; discriminate]|constructor].
  - intro tid; left; reflexivity.
Qed.

Require Import Coq.Logic.FunctionalExtensionality.
Lemma Zrange_head__tcb_link_and_publication : forall lo hi,
  lo < hi -> Zrange lo hi = lo :: Zrange (lo + 1) hi.
Proof.
  intros lo hi Hlt; unfold Zrange.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  reflexivity.
Qed.
Lemma Zrange_empty__tcb_link_and_publication : forall lo hi,
  hi <= lo -> Zrange lo hi = [].
Proof.
  intros lo hi Hle; unfold Zrange.
  replace (Z.to_nat (hi - lo)) with O by lia; reflexivity.
Qed.
Lemma Zrange_split__tcb_link_and_publication : forall lo mid hi,
  lo <= mid <= hi -> Zrange lo hi = (Zrange lo mid ++ Zrange mid hi)%list.
Proof.
  intros lo mid hi Hle; unfold Zrange.
  replace (Z.to_nat (hi - lo)) with
    (Z.to_nat (mid - lo) + Z.to_nat (hi - mid))%nat by lia.
  rewrite Zrange_aux_app.
  replace (lo + Z.of_nat (Z.to_nat (mid - lo))) with mid by lia.
  reflexivity.
Qed.
Lemma Zrange_snoc__tcb_link_and_publication : forall lo hi,
  lo <= hi -> Zrange lo (hi + 1) = (Zrange lo hi ++ [hi])%list.
Proof.
  intros lo hi Hle; rewrite (Zrange_split__tcb_link_and_publication lo hi (hi + 1)) by lia.
  rewrite (Zrange_head__tcb_link_and_publication hi (hi + 1)) by lia.
  rewrite (Zrange_empty__tcb_link_and_publication (hi + 1) (hi + 1)) by lia; reflexivity.
Qed.
Lemma task_free_storage_rep_app__tcb_link_and_publication : forall sg storage l r,
  task_free_storage_rep sg storage (l ++ r)%list --||--
    task_free_storage_rep sg storage l ** task_free_storage_rep sg storage r.
Proof.
  intros sg storage l; induction l as [|tid rest IH]; intro r;
    cbn [app task_free_storage_rep].
  - split; entailer!.
  - rewrite IH; split; Intros image; Exists image; entailer!.
Qed.
Lemma task_boot_storage_app_not_in__tcb_link_and_publication : forall sg name l r tid,
  ~ In tid l ->
  task_boot_storage sg name (l ++ r)%list tid = task_boot_storage sg name r tid.
Proof.
  intros sg name l; induction l as [|head rest IH]; intros r tid Hnot; cbn.
  - reflexivity.
  - destruct (Z.eq_dec tid head); [subst; exfalso; apply Hnot; left; reflexivity|].
    apply IH; intro Hin; apply Hnot; right; exact Hin.
Qed.
Lemma task_boot_storage_range_lookup__tcb_link_and_publication : forall sg name lo hi tid,
  lo <= tid < hi ->
  task_boot_storage sg name (Zrange lo hi) tid =
    Some (task_boot_image sg name (hd_error (Zrange (tid + 1) hi))).
Proof.
  intros sg name lo hi tid Hrange.
  rewrite (Zrange_split__tcb_link_and_publication lo tid hi) by lia.
  rewrite task_boot_storage_app_not_in__tcb_link_and_publication.
  - rewrite Zrange_head__tcb_link_and_publication by lia.
    cbn [task_boot_storage]; destruct (Z.eq_dec tid tid); [reflexivity|contradiction].
  - rewrite <- In_Zrange; lia.
Qed.
Lemma remove_preserves_nodup__tcb_link_and_publication : forall (A : Type)
  (dec : forall x y : A, {x = y} + {x <> y}) x fields,
  NoDup fields -> NoDup (remove dec x fields).
Proof.
  intros A dec x fields Hnd; induction Hnd as [|head rest Hnot Hnd IH]; cbn.
  - constructor.
  - destruct (dec x head) as [Heq|Hne]; [exact IH|].
    constructor; [|exact IH].
    intro Hin; apply Hnot; apply in_remove in Hin; tauto.
Qed.
Lemma tcb64_storage_split_next_name__tcb_link_and_publication : forall base image,
  tcb64_storage_rep base image |--
    tcb_cell base TCBNext (image TCBNext) **
    tcb_cell base TCBTaskName (image TCBTaskName) **
    tcb64_fields_rep base
      (remove TCBField_eq_dec TCBTaskName (remove TCBField_eq_dec TCBNext tcb_fields)) image.
Proof.
  intros base image; unfold tcb64_storage_rep.
  sep_apply_l_atomic (tcb64_fields_rep_split tcb_fields base image TCBNext
    tcb_fields_nodup (tcb_fields_complete TCBNext)).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBNext tcb_fields) base image TCBTaskName
    (remove_preserves_nodup__tcb_link_and_publication _ _ _ _ tcb_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply tcb_fields_complete])).
  entailer!.
Qed.
Lemma tcb64_storage_merge_next_name_updated__tcb_link_and_publication : forall base image next name,
  tcb_cell base TCBNext next ** tcb_cell base TCBTaskName name **
    tcb64_fields_rep base
      (remove TCBField_eq_dec TCBTaskName (remove TCBField_eq_dec TCBNext tcb_fields)) image |--
  tcb64_storage_rep base (tcb_write (tcb_write image TCBTaskName name) TCBNext next).
Proof.
  intros base image next name.
  sep_apply_l_atomic (tcb64_fields_rep_merge_updated
    (remove TCBField_eq_dec TCBNext tcb_fields) base image TCBTaskName name
    (remove_preserves_nodup__tcb_link_and_publication _ _ _ _ tcb_fields_nodup)
    ltac:(apply in_in_remove; [discriminate|apply tcb_fields_complete])).
  sep_apply_l_atomic (tcb64_storage_merge_updated base
    (tcb_write image TCBTaskName name) TCBNext next).
  entailer!.
Qed.
Lemma tcb_init_free_common_image_eq__tcb_link_and_publication : forall sg next name,
  tcb_layout_common_image (tcb_init_free_image sg next name) =
    tcb_write
      (tcb_write (tcb_layout_common_image (init_tcb_list_zero_image sg)) TCBTaskName (Some name))
      TCBNext (Some (encode_task_link sg next)).
Proof.
  intros; apply functional_extensionality; intros []; reflexivity.
Qed.
Lemma task_free_storage_range_extend__tcb_link_and_publication : forall sg storage lo hi image,
  lo <= hi -> storage hi = Some image ->
  task_free_storage_rep sg storage (Zrange lo hi) ** task_slot_storage_rep sg hi image |--
  task_free_storage_rep sg storage (Zrange lo (hi + 1)).
Proof.
  intros sg storage lo hi image Hle Hlookup.
  rewrite Zrange_snoc__tcb_link_and_publication by exact Hle.
  rewrite task_free_storage_rep_app__tcb_link_and_publication.
  cbn [task_free_storage_rep].
  Exists image; entailer!.
Qed.
Lemma init_tcb_list_zero_suffix_split_next_name__tcb_link_and_publication : forall sg ix,
  init_tcb_list_profile sg -> ix < 22 ->
  init_tcb_list_zero_suffix sg ix |--
  tcb_cell (tcb64_addr sg ix) TCBNext (Some 0) **
  tcb_cell (tcb64_addr sg ix) TCBTaskName (Some 0) **
  init_tcb_list_node_residual sg ix ** init_tcb_list_zero_suffix sg (ix + 1).
Proof.
  intros sg ix Hprofile Hrange.
  unfold init_tcb_list_zero_suffix at 1.
  rewrite Zrange_head__tcb_link_and_publication by exact Hrange.
  cbn [task_free_storage_rep].
  Intros image.
  injection H as Himage; subst image.
  rewrite (task_slot_storage_tcb64 sg ix (init_tcb_list_zero_image sg))
    by (first [apply init_tcb_list_profile_no_multi | apply init_tcb_list_profile_no_profiling]; exact Hprofile).
  sep_apply_l_atomic (tcb64_storage_split_next_name__tcb_link_and_publication
    (tcb64_addr sg ix) (tcb_layout_common_image (init_tcb_list_zero_image sg))).
  unfold init_tcb_list_node_residual, init_tcb_list_zero_suffix.
  entailer!.
Qed.
Lemma init_tcb_list_node_merge_next_name_updated__tcb_link_and_publication : forall sg ix next name,
  init_tcb_list_profile sg ->
  tcb_cell (tcb64_addr sg ix) TCBNext (Some (encode_task_link sg next)) **
  tcb_cell (tcb64_addr sg ix) TCBTaskName (Some name) **
  init_tcb_list_node_residual sg ix |--
  task_slot_storage_rep sg ix (tcb_init_free_image sg next name).
Proof.
  intros sg ix next name Hprofile.
  rewrite task_slot_storage_tcb64 by
    (first [apply init_tcb_list_profile_no_multi | apply init_tcb_list_profile_no_profiling]; exact Hprofile).
  rewrite tcb_init_free_common_image_eq__tcb_link_and_publication.
  apply tcb64_storage_merge_next_name_updated__tcb_link_and_publication.
Qed.
Lemma zero_bytes_to_store_ushort__tcb_zero_byte_reconstruction : forall p,
  p mod 2 = 0 ->
  UCharArray.full p 2 [0; 0] |-- p # UShort |-> 0.
Proof.
  intros p Halign.
  unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  unfold store_uchar, store_ushort, store_2byte.
  Intros.
  Exists 0 0.
  entailer!.
  all: try reflexivity.
  all: unfold isvalidptr_short, isvalidptr_char, aligned_2 in *; lia.
Qed.
Lemma repeat_zero_sublist_eq__tcb_zero_byte_reconstruction : forall lo hi n,
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
Lemma zero_bytes_split__tcb_zero_byte_reconstruction : forall p n m,
  0 <= n <= m ->
  UCharArray.full p m (repeat_Z 0 m) |--
    UCharArray.full p n (repeat_Z 0 n) **
    UCharArray.full (p + n) (m - n) (repeat_Z 0 (m - n)).
Proof.
  intros p n m Hrange.
  sep_apply (UCharArray.full_split_to_full p n m (repeat_Z 0 m) Hrange).
  rewrite !repeat_zero_sublist_eq__tcb_zero_byte_reconstruction by lia.
  replace (n - 0) with n by lia.
  change StoreUCharAsElement.sizeA with 1.
  rewrite Z.mul_1_r; entailer!.
Qed.
Lemma zero_bytes_to_store_uint__tcb_zero_byte_reconstruction : forall p,
  p mod 4 = 0 ->
  UCharArray.full p 4 [0; 0; 0; 0] |-- p # UInt |-> 0.
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
  unfold store_uchar.
  Intros.
  Exists 0 0 0 0.
  unfold store_char.
  entailer!.
  all: try reflexivity.
  all: change (0 >= -128); lia.
Qed.
Lemma zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction : forall p,
  p mod 4 = 0 ->
  UCharArray.full p 4 [0; 0; 0; 0] |-- p # Ptr |-> 0.
Proof.
  intros p Halign.
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction p Halign).
  apply kernel_store_uint_store_ptr.
Qed.
Lemma zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction : forall p,
  UCharArray.full p 1 [0] |-- p # UChar |-> 0.
Proof.
  intros p; unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1; replace (p + 0 * 1) with p by lia.
  entailer!.
Qed.
Lemma zero_bytes_to_tcb64_storage__tcb_zero_byte_reconstruction : forall p image,
  p mod 4 = 0 ->
  (forall field, image field = Some 0) ->
  (forall field, tcb_field_address p field = p + tcb_field_offset field) ->
  UCharArray.full p 64 (repeat_Z 0 64) |-- tcb64_storage_rep p image.
Proof.
  intros p image Hmod Hzero Hlayout.
  assert (Hmod2 : p mod 2 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hmod; [|lia].
    destruct Hmod as [k Hk]; exists (2 * k); lia. }
  unfold tcb64_storage_rep, tcb64_fields_rep, tcb_fields.
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite TaskFieldStorage.store_fields_nil.
  rewrite !Hzero.
  unfold tcb_cell; rewrite !Hlayout.
  cbn [tcb_field_offset].
  rewrite UIntArray.full_unfold, UIntArray.seg_empty.
  unfold StoreUIntAsElement.storeA.
  change (sizeof(UINT)) with 4.
  replace (p + 60 + 0 * 4) with (p + 60) by lia.
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction p 4 64); [|lia].
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction p);
    [|exact Hmod].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 4) 4 60); [|lia].
  replace (p + 4 + 4) with (p + 8) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 4));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 8) 4 56); [|lia].
  replace (p + 8 + 4) with (p + 12) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 8));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 12) 4 52); [|lia].
  replace (p + 12 + 4) with (p + 16) by lia.
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction (p + 12));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 16) 2 48); [|lia].
  replace (p + 16 + 2) with (p + 18) by lia.
  sep_apply (zero_bytes_to_store_ushort__tcb_zero_byte_reconstruction (p + 16));
    [|rewrite Z.add_mod, Hmod2 by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 18) 2 46); [|lia].
  replace (p + 18 + 2) with (p + 20) by lia.
  sep_apply (zero_bytes_to_store_ushort__tcb_zero_byte_reconstruction (p + 18));
    [|rewrite Z.add_mod, Hmod2 by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 20) 4 44); [|lia].
  replace (p + 20 + 4) with (p + 24) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 20));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 24) 4 40); [|lia].
  replace (p + 24 + 4) with (p + 28) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 24));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 28) 4 36); [|lia].
  replace (p + 28 + 4) with (p + 32) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 28));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 32) 4 32); [|lia].
  replace (p + 32 + 4) with (p + 36) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 32));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 36) 4 28); [|lia].
  replace (p + 36 + 4) with (p + 40) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 36));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 40) 2 24); [|lia].
  replace (p + 40 + 2) with (p + 42) by lia.
  sep_apply (zero_bytes_to_store_ushort__tcb_zero_byte_reconstruction (p + 40));
    [|rewrite Z.add_mod, Hmod2 by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 42) 1 22); [|lia].
  replace (p + 42 + 1) with (p + 43) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 42)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 43) 1 21); [|lia].
  replace (p + 43 + 1) with (p + 44) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 43)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 44) 4 20); [|lia].
  replace (p + 44 + 4) with (p + 48) by lia.
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction (p + 44));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 48) 1 16); [|lia].
  replace (p + 48 + 1) with (p + 49) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 48)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 49) 1 15); [|lia].
  replace (p + 49 + 1) with (p + 50) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 49)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 50) 1 14); [|lia].
  replace (p + 50 + 1) with (p + 51) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 50)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 51) 1 13); [|lia].
  replace (p + 51 + 1) with (p + 52) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 51)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 52) 1 12); [|lia].
  replace (p + 52 + 1) with (p + 53) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 52)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 53) 1 11); [|lia].
  replace (p + 53 + 1) with (p + 54) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 53)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 54) 1 10); [|lia].
  replace (p + 54 + 1) with (p + 55) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 54)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 55) 1 9); [|lia].
  replace (p + 55 + 1) with (p + 56) by lia.
  sep_apply (zero_bytes_to_store_uchar__tcb_zero_byte_reconstruction (p + 55)).
  sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction (p + 56) 4 8); [|lia].
  replace (p + 56 + 4) with (p + 60) by lia.
  sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction (p + 56));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  sep_apply (zero_bytes_to_store_uint__tcb_zero_byte_reconstruction (p + 60));
    [|rewrite Z.add_mod, Hmod by lia; reflexivity].
  entailer!; rewrite Z.add_0_r; reflexivity.
Qed.
Lemma zero_bytes_to_ptr_array__tcb_zero_byte_reconstruction : forall n p,
  p mod 4 = 0 ->
  UCharArray.full p (4 * Z.of_nat n) (repeat_Z 0 (4 * Z.of_nat n)) |--
  PtrArray.full p (Z.of_nat n) (repeat 0 n).
Proof.
  induction n as [|n IH]; intros p Hmod.
  - change (4 * Z.of_nat 0) with 0.
    change (repeat_Z 0 0) with (@nil Z).
    cbn [repeat Z.of_nat]; rewrite UCharArray.full_empty, PtrArray.full_empty.
    entailer!.
  - change (repeat 0 (S n)) with (0 :: repeat 0 n).
    rewrite PtrArray.full_unfold, PtrArray.seg_0_shift.
    unfold StorePtrAsElement.storeA.
    change (sizeof(PTR)) with 4.
    change ptr_size_Z with 4.
    replace (p + 0 * 4) with p by lia.
    replace (p + 1 * 4) with (p + 4) by lia.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    change (PtrArray.seg (p + 4) 0 (Z.of_nat n) (repeat 0 n))
      with (PtrArray.full (p + 4) (Z.of_nat n) (repeat 0 n)).
    sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction p 4
      (4 * Z.of_nat (S n)) ltac:(lia)).
    replace (4 * Z.of_nat (S n) - 4) with (4 * Z.of_nat n) by lia.
    sep_apply (zero_bytes_to_store_ptr__tcb_zero_byte_reconstruction p Hmod).
    sep_apply (IH (p + 4) ltac:(rewrite Z.add_mod, Hmod by lia; reflexivity)).
    entailer!.
Qed.
Lemma zero_bytes_to_task_free_storage__tcb_zero_byte_reconstruction : forall sg n first,
  init_tcb_list_profile sg -> init_tcb_list_layout sg ->
  0 <= first -> first + Z.of_nat n <= 22 ->
  UCharArray.full (tcb64_addr sg first) (64 * Z.of_nat n)
    (repeat_Z 0 (64 * Z.of_nat n)) |--
  task_free_storage_rep sg (fun _ => Some (init_tcb_list_zero_image sg))
    (Zrange_aux first n).
Proof.
  intros sg n; induction n as [|n IH]; intros first Hprofile Hlayout Hfirst Hend.
  - change (64 * Z.of_nat 0) with 0.
    change (repeat_Z 0 0) with (@nil Z).
    cbn [Zrange_aux task_free_storage_rep].
    rewrite UCharArray.full_empty; entailer!.
  - cbn [Zrange_aux task_free_storage_rep].
    sep_apply (zero_bytes_split__tcb_zero_byte_reconstruction
      (tcb64_addr sg first) 64 (64 * Z.of_nat (S n)) ltac:(lia)).
    replace (64 * Z.of_nat (S n) - 64) with (64 * Z.of_nat n) by lia.
    replace (tcb64_addr sg first + 64) with (tcb64_addr sg (first + 1))
      by (unfold tcb64_addr; lia).
    sep_apply (IH (first + 1) Hprofile Hlayout ltac:(lia) ltac:(lia)).
    Exists (init_tcb_list_zero_image sg).
    entailer!.
    rewrite task_slot_storage_tcb64 by
      (first [apply init_tcb_list_profile_no_multi | apply init_tcb_list_profile_no_profiling]; exact Hprofile).
    apply zero_bytes_to_tcb64_storage__tcb_zero_byte_reconstruction.
    + destruct Hlayout as [_ [_ [_ [Hmod _]]]].
      unfold tcb64_addr; rewrite Z.add_mod, Z.mul_mod, Hmod by lia.
      rewrite Z.mul_0_r; reflexivity.
    + intro field; unfold tcb_layout_common_image.
      apply init_tcb_list_zero_image_all_fields.
    + destruct Hlayout as [_ [_ [_ [_ [_ [_ [_ Hfields]]]]]]].
      intro field; apply Hfields; lia.
Qed.
