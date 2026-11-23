Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.kernel_resources.

Import UCOS2_C_Rules ListNotations.
Import KernelHeapStorage KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskStkInit, pinned ARM-Cortex-A/ARMv7-A/os_cpu_c.c:389--442.
    The selected GNU ABI is 32-bit, little-endian, descending OS_STK words.
    No VFP link variant is silently selected: these are the three actual
    OS_CPU_ARM_DRegCntGet implementations, not three runtime option guards.
    Each source binding must choose the variant supplied by its linked code.
    In particular the executable initializer ignores [opt], contrary to
    its older comment about optional short floating-point frames. *)
Inductive TaskStackVFP : Type :=
| TaskStackNoVFP
| TaskStackVFPD16
| TaskStackVFPD32.

Definition task_stack_init_dreg_count (variant : TaskStackVFP) : nat :=
  match variant with TaskStackNoVFP => 0 | TaskStackVFPD16 => 16 | TaskStackVFPD32 => 32 end.

Definition task_stack_init_word_count (variant : TaskStackVFP) : Z :=
  match variant with TaskStackNoVFP => 16 | TaskStackVFPD16 => 50 | TaskStackVFPD32 => 82 end.

Definition task_stack_init_frame_bytes (variant : TaskStackVFP) : Z :=
  4 * task_stack_init_word_count variant.

Lemma task_stack_init_dreg_count_cases : forall variant,
  task_stack_init_dreg_count variant = 0%nat \/
  task_stack_init_dreg_count variant = 16%nat \/ task_stack_init_dreg_count variant = 32%nat.
Proof. intros []; simpl; auto. Qed.

Lemma task_stack_init_fpu_loop_count_in_range : forall variant,
  (2 * task_stack_init_dreg_count variant <= 64)%nat /\
  (2 * task_stack_init_dreg_count variant < 256)%nat.
Proof. intros []; simpl; lia. Qed.

Lemma task_stack_init_word_count_positive : forall variant,
  0 < task_stack_init_word_count variant.
Proof. intros []; simpl; lia. Qed.

Lemma task_stack_init_frame_bytes_cases :
  task_stack_init_frame_bytes TaskStackNoVFP = 64 /\
  task_stack_init_frame_bytes TaskStackVFPD16 = 200 /\
  task_stack_init_frame_bytes TaskStackVFPD32 = 328.
Proof. repeat split; reflexivity. Qed.

(** Integer observations of the two explicit unsigned-word masks. *)
Definition task_stack_init_entry_pc (entry : addr) : Z := (entry / 2) * 2.
Definition task_stack_init_aligned_top (top : addr) : addr := ((top + 4) / 8) * 8.

Lemma task_stack_init_clear_low_bits : forall word bits,
  0 <= word < 4294967296 -> 0 <= bits ->
  Z.land word (Z.land (Z.ones 32) (Z.lnot (Z.ones bits))) =
    (word / 2 ^ bits) * 2 ^ bits.
Proof.
  intros word bits Hword Hbits.
  rewrite Z.land_assoc, Z.land_ones by lia.
  replace (2 ^ 32) with 4294967296 by reflexivity.
  rewrite Z.mod_small by exact Hword.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma task_stack_init_entry_pc_source_mask : forall entry,
  0 <= entry < 4294967296 ->
  task_stack_init_entry_pc entry = Z.land entry 4294967294.
Proof.
  intros entry Hentry.
  replace 4294967294 with (Z.land (Z.ones 32) (Z.lnot (Z.ones 1))) by reflexivity.
  rewrite task_stack_init_clear_low_bits by lia; reflexivity.
Qed.

Lemma task_stack_init_aligned_top_source_mask : forall top,
  0 <= top + 4 < 4294967296 ->
  task_stack_init_aligned_top top = Z.land (top + 4) 4294967288.
Proof.
  intros top Htop.
  replace 4294967288 with (Z.land (Z.ones 32) (Z.lnot (Z.ones 3))) by reflexivity.
  rewrite task_stack_init_clear_low_bits by lia; reflexivity.
Qed.

Lemma task_stack_init_entry_pc_in_range : forall entry,
  0 <= entry < 4294967296 -> 0 <= task_stack_init_entry_pc entry < 4294967296.
Proof.
  intros entry Hentry; unfold task_stack_init_entry_pc.
  pose proof (Z.div_mod entry 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound entry 2 ltac:(lia)) as Hmod.
  assert (Hq : 0 <= entry / 2) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma task_stack_init_entry_pc_even : forall entry,
  task_stack_init_entry_pc entry mod 2 = 0.
Proof. intros; unfold task_stack_init_entry_pc; apply Z.mod_mul; lia. Qed.

Definition task_stack_init_cpsr (entry : addr) : Z :=
  if Z.eqb (Z.land entry 1) 1 then 51 else 19.

Lemma task_stack_init_cpsr_arm : forall entry,
  entry mod 2 = 0 -> task_stack_init_cpsr entry = 19.
Proof.
  intros entry H; unfold task_stack_init_cpsr.
  replace 1 with (Z.ones 1) at 1 by reflexivity.
  rewrite Z.land_ones by lia; change ((if Z.eqb (entry mod 2) 1 then 51 else 19) = 19).
  rewrite H; reflexivity.
Qed.

Lemma task_stack_init_cpsr_thumb : forall entry,
  entry mod 2 = 1 -> task_stack_init_cpsr entry = 51.
Proof.
  intros entry H; unfold task_stack_init_cpsr.
  replace 1 with (Z.ones 1) at 1 by reflexivity.
  rewrite Z.land_ones by lia; change ((if Z.eqb (entry mod 2) 1 then 51 else 19) = 51).
  rewrite H; reflexivity.
Qed.

Lemma task_stack_init_cpsr_in_range : forall entry,
  0 <= task_stack_init_cpsr entry < 4294967296.
Proof. intros; unfold task_stack_init_cpsr; destruct Z.eqb; lia. Qed.

(** Source order: PC, LR, R12..R1, R0, CPSR.  The repeated bytes below are
    respectively 0x12, 0x11, 0x10, 0x09, ..., 0x01.  LR stores the actual
    OS_TaskReturn function address, including its interworking bit. *)
Definition task_stack_init_core_push_words (entry argument task_return : addr) : list Z :=
  [task_stack_init_entry_pc entry; task_return;
   303174162; 286331153; 269488144; 151587081; 134744072; 117901063;
   101058054; 84215045; 67372036; 50529027; 33686018; 16843009;
   argument; task_stack_init_cpsr entry].

(** The FPU-count call occurs AFTER all sixteen core stores.  With a linked
    FP variant: FPSCR=0, 2*d zero words, then FPEXC=0x40000000. *)
Definition task_stack_init_fpu_push_words (variant : TaskStackVFP) : list Z :=
  match variant with
  | TaskStackNoVFP => []
  | _ => [0] ++ repeat 0 (2 * task_stack_init_dreg_count variant) ++ [1073741824]
  end.

Definition task_stack_init_push_words (variant : TaskStackVFP)
  (entry argument task_return : addr) (_options : Z) : list Z :=
  task_stack_init_core_push_words entry argument task_return ++ task_stack_init_fpu_push_words variant.

Definition task_stack_init_frame_words (variant : TaskStackVFP)
  (entry argument task_return : addr) (options : Z) : list Z :=
  rev (task_stack_init_push_words variant entry argument task_return options).

Lemma task_stack_init_options_ignored : forall variant entry argument task_return first second,
  task_stack_init_push_words variant entry argument task_return first =
    task_stack_init_push_words variant entry argument task_return second /\
  task_stack_init_frame_words variant entry argument task_return first =
    task_stack_init_frame_words variant entry argument task_return second.
Proof. intros; split; reflexivity. Qed.

Lemma task_stack_init_push_words_length : forall variant entry argument task_return options,
  Zlength (task_stack_init_push_words variant entry argument task_return options) =
    task_stack_init_word_count variant.
Proof. intros [] entry argument task_return options; reflexivity. Qed.

Lemma task_stack_init_frame_words_length : forall variant entry argument task_return options,
  Zlength (task_stack_init_frame_words variant entry argument task_return options) =
    task_stack_init_word_count variant.
Proof.
  intros; unfold task_stack_init_frame_words; rewrite !Zlength_correct, length_rev.
  rewrite <- Zlength_correct.
  apply task_stack_init_push_words_length.
Qed.

Lemma task_stack_init_frame_words_source_order : forall variant entry argument task_return options,
  rev (task_stack_init_frame_words variant entry argument task_return options) =
    task_stack_init_push_words variant entry argument task_return options.
Proof. intros; apply rev_involutive. Qed.

Lemma task_stack_init_frame_words_decompose : forall variant entry argument task_return options,
  task_stack_init_frame_words variant entry argument task_return options =
    rev (task_stack_init_fpu_push_words variant) ++
    rev (task_stack_init_core_push_words entry argument task_return).
Proof. intros; apply rev_app_distr. Qed.

Lemma task_stack_init_no_vfp_frame_words : forall entry argument task_return options,
  task_stack_init_frame_words TaskStackNoVFP entry argument task_return options =
    [task_stack_init_cpsr entry; argument;
     16843009; 33686018; 50529027; 67372036; 84215045; 101058054;
     117901063; 134744072; 151587081; 269488144; 286331153; 303174162;
     task_return; task_stack_init_entry_pc entry].
Proof. reflexivity. Qed.

Lemma task_stack_init_frame_words_nth : forall variant entry argument task_return options index,
  (index < List.length (task_stack_init_push_words variant entry argument task_return options))%nat ->
  nth index (task_stack_init_frame_words variant entry argument task_return options) 0 =
    nth (List.length (task_stack_init_push_words variant entry argument task_return options) - S index)
      (task_stack_init_push_words variant entry argument task_return options) 0.
Proof. intros; apply rev_nth; assumption. Qed.

Lemma task_stack_init_core_words_in_range : forall entry argument task_return,
  0 <= entry < 4294967296 -> 0 <= argument < 4294967296 -> 0 <= task_return < 4294967296 ->
  Forall (fun word => 0 <= word < 4294967296)
    (task_stack_init_core_push_words entry argument task_return).
Proof.
  intros entry argument task_return Hentry Hargument Hreturn.
  pose proof (task_stack_init_entry_pc_in_range entry Hentry) as Hpc.
  pose proof (task_stack_init_cpsr_in_range entry) as Hcpsr.
  unfold task_stack_init_core_push_words; repeat constructor; lia.
Qed.

Lemma task_stack_init_frame_words_in_range : forall variant entry argument task_return options,
  0 <= entry < 4294967296 -> 0 <= argument < 4294967296 -> 0 <= task_return < 4294967296 ->
  Forall (fun word => 0 <= word < 4294967296)
    (task_stack_init_frame_words variant entry argument task_return options).
Proof.
  intros variant entry argument task_return options Hentry Hargument Hreturn.
  unfold task_stack_init_frame_words; apply Forall_rev.
  unfold task_stack_init_push_words; apply Forall_app; split.
  - apply task_stack_init_core_words_in_range; assumption.
  - destruct variant; cbn [task_stack_init_fpu_push_words task_stack_init_dreg_count repeat app];
      repeat constructor; lia.
Qed.

Definition task_stack_init_sp (variant : TaskStackVFP) (top : addr) : addr :=
  task_stack_init_aligned_top top - task_stack_init_frame_bytes variant.

Definition task_stack_init_push_address (top : addr) (index : Z) : addr :=
  task_stack_init_aligned_top top - 4 * (index + 1).

Lemma task_stack_init_aligned_top_bounds : forall top,
  0 <= top + 4 ->
  0 <= task_stack_init_aligned_top top <= top + 4 /\
  top + 4 < task_stack_init_aligned_top top + 8.
Proof.
  intros top Htop; unfold task_stack_init_aligned_top.
  pose proof (Z.div_mod (top + 4) 8 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (top + 4) 8 ltac:(lia)) as Hmod.
  assert (Hq : 0 <= (top + 4) / 8) by (apply Z.div_pos; lia).
  lia.
Qed.

Lemma task_stack_init_sp_aligned : forall variant top,
  task_stack_init_sp variant top mod 8 = 0.
Proof.
  intros; unfold task_stack_init_sp; rewrite Zminus_mod.
  unfold task_stack_init_aligned_top; rewrite Z.mod_mul by lia.
  destruct variant; reflexivity.
Qed.

Lemma task_stack_init_frame_upper_address : forall variant top,
  task_stack_init_sp variant top + task_stack_init_word_count variant * sizeof(UINT) =
    task_stack_init_aligned_top top.
Proof. intros; unfold task_stack_init_sp, task_stack_init_frame_bytes; rewrite sizeof_uint; lia. Qed.

Lemma task_stack_init_push_address_in_frame : forall variant top index,
  0 <= index < task_stack_init_word_count variant ->
  task_stack_init_sp variant top <= task_stack_init_push_address top index /\
  task_stack_init_push_address top index + 4 <= task_stack_init_aligned_top top.
Proof.
  intros; unfold task_stack_init_sp, task_stack_init_frame_bytes, task_stack_init_push_address; lia.
Qed.

Lemma task_stack_init_push_address_reversed_index : forall variant top index,
  task_stack_init_push_address top index = task_stack_init_sp variant top +
    4 * (task_stack_init_word_count variant - 1 - index).
Proof.
  intros; unfold task_stack_init_sp, task_stack_init_frame_bytes, task_stack_init_push_address; lia.
Qed.

(** A buffer descriptor can supply this geometry without adding fields to
    the kernel state.  [first] is a word offset of the frame in that buffer;
    it is not a new runtime check.  The final source pointer ptos+1 remains
    representable, and rounding it down may leave one upper word untouched. *)
Definition task_stack_init_buffer_geometry (variant : TaskStackVFP)
  (base size top first : Z) : Prop :=
  0 <= base /\ base mod 4 = 0 /\ 0 < size /\ base + 4 * size < 4294967296 /\
  top = base + 4 * (size - 1) /\
  0 <= first /\ first + task_stack_init_word_count variant <= size /\
  task_stack_init_sp variant top = base + first * sizeof(UINT).

Lemma task_stack_init_geometry_sp_in_buffer : forall variant base size top first,
  task_stack_init_buffer_geometry variant base size top first ->
  base <= task_stack_init_sp variant top /\
  task_stack_init_sp variant top + task_stack_init_frame_bytes variant <= base + 4 * size.
Proof.
  intros variant base size top first Hgeometry.
  unfold task_stack_init_buffer_geometry in Hgeometry; rewrite sizeof_uint in Hgeometry.
  unfold task_stack_init_frame_bytes; destruct Hgeometry as [_ [_ [_ [_ [_ [Hfirst [Hend Hsp]]]]]]].
  rewrite Hsp; lia.
Qed.

Definition task_stack_init_frame_rep (variant : TaskStackVFP)
  (top entry argument task_return : addr) (options : Z) : Assertion :=
  UIntArray.mixed_full (task_stack_init_sp variant top) (task_stack_init_word_count variant)
    (map (@Some Z) (task_stack_init_frame_words variant entry argument task_return options)).

(** The unchanged lower/upper arrays remain genuine spatial resources.
    None in an old word means unspecified ownership, not an initialized zero.
    These are source-boundary pre/post assertions, NOT a proved Hoare triple
    for the ARM port.  In particular no lemma below turns the old frame into
    the initialized frame without consuming its actual written ownership. *)
Definition task_stack_init_pre (variant : TaskStackVFP)
  (base size top entry argument task_return : Z)
  (lower old_frame upper : list (option Z)) : Assertion :=
  coq_prop (task_stack_init_buffer_geometry variant base size top (Zlength lower) /\
    Zlength old_frame = task_stack_init_word_count variant /\
    size = Zlength lower + task_stack_init_word_count variant + Zlength upper /\
    0 <= entry < 4294967296 /\ 0 <= argument < 4294967296 /\ 0 <= task_return < 4294967296) &&
  (UIntArray.mixed_full base (Zlength lower) lower **
   UIntArray.mixed_full (task_stack_init_sp variant top) (task_stack_init_word_count variant) old_frame **
   UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper).

Definition task_stack_init_post (variant : TaskStackVFP)
  (base top entry argument task_return : addr) (options : Z)
  (lower upper : list (option Z)) (returned_sp : addr) : Assertion :=
  coq_prop (returned_sp = task_stack_init_sp variant top) &&
  (UIntArray.mixed_full base (Zlength lower) lower **
   task_stack_init_frame_rep variant top entry argument task_return options **
   UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper).

Lemma task_stack_init_regions_merge : forall variant base top lower frame upper,
  task_stack_init_sp variant top = base + Zlength lower * sizeof(UINT) ->
  UIntArray.mixed_full base (Zlength lower) lower **
    UIntArray.mixed_full (task_stack_init_sp variant top) (task_stack_init_word_count variant) frame **
    UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper |--
  UIntArray.mixed_full base (Zlength lower + task_stack_init_word_count variant + Zlength upper)
    (lower ++ frame ++ upper).
Proof.
  intros variant base top lower frame upper Hsp.
  pose proof (task_stack_init_word_count_positive variant) as Hcount.
  pose proof (Zlength_nonneg lower) as Hlower.
  pose proof (Zlength_nonneg upper) as Hupper.
  pose proof (UIntArray.mixed_full_merge_to_mixed_full (task_stack_init_sp variant top)
    (task_stack_init_word_count variant) (task_stack_init_word_count variant + Zlength upper)
    frame upper ltac:(lia)) as Hframe_merge.
  replace (task_stack_init_word_count variant + Zlength upper - task_stack_init_word_count variant)
    with (Zlength upper) in Hframe_merge by lia.
  rewrite task_stack_init_frame_upper_address in Hframe_merge.
  sep_apply_l_atomic Hframe_merge.
  rewrite Hsp.
  pose proof (UIntArray.mixed_full_merge_to_mixed_full base (Zlength lower)
    (Zlength lower + task_stack_init_word_count variant + Zlength upper)
    lower (frame ++ upper) ltac:(lia)) as Hwhole_merge.
  replace (Zlength lower + task_stack_init_word_count variant + Zlength upper - Zlength lower)
    with (task_stack_init_word_count variant + Zlength upper) in Hwhole_merge by lia.
  sep_apply_l_atomic Hwhole_merge; entailer!.
Qed.

Lemma task_stack_init_post_merge_buffer : forall variant base top entry argument task_return options
  lower upper returned_sp,
  task_stack_init_sp variant top = base + Zlength lower * sizeof(UINT) ->
  task_stack_init_post variant base top entry argument task_return options lower upper returned_sp |--
  coq_prop (returned_sp = task_stack_init_sp variant top) &&
  UIntArray.mixed_full base (Zlength lower + task_stack_init_word_count variant + Zlength upper)
    (lower ++ map (@Some Z) (task_stack_init_frame_words variant entry argument task_return options) ++ upper).
Proof.
  intros; unfold task_stack_init_post, task_stack_init_frame_rep; Intros.
  sep_apply_l_atomic (task_stack_init_regions_merge variant base top lower
    (map (@Some Z) (task_stack_init_frame_words variant entry argument task_return options)) upper H).
  entailer!.
Qed.

(** Successful publication must transfer this new frame before the task can
    run.  A later Create error 66 returns the modified stack ownership, not
    its pre-initialization bytes.  The creator/lease/TCB generation transfer
    belongs to the caller model; no such lifetime permission is manufactured
    by this frame description.  Entry code validity, argument ownership
    required by that task, OS_TaskReturn behavior and context restoration
    also remain separate from these memory-layout assertions. *)

(** The actual descending C stores. Each four-byte list below is one
    typed OS_STK write, not four separately interruptible C statements.
    [cursor] is the aligned one-past pointer before predecrement. *)
Fixpoint task_stack_push_writes (cursor : Z) (words : list Z)
  : list (Mem.addr * Mem.byte) :=
  match words with
  | [] => []
  | word :: rest => pointer_store_writes (cursor - 4) word ++
      task_stack_push_writes (cursor - 4) rest
  end.

Lemma task_stack_uint_store_execution : forall address value (frame : Assertion) before,
  0 <= value < 4294967296 -> (address # UInt |->_ ** frame) before ->
  exists after, kernel_heap_execution (pointer_store_writes address value) before after /\
    (address # UInt |-> value ** frame) after.
Proof.
  intros address value frame before Hvalue Hbefore.
  assert (Hsplit : address # UInt |->_ ** frame |-- address # Ptr |->_ ** frame).
  { apply derivable1_sepcon_mono;
      [exact (proj1 (kernel_undef_store_uint_ptr_equiv address))|reflexivity]. }
  destruct (framed_pointer_store_execution address value frame before Hvalue
    (Hsplit before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : address # Ptr |-> value ** frame |-- address # UInt |-> value ** frame).
  { apply derivable1_sepcon_mono;
      [exact (store_ptr_store_uint address value eq_refl eq_refl)|reflexivity]. }
  exact (Hmerge after Hafter).
Qed.

Lemma task_stack_undef_single_cell : forall address,
  UIntArray.undef_full address 1 |-- address # UInt |->_ .
Proof.
  intros; unfold UIntArray.undef_full, store_undef_array.
  change (store_undef_array_rec StoreUIntAsElement.undefstoreA address 0 1 1 |--
    address # UInt |->_).
  cbn [store_undef_array_rec]; Intros.
  unfold StoreUIntAsElement.undefstoreA.
  replace (address + 0 * sizeof(UINT)) with address by lia; entailer!.
Qed.

Lemma task_stack_cell_mixed_single : forall address value,
  address # UInt |-> value |-- UIntArray.mixed_full address 1 [Some value].
Proof.
  intros; unfold UIntArray.mixed_full, store_array; cbn [store_array_rec].
  unfold UIntArray.mixedstoreA, StoreUIntAsElement.storeA.
  replace (address + 0 * sizeof(UINT)) with address by lia; entailer!.
Qed.

Lemma task_stack_push_store_execution : forall words cursor (frame : Assertion) before,
  Forall (fun value => 0 <= value < 4294967296) words ->
  (UIntArray.undef_full (cursor - 4 * Zlength words) (Zlength words) ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_push_writes cursor words) before after /\
    (UIntArray.mixed_full (cursor - 4 * Zlength words) (Zlength words)
      (map (@Some Z) (rev words)) ** frame) after.
Proof.
  induction words as [|word rest IH]; intros cursor frame before Hranges Hbefore.
  - exists before; split; [split; [constructor|split; reflexivity]|].
    assert (Hempty : UIntArray.undef_full (cursor - 4 * Zlength (@nil Z)) (Zlength (@nil Z)) ** frame |--
      UIntArray.mixed_full (cursor - 4 * Zlength (@nil Z)) (Zlength (@nil Z))
        (map (@Some Z) (rev [])) ** frame).
    { change (UIntArray.undef_full (cursor - 0) 0 ** frame |--
        UIntArray.mixed_full (cursor - 0) 0 [] ** frame).
      rewrite UIntArray.undef_full_empty, UIntArray.mixed_full_empty; entailer!. }
    exact (Hempty before Hbefore).
  - inversion Hranges as [|word0 rest0 Hword Hrest]; subst.
    pose proof (Zlength_nonneg rest) as Hnonneg.
    rewrite Zlength_cons in *.
    assert (Hsplit : UIntArray.undef_full (cursor - 4 * (Zlength rest + 1))
        (Zlength rest + 1) ** frame |--
      (cursor - 4) # UInt |->_ **
      (UIntArray.undef_full (cursor - 4 - 4 * Zlength rest) (Zlength rest) ** frame)).
    { sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full
        (cursor - 4 * (Zlength rest + 1)) (Zlength rest) (Zlength rest + 1) ltac:(lia)).
      replace (Zlength rest + 1 - Zlength rest) with 1 by lia.
      rewrite sizeof_uint.
      replace (cursor - 4 * (Zlength rest + 1) + Zlength rest * 4)
        with (cursor - 4) by ring.
      replace (cursor - 4 * (Zlength rest + 1))
        with (cursor - 4 - 4 * Zlength rest) by ring.
      sep_apply_l_atomic (task_stack_undef_single_cell (cursor - 4)); entailer!. }
    destruct (task_stack_uint_store_execution (cursor - 4) word
      (UIntArray.undef_full (cursor - 4 - 4 * Zlength rest) (Zlength rest) ** frame)
      before Hword (Hsplit before Hbefore)) as [middle [Hhead Hmiddle]].
    assert (Hreorder : (cursor - 4) # UInt |-> word **
      (UIntArray.undef_full (cursor - 4 - 4 * Zlength rest) (Zlength rest) ** frame) |--
      UIntArray.undef_full (cursor - 4 - 4 * Zlength rest) (Zlength rest) **
      ((cursor - 4) # UInt |-> word ** frame)) by entailer!.
    destruct (IH (cursor - 4) ((cursor - 4) # UInt |-> word ** frame)
      middle Hrest (Hreorder middle Hmiddle)) as [after [Htail Hafter]].
    exists after; split.
    + cbn [task_stack_push_writes]; eapply heap_execution_append; eassumption.
    + assert (Hmerge : UIntArray.mixed_full (cursor - 4 - 4 * Zlength rest)
        (Zlength rest) (map (@Some Z) (rev rest)) **
        ((cursor - 4) # UInt |-> word ** frame) |--
        UIntArray.mixed_full (cursor - 4 * (Zlength rest + 1)) (Zlength rest + 1)
          (map (@Some Z) (rev (word :: rest))) ** frame).
      { sep_apply_l_atomic (task_stack_cell_mixed_single (cursor - 4) word).
        pose proof (UIntArray.mixed_full_merge_to_mixed_full
          (cursor - 4 - 4 * Zlength rest) (Zlength rest) (Zlength rest + 1)
          (map (@Some Z) (rev rest)) [Some word] ltac:(lia)) as Hjoin.
        rewrite sizeof_uint in Hjoin.
        replace (Zlength rest + 1 - Zlength rest) with 1 in Hjoin by lia.
        replace (cursor - 4 - 4 * Zlength rest + Zlength rest * 4)
          with (cursor - 4) in Hjoin by ring.
        sep_apply_l_atomic Hjoin.
        cbn [rev]; rewrite map_app; cbn [map].
        replace (cursor - 4 * (Zlength rest + 1))
          with (cursor - 4 - 4 * Zlength rest) by ring; entailer!. }
      exact (Hmerge after Hafter).
Qed.

(** Heap projection of the selected NoVFP body. The following count call
    is the linked assembly MOV R0,#0; BX LR, so it performs no additional
    stack writes and the C floating-point branch is not entered. This is
    the local instruction branch; arbitrary intervening IRQ/callback
    execution still requires its own same-heap frame transport. *)
Definition task_stack_init_no_vfp_writes (top entry argument task_return : Z) :=
  task_stack_push_writes (task_stack_init_aligned_top top)
    (task_stack_init_core_push_words entry argument task_return).

Lemma task_stack_init_no_vfp_store_execution :
  forall base size top entry argument task_return options lower old_frame upper
    (frame : Assertion) before,
  (task_stack_init_pre TaskStackNoVFP base size top entry argument task_return
    lower old_frame upper ** frame) before ->
  exists after,
    kernel_heap_execution (task_stack_init_no_vfp_writes top entry argument task_return)
      before after /\
    (task_stack_init_post TaskStackNoVFP base top entry argument task_return options
      lower upper (task_stack_init_sp TaskStackNoVFP top) ** frame) after.
Proof.
  intros base size top entry argument task_return options lower old_frame upper frame before Hbefore.
  assert (Hextract : task_stack_init_pre TaskStackNoVFP base size top entry argument task_return
      lower old_frame upper ** frame |--
    coq_prop (0 <= entry < 4294967296 /\ 0 <= argument < 4294967296 /\
      0 <= task_return < 4294967296) &&
    (UIntArray.undef_full (task_stack_init_sp TaskStackNoVFP top) 16 **
     (UIntArray.mixed_full base (Zlength lower) lower **
      UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame))).
  { unfold task_stack_init_pre; Intros.
    sep_apply_l_atomic (UIntArray.mixed_full_to_undef_full
      (task_stack_init_sp TaskStackNoVFP top) 16 old_frame); entailer!. }
  destruct (Hextract before Hbefore) as [[Hentry [Harg Hreturn]] Howned].
  assert (Hlength : Zlength (task_stack_init_core_push_words entry argument task_return) = 16)
    by reflexivity.
  assert (Hinput :
    (UIntArray.undef_full
      (task_stack_init_aligned_top top -
        4 * Zlength (task_stack_init_core_push_words entry argument task_return))
      (Zlength (task_stack_init_core_push_words entry argument task_return)) **
     (UIntArray.mixed_full base (Zlength lower) lower **
      UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame)) before).
  { rewrite Hlength; exact Howned. }
  destruct (task_stack_push_store_execution
    (task_stack_init_core_push_words entry argument task_return)
    (task_stack_init_aligned_top top) _ before
    (task_stack_init_core_words_in_range entry argument task_return Hentry Harg Hreturn)
    Hinput) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  rewrite Hlength in Hafter.
  assert (Hmerge : UIntArray.mixed_full (task_stack_init_aligned_top top - 4 * 16) 16
      (map (@Some Z) (rev (task_stack_init_core_push_words entry argument task_return))) **
      (UIntArray.mixed_full base (Zlength lower) lower **
       UIntArray.mixed_full (task_stack_init_aligned_top top) (Zlength upper) upper ** frame) |--
    task_stack_init_post TaskStackNoVFP base top entry argument task_return options
      lower upper (task_stack_init_sp TaskStackNoVFP top) ** frame).
  { unfold task_stack_init_post, task_stack_init_frame_rep, task_stack_init_frame_words,
      task_stack_init_push_words, task_stack_init_fpu_push_words.
    rewrite app_nil_r; entailer!. }
  exact (Hmerge after Hafter).
Qed.
