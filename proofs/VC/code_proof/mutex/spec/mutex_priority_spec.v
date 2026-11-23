Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.

Import ListNotations.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are raw observations of the selected three native helpers, not
    public Mutex invariants.  In particular, an alias need not exist. *)
Definition mutex_priority_no_match (table : list Z) (pointer searched : Z) : Prop :=
  forall index, 0 <= index < searched -> Znth index table 0 <> pointer.

Definition mutex_base_priority_prefix
  (table : list Z) (pointer fallback searched result : Z) : Prop :=
  (mutex_priority_no_match table pointer searched /\ result = fallback) \/
  (0 <= result < searched /\ Znth result table 0 = pointer /\
   forall index, 0 <= index < searched -> Znth index table 0 = pointer -> index <= result).

Definition mutex_base_priority_result
  (table : list Z) (pointer fallback result : Z) : Prop :=
  mutex_base_priority_prefix table pointer fallback 64 result.

Definition mutex_effective_priority_result
  (table : list Z) (pointer fallback result : Z) : Prop :=
  (mutex_priority_no_match table pointer 64 /\ result = fallback) \/
  (0 <= result < 64 /\ Znth result table 0 = pointer /\
   forall index, 0 <= index < 64 -> Znth index table 0 = pointer -> result <= index).

Definition mutex_priority_fallback (image : TCBCommonImage) (priority : Z) : Prop :=
  image TCBPrio = Some priority.

(** The unchanged native fields are a structural residual, not an invariant
    or a second layout.  Addresses/cells remain owned by task.v. *)
Definition mutex_priority_unchanged_fields : list TCBField :=
  [TCBStkPtr; TCBExtPtr; TCBStkBottom; TCBStkSize; TCBOpt; TCBId;
   TCBNext; TCBPrev; TCBEventPtr; TCBMsg; TCBFlagNode; TCBFlagsRdy;
   TCBPadding42; TCBPadding43; TCBDly; TCBStat; TCBStatPend;
   TCBDelReq; TCBTaskName; TCBReg0].

Definition mutex_priority_tcb_rest (pointer : Z) (image : TCBCommonImage) : Assertion :=
  tcb64_fields_rep pointer mutex_priority_unchanged_fields image.

Definition mutex_priority_image_fields
  (image : TCBCommonImage) (priority x y bitx bity : Z) : Prop :=
  image TCBPrio = Some priority /\ image TCBX = Some x /\
  image TCBY = Some y /\ image TCBBitX = Some bitx /\ image TCBBitY = Some bity.

Definition mutex_priority_image (image : TCBCommonImage) (priority : Z) : TCBCommonImage :=
  tcb_write
    (tcb_write
      (tcb_write
        (tcb_write
          (tcb_write image TCBPrio (Some priority))
          TCBY (Some (tcb_y_of_prio priority)))
        TCBX (Some (tcb_x_of_prio priority)))
      TCBBitY (Some (tcb_bit_y_of_prio priority)))
    TCBBitX (Some (tcb_bit_x_of_prio priority)).

Definition mutex_priority_was_ready (rows : list Z) (old_y old_bitx : Z) : bool :=
  negb (Z.eqb (Z.land (Znth old_y rows 0) old_bitx) 0).

Definition mutex_priority_cleared_row (rows : list Z) (old_y old_bitx : Z) : Z :=
  Z.land (Znth old_y rows 0) (unsigned_last_nbits (Z.lnot old_bitx) 8).

Definition mutex_priority_removed_rows (rows : list Z) (old_y old_bitx : Z) : list Z :=
  if mutex_priority_was_ready rows old_y old_bitx
  then replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bitx) rows
  else rows.

Definition mutex_priority_removed_group
  (rows : list Z) (group old_y old_bitx old_bity : Z) : Z :=
  if mutex_priority_was_ready rows old_y old_bitx
  then if Z.eqb (mutex_priority_cleared_row rows old_y old_bitx) 0
       then Z.land group (unsigned_last_nbits (Z.lnot old_bity) 8)
       else group
  else group.

Definition mutex_priority_rows
  (rows : list Z) (old_y old_bitx priority : Z) : list Z :=
  if mutex_priority_was_ready rows old_y old_bitx
  then let removed := mutex_priority_removed_rows rows old_y old_bitx in
       replace_Znth (tcb_y_of_prio priority)
         (Z.lor (Znth (tcb_y_of_prio priority) removed 0) (tcb_bit_x_of_prio priority)) removed
  else rows.

Definition mutex_priority_group
  (rows : list Z) (group old_y old_bitx old_bity priority : Z) : Z :=
  if mutex_priority_was_ready rows old_y old_bitx
  then ready_group_after_relocation group
         (mutex_priority_cleared_row rows old_y old_bitx)
         old_bity (tcb_bit_y_of_prio priority)
  else group.

Definition mutex_priority_current (pointer current old_priority priority : Z) : Z :=
  if Z.eq_dec pointer current then priority else old_priority.

(** A case-local interpretation of the five native writes.  Every other
    abstract field, including native fields and generations, is retained. *)
Definition mutex_priority_task (task : TaskAbstractState) (priority : Z) : TaskAbstractState :=
  {| taskID := task.(taskID); taskGeneration := task.(taskGeneration);
     tcbStkPtr := task.(tcbStkPtr);
     tcbExtPtr := task.(tcbExtPtr);
     tcbStkBottom := task.(tcbStkBottom);
     tcbStkSize := task.(tcbStkSize);
     tcbOpt := task.(tcbOpt);
     tcbPublicId := task.(tcbPublicId);
     tcbFlagNode := task.(tcbFlagNode);
     tcbFlagsRdy := task.(tcbFlagsRdy);
     tcbTaskName := task.(tcbTaskName);
     tcbReg0 := task.(tcbReg0);
     tcbCtxSwCtr := task.(tcbCtxSwCtr);
     tcbCyclesTot := task.(tcbCyclesTot);
     tcbCyclesStart := task.(tcbCyclesStart);
     tcbStkBase := task.(tcbStkBase);
     tcbStkUsed := task.(tcbStkUsed);
     tcbPadding42 := task.(tcbPadding42);
     tcbPadding43 := task.(tcbPadding43);
     tcbEventMultiPtr := task.(tcbEventMultiPtr); curPrio := priority;
     stat := task.(stat); statPend := task.(statPend); dly := task.(dly);
     eventPtr := task.(eventPtr); eventMultiWaitEvents := task.(eventMultiWaitEvents);
     eventMultiRdy := task.(eventMultiRdy); msg := task.(msg);
     nextTCB := task.(nextTCB); prevTCB := task.(prevTCB); delReq := task.(delReq) |}.

Lemma mutex_priority_image_task_eq : forall sg task priority,
  mutex_priority_image (task_tcb64_image sg task) priority =
  task_tcb64_image sg (mutex_priority_task task priority).
Proof.
  intros; apply functional_extensionality; intros field; destruct field; reflexivity.
Qed.

Lemma mutex_priority_image_untouched : forall image priority field,
  In field mutex_priority_unchanged_fields ->
  mutex_priority_image image priority field = image field.
Proof.
  intros image priority field Hfield; destruct field; simpl in Hfield;
    try reflexivity; intuition discriminate.
Qed.

Lemma mutex_base_priority_no_alias : forall table pointer fallback,
  mutex_priority_no_match table pointer 64 ->
  mutex_base_priority_result table pointer fallback fallback.
Proof. intros; left; auto. Qed.

Lemma mutex_effective_priority_no_alias : forall table pointer fallback,
  mutex_priority_no_match table pointer 64 ->
  mutex_effective_priority_result table pointer fallback fallback.
Proof. intros; left; auto. Qed.

(** Connect the already source-bound scan contracts to the shared alias
    model. The table observation is the representation-layer obligation;
    a real registered alias excludes the literal no-match fallback. *)
Lemma mutex_base_priority_result_implies_task_base_priority :
  forall sg entries table tid pointer fallback result witness,
  sg.(osLowestPrio) = 63 ->
  (forall p, 0 <= p < 64 ->
     (Znth p entries 0 = pointer <-> table p = PTTask tid)) ->
  task_priority_alias sg table tid witness ->
  mutex_base_priority_result entries pointer fallback result ->
  task_base_priority sg table tid result.
Proof.
  intros sg entries table tid pointer fallback result witness Hlowest Htable
    [Hw Hentry] Hresult.
  unfold task_priority_in_range in Hw.
  destruct Hresult as [[Hnone _]|[Hr [Hhit Hmax]]].
  - exfalso; apply (Hnone witness); [lia|].
    apply (proj2 (Htable witness ltac:(lia))); exact Hentry.
  - split.
    + split; [unfold task_priority_in_range; lia|].
      apply (proj1 (Htable result Hr)); exact Hhit.
    + intros p [Hp Hget]; unfold task_priority_in_range in Hp.
      apply Hmax; [lia|]. apply (proj2 (Htable p ltac:(lia))); exact Hget.
Qed.

Lemma mutex_effective_priority_result_implies_task_effective_priority :
  forall sg entries table tid pointer fallback result witness,
  sg.(osLowestPrio) = 63 ->
  (forall p, 0 <= p < 64 ->
     (Znth p entries 0 = pointer <-> table p = PTTask tid)) ->
  task_priority_alias sg table tid witness ->
  mutex_effective_priority_result entries pointer fallback result ->
  task_effective_priority sg table tid result.
Proof.
  intros sg entries table tid pointer fallback result witness Hlowest Htable
    [Hw Hentry] Hresult.
  unfold task_priority_in_range in Hw.
  destruct Hresult as [[Hnone _]|[Hr [Hhit Hmin]]].
  - exfalso; apply (Hnone witness); [lia|].
    apply (proj2 (Htable witness ltac:(lia))); exact Hentry.
  - split.
    + split; [unfold task_priority_in_range; lia|].
      apply (proj1 (Htable result Hr)); exact Hhit.
    + intros p [Hp Hget]; unfold task_priority_in_range in Hp.
      apply Hmin; [lia|]. apply (proj2 (Htable p ltac:(lia))); exact Hget.
Qed.

Lemma land_seven_eq_mod_eight__priority_encoding : forall value,
  Z.land value 7 = value mod 8.
Proof.
  intro value; change (Z.land value (Z.ones 3) = value mod (2 ^ 3)).
  rewrite Z.land_ones by lia; reflexivity.
Qed.
Lemma priority_coordinates_in_range_and_encoding_eq__priority_encoding :
  forall priority, 0 <= priority < 64 ->
  0 <= tcb_x_of_prio priority < 8 /\
  0 <= tcb_y_of_prio priority < 8 /\
  Z.land priority 7 = tcb_x_of_prio priority /\
  Z.land (Z.shiftr priority 3) 7 = tcb_y_of_prio priority.
Proof.
  intros priority Hp; unfold tcb_x_of_prio, tcb_y_of_prio.
  assert (Hx : 0 <= priority mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hy : 0 <= priority / 8 < 8).
  { split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia. }
  repeat split; try lia.
  - apply land_seven_eq_mod_eight__priority_encoding.
  - rewrite land_seven_eq_mod_eight__priority_encoding,
      Z.shiftr_div_pow2 by lia.
    change ((priority / 8) mod 8 = priority / 8).
    apply Z.mod_small; exact Hy.
Qed.
Lemma shift_one_unsigned_byte_eq__priority_encoding :
  forall coordinate, 0 <= coordinate < 8 ->
  unsigned_last_nbits (Z.shiftl 1 coordinate) 8 = Z.shiftl 1 coordinate.
Proof.
  intros coordinate Hc; apply unsigned_last_nbits_eq.
  rewrite Z.shiftl_1_l.
  split; [apply Z.pow_nonneg; lia|].
  apply Z.pow_lt_mono_r; lia.
Qed.
Lemma uchar_array_rep_implies_forall_byte_range__priority_encoding :
  forall rows base lo hi,
  store_array_rec StoreUCharAsElement.storeA base lo hi rows |--
  “ Forall (fun value => 0 <= value < 256) rows ”.
Proof.
  induction rows as [|value rows IH]; intros base lo hi.
  - cbn [store_array_rec]; entailer!; constructor.
  - cbn [store_array_rec].
    prop_apply (IH base (lo + 1) hi).
    unfold StoreUCharAsElement.storeA at 1.
    prop_apply store_uchar_range.
    entailer!; constructor; try assumption.
    match goal with Hrange : 0 <= value <= _ |- _ =>
      change (0 <= value <= 255) in Hrange; lia
    end.
Qed.
Lemma byte_land_in_range__ready_bitmap_stages : forall value mask,
  0 <= value < 256 -> 0 <= Z.land value mask < 256.
Proof.
  intros value mask Hvalue.
  rewrite <- (unsigned_last_nbits_land_missing_l value mask 8) by lia.
  pose proof (unsigned_Lastnbits_range (Z.land value mask) 8 ltac:(lia)).
  exact H.
Qed.
Lemma byte_land_mask_eq__ready_bitmap_stages : forall value mask,
  0 <= value < 256 ->
  Z.land value mask = Z.land value (unsigned_last_nbits mask 8).
Proof.
  intros value mask Hvalue.
  pose proof (unsigned_last_nbits_land_clear_r value mask 8 ltac:(lia)) as Hclear.
  rewrite (unsigned_last_nbits_eq value 8) in Hclear by exact Hvalue.
  symmetry; exact Hclear.
Qed.
Lemma byte_unsigned_eq__ready_bitmap_stages : forall value,
  0 <= value < 256 -> unsigned_last_nbits value 8 = value.
Proof. intros; apply unsigned_last_nbits_eq; exact H. Qed.
Lemma single_bit_in_byte_range__ready_bitmap_stages : forall index,
  0 <= index < 8 -> 0 <= Z.shiftl 1 index < 256.
Proof.
  intros index Hindex; rewrite Z.shiftl_1_l.
  split.
  - apply Z.lt_le_incl, Z.pow_pos_nonneg; lia.
  - change (2 ^ index < 2 ^ 8); apply Z.pow_lt_mono_r; lia.
Qed.
Lemma mutex_priority_cleared_row_in_range__ready_bitmap_stages :
  forall rows old_y old_bitx,
  0 <= Znth old_y rows 0 < 256 ->
  0 <= mutex_priority_cleared_row rows old_y old_bitx < 256.
Proof.
  intros; unfold mutex_priority_cleared_row.
  apply byte_land_in_range__ready_bitmap_stages; assumption.
Qed.
Lemma mutex_priority_removed_rows_in_range__ready_bitmap_stages :
  forall rows old_y old_bitx index,
  Zlength rows = 8 -> 0 <= old_y < 8 ->
  (forall i, 0 <= i < 8 -> 0 <= Znth i rows 0 < 256) ->
  0 <= index < 8 ->
  0 <= Znth index (mutex_priority_removed_rows rows old_y old_bitx) 0 < 256.
Proof.
  intros rows old_y old_bitx index Hlength Hold Hrows Hindex.
  unfold mutex_priority_removed_rows.
  destruct (mutex_priority_was_ready rows old_y old_bitx).
  - destruct (Z.eq_dec old_y index) as [Heq | Hneq].
    + subst index; rewrite Znth_replace_Znth_Same by lia.
      apply mutex_priority_cleared_row_in_range__ready_bitmap_stages, Hrows; assumption.
    + rewrite Znth_replace_Znth_Diff by lia; apply Hrows; assumption.
  - apply Hrows; assumption.
Qed.
Lemma mutex_priority_removed_group_in_range__ready_bitmap_stages :
  forall rows group old_y old_bitx old_bity,
  0 <= group < 256 ->
  0 <= mutex_priority_removed_group rows group old_y old_bitx old_bity < 256.
Proof.
  intros rows group old_y old_bitx old_bity Hgroup.
  unfold mutex_priority_removed_group.
  destruct (mutex_priority_was_ready rows old_y old_bitx); [|assumption].
  destruct (Z.eqb (mutex_priority_cleared_row rows old_y old_bitx) 0); [|assumption].
  apply byte_land_in_range__ready_bitmap_stages; assumption.
Qed.

Lemma mutex_priority_reordered_fields : forall base image,
  tcb64_fields_rep base
    (TCBBitY :: TCBBitX :: TCBY :: TCBX :: TCBPrio ::
      mutex_priority_unchanged_fields) image =
  tcb64_storage_rep base image.
Proof.
  intros; unfold tcb64_storage_rep, tcb64_fields_rep,
    TaskFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intro field.
  destruct field; simpl; repeat (destruct in_dec; simpl); reflexivity.
Qed.

Lemma mutex_priority_reordered_nodup :
  NoDup (TCBBitY :: TCBBitX :: TCBY :: TCBX :: TCBPrio ::
    mutex_priority_unchanged_fields).
Proof.
  unfold mutex_priority_unchanged_fields.
  repeat (apply NoDup_cons; [simpl; intuition discriminate|]).
  apply NoDup_nil.
Qed.

Lemma mutex_priority_rest_updated : forall base image prio,
  mutex_priority_tcb_rest base (mutex_priority_image image prio) =
  mutex_priority_tcb_rest base image.
Proof.
  intros; unfold mutex_priority_tcb_rest, mutex_priority_image.
  repeat rewrite tcb64_fields_rep_off_field by
    (unfold mutex_priority_unchanged_fields; simpl; intuition discriminate).
  reflexivity.
Qed.
