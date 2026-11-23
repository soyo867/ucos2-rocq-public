Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import IntLib.
From compcert.lib Require Import Integers.
Local Open Scope Z_scope.

Inductive PendType : Type :=
| PendSem | PendMbox | PendQ | PendMutex | PendFlag | PendMulti.

Inductive PendStatus : Type :=
| PendOK | PendTimeout | PendAbort.

(** The canonical status is the existing machine-byte type.  All 256
    values are representable; source protocol validity is separate.  The
    byte is not duplicated by a mutually exclusive pending-kind record. *)
Definition TaskStatus : Type := Byte.int.

(** OSTCBStat is a byte, not an enumeration of mutually exclusive waits.
    Constants follow uC/OS-II 2.93.01 ucos_ii.h.  In particular PEND_ANY
    excludes MULTI.  These source-level operations also describe transient
    bytes; neither pending bits nor the MULTI marker alone determine ready
    bitmap membership.  Registration/continuation relations own that fact. *)
Definition task_pend_mask (kind : PendType) : Z :=
  match kind with
  | PendSem => 1 | PendMbox => 2 | PendQ => 4
  | PendMutex => 16 | PendFlag => 32 | PendMulti => 128
  end.

Definition task_suspend_mask : Z := 8.
Definition task_pend_any_mask : Z := 55.

Definition encode_pend_type (kind : option PendType) : Z :=
  match kind with Some k => task_pend_mask k | None => 0 end.

Definition encode_task_status (status : TaskStatus) : Z :=
  Byte.unsigned status.

(** A constructor for single-wait initial/legacy states, not a decoder of
    arbitrary status bytes.  Native updates below retain all other bits. *)
Definition task_status_single (kind : option PendType) (suspended : bool) : TaskStatus :=
  Byte.repr (Z.lor (encode_pend_type kind) (if suspended then task_suspend_mask else 0)).

Definition task_status_set_wait (bits : Z) (kind : PendType) : Z :=
  Z.lor bits (task_pend_mask kind).

Definition task_status_set_multi_wait (bits events_mask : Z) : Z :=
  Z.lor bits (Z.lor events_mask (task_pend_mask PendMulti)).

(** [mask] is the INT8U argument of OS_EventTaskRdy.  For a byte mask,
    xor 255 is precisely the source's casted complement. *)
Definition task_status_clear_wait (bits mask : Z) : Z :=
  Z.land bits (Z.lxor mask 255).

Definition task_status_has_pending (bits : Z) : bool :=
  negb (Z.eqb (Z.land bits task_pend_any_mask) 0).

Definition task_status_is_suspended (bits : Z) : bool :=
  negb (Z.eqb (Z.land bits task_suspend_mask) 0).

Definition task_status_is_multi (bits : Z) : bool :=
  negb (Z.eqb (Z.land bits (task_pend_mask PendMulti)) 0).

Definition task_is_suspended (status : TaskStatus) : bool :=
  task_status_is_suspended (encode_task_status status).

(** All bits except SUSPEND, including MULTI and the otherwise unused bit
    6.  This is not OS_STAT_PEND_ANY and never drops residual Multi bits. *)
Definition task_non_suspension_bits (status : TaskStatus) : Z :=
  Z.land (encode_task_status status) 247.

(** Ordinary quiescent/single-wait readiness.  Multi wake/timeout phases
    additionally depend on real registration fields and are modeled at
    Task level, not by treating residual pending bits as zero. *)
Definition is_effectively_ready (status : TaskStatus) (delay : Z) : bool :=
  if Z.eqb (task_non_suspension_bits status) 0
  then negb (task_is_suspended status) && Z.eqb delay 0
  else false.

(** Called only when the actual delay decrement has reached zero.  The
    no-pending branch writes StatPend=OK without writing OSTCBStat. *)
Definition task_status_timeout (bits : Z) : Z * PendStatus :=
  if task_status_has_pending bits
  then (task_status_clear_wait bits task_pend_any_mask, PendTimeout)
  else (bits, PendOK).

Lemma task_pend_mask_in_range : forall kind, 0 < task_pend_mask kind < 256.
Proof. intros []; cbn; lia. Qed.

Lemma encode_task_status_in_range : forall status,
  0 <= encode_task_status status < 256.
Proof.
  intros; apply Byte.unsigned_range.
Qed.

Lemma task_status_set_wait_in_range : forall bits kind,
  0 <= bits < 256 -> 0 <= task_status_set_wait bits kind < 256.
Proof.
  intros bits kind Hbits; unfold task_status_set_wait.
  pose proof (task_pend_mask_in_range kind) as Hmask.
  pose proof (unsigned_Lastnbits_range (Z.lor bits (task_pend_mask kind)) 8
    ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_lor_distr_missing in Hrange by (cbn; lia).
  exact Hrange.
Qed.

Lemma task_status_set_multi_wait_in_range : forall bits events_mask,
  0 <= bits < 256 -> 0 <= events_mask < 8 ->
  0 <= task_status_set_multi_wait bits events_mask < 256.
Proof.
  intros bits events_mask Hbits Hmask.
  pose proof (task_status_set_wait_in_range events_mask PendMulti ltac:(lia)) as Hmulti.
  unfold task_status_set_multi_wait.
  pose proof (unsigned_Lastnbits_range
    (Z.lor bits (Z.lor events_mask (task_pend_mask PendMulti))) 8 ltac:(lia)) as Hrange.
  unfold task_status_set_wait in Hmulti.
  rewrite unsigned_last_nbits_lor_distr_missing in Hrange by (cbn in *; lia).
  exact Hrange.
Qed.

Lemma task_status_clear_wait_in_range : forall bits mask,
  0 <= bits < 256 -> 0 <= task_status_clear_wait bits mask < 256.
Proof.
  intros bits mask Hbits; unfold task_status_clear_wait.
  pose proof (unsigned_Lastnbits_range (Z.land bits (Z.lxor mask 255)) 8
    ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_land_missing_l in Hrange by (cbn; lia).
  exact Hrange.
Qed.

Lemma task_status_clear_wait_byte_complement : forall bits mask,
  0 <= mask < 256 ->
  task_status_clear_wait bits mask =
    Z.land bits (unsigned_last_nbits (Z.lnot mask) 8).
Proof.
  intros bits mask Hmask; unfold task_status_clear_wait.
  f_equal; apply Z.bits_inj'; intros n Hn; rewrite Z.lxor_spec.
  destruct (Z_lt_ge_dec n 8) as [Hlow|Hhigh].
  - rewrite Ztestbits_unsigned_eq by lia; rewrite Z.lnot_spec by lia.
    assert (Hones : Z.testbit 255 n = true).
    { change (Z.testbit (Z.ones 8) n = true); rewrite Z.ones_spec_low by lia; reflexivity. }
    rewrite Hones; destruct (Z.testbit mask n); reflexivity.
  - rewrite Ztestbits_unsigned_high by lia.
    rewrite <- (unsigned_last_nbits_eq mask 8 ltac:(cbn; lia)).
    rewrite Ztestbits_unsigned_high by lia.
    change (xorb false (Z.testbit (unsigned_last_nbits 255 8) n) = false).
    rewrite Ztestbits_unsigned_high by lia; reflexivity.
Qed.

Lemma task_status_clear_pend_any_clears_pending : forall bits,
  task_status_has_pending (task_status_clear_wait bits task_pend_any_mask) = false.
Proof.
  intros; unfold task_status_has_pending, task_status_clear_wait, task_pend_any_mask.
  rewrite <- Z.land_assoc; change (negb (Z.eqb (Z.land bits 0) 0) = false).
  rewrite Z.land_0_r; reflexivity.
Qed.

Lemma task_status_clear_pend_any_preserves_suspension : forall bits,
  task_status_is_suspended (task_status_clear_wait bits task_pend_any_mask) =
    task_status_is_suspended bits.
Proof.
  intros; unfold task_status_is_suspended, task_status_clear_wait,
    task_pend_any_mask, task_suspend_mask; rewrite <- Z.land_assoc; reflexivity.
Qed.

Lemma task_status_clear_pend_any_preserves_multi : forall bits,
  task_status_is_multi (task_status_clear_wait bits task_pend_any_mask) =
    task_status_is_multi bits.
Proof.
  intros; unfold task_status_is_multi, task_status_clear_wait, task_pend_any_mask.
  rewrite <- Z.land_assoc; reflexivity.
Qed.

Lemma task_status_clear_kind_preserves_suspension : forall bits kind,
  task_status_is_suspended (task_status_clear_wait bits (task_pend_mask kind)) =
    task_status_is_suspended bits.
Proof.
  intros bits []; unfold task_status_is_suspended, task_status_clear_wait,
    task_suspend_mask; rewrite <- Z.land_assoc; reflexivity.
Qed.

Lemma task_status_clear_kind_preserves_multi : forall bits kind,
  kind <> PendMulti ->
  task_status_is_multi (task_status_clear_wait bits (task_pend_mask kind)) =
    task_status_is_multi bits.
Proof.
  intros bits [] Hkind; try contradiction;
    unfold task_status_is_multi, task_status_clear_wait;
    rewrite <- Z.land_assoc; reflexivity.
Qed.

Lemma task_status_timeout_in_range : forall bits,
  0 <= bits < 256 -> 0 <= fst (task_status_timeout bits) < 256.
Proof.
  intros bits Hbits; unfold task_status_timeout; destruct task_status_has_pending;
    simpl; [apply task_status_clear_wait_in_range|]; assumption.
Qed.

Lemma task_status_timeout_clears_pending : forall bits,
  task_status_has_pending (fst (task_status_timeout bits)) = false.
Proof.
  intros; unfold task_status_timeout; destruct (task_status_has_pending bits) eqn:Hpending;
    simpl; [apply task_status_clear_pend_any_clears_pending|exact Hpending].
Qed.

Lemma task_status_timeout_preserves_suspension : forall bits,
  task_status_is_suspended (fst (task_status_timeout bits)) = task_status_is_suspended bits.
Proof.
  intros; unfold task_status_timeout; destruct task_status_has_pending; simpl;
    [apply task_status_clear_pend_any_preserves_suspension|reflexivity].
Qed.

Lemma task_status_timeout_preserves_multi : forall bits,
  task_status_is_multi (fst (task_status_timeout bits)) = task_status_is_multi bits.
Proof.
  intros; unfold task_status_timeout; destruct task_status_has_pending; simpl;
    [apply task_status_clear_pend_any_preserves_multi|reflexivity].
Qed.

(** A complete Multi wait byte at registration contains exactly the three
    supported Event kind bits, the marker, and the independent suspension
    bit.  No pending bit is silently thrown away. *)
Definition encode_multi_wait_status (events_mask : Z) (suspended : bool) : Z :=
  task_status_set_multi_wait (if suspended then task_suspend_mask else 0) events_mask.

Lemma encode_multi_wait_status_in_range : forall events_mask suspended,
  0 <= events_mask < 8 -> 0 <= encode_multi_wait_status events_mask suspended < 256.
Proof.
  intros; apply task_status_set_multi_wait_in_range;
    [destruct suspended; unfold task_suspend_mask; lia|assumption].
Qed.

Lemma encode_multi_wait_status_observations : forall events_mask suspended,
  0 <= events_mask < 8 ->
  Z.land (encode_multi_wait_status events_mask suspended) task_pend_any_mask = events_mask /\
  task_status_is_suspended (encode_multi_wait_status events_mask suspended) = suspended /\
  task_status_is_multi (encode_multi_wait_status events_mask suspended) = true.
Proof.
  intros events_mask suspended Hmask.
  assert (events_mask = 0 \/ events_mask = 1 \/ events_mask = 2 \/ events_mask = 3 \/
    events_mask = 4 \/ events_mask = 5 \/ events_mask = 6 \/ events_mask = 7) as Hcases by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst events_mask; destruct suspended;
    repeat split; reflexivity.
Qed.

Lemma task_status_timeout_multi : forall events_mask suspended,
  0 < events_mask < 8 ->
  task_status_timeout (encode_multi_wait_status events_mask suspended) =
    (encode_multi_wait_status 0 suspended, PendTimeout).
Proof.
  intros events_mask suspended Hmask.
  assert (events_mask = 1 \/ events_mask = 2 \/ events_mask = 3 \/
    events_mask = 4 \/ events_mask = 5 \/ events_mask = 6 \/ events_mask = 7) as Hcases by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst events_mask; destruct suspended; reflexivity.
Qed.

(** Concrete distinguishing cases for the source-level scheduling audit.
    A Sem wake leaves Q|MULTI yet passes the suspension test.  Timeout then
    keeps MULTI; timeout on the marker alone takes the no-pending branch. *)
Lemma task_status_sem_wake_leaves_queue_multi :
  task_status_clear_wait (encode_multi_wait_status 5 false) (task_pend_mask PendSem) =
    encode_multi_wait_status 4 false /\
  task_status_is_suspended (encode_multi_wait_status 4 false) = false /\
  task_status_has_pending (encode_multi_wait_status 4 false) = true.
Proof. repeat split; reflexivity. Qed.

Lemma task_status_timeout_multi_marker : forall suspended,
  task_status_timeout (encode_multi_wait_status 0 suspended) =
    (encode_multi_wait_status 0 suspended, PendOK).
Proof. intros []; reflexivity. Qed.

Lemma encode_task_status_repr : forall bits,
  0 <= bits < 256 -> encode_task_status (Byte.repr bits) = bits.
Proof. intros bits Hbits; apply Byte.unsigned_repr; change (0 <= bits <= 255); lia. Qed.

Lemma task_status_single_encoding : forall kind suspended,
  encode_task_status (task_status_single kind suspended) =
    Z.lor (encode_pend_type kind) (if suspended then task_suspend_mask else 0).
Proof. intros [kind|] suspended; [destruct kind|]; destruct suspended; reflexivity. Qed.

Lemma task_status_single_observations : forall kind suspended,
  task_non_suspension_bits (task_status_single kind suspended) = encode_pend_type kind /\
  task_is_suspended (task_status_single kind suspended) = suspended.
Proof. intros [kind|] suspended; [destruct kind|]; destruct suspended; split; reflexivity. Qed.

Lemma task_status_suspension_mask_value : forall bits,
  Z.land bits task_suspend_mask = if task_status_is_suspended bits then task_suspend_mask else 0.
Proof.
  intro bits.
  assert (Hbit : Z.land bits 8 = if Z.testbit bits 3 then 8 else 0).
  { destruct (Z.testbit bits 3) eqn:Hthree.
    - apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec.
      change ((Z.testbit bits n && Z.testbit (2 ^ 3) n)%bool = Z.testbit (2 ^ 3) n).
      rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eqb 3 n) eqn:E;
        [apply Z.eqb_eq in E; subst n; rewrite Hthree|rewrite Bool.andb_false_r]; reflexivity.
    - apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec, Z.bits_0.
      change ((Z.testbit bits n && Z.testbit (2 ^ 3) n)%bool = false).
      rewrite Z.pow2_bits_eqb by lia.
      destruct (Z.eqb 3 n) eqn:E;
        [apply Z.eqb_eq in E; subst n; rewrite Hthree|rewrite Bool.andb_false_r]; reflexivity. }
  unfold task_status_is_suspended, task_suspend_mask; rewrite Hbit.
  destruct (Z.testbit bits 3); reflexivity.
Qed.

Lemma task_status_value_decomposition : forall status,
  encode_task_status status = Z.lor (task_non_suspension_bits status)
    (if task_is_suspended status then task_suspend_mask else 0).
Proof.
  intro status; unfold task_non_suspension_bits, task_is_suspended.
  rewrite <- task_status_suspension_mask_value, <- Z.land_lor_distr_r.
  change (encode_task_status status = Z.land (encode_task_status status) (Z.ones 8)).
  rewrite Z.land_ones by lia; rewrite Z.mod_small by apply encode_task_status_in_range; reflexivity.
Qed.

(** OS_FlagTaskRdy tests the complete status byte after clearing delay.
    Unlike Event wake, it does not test only SUSPEND.  This equality is
    valid for every byte, including residual pending and reserved bits. *)
Lemma is_effectively_ready_zero_delay_eq : forall status,
  is_effectively_ready status 0 = Z.eqb (encode_task_status status) 0.
Proof.
  intro status.
  destruct (is_effectively_ready status 0) eqn:Hready;
    destruct (Z.eqb (encode_task_status status) 0) eqn:Hzero; try reflexivity.
  - exfalso; apply Z.eqb_neq in Hzero; apply Hzero.
    unfold is_effectively_ready in Hready.
    destruct (Z.eqb (task_non_suspension_bits status) 0) eqn:Hpending;
      [|discriminate].
    apply Z.eqb_eq in Hpending.
    apply Bool.andb_true_iff in Hready as [Hsuspended _].
    apply Bool.negb_true_iff in Hsuspended.
    rewrite task_status_value_decomposition, Hpending, Hsuspended; reflexivity.
  - apply Z.eqb_eq in Hzero.
    unfold is_effectively_ready, task_non_suspension_bits,
      task_is_suspended, task_status_is_suspended in Hready.
    rewrite Hzero in Hready; discriminate.
Qed.

(** A single-kind observation is usable only with its equality premise;
    no arbitrary Multi combination is projected to an enum. *)
Lemma task_status_single_of_mask : forall status kind,
  task_non_suspension_bits status = encode_pend_type kind ->
  status = task_status_single kind (task_is_suspended status).
Proof.
  intros status kind Hmask.
  rewrite <- (Byte.repr_unsigned status) at 1.
  unfold task_status_single; f_equal.
  change (encode_task_status status = Z.lor (encode_pend_type kind)
    (if task_is_suspended status then task_suspend_mask else 0)).
  rewrite task_status_value_decomposition, Hmask; reflexivity.
Qed.

Definition task_status_after_timeout (status : TaskStatus) : TaskStatus :=
  Byte.repr (fst (task_status_timeout (encode_task_status status))).

Lemma task_status_after_timeout_encoding : forall status,
  encode_task_status (task_status_after_timeout status) =
    fst (task_status_timeout (encode_task_status status)).
Proof.
  intros; apply encode_task_status_repr, task_status_timeout_in_range, encode_task_status_in_range.
Qed.

Lemma task_status_after_timeout_single_kind : forall status kind,
  task_non_suspension_bits status = task_pend_mask kind -> kind <> PendMulti ->
  task_non_suspension_bits (task_status_after_timeout status) = 0 /\
  snd (task_status_timeout (encode_task_status status)) = PendTimeout.
Proof.
  intros status kind Hmask Hkind.
  rewrite (task_status_single_of_mask status (Some kind) Hmask).
  destruct kind; try contradiction; destruct (task_is_suspended status); split; reflexivity.
Qed.

Lemma task_status_after_timeout_preserves_suspension : forall status,
  task_is_suspended (task_status_after_timeout status) = task_is_suspended status.
Proof.
  intro status; unfold task_is_suspended; rewrite task_status_after_timeout_encoding.
  apply task_status_timeout_preserves_suspension.
Qed.

Lemma task_status_pending_bits_value : forall status,
  Z.land (encode_task_status status) task_pend_any_mask =
    Z.land (task_non_suspension_bits status) task_pend_any_mask.
Proof. intros; unfold task_non_suspension_bits; rewrite <- Z.land_assoc; reflexivity. Qed.

Lemma task_status_after_timeout_no_single_pending : forall status kind,
  kind <> PendMulti ->
  task_non_suspension_bits (task_status_after_timeout status) <> task_pend_mask kind.
Proof.
  intros status kind Hkind Hmask.
  assert (Hclear : task_status_has_pending (encode_task_status (task_status_after_timeout status)) = false).
  { rewrite task_status_after_timeout_encoding; apply task_status_timeout_clears_pending. }
  unfold task_status_has_pending in Hclear.
  rewrite task_status_pending_bits_value, Hmask in Hclear.
  destruct kind; discriminate || contradiction.
Qed.

Definition task_clear_pending_status (status : TaskStatus) (kind : PendType) : TaskStatus :=
  Byte.repr (task_status_clear_wait (encode_task_status status) (task_pend_mask kind)).

Lemma task_clear_pending_status_encoding : forall status kind,
  encode_task_status (task_clear_pending_status status kind) =
    Z.land (encode_task_status status) (Z.lxor (encode_pend_type (Some kind)) 255).
Proof.
  intros; apply encode_task_status_repr, task_status_clear_wait_in_range, encode_task_status_in_range.
Qed.

Lemma task_clear_pending_status_same_kind : forall status kind,
  task_non_suspension_bits status = task_pend_mask kind ->
  task_non_suspension_bits (task_clear_pending_status status kind) = 0.
Proof.
  intros status kind Hmask; rewrite (task_status_single_of_mask status (Some kind) Hmask).
  destruct kind; destruct (task_is_suspended status); reflexivity.
Qed.

Lemma task_clear_pending_status_none : forall status kind,
  task_non_suspension_bits status = 0 -> task_clear_pending_status status kind = status.
Proof.
  intros status kind Hmask; rewrite (task_status_single_of_mask status None Hmask).
  destruct kind; destruct (task_is_suspended status); reflexivity.
Qed.

Lemma task_clear_pending_status_preserves_suspension : forall status kind,
  task_is_suspended (task_clear_pending_status status kind) = task_is_suspended status.
Proof.
  intros; unfold task_is_suspended; rewrite task_clear_pending_status_encoding.
  apply task_status_clear_kind_preserves_suspension.
Qed.

Lemma task_clear_pending_status_not_same_kind : forall status kind,
  task_non_suspension_bits (task_clear_pending_status status kind) <> task_pend_mask kind.
Proof.
  intros status kind Hmask.
  pose proof (f_equal (fun bits => Z.land bits (task_pend_mask kind)) Hmask) as Hbit.
  unfold task_non_suspension_bits in Hbit; rewrite task_clear_pending_status_encoding in Hbit.
  rewrite <- !Z.land_assoc, Z.land_diag in Hbit.
  assert (Hkill : Z.land (Z.lxor (encode_pend_type (Some kind)) 255)
    (Z.land 247 (task_pend_mask kind)) = 0) by (destruct kind; reflexivity).
  rewrite Hkill, Z.land_0_r in Hbit.
  pose proof (task_pend_mask_in_range kind); lia.
Qed.

Lemma task_status_set_wait_non_suspension_nonzero : forall status kind,
  task_non_suspension_bits (Byte.repr (task_status_set_wait (encode_task_status status) kind)) <> 0.
Proof.
  intros status kind Hzero.
  unfold task_non_suspension_bits in Hzero.
  rewrite encode_task_status_repr in Hzero by
    (apply task_status_set_wait_in_range, encode_task_status_in_range).
  pose proof (f_equal (fun bits => Z.land bits (task_pend_mask kind)) Hzero) as Hbit.
  unfold task_status_set_wait in Hbit.
  rewrite <- Z.land_assoc in Hbit.
  assert (Hmask : Z.land 247 (task_pend_mask kind) = task_pend_mask kind) by
    (destruct kind; reflexivity).
  rewrite Hmask, Z.land_lor_distr_l, Z.land_diag, Z.land_0_l in Hbit.
  apply Z.lor_eq_0_iff in Hbit; destruct Hbit as [_ Hnonzero].
  pose proof (task_pend_mask_in_range kind); lia.
Qed.

(** OSTaskSuspend/Resume change only SUSPEND.  In particular Resume does
    not clear the remaining pending bits of a previously woken Multi wait. *)
Definition task_status_suspend (status : TaskStatus) : TaskStatus :=
  Byte.repr (Z.lor (encode_task_status status) task_suspend_mask).

Definition task_status_resume (status : TaskStatus) : TaskStatus :=
  Byte.repr (task_status_clear_wait (encode_task_status status) task_suspend_mask).

Lemma task_status_suspend_encoding : forall status,
  encode_task_status (task_status_suspend status) =
    Z.lor (encode_task_status status) task_suspend_mask.
Proof.
  intro status; apply encode_task_status_repr.
  pose proof (encode_task_status_in_range status) as Hstatus.
  pose proof (unsigned_Lastnbits_range
    (Z.lor (encode_task_status status) task_suspend_mask) 8 ltac:(lia)) as Hrange.
  rewrite unsigned_last_nbits_lor_distr_missing in Hrange by
    (unfold task_suspend_mask; cbn; lia).
  exact Hrange.
Qed.

Lemma task_status_resume_encoding : forall status,
  encode_task_status (task_status_resume status) =
    task_status_clear_wait (encode_task_status status) task_suspend_mask.
Proof.
  intro status; apply encode_task_status_repr, task_status_clear_wait_in_range,
    encode_task_status_in_range.
Qed.

Lemma task_status_suspend_observations : forall status,
  task_non_suspension_bits (task_status_suspend status) = task_non_suspension_bits status /\
  task_is_suspended (task_status_suspend status) = true.
Proof.
  intro status; split.
  - unfold task_non_suspension_bits; rewrite task_status_suspend_encoding, Z.land_lor_distr_l.
    change (Z.lor (Z.land (encode_task_status status) 247) 0 =
      Z.land (encode_task_status status) 247).
    apply Z.lor_0_r.
  - unfold task_is_suspended, task_status_is_suspended.
    rewrite task_status_suspend_encoding, Z.land_lor_distr_l, Z.land_diag.
    rewrite task_status_suspension_mask_value.
    destruct (task_status_is_suspended (encode_task_status status)); reflexivity.
Qed.

Lemma task_status_resume_observations : forall status,
  task_non_suspension_bits (task_status_resume status) = task_non_suspension_bits status /\
  task_is_suspended (task_status_resume status) = false.
Proof.
  intro status; split.
  - unfold task_non_suspension_bits; rewrite task_status_resume_encoding.
    unfold task_status_clear_wait; rewrite <- Z.land_assoc; reflexivity.
  - unfold task_is_suspended, task_status_is_suspended; rewrite task_status_resume_encoding.
    unfold task_status_clear_wait; rewrite <- Z.land_assoc.
    change (negb (Z.eqb (Z.land (encode_task_status status) 0) 0) = false).
    rewrite Z.land_0_r; reflexivity.
Qed.

(** Bit 6 is not assigned by this kernel version.  MULTI is also unused
    when its API is disabled.  This is a source-established protocol fact,
    not a restriction on Byte.int or an extra guard in a raw update. *)
Definition task_status_reserved_bits_clear (multi_enabled : bool) (status : TaskStatus) : Prop :=
  Z.land (encode_task_status status) (if multi_enabled then 64 else 192) = 0.

Lemma task_status_no_pending_reserved_bits_clear : forall multi status,
  task_non_suspension_bits status = 0 -> task_status_reserved_bits_clear multi status.
Proof.
  intros multi status Hnone; rewrite (task_status_single_of_mask status None Hnone).
  destruct multi; destruct (task_is_suspended status); reflexivity.
Qed.

Lemma task_status_no_multi_pending_mask_eq : forall status,
  task_status_reserved_bits_clear false status ->
  task_non_suspension_bits status = Z.land (encode_task_status status) task_pend_any_mask.
Proof.
  intros status Hclear; unfold task_status_reserved_bits_clear in Hclear.
  change (Z.land (encode_task_status status) (Z.lor task_pend_any_mask 192) =
    Z.land (encode_task_status status) task_pend_any_mask).
  rewrite Z.land_lor_distr_r, Hclear, Z.lor_0_r; reflexivity.
Qed.

Lemma task_status_clear_wait_preserves_reserved_bits : forall multi status mask,
  task_status_reserved_bits_clear multi status ->
  task_status_reserved_bits_clear multi
    (Byte.repr (task_status_clear_wait (encode_task_status status) mask)).
Proof.
  intros multi status mask Hclear; unfold task_status_reserved_bits_clear in *.
  rewrite encode_task_status_repr by
    (apply task_status_clear_wait_in_range, encode_task_status_in_range).
  unfold task_status_clear_wait.
  rewrite (Z.land_comm (encode_task_status status) (Z.lxor mask 255)), <- Z.land_assoc,
    Hclear, Z.land_0_r; reflexivity.
Qed.

Lemma task_status_set_wait_preserves_reserved_bits : forall multi status kind,
  task_status_reserved_bits_clear multi status -> (kind <> PendMulti \/ multi = true) ->
  task_status_reserved_bits_clear multi
    (Byte.repr (task_status_set_wait (encode_task_status status) kind)).
Proof.
  intros multi status kind Hclear Hkind.
  assert (Hmask : Z.land (task_pend_mask kind) (if multi then 64 else 192) = 0).
  { destruct multi, kind; try reflexivity; intuition discriminate. }
  unfold task_status_reserved_bits_clear in *.
  rewrite encode_task_status_repr by
    (apply task_status_set_wait_in_range, encode_task_status_in_range).
  unfold task_status_set_wait; rewrite Z.land_lor_distr_l, Hclear, Hmask; reflexivity.
Qed.

Lemma task_status_set_multi_wait_preserves_reserved_bits : forall status mask,
  task_status_reserved_bits_clear true status -> 0 <= mask < 8 ->
  task_status_reserved_bits_clear true
    (Byte.repr (task_status_set_multi_wait (encode_task_status status) mask)).
Proof.
  intros status mask Hclear Hmask; unfold task_status_reserved_bits_clear in *.
  rewrite encode_task_status_repr by
    (apply task_status_set_multi_wait_in_range; [apply encode_task_status_in_range|exact Hmask]).
  unfold task_status_set_multi_wait; rewrite !Z.land_lor_distr_l, Hclear.
  assert (Hcases : mask = 0 \/ mask = 1 \/ mask = 2 \/ mask = 3 \/
    mask = 4 \/ mask = 5 \/ mask = 6 \/ mask = 7) by lia.
  repeat destruct Hcases as [Hcases|Hcases]; subst mask; reflexivity.
Qed.

Lemma task_status_after_timeout_preserves_reserved_bits : forall multi status,
  task_status_reserved_bits_clear multi status ->
  task_status_reserved_bits_clear multi (task_status_after_timeout status).
Proof.
  intros multi status Hclear; unfold task_status_after_timeout, task_status_timeout.
  destruct (task_status_has_pending (encode_task_status status)); cbn [fst].
  - apply task_status_clear_wait_preserves_reserved_bits; exact Hclear.
  - change (task_status_reserved_bits_clear multi (Byte.repr (Byte.unsigned status))).
    rewrite Byte.repr_unsigned; exact Hclear.
Qed.

Lemma task_status_after_timeout_no_multi_pending_bits : forall status,
  task_status_reserved_bits_clear false status ->
  task_non_suspension_bits (task_status_after_timeout status) = 0.
Proof.
  intros status Hclear.
  rewrite task_status_no_multi_pending_mask_eq by
    (apply task_status_after_timeout_preserves_reserved_bits; exact Hclear).
  pose proof (task_status_timeout_clears_pending (encode_task_status status)) as Hpending.
  unfold task_status_has_pending in Hpending.
  apply Bool.negb_false_iff in Hpending; apply Z.eqb_eq in Hpending.
  rewrite task_status_after_timeout_encoding; exact Hpending.
Qed.

Lemma task_status_suspend_preserves_reserved_bits : forall multi status,
  task_status_reserved_bits_clear multi status ->
  task_status_reserved_bits_clear multi (task_status_suspend status).
Proof.
  intros multi status Hclear; unfold task_status_reserved_bits_clear in *.
  rewrite task_status_suspend_encoding, Z.land_lor_distr_l, Hclear.
  destruct multi; reflexivity.
Qed.

Lemma task_status_resume_preserves_reserved_bits : forall multi status,
  task_status_reserved_bits_clear multi status ->
  task_status_reserved_bits_clear multi (task_status_resume status).
Proof. intros; apply task_status_clear_wait_preserves_reserved_bits; assumption. Qed.
