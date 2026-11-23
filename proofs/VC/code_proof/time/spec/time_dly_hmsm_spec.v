Require Export Ucos2Verify.VC.code.time.spec.time_dly_spec.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.micromega.Lia.
Require Import AUXLib.int_auto.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic StateRelHoare safeexec_lib.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are precisely the four public C parameter domains. The smaller
    minute/second/millisecond bounds are established only by the C guards. *)
Definition time_dly_hmsm_input_ranges (hours minutes seconds ms : Z) : Prop :=
  0 <= hours <= 255 /\ 0 <= minutes <= 255 /\
  0 <= seconds <= 255 /\ 0 <= ms <= 65535.

Definition time_dly_hmsm_error (hours minutes seconds ms : Z)
  (before : UCOS2_Verify_State) : Z :=
  if 0 <? os_sched_ints before then 85 else
  if 0 <? os_sched_locks before then 50 else
  if ((hours =? 0) && (minutes =? 0) && (seconds =? 0) && (ms =? 0))%bool then 84 else
  if 59 <? minutes then 81 else
  if 59 <? seconds then 82 else
  if 999 <? ms then 83 else 0.

(** The shared unsigned transformer owns every wrap. The None arm is
    unreachable at the fixed nonzero rate; no API error is assigned to it. *)
Definition time_dly_hmsm_ticks (hours minutes seconds ms : Z) : Z :=
  match time_hmsm_ticks 100 hours minutes seconds ms with
  | Some ticks => ticks
  | None => 0
  end.

Lemma time_dly_hmsm_ticks_shared : forall hours minutes seconds ms,
  time_hmsm_ticks 100 hours minutes seconds ms =
    Some (time_dly_hmsm_ticks hours minutes seconds ms).
Proof. intros; unfold time_dly_hmsm_ticks, time_hmsm_ticks; reflexivity. Qed.

Lemma time_dly_hmsm_ticks_unsigned_range : forall hours minutes seconds ms,
  0 <= time_dly_hmsm_ticks hours minutes seconds ms < 4294967296.
Proof. intros; eapply time_hmsm_ticks_in_range; apply time_dly_hmsm_ticks_shared. Qed.

Lemma time_dly_hmsm_intermediate_ranges : forall hours minutes seconds ms,
  0 <= hours <= 255 -> 0 <= minutes <= 59 ->
  0 <= seconds <= 59 -> 0 <= ms <= 999 ->
  0 <= hours * 3600 <= 918000 /\
  0 <= minutes * 60 <= 3540 /\
  0 <= hours * 3600 + minutes * 60 <= 921540 /\
  0 <= hours * 3600 + minutes * 60 + seconds <= 921599 /\
  0 <= (hours * 3600 + minutes * 60 + seconds) * 100 <= 92159900 /\
  5 <= ms + 5 <= 1004 /\
  500 <= 100 * (ms + 5) <= 100400 /\
  0 <= 100 * (ms + 5) / 1000 <= 100 /\
  0 <= (hours * 3600 + minutes * 60 + seconds) * 100 +
    100 * (ms + 5) / 1000 <= 92160000.
Proof.
  intros hours minutes seconds ms Hh Hm Hs Hms.
  assert (Hfraction : 0 <= 100 * (ms + 5) / 1000 <= 100).
  { split; [apply Z.div_pos; lia|].
    assert (100 * (ms + 5) / 1000 < 101) by (apply Z.div_lt_upper_bound; lia); lia. }
  repeat split; lia.
Qed.

Lemma time_dly_hmsm_ticks_at_100 : forall hours minutes seconds ms,
  0 <= hours <= 255 -> 0 <= minutes <= 59 ->
  0 <= seconds <= 59 -> 0 <= ms <= 999 ->
  time_dly_hmsm_ticks hours minutes seconds ms =
    (hours * 3600 + minutes * 60 + seconds) * 100 + 100 * (ms + 5) / 1000.
Proof.
  intros hours minutes seconds ms Hh Hm Hs Hms.
  pose proof (time_dly_hmsm_intermediate_ranges hours minutes seconds ms Hh Hm Hs Hms).
  unfold time_dly_hmsm_ticks, time_hmsm_ticks.
  change (match Some (kernel_u32
    (kernel_u32 (kernel_u32
      (kernel_u32 (kernel_u32 (hours * 3600) + kernel_u32 (minutes * 60)) + seconds) * 100) +
      kernel_u32 (100 * kernel_u32 (ms + 5)) / 1000)) with
    | Some ticks => ticks | None => 0 end =
    (hours * 3600 + minutes * 60 + seconds) * 100 + 100 * (ms + 5) / 1000).
  rewrite (kernel_u32_identity (hours * 3600)) by lia.
  rewrite (kernel_u32_identity (minutes * 60)) by lia.
  rewrite (kernel_u32_identity (hours * 3600 + minutes * 60)) by lia.
  rewrite (kernel_u32_identity (hours * 3600 + minutes * 60 + seconds)) by lia.
  rewrite (kernel_u32_identity ((hours * 3600 + minutes * 60 + seconds) * 100)) by lia.
  rewrite (kernel_u32_identity (ms + 5)) by lia.
  rewrite (kernel_u32_identity (100 * (ms + 5))) by lia.
  rewrite kernel_u32_identity by lia.
  reflexivity.
Qed.

Lemma time_dly_hmsm_fraction_at_100 : forall ms,
  0 <= ms -> 100 * (ms + 5) / 1000 = (ms + 5) / 10.
Proof.
  intros ms Hms.
  pose proof (Z.div_mod (ms + 5) 10 ltac:(lia)) as Hdivide.
  pose proof (Z.mod_pos_bound (ms + 5) 10 ltac:(lia)) as Hmod.
  symmetry; apply Z.div_unique with (r := 100 * ((ms + 5) mod 10)); nia.
Qed.

Lemma time_dly_hmsm_ticks_at_100_in_range : forall hours minutes seconds ms,
  0 <= hours <= 255 -> 0 <= minutes <= 59 ->
  0 <= seconds <= 59 -> 0 <= ms <= 999 ->
  0 <= time_dly_hmsm_ticks hours minutes seconds ms <= 92160000.
Proof.
  intros; rewrite time_dly_hmsm_ticks_at_100 by assumption.
  pose proof (time_dly_hmsm_intermediate_ranges hours minutes seconds ms H H0 H1 H2); tauto.
Qed.

Lemma time_dly_hmsm_ticks_zero_iff : forall hours minutes seconds ms,
  0 <= hours <= 255 -> 0 <= minutes <= 59 ->
  0 <= seconds <= 59 -> 0 <= ms <= 999 ->
  (hours <> 0 \/ minutes <> 0 \/ seconds <> 0 \/ ms <> 0) ->
  (time_dly_hmsm_ticks hours minutes seconds ms = 0 <->
    hours = 0 /\ minutes = 0 /\ seconds = 0 /\ 1 <= ms <= 4).
Proof.
  intros hours minutes seconds ms Hh Hm Hs Hms Hnonzero.
  rewrite time_dly_hmsm_ticks_at_100 by assumption.
  rewrite time_dly_hmsm_fraction_at_100 by lia.
  pose proof (Z.div_pos (ms + 5) 10 ltac:(lia) ltac:(lia)) as Hq.
  pose proof (Z.div_mod (ms + 5) 10 ltac:(lia)) as Hdivide.
  pose proof (Z.mod_pos_bound (ms + 5) 10 ltac:(lia)) as Hmod.
  split.
  - intros Hzero; assert (hours = 0 /\ minutes = 0 /\ seconds = 0) by lia.
    destruct H as [-> [-> ->]]; repeat split; lia.
  - intros [-> [-> [-> Hsmall]]]; rewrite Z.div_small by lia; reflexivity.
Qed.

(** The exact canonical C expression uses truncating division and a final
    UInt observation. The preceding bounds justify both conversions. *)
Lemma time_dly_hmsm_c_ticks : forall hours minutes seconds ms,
  0 <= hours <= 255 -> 0 <= minutes <= 59 ->
  0 <= seconds <= 59 -> 0 <= ms <= 999 ->
  unsigned_last_nbits ((hours * 3600 + minutes * 60 + seconds) * 100 +
    (100 * (ms + (500 ÷ 100))) ÷ 1000) 32 = time_dly_hmsm_ticks hours minutes seconds ms.
Proof.
  intros hours minutes seconds ms Hh Hm Hs Hms.
  replace (500 ÷ 100) with 5 by reflexivity.
  rewrite zdiv_equiv by lia.
  pose proof (time_dly_hmsm_intermediate_ranges hours minutes seconds ms Hh Hm Hs Hms).
  rewrite unsigned_last_nbits_eq by
    (change (0 <= (hours * 3600 + minutes * 60 + seconds) * 100 +
       100 * (ms + 5) / 1000 < 4294967296); lia).
  symmetry; apply time_dly_hmsm_ticks_at_100; assumption.
Qed.

Definition time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (StateRelBasic.get' (fun state => state)) (fun before =>
    let code := time_dly_hmsm_error hours minutes seconds ms before in
    if code =? 0 then
      StateRelMonad.bind
        (time_dly_program environment critical sg caller mask
          (time_dly_hmsm_ticks hours minutes seconds ms))
        (fun _ => StateRelMonad.ret 0)
    else StateRelMonad.ret code).

Definition time_dly_hmsm_safe environment critical sg caller mask hours minutes seconds ms before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms) X.

Definition time_dly_hmsm_return_safe result current
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret result) X.

Definition time_dly_hmsm_delay_post (X : Z -> UCOS2_Verify_State -> Prop)
  (_ : unit) (current : UCOS2_Verify_State) : Prop := X 0 current.

Definition time_dly_hmsm_result environment critical sg caller mask hours minutes seconds ms
  before result returned current : Prop :=
  let code := time_dly_hmsm_error hours minutes seconds ms before in
  if code =? 0 then result = 0 /\
    time_dly_result environment critical sg caller mask
      (time_dly_hmsm_ticks hours minutes seconds ms) before returned current
  else result = code /\ returned = caller /\ current = before.

(** Admission is explicit and only belongs to the source path that calls
    OSTimeDly. Its existing noop guard exempts rounded-zero calls from the
    positive-delay Task/stack/completed-call/Scheduler protocol. *)
Definition time_dly_hmsm_entry_facts environment critical sg caller mask hours minutes seconds ms before : Prop :=
  time_dly_hmsm_input_ranges hours minutes seconds ms /\
  (time_dly_hmsm_error hours minutes seconds ms before = 0 ->
    time_dly_entry_facts environment critical sg caller mask
      (time_dly_hmsm_ticks hours minutes seconds ms) before).

Definition time_dly_hmsm_call_pre environment critical saved_local sg caller mask hours minutes seconds ms
  before (frame : Assertion) : Assertion :=
  coq_prop (time_dly_hmsm_entry_facts environment critical sg caller mask hours minutes seconds ms before) &&
    (task_suspend_closed environment critical saved_local sg caller mask before ** frame).

Definition time_dly_hmsm_call_post environment critical saved_local sg caller mask hours minutes seconds ms
  before result (frame : Assertion) (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (time_dly_hmsm_result environment critical sg caller mask hours minutes seconds ms
      before result returned current /\
      time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms before result current /\
      time_dly_hmsm_return_safe result current X) &&
    (task_suspend_closed environment critical saved_local sg returned mask current ** frame).

Lemma time_dly_hmsm_error_program : forall environment critical sg caller mask hours minutes seconds ms before code,
  time_dly_hmsm_error hours minutes seconds ms before = code -> code <> 0 ->
  time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms before code before.
Proof.
  intros; unfold time_dly_hmsm_program; exists before, before; split; [split; reflexivity|].
  rewrite H, (proj2 (Z.eqb_neq _ _) H0); split; reflexivity.
Qed.

Lemma time_dly_hmsm_delay_program : forall environment critical sg caller mask hours minutes seconds ms before current,
  time_dly_hmsm_error hours minutes seconds ms before = 0 ->
  time_dly_program environment critical sg caller mask
    (time_dly_hmsm_ticks hours minutes seconds ms) before tt current ->
  time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms before 0 current.
Proof.
  intros; unfold time_dly_hmsm_program; exists before, before; split; [split; reflexivity|].
  rewrite H; exists tt, current; split; [exact H0|split; reflexivity].
Qed.

Lemma time_dly_hmsm_result_program : forall environment critical sg caller mask hours minutes seconds ms
  before result returned current,
  time_dly_hmsm_result environment critical sg caller mask hours minutes seconds ms before result returned current ->
  time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms before result current.
Proof.
  intros; unfold time_dly_hmsm_result in H.
  destruct (time_dly_hmsm_error hours minutes seconds ms before =? 0) eqn:Hcode.
  - apply Z.eqb_eq in Hcode; destruct H as [-> Hresult].
    apply time_dly_hmsm_delay_program; [exact Hcode|].
    eapply time_dly_result_program; exact Hresult.
  - apply Z.eqb_neq in Hcode; destruct H as [-> [-> ->]].
    apply time_dly_hmsm_error_program; [reflexivity|exact Hcode].
Qed.

Lemma time_dly_hmsm_delay_safe : forall environment critical sg caller mask hours minutes seconds ms before X,
  time_dly_hmsm_error hours minutes seconds ms before = 0 ->
  time_dly_hmsm_safe environment critical sg caller mask hours minutes seconds ms before X ->
  time_dly_safe environment critical sg caller mask
    (time_dly_hmsm_ticks hours minutes seconds ms) before (time_dly_hmsm_delay_post X).
Proof.
  intros environment critical sg caller mask hours minutes seconds ms before X Hcode Hsafe.
  destruct Hsafe as [initial [-> Hsafe]].
  exists before; split; [reflexivity|].
  change (forall result current,
    time_dly_program environment critical sg caller mask
      (time_dly_hmsm_ticks hours minutes seconds ms) before result current -> X 0 current).
  intros [] current Hstep.
  eapply wp_spec; [apply time_dly_hmsm_delay_program; eassumption|exact Hsafe].
Qed.

Lemma time_dly_hmsm_delay_return_safe : forall current X,
  time_dly_return_safe current (time_dly_hmsm_delay_post X) ->
  time_dly_hmsm_return_safe 0 current X.
Proof.
  intros current X Hsafe.
  apply safeExec_ret in Hsafe; destruct Hsafe as [initial [-> Hsafe]].
  exists current; split; [reflexivity|].
  change (forall result final, result = 0 /\ current = final -> X result final).
  intros result final [-> <-]; exact Hsafe.
Qed.

Lemma time_dly_hmsm_error_call_post : forall environment critical saved_local sg caller mask hours minutes seconds ms
  before code frame X,
  time_dly_hmsm_error hours minutes seconds ms before = code -> code <> 0 ->
  time_dly_hmsm_safe environment critical sg caller mask hours minutes seconds ms before X ->
  task_suspend_closed environment critical saved_local sg caller mask before ** frame |--
  time_dly_hmsm_call_post environment critical saved_local sg caller mask hours minutes seconds ms before code frame X.
Proof.
  intros environment critical saved_local sg caller mask hours minutes seconds ms before code frame X Hcode Hnonzero Hsafe.
  assert (Hreturn : time_dly_hmsm_return_safe code before X).
  { eapply (highstependret_derive
      (time_dly_hmsm_program environment critical sg caller mask hours minutes seconds ms)
      (fun state => state = before) code (fun _ state => state = before)).
    - intros state ->; exists before; split; [apply time_dly_hmsm_error_program; eassumption|reflexivity].
    - exact Hsafe. }
  assert (Hresult : time_dly_hmsm_result environment critical sg caller mask hours minutes seconds ms
    before code caller before).
  { unfold time_dly_hmsm_result; rewrite Hcode, (proj2 (Z.eqb_neq _ _) Hnonzero); auto. }
  pose proof (time_dly_hmsm_result_program environment critical sg caller mask hours minutes seconds ms
    before code caller before Hresult) as Hprogram.
  unfold time_dly_hmsm_call_post; Exists caller before; entailer!.
Qed.

Lemma time_dly_hmsm_delay_call_post : forall environment critical saved_local sg caller mask hours minutes seconds ms
  before frame X,
  time_dly_hmsm_error hours minutes seconds ms before = 0 ->
  time_dly_call_post environment critical saved_local sg caller mask
    (time_dly_hmsm_ticks hours minutes seconds ms) before frame (time_dly_hmsm_delay_post X) |--
  time_dly_hmsm_call_post environment critical saved_local sg caller mask hours minutes seconds ms before 0 frame X.
Proof.
  intros; unfold time_dly_call_post at 1; Intros returned current.
  assert (Hreturn : time_dly_hmsm_return_safe 0 current X).
  { apply time_dly_hmsm_delay_return_safe; tauto. }
  assert (Hresult : time_dly_hmsm_result environment critical sg caller mask hours minutes seconds ms
    before 0 returned current).
  { unfold time_dly_hmsm_result; rewrite H; split; [reflexivity|tauto]. }
  pose proof (time_dly_hmsm_result_program environment critical sg caller mask hours minutes seconds ms
    before 0 returned current Hresult) as Hprogram.
  unfold time_dly_hmsm_call_post; Exists returned current; entailer!.
Qed.

Lemma time_dly_hmsm_zero_ticks_entry_facts : forall environment critical sg caller mask hours minutes seconds ms before,
  time_dly_hmsm_input_ranges hours minutes seconds ms ->
  time_dly_hmsm_ticks hours minutes seconds ms = 0 ->
  time_dly_hmsm_entry_facts environment critical sg caller mask hours minutes seconds ms before.
Proof.
  intros; split; [assumption|]. intros _; unfold time_dly_entry_facts; rewrite H0.
  split; [lia|]. rewrite time_dly_noop_zero; discriminate.
Qed.

Lemma time_dly_hmsm_error_entry_facts : forall environment critical sg caller mask hours minutes seconds ms before,
  time_dly_hmsm_input_ranges hours minutes seconds ms ->
  time_dly_hmsm_error hours minutes seconds ms before <> 0 ->
  time_dly_hmsm_entry_facts environment critical sg caller mask hours minutes seconds ms before.
Proof. intros; split; [assumption|]; intros Hcode; contradiction. Qed.
