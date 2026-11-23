Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Export Ucos2Verify.VC.code.timer.spec.tmr_alloc_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Export Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.error_codes.
Require Import Coq.Strings.String.
From MonadLib Require Export Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Import Monad MonadNotation.
Local Open Scope sac_scope.
Local Open Scope Z_scope.

(** OSTmrCreate source composition. Raw callers retain the initialized private
    image across the actual Unlock. Configured callers transfer name bytes
    when needed and publish before Unlock; the later return permits the
    scheduler's real interference. Both modes use the same arbitrary QCP
    safeExec postcondition, exact C output pair and actual returned resources. *)
Definition tmr_create_argument_error (delay period option : Z) : Datatypes.option OSErrCode :=
  if option =? 2 then
    if period =? 0 then Some OS_ERR_TMR_INVALID_PERIOD else None
  else if option =? 1 then
    if delay =? 0 then Some OS_ERR_TMR_INVALID_DLY else None
  else Some OS_ERR_TMR_INVALID_OPT.

Definition tmr_create_early_error (delay period option nesting : Z) : Datatypes.option OSErrCode :=
  match tmr_create_argument_error delay period option with
  | Some error => Some error
  | None => if 0 <? nesting then Some OS_ERR_TMR_ISR else None
  end.

Definition tmr_create_name (default_name pname : addr) : addr :=
  if pname =? 0 then default_name else pname.

Lemma tmr_create_argument_error_periodic : forall delay period,
  tmr_create_argument_error delay period 2 =
    if period =? 0 then Some OS_ERR_TMR_INVALID_PERIOD else None.
Proof. reflexivity. Qed.

Lemma tmr_create_argument_error_one_shot : forall delay period,
  tmr_create_argument_error delay period 1 =
    if delay =? 0 then Some OS_ERR_TMR_INVALID_DLY else None.
Proof. reflexivity. Qed.

Lemma tmr_create_argument_error_invalid : forall delay period option,
  option <> 1 -> option <> 2 ->
  tmr_create_argument_error delay period option = Some OS_ERR_TMR_INVALID_OPT.
Proof.
  intros; unfold tmr_create_argument_error.
  rewrite (proj2 (Z.eqb_neq option 2) H0), (proj2 (Z.eqb_neq option 1) H); reflexivity.
Qed.

(** The name plan is a caller resource choice.  Raw names are only stored;
    the other two choices publish a complete public Timer before Unlock.
    A source registration moves already-owned bytes into the unique Name
    owner.  Its source/lifetime identity is retained by nameSources. *)
Inductive TmrCreateNamePlan : Type :=
| TmrCreateRawName
| TmrCreateRegisteredName (chars : list Z)
| TmrCreateOwnedName (key : nat) (source : NameStorageSource)
    (bytes : addr -> option Z) (chars : list Z).

Definition tmr_create_source_map (source : NameStorageSource)
  (bytes : addr -> option Z) : addr -> option Z :=
  fun p => if in_dec Z.eq_dec p source.(nameStorageDomain) then bytes p else None.

Definition tmr_create_source_rep (source : NameStorageSource)
  (bytes : addr -> option Z) : Assertion :=
  store_map name_byte_rep (tmr_create_source_map source bytes).

Definition tmr_create_name_storage (plan : TmrCreateNamePlan) : Assertion :=
  match plan with
  | TmrCreateOwnedName _ source bytes _ => tmr_create_source_rep source bytes
  | _ => emp
  end.

Definition tmr_create_name_state (plan : TmrCreateNamePlan)
  (names : NameResourceState) : NameResourceState :=
  match plan with
  | TmrCreateOwnedName key source bytes _ => name_register_source names key source bytes
  | _ => names
  end.

Definition tmr_create_source_string (source : NameStorageSource)
  (bytes : addr -> option Z) (name : addr) (chars : list Z) : Prop :=
  Forall (fun c => 0 < c < 256) chars /\
  (forall i c, nth_error chars i = Some c ->
     In (name + Z.of_nat i) source.(nameStorageDomain) /\
     bytes (name + Z.of_nat i) = Some c) /\
  In (name + Z.of_nat (List.length chars)) source.(nameStorageDomain) /\
  bytes (name + Z.of_nat (List.length chars)) = Some 0.

Definition tmr_create_name_condition (plan : TmrCreateNamePlan)
  (names : NameResourceState) (name : addr) : Prop :=
  match plan with
  | TmrCreateRawName => True
  | TmrCreateRegisteredName chars => readable_name names name chars
  | TmrCreateOwnedName key source bytes chars =>
      names.(nameSources) key = None /\ name_source_bytes_valid source bytes /\
      name_source_disjoint names source /\
      tmr_create_source_string source bytes name chars
  end.

Definition tmr_create_is_public (plan : TmrCreateNamePlan) : bool :=
  match plan with TmrCreateRawName => false | _ => true end.

Lemma tmr_create_registered_source_readable : forall names key source bytes name chars,
  tmr_create_source_string source bytes name chars ->
  readable_name (name_register_source names key source bytes) name chars.
Proof.
  intros names key source bytes name chars [Hchars [Hbytes [Hnul Hzero]]].
  unfold readable_name; split; [exact Hchars|]; split.
  - intros i c Hi; destruct (Hbytes i c Hi) as [Hin Hb].
    unfold name_register_source; cbn.
    destruct (in_dec Z.eq_dec (name + Z.of_nat i) (nameStorageDomain source));
      [exact Hb|contradiction].
  - unfold name_register_source; cbn.
    destruct (in_dec Z.eq_dec (name + Z.of_nat (List.length chars))
      (nameStorageDomain source)); [exact Hzero|contradiction].
Qed.

Lemma tmr_create_registered_source_preserves_readable : forall names key source bytes name chars,
  name_source_disjoint names source -> readable_name names name chars ->
  readable_name (name_register_source names key source bytes) name chars.
Proof.
  intros names key source bytes name chars Hdis [Hchars [Hbytes Hnul]].
  unfold readable_name; split; [exact Hchars|]; split.
  - intros i c Hi; specialize (Hbytes i c Hi).
    unfold name_register_source; cbn.
    destruct (in_dec Z.eq_dec (name + Z.of_nat i) (nameStorageDomain source));
      [rewrite Hdis in Hbytes by assumption; discriminate|exact Hbytes].
  - unfold name_register_source; cbn.
    destruct (in_dec Z.eq_dec (name + Z.of_nat (List.length chars))
      (nameStorageDomain source));
      [rewrite Hdis in Hnul by assumption; discriminate|exact Hnul].
Qed.

Lemma tmr_create_name_plan_readable : forall plan names name,
  tmr_create_is_public plan = true -> tmr_create_name_condition plan names name ->
  exists chars, readable_name (tmr_create_name_state plan names) name chars.
Proof.
  intros plan names name Hpublic Hcondition; destruct plan; cbn in *; try discriminate.
  - exists chars; exact Hcondition.
  - exists chars; apply tmr_create_registered_source_readable; tauto.
Qed.

Lemma tmr_create_name_plan_preserves_validity : forall sg before plan name,
  UCOS2_state_inv sg before -> tmr_create_name_condition plan before.(NameState) name ->
  UCOS2_state_inv sg (replace_NameS (tmr_create_name_state plan before.(NameState)) before).
Proof.
  intros sg before plan name Hv Hcondition; destruct plan; cbn in *.
  - rewrite replace_NameS_put_back; exact Hv.
  - rewrite replace_NameS_put_back; exact Hv.
  - destruct Hcondition as [Hfresh [Hbytes [Hdis Hstring]]].
    assert (Hnames : valid_name_resources
      (name_register_source before.(NameState) key source bytes)).
    { apply name_register_source_preserves_resources; try assumption.
      unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hv; tauto. }
    assert (Hroots : kernel_names_valid sg
      (replace_NameS (name_register_source before.(NameState) key source bytes) before)).
    { intros p Hroot; change (kernel_name_root sg before p) in Hroot.
      destruct (UCOS2_state_inv_names_valid sg before Hv p Hroot) as [cs Hread].
      exists cs; eapply tmr_create_registered_source_preserves_readable; eassumption. }
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
    cbn; intuition.
Qed.

Lemma tmr_create_register_source_rep : forall names key source bytes,
  name_source_disjoint names source ->
  store_name_bytes names ** tmr_create_source_rep source bytes |--
  store_name_bytes (name_register_source names key source bytes).
Proof.
  intros names key source bytes Hdis.
  unfold store_name_bytes, tmr_create_source_rep, store_map.
  Intros old fresh.
  rename H into Hold; rename H0 into Holdnd; rename H1 into Hfresh; rename H2 into Hfreshnd.
  assert (Hnew : forall p, In p fresh -> In p source.(nameStorageDomain)).
  { intros p Hp; apply Hfresh in Hp; destruct Hp as [b Hb].
    unfold tmr_create_source_map in Hb.
    destruct (in_dec Z.eq_dec p (nameStorageDomain source)); [assumption|discriminate]. }
  assert (Hapart : forall p, In p old -> ~ In p fresh).
  { intros p Hp Hq; destruct (proj1 (Hold p) Hp) as [b Hb].
    rewrite Hdis in Hb by (apply Hnew; exact Hq); discriminate. }
  Exists (old ++ fresh).
  assert (Hdomain : forall p, In p (old ++ fresh) <->
    exists b, (name_register_source names key source bytes).(nameBytes) p = Some b).
  { intro p; rewrite in_app_iff, Hold, Hfresh.
    unfold name_register_source, tmr_create_source_map; cbn.
    destruct (in_dec Z.eq_dec p (nameStorageDomain source)) as [Hin|Hout].
    - rewrite Hdis by exact Hin; split; intros; intuition eauto; destruct H0; discriminate.
    - split; intros; intuition eauto; destruct H0; discriminate. }
  assert (Hnd : NoDup (old ++ fresh)).
  { apply NoDup_app; repeat split; assumption. }
  assert (Holdmap : map (fun a => match nameBytes names a with
      Some b => name_byte_rep a b | None => emp end) old =
    map (fun a => match nameBytes (name_register_source names key source bytes) a with
      Some b => name_byte_rep a b | None => emp end) old).
  { apply map_ext_in; intros p Hp; unfold name_register_source; cbn.
    destruct (in_dec Z.eq_dec p (nameStorageDomain source)) as [Hin|Hout]; [|reflexivity].
    destruct (proj1 (Hold p) Hp) as [b Hb]; rewrite Hdis in Hb by exact Hin; discriminate. }
  assert (Hfreshmap : map (fun a => match tmr_create_source_map source bytes a with
      Some b => name_byte_rep a b | None => emp end) fresh =
    map (fun a => match nameBytes (name_register_source names key source bytes) a with
      Some b => name_byte_rep a b | None => emp end) fresh).
  { apply map_ext_in; intros p Hp; unfold name_register_source, tmr_create_source_map; cbn.
    destruct (in_dec Z.eq_dec p (nameStorageDomain source));
      [reflexivity|exfalso; apply n; apply Hnew; exact Hp]. }
  rewrite map_app, <- Holdmap, <- Hfreshmap.
  entailer!.
  sep_apply_r_atomic (derivable1_sepcon_iter_sepcon1
    (map (fun a => match nameBytes names a with Some b => name_byte_rep a b | None => emp end) old)
    (map (fun a => match tmr_create_source_map source bytes a with
      Some b => name_byte_rep a b | None => emp end) fresh)).
  entailer!.
Qed.

Lemma tmr_create_argument_error_none_iff : forall delay period option,
  tmr_create_argument_error delay period option = None <->
  (option = 2 /\ period <> 0) \/ (option = 1 /\ delay <> 0).
Proof.
  intros; unfold tmr_create_argument_error.
  destruct (option =? 2) eqn:Ht.
  - apply Z.eqb_eq in Ht.
    destruct (period =? 0) eqn:Hp.
    + apply Z.eqb_eq in Hp; split; intros; try discriminate; intuition lia.
    + apply Z.eqb_neq in Hp; split; intros; [left; auto|reflexivity].
  - apply Z.eqb_neq in Ht.
    destruct (option =? 1) eqn:Ho.
    + apply Z.eqb_eq in Ho.
      destruct (delay =? 0) eqn:Hd.
      * apply Z.eqb_eq in Hd; split; intros; try discriminate; intuition lia.
      * apply Z.eqb_neq in Hd; split; intros; [right; auto|reflexivity].
    + apply Z.eqb_neq in Ho; split; intros; try discriminate; intuition lia.
Qed.

Lemma tmr_create_argument_error_precedes_isr : forall delay period option nesting error,
  tmr_create_argument_error delay period option = Some error ->
  tmr_create_early_error delay period option nesting = Some error.
Proof. intros; unfold tmr_create_early_error; rewrite H; reflexivity. Qed.

Lemma tmr_create_early_error_isr : forall delay period option nesting,
  tmr_create_argument_error delay period option = None -> 0 < nesting ->
  tmr_create_early_error delay period option nesting = Some OS_ERR_TMR_ISR.
Proof.
  intros delay period option nesting Hargs Hnest.
  unfold tmr_create_early_error; rewrite Hargs, (proj2 (Z.ltb_lt 0 nesting) Hnest); reflexivity.
Qed.

Lemma tmr_create_name_null : forall default_name,
  tmr_create_name default_name 0 = default_name.
Proof. reflexivity. Qed.

Lemma tmr_create_name_nonnull : forall default_name pname,
  pname <> 0 -> tmr_create_name default_name pname = pname.
Proof.
  intros; unfold tmr_create_name; rewrite (proj2 (Z.eqb_neq pname 0) H); reflexivity.
Qed.

Lemma tmr_create_zero_unused_argument_allowed :
  tmr_create_argument_error 0 1 2 = None /\
  tmr_create_argument_error 1 0 1 = None.
Proof. split; reflexivity. Qed.

(** Exactly the seven Create stores. Type, links, Match and padding are
    retained; callback and name are values, never dereferenced here. *)
Definition tmr_create_image (old : TimerImage)
  (delay period option callback arg name : Z) : TimerImage :=
  {| timerImageType := old.(timerImageType); timerImageCallback := callback;
     timerImageArg := arg; timerImageNext := old.(timerImageNext);
     timerImagePrev := old.(timerImagePrev); timerImageMatch := old.(timerImageMatch);
     timerImageDelay := delay; timerImagePeriod := period; timerImageName := name;
     timerImageOption := option; timerImageState := 1;
     timerImagePadding := old.(timerImagePadding) |}.

Definition tmr_create_fields (p delay period option callback arg name : Z) : Assertion :=
  (p + 37) # UChar |-> 1 ** (p + 24) # UInt |-> delay **
  (p + 28) # UInt |-> period ** (p + 36) # UChar |-> option **
  (p + 4) # Ptr |-> callback ** (p + 8) # Ptr |-> arg **
  (p + 32) # Ptr |-> name.

Definition tmr_create_old_fields (p : addr) (old : TimerImage) : Assertion :=
  (p + 37) # UChar |-> old.(timerImageState) **
  (p + 24) # UInt |-> old.(timerImageDelay) **
  (p + 28) # UInt |-> old.(timerImagePeriod) **
  (p + 36) # UChar |-> old.(timerImageOption) **
  (p + 4) # Ptr |-> old.(timerImageCallback) **
  (p + 8) # Ptr |-> old.(timerImageArg) **
  (p + 32) # Ptr |-> old.(timerImageName).

Definition tmr_create_retained_fields (p : addr) (old : TimerImage) : Assertion :=
  p # UChar |-> old.(timerImageType) **
  store_optional_bytes (p + 1) (firstn 3 old.(timerImagePadding)) **
  (p + 12) # Ptr |-> old.(timerImageNext) **
  (p + 16) # Ptr |-> old.(timerImagePrev) **
  (p + 20) # UInt |-> old.(timerImageMatch) **
  store_optional_bytes (p + 38) (skipn 3 old.(timerImagePadding)).

Lemma tmr_create_split_private_fields : forall sg i private,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  timer_private_rep sg i private |--
  tmr_create_old_fields (timer_pool_addr sg i) private.(timerPrivateImage) **
  tmr_create_retained_fields (timer_pool_addr sg i) private.(timerPrivateImage).
Proof.
  intros sg i private Hconfig; unfold timer_private_rep, timer_object_rep,
    tmr_create_old_fields, tmr_create_retained_fields.
  rewrite Hconfig; cbn.
  replace (timer_pool_addr sg i + 36 + 1) with (timer_pool_addr sg i + 37) by lia.
  replace (timer_pool_addr sg i + 36 + 2) with (timer_pool_addr sg i + 38) by lia.
  entailer!.
Qed.

Lemma tmr_create_merge_initialized_fields : forall p old delay period option callback arg name,
  tmr_create_fields p delay period option callback arg name **
  tmr_create_retained_fields p old |--
  timer_object_rep selected_kernel_configuration p
    (tmr_create_image old delay period option callback arg name).
Proof.
  intros; unfold tmr_create_fields, tmr_create_retained_fields,
    timer_object_rep, tmr_create_image; cbn.
  replace (p + 36 + 1) with (p + 37) by lia.
  replace (p + 36 + 2) with (p + 38) by lia.
  entailer!.
Qed.

Lemma tmr_create_private_match_in_range : forall sg i private,
  timer_private_rep sg i private |--
  coq_prop (0 <= private.(timerPrivateImage).(timerImageMatch) < 4294967296) &&
  timer_private_rep sg i private.
Proof.
  intros; unfold timer_private_rep, timer_object_rep.
  prop_apply_p (store_uint_range (timer_pool_addr sg i + 20)
    private.(timerPrivateImage).(timerImageMatch)).
  entailer!.
  change (0 <= private.(timerPrivateImage).(timerImageMatch) <= 4294967295) in H.
  lia.
Qed.

Lemma tmr_create_allocated_image_facts : forall sg before i private allocated,
  valid_timer_state sg before -> timer_allocate before = Some (i, private, allocated) ->
  private.(timerPrivateImage).(timerImageType) = 100 /\
  private.(timerPrivateImage).(timerImageNext) = 0 /\
  private.(timerPrivateImage).(timerImagePrev) = 0 /\
  (private.(timerPrivateGeneration) < allocated.(timerNextGeneration))%nat /\
  List.length private.(timerPrivateImage).(timerImagePadding) = 5%nat.
Proof.
  intros sg before i private allocated Hvalid Hstep.
  assert (Hlinks : forall pre j rest, before.(timerFree) = pre ++ j :: rest ->
    exists v, before.(timerImages) j = Some v /\ v.(timerImageType) = 100 /\
      v.(timerImageState) = 0 /\ v.(timerImageNext) = timer_id_pointer sg rest /\
      v.(timerImagePrev) = 0) by (unfold valid_timer_state in Hvalid; tauto).
  assert (Hpadding : forall j v, before.(timerImages) j = Some v ->
    List.length v.(timerImagePadding) = 5%nat) by (unfold valid_timer_state in Hvalid; tauto).
  unfold timer_allocate in Hstep.
  destruct (timerFree before) as [|j rest] eqn:Hfree; [discriminate|].
  destruct (timerImages before j) as [old|] eqn:Hold; [|discriminate].
  destruct (Hlinks [] j rest eq_refl) as [v [Hv [Htype _]]].
  assert (v = old) by congruence; subst v.
  inversion Hstep; subst; cbn; repeat split; try assumption; try reflexivity; try lia.
  eapply Hpadding; exact Hold.
Qed.

Lemma tmr_create_image_object_eq : forall old private delay period mode callback arg name,
  old = private.(timerPrivateImage) ->
  old.(timerImageType) = 100 -> old.(timerImageNext) = 0 -> old.(timerImagePrev) = 0 ->
  tmr_create_image old delay period (encode_timer_mode mode) callback arg name =
  timer_object_image (timer_create_object private delay period mode callback arg name)
    0 0 old.(timerImagePadding).
Proof.
  intros old private delay period mode callback arg name -> Htype Hnext Hprev.
  unfold tmr_create_image, timer_object_image, timer_create_object; cbn.
  rewrite Htype, Hnext, Hprev; reflexivity.
Qed.

Lemma tmr_create_object_valid : forall private delay period mode callback arg name,
  0 <= delay < 4294967296 -> 0 <= period < 4294967296 ->
  0 <= private.(timerPrivateImage).(timerImageMatch) < 4294967296 ->
  tmr_create_argument_error delay period (encode_timer_mode mode) = None ->
  valid_timer_object (timer_create_object private delay period mode callback arg name).
Proof.
  intros private delay period mode callback arg name Hd Hp Hm Hargs.
  unfold valid_timer_object, timer_create_object; cbn.
  repeat split; try lia; try discriminate.
  destruct mode; cbn in *; unfold tmr_create_argument_error in Hargs; cbn in Hargs.
  - destruct (delay =? 0) eqn:Hz; [discriminate|apply Z.eqb_neq in Hz; lia].
  - destruct (period =? 0) eqn:Hz; [discriminate|apply Z.eqb_neq in Hz; lia].
Qed.

Lemma tmr_create_publish_configuration : forall sg before i private allocated
  delay period mode callback arg name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  valid_timer_configuration sg before -> timer_api_initialized before ->
  timer_allocate before = Some (i, private, allocated) ->
  0 <= delay < 4294967296 -> 0 <= period < 4294967296 ->
  0 <= private.(timerPrivateImage).(timerImageMatch) < 4294967296 ->
  tmr_create_argument_error delay period (encode_timer_mode mode) = None ->
  valid_timer_configuration sg (timer_publish allocated i private delay period mode callback arg name) /\
  timer_api_initialized (timer_publish allocated i private delay period mode callback arg name).
Proof.
  intros sg before i private allocated delay period mode callback arg name
    He Hcap Hv Hinit Halloc Hd Hp Hmatch Hargs.
  pose proof (proj1 (timer_initialized_configuration_iff sg before He Hinit) Hv) as Hvalid.
  destruct (tmr_create_allocated_image_facts sg before i private allocated Hvalid Halloc)
    as [_ [_ [_ [Hgen Hpad]]]].
  destruct (timer_allocate_preserves_configuration sg before i private allocated
    He Hcap Hv Hinit Halloc) as [Hallocated Hallocated_init].
  destruct (timer_allocate_excludes_global_image before i private allocated Halloc)
    as [_ [Hprivate _]].
  eapply timer_publish_preserves_configuration; try eassumption.
  apply tmr_create_object_valid; assumption.
Qed.

Lemma tmr_create_publish_name_references : forall before i private delay period mode callback arg name p,
  timer_name_reference (timer_publish before i private delay period mode callback arg name) p ->
  timer_name_reference before p \/ p = name.
Proof.
  intros before i private delay period mode callback arg name p [j [timer [Hlookup Hname]]].
  change (kernel_map_set before.(timerUsed) i
    (Some (timer_create_object private delay period mode callback arg name)) j = Some timer) in Hlookup.
  destruct (Z.eq_dec j i) as [->|Hji].
  - rewrite kernel_map_set_same in Hlookup; injection Hlookup as Heq.
    subst timer; right; exact Hname.
  - rewrite kernel_map_set_other in Hlookup by exact Hji.
    left; exists j, timer; auto.
Qed.

(** Configured callers provide a genuine existing readable string and its
    shared Name ownership.  This lemma creates neither bytes nor registration. *)
Lemma tmr_create_publish_names_valid : forall sg before allocated i private delay period mode callback arg name chars,
  kernel_names_valid sg before -> readable_name before.(NameState) name chars ->
  allocated.(timerUsed) = before.(TimerState).(timerUsed) ->
  kernel_names_valid sg
    (replace_TimerS (timer_publish allocated i private delay period mode callback arg name) before).
Proof.
  intros sg before allocated i private delay period mode callback arg name chars Hv Hname Hused.
  eapply kernel_names_valid_add_root; [exact Hv|exact Hname|reflexivity|].
  intros p [[He Hr]|[[He Hr]|[[He [Hn Hr]]|[[He [Hn Hr]]|[He [Hn Hr]]]]]].
  - left; left; split; assumption.
  - left; right; left; split; assumption.
  - left; right; right; left; repeat split; assumption.
  - left; right; right; right; left; repeat split; assumption.
  - destruct (tmr_create_publish_name_references allocated i private delay period mode callback arg name p Hr)
      as [Hold | Hnew].
    + left; right; right; right; right; repeat split; try assumption.
      unfold timer_name_reference in *; rewrite Hused in Hold; exact Hold.
    + right; exact Hnew.
Qed.

Lemma tmr_create_publish_requires_readable_name : forall sg before allocated i private
  delay period mode callback arg name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  kernel_names_valid sg
    (replace_TimerS (timer_publish allocated i private delay period mode callback arg name) before) ->
  exists chars, readable_name before.(NameState) name chars.
Proof.
  intros sg before allocated i private delay period mode callback arg name He Hn Hv.
  apply Hv; right; right; right; right; split; [exact He|].
  split; [exact Hn|]. exists i, (timer_create_object private delay period mode callback arg name).
  split; [apply kernel_map_set_same|reflexivity].
Qed.

Lemma tmr_create_readable_name_has_first_byte : forall names name chars,
  readable_name names name chars -> exists byte, names.(nameBytes) name = Some byte.
Proof.
  intros names name [|byte chars] [Hchars [Hbytes Hnul]].
  - exists 0; cbn in Hnul; rewrite Z.add_0_r in Hnul; exact Hnul.
  - exists byte; specialize (Hbytes 0%nat byte eq_refl); cbn in Hbytes.
    rewrite Z.add_0_r in Hbytes; exact Hbytes.
Qed.

(** A direct counterexample condition for the actual Unlock precondition.
    An arbitrary non-NULL C value need not occur in NameState.  Neither the
    seven stores nor Alloc changes NameState, and writing the pointer does not
    establish a terminated string at that pointer. *)
Lemma tmr_create_unregistered_name_prevents_global_inv : forall sg before allocated i private
  delay period mode callback arg name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true -> sg.(osKernelConfig).(cfgTimerNames) = true ->
  before.(NameState).(nameBytes) name = None ->
  ~ UCOS2_state_inv sg
    (replace_TimerS (timer_publish allocated i private delay period mode callback arg name) before).
Proof.
  intros sg before allocated i private delay period mode callback arg name He Hn Hmissing Hvalid.
  destruct (tmr_create_publish_requires_readable_name sg before allocated i private
    delay period mode callback arg name He Hn (UCOS2_state_inv_names_valid _ _ Hvalid))
    as [chars Hread].
  destruct (tmr_create_readable_name_has_first_byte _ _ _ Hread) as [byte Hbyte].
  congruence.
Qed.

Lemma tmr_create_question_mark_is_readable : forall p,
  readable_name (name_question_mark_resources p) p [63].
Proof.
  intro p; unfold readable_name; split.
  - constructor; [lia|constructor].
  - split.
    + intros [|i] c Hlookup; [inversion Hlookup; subst c|destruct i; discriminate].
      unfold name_question_mark_resources, name_register_source, name_question_mark_source; cbn.
      rewrite Z.add_0_r.
      destruct (in_dec Z.eq_dec p [p; p + 1]); [|exfalso; apply n; simpl; auto].
      unfold name_question_mark_bytes; destruct (Z.eq_dec p p); congruence.
    + unfold name_question_mark_resources, name_register_source, name_question_mark_source; cbn.
      destruct (in_dec Z.eq_dec (p + 1) [p; p + 1]); [|exfalso; apply n; simpl; auto].
      unfold name_question_mark_bytes; destruct (Z.eq_dec (p + 1) p); [lia|].
      destruct (Z.eq_dec (p + 1) (p + 1)); try congruence.
      destruct (Z.eq_dec p (p + 1)); reflexivity.
Qed.

(** The complete configured publication consequence is conditional only on
    the actual input fields, the actual Alloc result and the supplied string.
    It never assumes validity of the desired successor global state. *)
Lemma tmr_create_publish_preserves_global_validity : forall sg before allocated i private
  delay period mode callback arg name chars,
  UCOS2_state_inv sg before ->
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  sg.(osKernelConfig).(cfgMaxTimers) < 65536 ->
  timer_api_initialized before.(TimerState) ->
  timer_allocate before.(TimerState) = Some (i, private, allocated) ->
  0 <= delay < 4294967296 -> 0 <= period < 4294967296 ->
  0 <= private.(timerPrivateImage).(timerImageMatch) < 4294967296 ->
  tmr_create_argument_error delay period (encode_timer_mode mode) = None ->
  readable_name before.(NameState) name chars ->
  UCOS2_state_inv sg
    (replace_TimerS (timer_publish allocated i private delay period mode callback arg name) before).
Proof.
  intros sg before allocated i private delay period mode callback arg name chars
    Hvalid He Hcap Hinit Halloc Hd Hp Hmatch Hargs Hname.
  assert (Htimers : valid_timer_configuration sg before.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto).
  destruct (tmr_create_publish_configuration sg before.(TimerState) i private allocated
    delay period mode callback arg name He Hcap Htimers Hinit Halloc Hd Hp Hmatch Hargs)
    as [Hconfiguration Hinitialized].
  assert (Hused : allocated.(timerUsed) = before.(TimerState).(timerUsed))
    by (exact (proj1 (tmr_alloc_allocate_effects _ _ _ _ Halloc))).
  pose proof (tmr_create_publish_names_valid sg before allocated i private delay period
    mode callback arg name chars (UCOS2_state_inv_names_valid _ _ Hvalid) Hname Hused)
    as Hnames_after.
  destruct Hvalid as [Hprofile [Ht [Hs [Hevent [Hcross [Hi [Hstatus [Hf [Hm [Htm Hrest]]]]]]]]]].
  destruct Hrest as [Hstats [Hcontrol [Hnames [Hroots Hstacks]]]].
  split; [exact Hprofile|]. split; [exact Ht|]. split; [exact Hs|]. split; [exact Hevent|].
  split.
  - destruct Hcross as [Ha [Ho [Hw [Hprotocol [Hunique [Hflags Hphase]]]]]].
    split; [exact Ha|]. split; [exact Ho|]. split; [exact Hw|].
    split; [exact Hprotocol|]. split; [exact Hunique|]. split; [exact Hflags|].
    unfold cross_module_invariants.timer_running_initialization_consistency.
    cbn; intros; exact Hinitialized.
  - split; [exact Hi|]. split; [exact Hstatus|]. split; [exact Hf|]. split; [exact Hm|].
    split; [exact Hconfiguration|]. split; [exact Hstats|]. split; [exact Hcontrol|].
    split; [exact Hnames|]. split; [exact Hnames_after|exact Hstacks].
Qed.

(** This is the storage-only insertion. It transports all non-target Timer
    bytes and all unchanged globals. Other private allocations are still
    outside timer_raw_rep and remain in the caller's disjoint frame. *)
Lemma tmr_create_publish_rep : forall sg allocated i private delay period mode callback arg name,
  allocated.(timerImages) i = None ->
  timer_raw_rep sg allocated **
  timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg i)
    (timer_object_image (timer_create_object private delay period mode callback arg name)
      0 0 private.(timerPrivateImage).(timerImagePadding)) |--
  timer_raw_rep sg (timer_publish allocated i private delay period mode callback arg name).
Proof.
  intros sg allocated i private delay period mode callback arg name Hnone.
  set (post := timer_publish allocated i private delay period mode callback arg name).
  set (image := timer_object_image (timer_create_object private delay period mode callback arg name)
    0 0 private.(timerPrivateImage).(timerImagePadding)).
  assert (Hlookup : post.(timerImages) i = Some image)
    by (unfold post, timer_publish; cbn; apply kernel_map_set_same).
  assert (Hothers : forall j, j <> i -> allocated.(timerImages) j = post.(timerImages) j).
  { intros j Hj; unfold post, timer_publish; cbn; rewrite kernel_map_set_other by exact Hj; reflexivity. }
  unfold timer_raw_rep, timer_images_rep at 1.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun j v => timer_object_rep sg.(osKernelConfig) (timer_pool_addr sg j) v)
    allocated.(timerImages) i Hnone).
  fold (timer_images_without sg allocated i).
  sep_apply_l_atomic (timer_images_merge_updated_object sg allocated post i image Hlookup Hothers).
  unfold timer_raw_rep, post, timer_publish; cbn; entailer!.
Qed.

Lemma tmr_create_lock_preserves_name_state : forall critical sg invocation before acquired locked,
  os_sched_lock_call_relation critical sg invocation before acquired locked ->
  before.(NameState) = locked.(NameState).
Proof.
  intros critical sg invocation before acquired locked [Hinterval ->].
  unfold os_sched_lock_checkpoint; cbn [replace_IntrS NameState].
  destruct before.(SchedState).(isRunning) eqn:Hrunning.
  - eapply critical_region_interval_preserves_name_state; exact Hinterval.
  - subst acquired; reflexivity.
Qed.

Lemma tmr_create_missing_name_rejects_unlock_pre : forall external platform critical sg context mask
  before allocated i private delay period mode callback arg name,
  sg.(osKernelConfig).(cfgTimerEnabled) = true ->
  sg.(osKernelConfig).(cfgTimerNames) = true ->
  before.(NameState).(nameBytes) name = None ->
  os_sched_unlock_pre external platform critical sg context mask
    (replace_TimerS (timer_publish allocated i private delay period mode callback arg name) before)
  |-- coq_prop False.
Proof.
  intros external platform critical sg context mask before allocated i private delay period
    mode callback arg name He Hnames Hmissing.
  unfold os_sched_unlock_pre; Intros.
  pose proof (tmr_create_unregistered_name_prevents_global_inv sg before allocated i private
    delay period mode callback arg name He Hnames Hmissing) as Hnot.
  entailer!.
Qed.

Inductive TmrCreateLiteralOwner : Type :=
| TmrCreateLiteralGlobal
| TmrCreateLiteralShared
| TmrCreateLiteralPrivate.

Record TmrCreateEnvironment : Type := {
  tmr_create_external : OsSchedExternalResources;
  tmr_create_platform : InterruptPlatformResources;
  tmr_create_critical : CriticalRegionResources;
  tmr_create_globals : StableGlobVars;
  tmr_create_caller : OsSchedCallContext;
  tmr_create_mask : Z;
  tmr_create_name_plan : TmrCreateNamePlan;
  tmr_create_literal_owner : TmrCreateLiteralOwner
}.

Record TmrCreateArguments : Type := {
  tmr_create_delay : Z;
  tmr_create_period : Z;
  tmr_create_option : Z;
  tmr_create_callback : addr;
  tmr_create_callback_arg : addr;
  tmr_create_name_argument : addr;
  tmr_create_default_name : addr
}.

Definition tmr_create_chosen_name (args : TmrCreateArguments) : addr :=
  tmr_create_name args.(tmr_create_default_name) args.(tmr_create_name_argument).

Definition tmr_create_mode (args : TmrCreateArguments) : TimerMode :=
  if args.(tmr_create_option) =? 2 then TimerPeriodic else TimerOneShot.

Definition tmr_create_arguments_in_range (args : TmrCreateArguments) : Prop :=
  0 <= args.(tmr_create_delay) < 4294967296 /\
  0 <= args.(tmr_create_period) < 4294967296 /\
  0 <= args.(tmr_create_option) < 256.

Definition tmr_create_first_error (args : TmrCreateArguments)
  (before : UCOS2_Verify_State) : option OSErrCode :=
  tmr_create_early_error args.(tmr_create_delay) args.(tmr_create_period)
    args.(tmr_create_option) before.(IntrState).(intNesting).

Definition tmr_create_completion (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (locked : UCOS2_Verify_State) (i : TimerID) (private : TimerPrivateAllocation)
  (allocated : GlobTimerState) : UCOS2_Verify_State :=
  if tmr_create_is_public env.(tmr_create_name_plan) then
    replace_TimerS (timer_publish allocated i private args.(tmr_create_delay)
      args.(tmr_create_period) (tmr_create_mode args) args.(tmr_create_callback)
      args.(tmr_create_callback_arg) (tmr_create_chosen_name args))
      (replace_NameS (tmr_create_name_state env.(tmr_create_name_plan) locked.(NameState)) locked)
  else replace_TimerS allocated locked.

Inductive TmrCreateResult : Type :=
| TmrCreateEarly (error : OSErrCode)
| TmrCreateExhausted
| TmrCreateStored (i : TimerID) (private : TimerPrivateAllocation).

Definition tmr_create_result_pointer (sg : StableGlobVars) (result : TmrCreateResult) : addr :=
  match result with TmrCreateStored i _ => timer_pool_addr sg i | _ => 0 end.

Definition tmr_create_result_error (result : TmrCreateResult) : OSErrCode :=
  match result with
  | TmrCreateEarly error => error
  | TmrCreateExhausted => OS_ERR_TMR_NON_AVAIL
  | TmrCreateStored _ _ => OS_ERR_NONE
  end.

Definition tmr_create_needs_unlock (result : TmrCreateResult) : bool :=
  match result with TmrCreateEarly _ => false | _ => true end.

Definition TmrCreateOutput : Type := (addr * Z)%type.
Definition tmr_create_output (sg : StableGlobVars) (result : TmrCreateResult) : TmrCreateOutput :=
  (tmr_create_result_pointer sg result, encode_os_err_code (tmr_create_result_error result)).

(** The source prefix has six return shapes, keeps the pre-Lock ISR
    observation, and allocates from the actual post-Lock pool.  Registration
    only reindexes existing owned bytes; it is not a string scan or C store. *)
Definition tmr_create_prefix (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before : UCOS2_Verify_State) (result : TmrCreateResult)
  (completion : UCOS2_Verify_State) : Prop :=
  match tmr_create_first_error args before with
  | Some error => result = TmrCreateEarly error /\ completion = before
  | None => exists acquired locked,
      os_sched_lock_call_relation env.(tmr_create_critical) env.(tmr_create_globals)
        env.(tmr_create_caller).(os_sched_call_invocation) before acquired locked /\
      match result with
      | TmrCreateEarly _ => False
      | TmrCreateExhausted => locked.(TimerState).(timerFree) = [] /\ completion = locked
      | TmrCreateStored i private => exists allocated,
          timer_allocate locked.(TimerState) = Some (i, private, allocated) /\
          completion = tmr_create_completion env args locked i private allocated
      end
  end.

(** This projection is exactly the existing Unlock post, including its
    separate Scheduler acquisition and original-call ordinary return. *)
Definition tmr_create_unlock_return (env : TmrCreateEnvironment)
  (before : UCOS2_Verify_State) (returned : OsSchedCallContext)
  (final : UCOS2_Verify_State) : Prop :=
  (before.(SchedState).(isRunning) = false /\ UCOS2_state_inv env.(tmr_create_globals) before /\
    returned = env.(tmr_create_caller) /\ final = before) \/
  (exists entry,
    before.(SchedState).(isRunning) = true /\
    critical_region_interval env.(tmr_create_critical) env.(tmr_create_globals)
      env.(tmr_create_caller).(os_sched_call_invocation) before entry /\
    UCOS2_state_inv env.(tmr_create_globals) (os_sched_unlock_checkpoint true entry) /\
    ((os_sched_unlock_requests entry = true /\ exists sched_entry,
       critical_region_interval env.(tmr_create_critical) env.(tmr_create_globals)
         env.(tmr_create_caller).(os_sched_call_invocation)
         (os_sched_unlock_checkpoint true entry) sched_entry /\
       os_sched_c_return env.(tmr_create_external) env.(tmr_create_critical)
         env.(tmr_create_globals) sched_entry env.(tmr_create_caller) returned final) \/
     (os_sched_unlock_requests entry = false /\ returned = env.(tmr_create_caller) /\
       final = os_sched_unlock_checkpoint true entry))).

Definition tmr_create_return_program (env : TmrCreateEnvironment) (result : TmrCreateResult)
  : program UCOS2_Verify_State OsSchedCallContext :=
  if tmr_create_needs_unlock result then tmr_create_unlock_return env
  else StateRelMonad.ret env.(tmr_create_caller).

Definition tmr_create_program (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  : program UCOS2_Verify_State TmrCreateOutput :=
  bind (tmr_create_prefix env args) (fun result =>
    bind (tmr_create_return_program env result) (fun _ =>
      StateRelMonad.ret (tmr_create_output env.(tmr_create_globals) result))).

Definition tmr_create_at_state (before : UCOS2_Verify_State)
  : UCOS2_Verify_State -> Prop := fun current => current = before.

Lemma tmr_create_program_result_iff : forall env args before output final,
  tmr_create_program env args before output final <->
  exists result completion returned,
    tmr_create_prefix env args before result completion /\
    tmr_create_return_program env result completion returned final /\
    output = tmr_create_output env.(tmr_create_globals) result.
Proof.
  intros; unfold tmr_create_program.
  change ((exists result completion, tmr_create_prefix env args before result completion /\
    exists returned endpoint, tmr_create_return_program env result completion returned endpoint /\
      output = tmr_create_output env.(tmr_create_globals) result /\ endpoint = final) <->
    exists result completion returned, tmr_create_prefix env args before result completion /\
      tmr_create_return_program env result completion returned final /\
      output = tmr_create_output env.(tmr_create_globals) result).
  split.
  - intros [result [completion [Hprefix [returned [endpoint [Hreturn [Houtput ->]]]]]]].
    exists result, completion, returned; auto.
  - intros [result [completion [returned [Hprefix [Hreturn Houtput]]]]].
    exists result, completion; split; [exact Hprefix|].
    exists returned, final; auto.
Qed.

Lemma tmr_create_safe_return : forall env args before result completion returned final
  (X : TmrCreateOutput -> UCOS2_Verify_State -> Prop),
  tmr_create_prefix env args before result completion ->
  tmr_create_return_program env result completion returned final ->
  safeExec (tmr_create_at_state before) (tmr_create_program env args) X ->
  safeExec (tmr_create_at_state final)
    (StateRelMonad.ret (tmr_create_output env.(tmr_create_globals) result)) X.
Proof.
  intros env args before result completion returned final X Hprefix Hreturn Hsafe.
  eapply (highstependret_derive (tmr_create_program env args)
    (tmr_create_at_state before) (tmr_create_output env.(tmr_create_globals) result)
    (fun _ => tmr_create_at_state final)); [|exact Hsafe].
  unfold hs_eval, tmr_create_at_state; intros initial ->.
  exists final; split; [|reflexivity].
  apply tmr_create_program_result_iff; exists result, completion, returned; auto.
Qed.

Definition tmr_create_return_frame (env : TmrCreateEnvironment)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running env.(tmr_create_platform)
    env.(tmr_create_caller).(os_sched_call_invocation)
    env.(tmr_create_caller).(os_sched_call_origin) env.(tmr_create_mask) **
  critical_region_outside env.(tmr_create_critical) env.(tmr_create_globals)
    env.(tmr_create_caller).(os_sched_call_invocation) final **
  os_sched_context_resources env.(tmr_create_external) returned **
  unmap_table_rep env.(tmr_create_globals).

Lemma tmr_create_unlock_post_return : forall env before,
  os_sched_unlock_post env.(tmr_create_external) env.(tmr_create_platform)
    env.(tmr_create_critical) env.(tmr_create_globals) env.(tmr_create_caller)
    env.(tmr_create_mask) before |--
  EX returned final, coq_prop (tmr_create_unlock_return env before returned final) &&
    tmr_create_return_frame env returned final.
Proof.
  intros; unfold os_sched_unlock_post; apply derivable1_orp_elim.
  - Intros. Exists env.(tmr_create_caller) before.
    assert (Hreturn : tmr_create_unlock_return env before env.(tmr_create_caller) before).
    { unfold tmr_create_unlock_return; left; tauto. }
    unfold tmr_create_return_frame, os_sched_unlock_observation_frame,
      critical_region_outside, os_sched_unlock_running; entailer!.
  - Intros entry; destruct (os_sched_unlock_requests entry) eqn:Hrequests.
    + unfold os_sched_post; Intros sched_entry final returned.
      Exists returned final.
      assert (Hreturn : tmr_create_unlock_return env before returned final).
      { unfold tmr_create_unlock_return; right; exists entry.
        split; [tauto|]. split; [tauto|]. split; [tauto|].
        left; split; [exact Hrequests|]; exists sched_entry; tauto. }
      unfold tmr_create_return_frame; entailer!.
    + Exists env.(tmr_create_caller) (os_sched_unlock_checkpoint true entry).
      assert (Hreturn : tmr_create_unlock_return env before env.(tmr_create_caller)
        (os_sched_unlock_checkpoint true entry)).
      { unfold tmr_create_unlock_return; right; exists entry.
        split; [tauto|]. split; [tauto|]. split; [tauto|]. right; auto. }
      unfold tmr_create_return_frame, os_sched_unlock_outside_frame; entailer!.
Qed.

(** The raw result owns exactly the initialized image. It makes no claim
    about a final private-map lookup or public use of that pointer. Public
    success transfers that ownership before Unlock, so later interference
    follows the existing public Timer semantics. Error paths keep the
    caller's optional name storage without requiring string readability. *)
Definition tmr_create_result_storage (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (result : TmrCreateResult) : Assertion :=
  match result with
  | TmrCreateStored i private =>
      if tmr_create_is_public env.(tmr_create_name_plan) then emp
      else timer_object_rep env.(tmr_create_globals).(osKernelConfig)
        (timer_pool_addr env.(tmr_create_globals) i)
        (tmr_create_image private.(timerPrivateImage) args.(tmr_create_delay)
          args.(tmr_create_period) args.(tmr_create_option) args.(tmr_create_callback)
          args.(tmr_create_callback_arg) (tmr_create_chosen_name args))
  | _ => tmr_create_name_storage env.(tmr_create_name_plan)
  end.

Definition tmr_create_api_post (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before : UCOS2_Verify_State) (perr ret : addr)
  (X : TmrCreateOutput -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX result completion returned final,
    coq_prop (tmr_create_prefix env args before result completion /\
      tmr_create_return_program env result completion returned final /\
      ret = tmr_create_result_pointer env.(tmr_create_globals) result /\
      safeExec (tmr_create_at_state final)
        (StateRelMonad.ret (tmr_create_output env.(tmr_create_globals) result)) X) &&
    (tmr_create_return_frame env returned final **
     tmr_create_result_storage env args result **
     perr # UChar |-> encode_os_err_code (tmr_create_result_error result)).

Lemma tmr_create_api_post_after_unlock : forall env args before result completion perr X,
  tmr_create_prefix env args before result completion ->
  tmr_create_needs_unlock result = true ->
  safeExec (tmr_create_at_state before) (tmr_create_program env args) X ->
  os_sched_unlock_post env.(tmr_create_external) env.(tmr_create_platform)
    env.(tmr_create_critical) env.(tmr_create_globals) env.(tmr_create_caller)
    env.(tmr_create_mask) completion ** tmr_create_result_storage env args result **
    perr # UChar |-> encode_os_err_code (tmr_create_result_error result) |--
  tmr_create_api_post env args before perr
    (tmr_create_result_pointer env.(tmr_create_globals) result) X.
Proof.
  intros env args before result completion perr X Hprefix Hneeds Hsafe.
  sep_apply_l_atomic (tmr_create_unlock_post_return env completion); Intros returned final.
  assert (Hreturn : tmr_create_return_program env result completion returned final).
  { unfold tmr_create_return_program; rewrite Hneeds; assumption. }
  pose proof (tmr_create_safe_return env args before result completion returned final
    X Hprefix Hreturn Hsafe) as Hexec.
  unfold tmr_create_api_post; Exists result completion returned final; entailer!.
Qed.

Local Open Scope string_scope.
Definition tmr_create_c_bindings (sg : StableGlobVars) : Prop :=
  tmr_alloc_source_binding sg /\
  os_sched_unlock_global_addresses sg &("OSRunning") &("OSIntNesting")
    &("OSLockNesting") &("OSPrioHighRdy") &("OSPrioCur") &("OSTCBHighRdy")
    &("OSTCBPrioTbl") &("OSCtxSwCtr") &("OSUnMapTbl") &("OSRdyGrp") &("OSRdyTbl") /\
  (forall i, 0 <= i < sg.(osKernelConfig).(cfgMaxTimers) ->
    let p := timer_pool_addr sg i in
    &((p) # "os_tmr" ->ₛ "OSTmrState") = p + 37 /\
    &((p) # "os_tmr" ->ₛ "OSTmrDly") = p + 24 /\
    &((p) # "os_tmr" ->ₛ "OSTmrPeriod") = p + 28 /\
    &((p) # "os_tmr" ->ₛ "OSTmrOpt") = p + 36 /\
    &((p) # "os_tmr" ->ₛ "OSTmrCallback") = p + 4 /\
    &((p) # "os_tmr" ->ₛ "OSTmrCallbackArg") = p + 8 /\
    &((p) # "os_tmr" ->ₛ "OSTmrName") = p + 32).

(** This is ownership routing for the one source literal, not a check of an
    arbitrary pname value. The global-string case is used only by raw storage;
    configured callers borrow the already owned bytes before the C expression. *)
Definition tmr_create_global_strings (env : TmrCreateEnvironment)
  (literals : string -> addr) : Assertion :=
  match env.(tmr_create_literal_owner) with
  | TmrCreateLiteralGlobal => GlobalStrings literals
  | _ => GlobalStrings_missing literals ["?"]
  end.

Definition tmr_create_literal_condition (env : TmrCreateEnvironment)
  (args : TmrCreateArguments) (names : NameResourceState) : Prop :=
  args.(tmr_create_name_argument) = 0 ->
  match env.(tmr_create_literal_owner) with
  | TmrCreateLiteralGlobal => env.(tmr_create_name_plan) = TmrCreateRawName
  | TmrCreateLiteralShared =>
      readable_name names args.(tmr_create_default_name) [63]
  | TmrCreateLiteralPrivate =>
      match env.(tmr_create_name_plan) with
      | TmrCreateOwnedName _ source bytes _ =>
          source.(nameStorageOrigin) = StaticNameStorage /\
          tmr_create_source_map source bytes args.(tmr_create_default_name) = Some 63 /\
          tmr_create_source_map source bytes (args.(tmr_create_default_name) + 1) = Some 0
      | _ => False
      end
  end.

Definition tmr_create_name_admission (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before : UCOS2_Verify_State) : Prop :=
  forall acquired locked i private allocated,
    tmr_create_first_error args before = None ->
    os_sched_lock_call_relation env.(tmr_create_critical) env.(tmr_create_globals)
      env.(tmr_create_caller).(os_sched_call_invocation) before acquired locked ->
    timer_allocate locked.(TimerState) = Some (i, private, allocated) ->
    tmr_create_name_condition env.(tmr_create_name_plan) locked.(NameState)
      (tmr_create_chosen_name args) /\ tmr_create_literal_condition env args locked.(NameState).

Definition tmr_create_scheduler_safety (env : TmrCreateEnvironment)
  (args : TmrCreateArguments) (before : UCOS2_Verify_State) : Prop :=
  forall result completion,
    tmr_create_prefix env args before result completion ->
    tmr_create_needs_unlock result = true ->
    os_sched_unlock_acquire_safety env.(tmr_create_external) env.(tmr_create_critical)
      env.(tmr_create_globals) env.(tmr_create_caller) completion.

Definition tmr_create_entry_facts (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before : UCOS2_Verify_State) : Prop :=
  valid_stable_glob_vars env.(tmr_create_globals) /\
  tmr_create_c_bindings env.(tmr_create_globals) /\
  UCOS2_state_inv env.(tmr_create_globals) before /\
  tmr_create_arguments_in_range args /\
  (tmr_create_first_error args before = None -> timer_api_initialized before.(TimerState)) /\
  tmr_create_name_admission env args before /\ tmr_create_scheduler_safety env args before.

Definition tmr_create_api_pre (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before : UCOS2_Verify_State) (perr : addr)
  (X : TmrCreateOutput -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (tmr_create_entry_facts env args before /\
    safeExec (tmr_create_at_state before) (tmr_create_program env args) X) &&
  (tmr_create_return_frame env env.(tmr_create_caller) before **
   tmr_create_name_storage env.(tmr_create_name_plan) ** perr # UChar |->_).

Definition tmr_create_nesting (before : UCOS2_Verify_State) : Z := before.(IntrState).(intNesting).
Definition tmr_create_output_binding (actual expected : addr) : Prop := actual = expected.
Definition tmr_create_pointer_null (pointer : addr) : Prop := pointer = 0.
Definition tmr_create_timers (before : UCOS2_Verify_State) : GlobTimerState := before.(TimerState).

Definition tmr_create_observation_rest (env : TmrCreateEnvironment)
  (before : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running env.(tmr_create_platform)
    env.(tmr_create_caller).(os_sched_call_invocation)
    env.(tmr_create_caller).(os_sched_call_origin) env.(tmr_create_mask) **
  env.(tmr_create_globals).(g_OSLockNesting) # UChar |-> before.(IntrState).(lockNesting) **
  UCOS2_raw_rep_missing_interrupt env.(tmr_create_globals) before **
  os_sched_context_resources env.(tmr_create_external) env.(tmr_create_caller) **
  unmap_table_rep env.(tmr_create_globals).

Definition tmr_create_kernel_frame (env : TmrCreateEnvironment)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running env.(tmr_create_platform)
    env.(tmr_create_caller).(os_sched_call_invocation)
    env.(tmr_create_caller).(os_sched_call_origin) env.(tmr_create_mask) **
  UCOS2_raw_rep_missing_timer env.(tmr_create_globals) state **
  os_sched_context_resources env.(tmr_create_external) env.(tmr_create_caller) **
  unmap_table_rep env.(tmr_create_globals).

Definition tmr_create_locked_facts (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before locked : UCOS2_Verify_State) : Prop :=
  tmr_create_entry_facts env args before /\ tmr_create_first_error args before = None /\
  (exists acquired, os_sched_lock_call_relation env.(tmr_create_critical)
    env.(tmr_create_globals) env.(tmr_create_caller).(os_sched_call_invocation)
    before acquired locked) /\
  UCOS2_state_inv env.(tmr_create_globals) locked /\ timer_api_initialized locked.(TimerState).

Definition tmr_create_allocated_facts (env : TmrCreateEnvironment) (args : TmrCreateArguments)
  (before locked : UCOS2_Verify_State) (pointer i : Z)
  (private : TimerPrivateAllocation) (allocated : GlobTimerState) : Prop :=
  tmr_create_locked_facts env args before locked /\
  timer_allocate locked.(TimerState) = Some (i, private, allocated) /\
  pointer = timer_pool_addr env.(tmr_create_globals) i /\ pointer <> 0 /\
  0 <= i < env.(tmr_create_globals).(osKernelConfig).(cfgMaxTimers) /\
  0 <= private.(timerPrivateImage).(timerImageMatch) < 4294967296 /\
  private.(timerPrivateImage).(timerImageType) = 100 /\
  private.(timerPrivateImage).(timerImageNext) = 0 /\
  private.(timerPrivateImage).(timerImagePrev) = 0 /\
  (private.(timerPrivateGeneration) < allocated.(timerNextGeneration))%nat /\
  List.length private.(timerPrivateImage).(timerImagePadding) = 5%nat /\
  tmr_create_name_condition env.(tmr_create_name_plan) locked.(NameState)
    (tmr_create_chosen_name args) /\ tmr_create_literal_condition env args locked.(NameState).

Definition tmr_create_literal_rejoin (env : TmrCreateEnvironment)
  (locked : UCOS2_Verify_State) (literals : string -> addr) (rest : Assertion) : Prop :=
  store_stringLit (literals "?") "?" ** rest ** GlobalStrings_missing literals ["?"] |--
    tmr_create_kernel_frame env locked ** tmr_create_name_storage env.(tmr_create_name_plan) **
    tmr_create_global_strings env literals.

Lemma tmr_create_question_mark_storage_equiv : forall p,
  store_stringLit p "?" --||-- name_byte_rep p 63 ** name_byte_rep (p + 1) 0.
Proof.
  intro p.
  assert (Hvalid : valid_stringLit "?").
  { unfold valid_stringLit, valid_string, StringToList, StringLength.
    change (Forall valid_char [63]); repeat constructor; unfold valid_char; lia. }
  change ((coq_prop (valid_stringLit "?") && CharArray.full p 2 [63; 0]) --||--
    name_byte_rep p 63 ** name_byte_rep (p + 1) 0).
  unfold CharArray.full, store_array.
  cbn [store_array_rec].
  unfold name_byte_rep, StoreCharAsElement.storeA.
  rewrite sizeof_char.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  unfold store_char, store_uchar.
  split; entailer!.
Qed.

Definition tmr_create_map_remove_byte (bytes : addr -> option Z) (p : addr) :=
  fun q => if Z.eq_dec q p then None else bytes q.

Lemma tmr_create_map_remove_byte_rep : forall bytes p,
  store_map_missing_i name_byte_rep bytes p --||--
    store_map name_byte_rep (tmr_create_map_remove_byte bytes p).
Proof.
  intros bytes p.
  assert (Heq : forall q, q <> p -> bytes q = tmr_create_map_remove_byte bytes p q).
  { intros q Hq; unfold tmr_create_map_remove_byte; destruct (Z.eq_dec q p); congruence. }
  assert (Hnone : tmr_create_map_remove_byte bytes p p = None).
  { unfold tmr_create_map_remove_byte; destruct (Z.eq_dec p p); congruence. }
  split.
  - sep_apply_l_atomic (proj1 (store_map_missing_i_equiv name_byte_rep _ _ p Heq)).
    sep_apply_l_atomic (store_map_missing_equiv_store_map name_byte_rep _ p Hnone); entailer!.
  - sep_apply_l_atomic (store_map_equiv_store_map_missing name_byte_rep _ p Hnone).
    sep_apply_l_atomic (proj2 (store_map_missing_i_equiv name_byte_rep _ _ p Heq)); entailer!.
Qed.

Definition tmr_create_literal_map_rest (bytes : addr -> option Z) (p : addr) : Assertion :=
  store_map_missing_i name_byte_rep (tmr_create_map_remove_byte bytes p) (p + 1).

Lemma tmr_create_map_split_question_mark : forall bytes p,
  bytes p = Some 63 -> bytes (p + 1) = Some 0 ->
  store_map name_byte_rep bytes --||--
    store_stringLit p "?" ** tmr_create_literal_map_rest bytes p.
Proof.
  intros bytes p Hfirst Hnul.
  assert (Hnul' : tmr_create_map_remove_byte bytes p (p + 1) = Some 0).
  { unfold tmr_create_map_remove_byte; destruct (Z.eq_dec (p + 1) p); [lia|exact Hnul]. }
  unfold tmr_create_literal_map_rest.
  rewrite tmr_create_question_mark_storage_equiv.
  split.
  - sep_apply_l_atomic (store_map_split name_byte_rep p 63 bytes Hfirst).
    sep_apply_l_atomic (proj1 (tmr_create_map_remove_byte_rep bytes p)).
    sep_apply_l_atomic (store_map_split name_byte_rep (p + 1) 0
      (tmr_create_map_remove_byte bytes p) Hnul').
    entailer!.
  - sep_apply_l_atomic (store_map_merge name_byte_rep (p + 1) 0
      (tmr_create_map_remove_byte bytes p) Hnul').
    sep_apply_l_atomic (proj2 (tmr_create_map_remove_byte_rep bytes p)).
    sep_apply_l_atomic (store_map_merge name_byte_rep p 63 bytes Hfirst).
    entailer!.
Qed.

Definition tmr_create_kernel_frame_without_names (env : TmrCreateEnvironment)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running env.(tmr_create_platform)
    env.(tmr_create_caller).(os_sched_call_invocation)
    env.(tmr_create_caller).(os_sched_call_origin) env.(tmr_create_mask) **
  UCOS2_raw_rep_missing_two env.(tmr_create_globals) state TimerModule NamesModule **
  os_sched_context_resources env.(tmr_create_external) env.(tmr_create_caller) **
  unmap_table_rep env.(tmr_create_globals).

Lemma tmr_create_kernel_frame_split_names : forall env state,
  tmr_create_kernel_frame env state --||--
    store_name_bytes state.(NameState) ** tmr_create_kernel_frame_without_names env state.
Proof.
  intros env state; unfold tmr_create_kernel_frame, tmr_create_kernel_frame_without_names,
    UCOS2_raw_rep_missing_timer.
  rewrite (UCOS2_raw_rep_missing_module_split_module
    env.(tmr_create_globals) state TimerModule NamesModule) by discriminate.
  cbn [UCOS2_module_rep]; split; entailer!.
Qed.

Lemma tmr_create_literal_resources_split : forall env args locked literals,
  args.(tmr_create_name_argument) = 0 -> args.(tmr_create_default_name) = literals "?" ->
  tmr_create_literal_condition env args locked.(NameState) ->
  tmr_create_kernel_frame env locked ** tmr_create_name_storage env.(tmr_create_name_plan) **
    tmr_create_global_strings env literals |--
  EX rest : Assertion, coq_prop (tmr_create_literal_rejoin env locked literals rest) &&
    store_stringLit (literals "?") "?" ** rest ** GlobalStrings_missing literals ["?"].
Proof.
  intros env args locked literals Hnull Haddress Hcondition.
  specialize (Hcondition Hnull).
  unfold tmr_create_global_strings.
  destruct (tmr_create_literal_owner env) eqn:Howner.
  - Exists (tmr_create_kernel_frame env locked **
      tmr_create_name_storage env.(tmr_create_name_plan)).
    assert (Hrejoin : tmr_create_literal_rejoin env locked literals
      (tmr_create_kernel_frame env locked ** tmr_create_name_storage env.(tmr_create_name_plan))).
    { unfold tmr_create_literal_rejoin, tmr_create_global_strings; rewrite Howner.
      sep_apply_l_atomic (GlobalStrings_merge literals "?"); entailer!. }
    sep_apply_l_atomic (GlobalStrings_split literals "?"); entailer!.
  - change (readable_name locked.(NameState) args.(tmr_create_default_name) [63]) in Hcondition.
    destruct Hcondition as [_ [Hbytes Hnul]].
    assert (Hfirst : locked.(NameState).(nameBytes) (literals "?") = Some 63).
    { specialize (Hbytes O 63 eq_refl); cbn in Hbytes; rewrite Z.add_0_r, Haddress in Hbytes; exact Hbytes. }
    change (locked.(NameState).(nameBytes) (args.(tmr_create_default_name) + 1) = Some 0) in Hnul.
    rewrite Haddress in Hnul.
    Exists (tmr_create_literal_map_rest locked.(NameState).(nameBytes) (literals "?") **
      tmr_create_kernel_frame_without_names env locked **
      tmr_create_name_storage env.(tmr_create_name_plan)).
    assert (Hrejoin : tmr_create_literal_rejoin env locked literals
      (tmr_create_literal_map_rest locked.(NameState).(nameBytes) (literals "?") **
       tmr_create_kernel_frame_without_names env locked **
       tmr_create_name_storage env.(tmr_create_name_plan))).
    { unfold tmr_create_literal_rejoin, tmr_create_global_strings; rewrite Howner.
      sep_apply_l_atomic (proj2 (tmr_create_map_split_question_mark _ _ Hfirst Hnul)).
      fold (store_name_bytes locked.(NameState)).
      sep_apply_l_atomic (proj2 (tmr_create_kernel_frame_split_names env locked)); entailer!. }
    sep_apply_l_atomic (proj1 (tmr_create_kernel_frame_split_names env locked)).
    unfold store_name_bytes.
    sep_apply_l_atomic (proj1 (tmr_create_map_split_question_mark _ _ Hfirst Hnul)); entailer!.
  - destruct (tmr_create_name_plan env) eqn:Hplan; try contradiction.
    change (nameStorageOrigin source = StaticNameStorage /\
      tmr_create_source_map source bytes (tmr_create_default_name args) = Some 63 /\
      tmr_create_source_map source bytes (tmr_create_default_name args + 1) = Some 0) in Hcondition.
    destruct Hcondition as [_ [Hfirst Hnul]]; rewrite Haddress in Hfirst, Hnul.
    Exists (tmr_create_literal_map_rest (tmr_create_source_map source bytes) (literals "?") **
      tmr_create_kernel_frame env locked).
    assert (Hrejoin : tmr_create_literal_rejoin env locked literals
      (tmr_create_literal_map_rest (tmr_create_source_map source bytes) (literals "?") **
       tmr_create_kernel_frame env locked)).
    { unfold tmr_create_literal_rejoin, tmr_create_global_strings; rewrite Howner, Hplan.
      cbn [tmr_create_name_storage]; unfold tmr_create_source_rep.
      sep_apply_l_atomic (proj2 (tmr_create_map_split_question_mark _ _ Hfirst Hnul)); entailer!. }
    cbn [tmr_create_name_storage]; unfold tmr_create_source_rep.
    sep_apply_l_atomic (proj1 (tmr_create_map_split_question_mark _ _ Hfirst Hnul)); entailer!.
Qed.

(** These are the two entailments returned by the already checked Alloc
    consequence. The actual C call still consumes its unchanged low contract. *)
Definition tmr_create_alloc_consequence (sg : StableGlobVars) (timers : GlobTimerState)
  (head next prev used free : Z) (frame : Assertion) : Prop :=
  head = timer_id_pointer sg timers.(timerFree) /\
  used = timers.(timerUsedCount) /\ free = timers.(timerFreeCount) /\
  (timer_inv sg timers |-- tmr_alloc_low_pre head next prev used free ** frame) /\
  (forall ret, tmr_alloc_low_post head next prev used free ret ** frame |--
    tmr_alloc_configured_result sg timers ret).

Lemma tmr_create_alloc_consequence_exists : forall sg timers,
  tmr_alloc_source_binding sg -> valid_timer_configuration sg timers -> timer_api_initialized timers ->
  exists head next prev used free frame,
    tmr_create_alloc_consequence sg timers head next prev used free frame.
Proof.
  intros sg timers Hb Hv Hi.
  destruct (tmr_alloc_configured_contract_consequence sg timers Hb Hv Hi)
    as [next [prev [frame [Hpre Hpost]]]].
  exists (timer_id_pointer sg timers.(timerFree)), next, prev,
    timers.(timerUsedCount), timers.(timerFreeCount), frame.
  unfold tmr_create_alloc_consequence; auto.
Qed.

Lemma tmr_create_allocate_global_validity : forall sg before i private allocated,
  UCOS2_state_inv sg before -> tmr_alloc_source_binding sg ->
  timer_api_initialized before.(TimerState) ->
  timer_allocate before.(TimerState) = Some (i, private, allocated) ->
  UCOS2_state_inv sg (replace_TimerS allocated before).
Proof.
  intros sg before i private allocated Hv [Hcfg Hb] Hi Ha.
  assert (He : sg.(osKernelConfig).(cfgTimerEnabled) = true) by (rewrite Hcfg; reflexivity).
  assert (Hcap : sg.(osKernelConfig).(cfgMaxTimers) < 65536) by (rewrite Hcfg; cbn; lia).
  assert (Htimer : valid_timer_configuration sg before.(TimerState))
    by (unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hv; tauto).
  destruct (timer_allocate_preserves_configuration sg before.(TimerState) i private allocated
    He Hcap Htimer Hi Ha) as [Hvalid Hinit].
  apply UCOS2_replace_timer_preserves_validity; try assumption.
  - intros; exact Hinit.
  - unfold timer_name_reference.
    rewrite (proj1 (tmr_alloc_allocate_effects _ _ _ _ Ha)); intros; assumption.
Qed.

Lemma tmr_create_name_storage_to_global : forall sg before plan name,
  tmr_create_name_condition plan before.(NameState) name ->
  UCOS2_inv sg before ** tmr_create_name_storage plan |--
  UCOS2_inv sg (replace_NameS (tmr_create_name_state plan before.(NameState)) before).
Proof.
  intros sg before plan name Hcondition.
  destruct plan; cbn in *.
  - rewrite replace_NameS_put_back; entailer!.
  - rewrite replace_NameS_put_back; entailer!.
  - rewrite UCOS2_inv_split_names; Intros.
    sep_apply_l_atomic (tmr_create_register_source_rep before.(NameState) key source bytes
      ltac:(tauto)).
    apply (UCOS2_inv_merge_updated_module sg before
      (replace_NameS (name_register_source before.(NameState) key source bytes) before) NamesModule).
    + eapply tmr_create_name_plan_preserves_validity with
        (plan := TmrCreateOwnedName key source bytes chars) (name := name); eassumption.
    + assert (Hframe : UCOS2_raw_rep_missing_module sg before NamesModule =
        UCOS2_raw_rep_missing_module sg
          (replace_NameS (name_register_source before.(NameState) key source bytes) before) NamesModule).
      { apply UCOS2_raw_rep_missing_module_frame; intros m Hm; destruct m; try reflexivity; contradiction. }
      rewrite Hframe; reflexivity.
Qed.

Lemma tmr_create_api_post_early__return_refinement :
  forall env args before error perr X,
  tmr_create_first_error args before = Some error ->
  safeExec (tmr_create_at_state before) (tmr_create_program env args) X ->
  tmr_create_return_frame env env.(tmr_create_caller) before **
  tmr_create_name_storage env.(tmr_create_name_plan) **
  perr # UChar |-> encode_os_err_code error |--
  tmr_create_api_post env args before perr 0 X.
Proof.
  intros env args before error perr X Herror Hsafe.
  assert (Hprefix : tmr_create_prefix env args before (TmrCreateEarly error) before).
  { unfold tmr_create_prefix; rewrite Herror; auto. }
  assert (Hreturn : tmr_create_return_program env (TmrCreateEarly error)
    before env.(tmr_create_caller) before).
  { split; reflexivity. }
  pose proof (tmr_create_safe_return env args before (TmrCreateEarly error)
    before env.(tmr_create_caller) before X Hprefix Hreturn Hsafe) as Hexec.
  unfold tmr_create_api_post.
  Exists (TmrCreateEarly error) before env.(tmr_create_caller) before.
  cbn [tmr_create_result_pointer tmr_create_result_error tmr_create_result_storage].
  entailer!.
Qed.
Lemma tmr_create_observation_merge__return_refinement : forall env before,
  env.(tmr_create_globals).(g_OSIntNesting) # UChar |-> tmr_create_nesting before **
  tmr_create_observation_rest env before |--
  tmr_create_return_frame env env.(tmr_create_caller) before.
Proof.
  intros env before.
  unfold tmr_create_observation_rest, tmr_create_return_frame, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module env.(tmr_create_globals) before InterruptModule).
  cbn [UCOS2_module_rep].
  unfold UCOS2_raw_rep_missing_interrupt.
  prop_apply_p (store_uchar_range env.(tmr_create_globals).(g_OSIntNesting)
    (tmr_create_nesting before)); Intros.
  prop_apply_p (store_uchar_range env.(tmr_create_globals).(g_OSLockNesting)
    before.(IntrState).(lockNesting)); Intros.
  unfold interrupt.interrupt_inv, interrupt.interrupt_in_range,
    interrupt.store_int_state, tmr_create_nesting; entailer!.
Qed.
