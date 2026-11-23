Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import String.
From AUXLib Require Import Axioms Feq ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.field_storage.
Import UCOS2_C_Rules ListNotations.
Module TaskFieldStorage := FieldStorage Arch32 LittleEndian
  UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.

(** TCB byte ownership and configuration layout.  Task protocol and
    scheduler validity stay with their semantic owners.  All field
    separation is an instance of QCP MapLib through field_storage. *)
Definition tcb64_addr (sg : StableGlobVars) (tid : Z) : addr :=
  sg.(g_OSTCBTbl) + tid * 64.

Definition tcb_fields : list TCBField :=
  [TCBStkPtr; TCBExtPtr; TCBStkBottom; TCBStkSize; TCBOpt; TCBId;
   TCBNext; TCBPrev; TCBEventPtr; TCBMsg; TCBFlagNode; TCBFlagsRdy;
   TCBPadding42; TCBPadding43; TCBDly; TCBStat; TCBStatPend; TCBPrio;
   TCBX; TCBY; TCBBitX; TCBBitY; TCBDelReq; TCBTaskName; TCBReg0].

Definition tcb_field_offset (f : TCBField) : Z :=
  match f with
  | TCBStkPtr => 0 | TCBExtPtr => 4 | TCBStkBottom => 8 | TCBStkSize => 12
  | TCBOpt => 16 | TCBId => 18 | TCBNext => 20 | TCBPrev => 24
  | TCBEventPtr => 28 | TCBMsg => 32 | TCBFlagNode => 36 | TCBFlagsRdy => 40
  | TCBPadding42 => 42 | TCBPadding43 => 43 | TCBDly => 44 | TCBStat => 48
  | TCBStatPend => 49 | TCBPrio => 50 | TCBX => 51 | TCBY => 52
  | TCBBitX => 53 | TCBBitY => 54 | TCBDelReq => 55
  | TCBTaskName => 56 | TCBReg0 => 60
  end.

Definition tcb_field_width (f : TCBField) : nat :=
  match f with
  | TCBStkPtr | TCBExtPtr | TCBStkBottom | TCBStkSize | TCBNext | TCBPrev
  | TCBEventPtr | TCBMsg | TCBFlagNode | TCBDly | TCBTaskName | TCBReg0 => 4
  | TCBOpt | TCBId | TCBFlagsRdy => 2
  | _ => 1
  end.

(** This computed layout partition is an internal representation theorem,
    not an unproved equality with QCP's opaque field_address or an ARM ABI
    theorem.  The C-layout bridge remains a separate obligation. *)
Lemma tcb_layout_covers_exactly_64_bytes :
  flat_map
    (fun f => map (fun n => tcb_field_offset f + Z.of_nat n)
                  (seq 0 (tcb_field_width f)))
    tcb_fields = map Z.of_nat (seq 0 64).
Proof. reflexivity. Qed.

Lemma tcb_fields_complete : forall f, In f tcb_fields.
Proof. intros []; simpl; tauto. Qed.

Lemma tcb_fields_nodup : NoDup tcb_fields.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Definition tcb_write
  (image : TCBCommonImage) (field : TCBField) (value : option Z)
  : TCBCommonImage :=
  field_update TCBField_eq_dec image field value.

Lemma tcb_write_target : forall image f value,
  tcb_write image f value f = value.
Proof. intros; apply field_update_same. Qed.

Lemma tcb_write_frame : forall image f value other,
  other <> f -> tcb_write image f value other = image other.
Proof. intros; apply field_update_other; assumption. Qed.

(** C-facing addresses use the native tag emitted by canonical QCP.  The
    arithmetic table above is retained for the separate numeric ABI/byte-copy
    interface, not used as an assumed field-address equality.  The two padding
    bytes are retained, unchanged, at their selected numeric-profile locations;
    relating those locations and the pool stride to QCP's named sizeof remains
    the explicit ABI/byte-copy boundary.  OS_TCBInit does not access padding. *)
Definition tcb_field_address (base : addr) (field : TCBField) : addr :=
  match field with
  | TCBStkPtr => &(base # "os_tcb" ->ₛ "OSTCBStkPtr")
  | TCBExtPtr => &(base # "os_tcb" ->ₛ "OSTCBExtPtr")
  | TCBStkBottom => &(base # "os_tcb" ->ₛ "OSTCBStkBottom")
  | TCBStkSize => &(base # "os_tcb" ->ₛ "OSTCBStkSize")
  | TCBOpt => &(base # "os_tcb" ->ₛ "OSTCBOpt")
  | TCBId => &(base # "os_tcb" ->ₛ "OSTCBId")
  | TCBNext => &(base # "os_tcb" ->ₛ "OSTCBNext")
  | TCBPrev => &(base # "os_tcb" ->ₛ "OSTCBPrev")
  | TCBEventPtr => &(base # "os_tcb" ->ₛ "OSTCBEventPtr")
  | TCBMsg => &(base # "os_tcb" ->ₛ "OSTCBMsg")
  | TCBFlagNode => &(base # "os_tcb" ->ₛ "OSTCBFlagNode")
  | TCBFlagsRdy => &(base # "os_tcb" ->ₛ "OSTCBFlagsRdy")
  | TCBPadding42 => base + 42
  | TCBPadding43 => base + 43
  | TCBDly => &(base # "os_tcb" ->ₛ "OSTCBDly")
  | TCBStat => &(base # "os_tcb" ->ₛ "OSTCBStat")
  | TCBStatPend => &(base # "os_tcb" ->ₛ "OSTCBStatPend")
  | TCBPrio => &(base # "os_tcb" ->ₛ "OSTCBPrio")
  | TCBX => &(base # "os_tcb" ->ₛ "OSTCBX")
  | TCBY => &(base # "os_tcb" ->ₛ "OSTCBY")
  | TCBBitX => &(base # "os_tcb" ->ₛ "OSTCBBitX")
  | TCBBitY => &(base # "os_tcb" ->ₛ "OSTCBBitY")
  | TCBDelReq => &(base # "os_tcb" ->ₛ "OSTCBDelReq")
  | TCBTaskName => &(base # "os_tcb" ->ₛ "OSTCBTaskName")
  | TCBReg0 => &(base # "os_tcb" ->ₛ "OSTCBRegTbl")
  end.

(** Padding has been initialized by the pool clear.  [None] forgets its value,
    not its initialization; named fields keep their ordinary undef meaning. *)
Definition tcb_padding_cell (p : addr) (observation : option Z) : Assertion :=
  match observation with
  | Some byte => p # UChar |-> byte
  | None => EX byte, p # UChar |-> byte
  end.

Lemma tcb_padding_cell_forget : forall p observation,
  tcb_padding_cell p observation |-- tcb_padding_cell p None.
Proof.
  intros p [byte|]; [unfold tcb_padding_cell; Exists byte; entailer!|reflexivity].
Qed.

Lemma tcb_padding_cell_initialized_byte : forall p observation,
  tcb_padding_cell p observation |--
  EX byte, coq_prop (observation = None \/ observation = Some byte) && p # UChar |-> byte.
Proof.
  intros p [byte|]; unfold tcb_padding_cell.
  - Exists byte; entailer!.
  - Intros byte; Exists byte; entailer!.
Qed.

Lemma tcb_padding_cell_restore : forall p observation byte,
  observation = None \/ observation = Some byte ->
  p # UChar |-> byte |-- tcb_padding_cell p observation.
Proof.
  intros p observation byte Hmatch.
  destruct Hmatch as [Hnone | Hsome].
  - rewrite Hnone. unfold tcb_padding_cell. Exists byte. entailer!.
  - rewrite Hsome. reflexivity.
Qed.

Definition tcb_cell
  (base : addr) (field : TCBField) (value : option Z) : Assertion :=
  let p := tcb_field_address base field in
  match field with
  | TCBStkPtr | TCBExtPtr | TCBStkBottom | TCBNext | TCBPrev
  | TCBEventPtr | TCBMsg | TCBFlagNode | TCBTaskName =>
      match value with Some v => p # Ptr |-> v | None => p # Ptr |->_ end
  | TCBReg0 =>
      match value with
      | Some v => UIntArray.full p 1 [v]
      | None => UIntArray.undef_full p 1
      end
  | TCBStkSize | TCBDly =>
      match value with Some v => p # UInt |-> v | None => p # UInt |->_ end
  | TCBOpt | TCBId | TCBFlagsRdy =>
      match value with Some v => p # UShort |-> v | None => p # UShort |->_ end
  | TCBPadding42 | TCBPadding43 => tcb_padding_cell p value
  | _ =>
      match value with Some v => p # UChar |-> v | None => p # UChar |->_ end
  end.

(** Conditional OS_EVENT_MULTI_EN fields, using the actual C field names.
    [array] is an OS_EVENT ** array address, not the first Event in that
    array; [ready] is an OS_EVENT * value.  This is a two-field slice, not
    a claim that the 64-byte, Multi-disabled whole-TCB layout contains it. *)
Definition task_multi_fields_rep (base array ready : addr) : Assertion :=
  &(base # "os_tcb" ->ₛ "OSTCBEventMultiPtr") # Ptr |-> array **
  &(base # "os_tcb" ->ₛ "OSTCBEventMultiRdy") # Ptr |-> ready.

Definition tcb64_fields_rep
  (base : addr) (fields : list TCBField) (image : TCBCommonImage)
  : Assertion :=
  TaskFieldStorage.store_fields TCBField_eq_dec (tcb_cell base) fields image.

Definition tcb64_storage_rep (base : addr) (image : TCBCommonImage)
  : Assertion := tcb64_fields_rep base tcb_fields image.

Definition tcb64_storage_without
  (base : addr) (field : TCBField) (image : TCBCommonImage)
  : Assertion :=
  tcb64_fields_rep base (remove TCBField_eq_dec field tcb_fields) image.

Lemma tcb64_fields_rep_off_field : forall fields base image f value,
  ~ In f fields ->
  tcb64_fields_rep base fields (tcb_write image f value) =
  tcb64_fields_rep base fields image.
Proof.
  intros; apply TaskFieldStorage.store_fields_update_unlisted; assumption.
Qed.

Lemma tcb64_fields_rep_split : forall fields base image f,
  NoDup fields -> In f fields ->
  tcb64_fields_rep base fields image |--
    tcb_cell base f (image f) **
    tcb64_fields_rep base (remove TCBField_eq_dec f fields) image.
Proof.
  intros; apply TaskFieldStorage.store_fields_split_field; assumption.
Qed.

Lemma tcb64_fields_rep_merge : forall fields base image f,
  NoDup fields -> In f fields ->
  tcb_cell base f (image f) **
    tcb64_fields_rep base (remove TCBField_eq_dec f fields) image |--
  tcb64_fields_rep base fields image.
Proof.
  intros; apply TaskFieldStorage.store_fields_merge_field; assumption.
Qed.

Lemma tcb64_storage_split : forall base image f,
  tcb64_storage_rep base image |--
  tcb_cell base f (image f) ** tcb64_storage_without base f image.
Proof.
  intros; apply tcb64_fields_rep_split;
    [apply tcb_fields_nodup | apply tcb_fields_complete].
Qed.

Lemma tcb64_storage_merge : forall base image f,
  tcb_cell base f (image f) ** tcb64_storage_without base f image |--
  tcb64_storage_rep base image.
Proof.
  intros; apply tcb64_fields_rep_merge;
    [apply tcb_fields_nodup | apply tcb_fields_complete].
Qed.

Lemma tcb64_fields_rep_merge_updated : forall fields base image f value,
  NoDup fields -> In f fields ->
  tcb_cell base f value **
    tcb64_fields_rep base (remove TCBField_eq_dec f fields) image |--
  tcb64_fields_rep base fields (tcb_write image f value).
Proof.
  intros; apply TaskFieldStorage.store_fields_merge_updated_field; assumption.
Qed.

Lemma tcb64_storage_merge_updated : forall base image f value,
  tcb_cell base f value ** tcb64_storage_without base f image |--
  tcb64_storage_rep base (tcb_write image f value).
Proof.
  intros; unfold tcb64_storage_rep, tcb64_storage_without.
  apply tcb64_fields_rep_merge_updated;
    [apply tcb_fields_nodup|apply tcb_fields_complete].
Qed.

(** The configured image type is owned by TaskStateDef and is shared by
    lifecycle allocations.  This file supplies its physical interpretation;
    all other configuration switches still use the selected native values. *)
Definition tcb_layout_fields (multi : bool) : list TCBLayoutField :=
  map TCBCommonField (firstn 9 tcb_fields) ++
  (if multi then [TCBEventMultiPtr; TCBEventMultiRdy] else []) ++
  map TCBCommonField (skipn 9 tcb_fields).

Definition tcb_layout_addr (multi : bool) (sg : StableGlobVars) (tid : TaskID) : addr :=
  sg.(g_OSTCBTbl) + tid * tcb_layout_size multi.

Lemma tcb_layout_addr_no_multi : forall sg tid,
  tcb_layout_addr false sg tid = tcb64_addr sg tid.
Proof. reflexivity. Qed.

Lemma tcb_layout_addr_injective : forall multi sg first second,
  tcb_layout_addr multi sg first = tcb_layout_addr multi sg second -> first = second.
Proof. intros [] sg first second; unfold tcb_layout_addr, tcb_layout_size; lia. Qed.

(** One configured pool address for live, free and private TCBs and all
    pointers into that pool. [tcb64_addr] remains the fixed-layout view. *)
Definition task_slot_addr (sg : StableGlobVars) (tid : TaskID) : addr :=
  sg.(g_OSTCBTbl) + tid * tcb_configured_size
    sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile).

Lemma task_slot_addr_object_size : forall sg tid,
  task_slot_addr sg tid = sg.(g_OSTCBTbl) + tid * task_object_size sg.(osKernelConfig).
Proof. reflexivity. Qed.

Lemma task_slot_addr_selected_bounds : forall sg tid,
  selected_kernel_profile sg -> task_slot_in_range sg tid ->
  0 <= task_slot_addr sg tid /\ task_slot_addr sg tid + 64 <= 4294967295.
Proof.
  intros sg tid Hprofile Hslot.
  pose proof (selected_kernel_profile_tcb_slot_bounds sg tid Hprofile Hslot)
    as Hbounds.
  assert (Hconfig : tcb64_configuration sg.(osKernelConfig))
    by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (task_object_size_tcb64 _ Hconfig) as Hsize.
  rewrite task_slot_addr_object_size, <- Hsize; exact Hbounds.
Qed.

Lemma task_slot_addr_tcb64 : forall sg tid,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  task_slot_addr sg tid = tcb64_addr sg tid.
Proof.
  intros sg tid Hmulti Hprofile; unfold task_slot_addr; rewrite Hmulti, Hprofile; reflexivity.
Qed.

Lemma task_slot_addr_injective : forall sg first second,
  task_slot_addr sg first = task_slot_addr sg second -> first = second.
Proof.
  intros sg first second; unfold task_slot_addr, tcb_configured_size, tcb_layout_size.
  destruct sg.(osKernelConfig).(cfgEventMultiEnabled), sg.(osKernelConfig).(cfgTaskProfile); lia.
Qed.

Definition tcb_layout_field_offset (multi : bool) (field : TCBLayoutField) : Z :=
  match field with
  | TCBCommonField f => tcb_field_offset f +
      if andb multi (Z.leb 32 (tcb_field_offset f)) then 8 else 0
  | TCBEventMultiPtr => 32
  | TCBEventMultiRdy => 36
  | TCBCtxSwCtr => if multi then 64 else 56
  | TCBCyclesTot => if multi then 68 else 60
  | TCBCyclesStart => if multi then 72 else 64
  | TCBStkBase => if multi then 76 else 68
  | TCBStkUsed => if multi then 80 else 72
  end.

Definition tcb_layout_field_width (field : TCBLayoutField) : nat :=
  match field with TCBCommonField f => tcb_field_width f | _ => 4%nat end.

Lemma tcb_layout_covers_bytes : forall multi,
  flat_map (fun f => map (fun n => tcb_layout_field_offset multi f + Z.of_nat n)
    (seq 0 (tcb_layout_field_width f))) (tcb_layout_fields multi) =
  map Z.of_nat (seq 0 (Z.to_nat (tcb_layout_size multi))).
Proof. intros []; reflexivity. Qed.

Lemma tcb_layout_fields_nodup : forall multi, NoDup (tcb_layout_fields multi).
Proof. intros []; repeat constructor; simpl; intuition discriminate. Qed.

Lemma tcb_layout_common_field_in : forall multi f,
  In (TCBCommonField f) (tcb_layout_fields multi).
Proof. intros [] []; simpl; tauto. Qed.

(** Named C addresses are evaluated in the selected compilation unit.
    Padding is numerical and must move too: old padding keys 42/43 denote
    the corresponding bytes at 50/51 when Multi is enabled.  The numeric
    coverage theorem above is not an axiom about QCP's opaque field_address. *)
Definition tcb_layout_cell (multi : bool) (base : addr)
  (field : TCBLayoutField) (value : option Z) : Assertion :=
  match field with
  | TCBCommonField TCBPadding42 =>
      let p := base + (if multi then 50 else 42) in
      tcb_padding_cell p value
  | TCBCommonField TCBPadding43 =>
      let p := base + (if multi then 51 else 43) in
      tcb_padding_cell p value
  | TCBCommonField f => tcb_cell base f value
  | TCBEventMultiPtr =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBEventMultiPtr") in
      match value with Some v => p # Ptr |-> v | None => p # Ptr |->_ end
  | TCBEventMultiRdy =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBEventMultiRdy") in
      match value with Some v => p # Ptr |-> v | None => p # Ptr |->_ end
  | TCBCtxSwCtr =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBCtxSwCtr") in
      match value with Some v => p # UInt |-> v | None => p # UInt |->_ end
  | TCBCyclesTot =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBCyclesTot") in
      match value with Some v => p # UInt |-> v | None => p # UInt |->_ end
  | TCBCyclesStart =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBCyclesStart") in
      match value with Some v => p # UInt |-> v | None => p # UInt |->_ end
  | TCBStkBase =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBStkBase") in
      match value with Some v => p # Ptr |-> v | None => p # Ptr |->_ end
  | TCBStkUsed =>
      let p := &(base # "os_tcb" ->ₛ "OSTCBStkUsed") in
      match value with Some v => p # UInt |-> v | None => p # UInt |->_ end
  end.

Definition tcb_layout_image (common : TCBCommonImage) (array ready : option Z)
  (switches cycles start stack_base used : option Z)
  : TCBLayoutImage :=
  fun field => match field with TCBCommonField f => common f
    | TCBEventMultiPtr => array | TCBEventMultiRdy => ready
    | TCBCtxSwCtr => switches | TCBCyclesTot => cycles | TCBCyclesStart => start
    | TCBStkBase => stack_base | TCBStkUsed => used end.

Definition tcb_layout_common_image (image : TCBLayoutImage) : TCBCommonImage :=
  fun field => image (TCBCommonField field).

(** Lift existing common-field write sequences without reimplementing
    their status/timeout semantics or touching the conditional pointers. *)
Definition tcb_layout_update_common (update : TCBCommonImage -> TCBCommonImage)
  (image : TCBLayoutImage) : TCBLayoutImage :=
  tcb_layout_image (update (tcb_layout_common_image image))
    (image TCBEventMultiPtr) (image TCBEventMultiRdy)
    (image TCBCtxSwCtr) (image TCBCyclesTot) (image TCBCyclesStart)
    (image TCBStkBase) (image TCBStkUsed).

Lemma tcb_layout_image_eta : forall image,
  tcb_layout_image (tcb_layout_common_image image)
    (image TCBEventMultiPtr) (image TCBEventMultiRdy)
    (image TCBCtxSwCtr) (image TCBCyclesTot) (image TCBCyclesStart)
    (image TCBStkBase) (image TCBStkUsed) = image.
Proof. intros; apply functional_extensionality; intros []; reflexivity. Qed.

Definition tcb_layout_write :=
  @field_update TCBLayoutField (option Z) TCBLayoutField_eq_dec.

Definition tcb_layout_storage_rep (multi : bool) (base : addr)
  (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (tcb_layout_fields multi) image.

Definition tcb_layout_storage_without_field (multi : bool) (base : addr)
  (image : TCBLayoutImage) (field : TCBLayoutField) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (remove TCBLayoutField_eq_dec field (tcb_layout_fields multi)) image.

Lemma tcb_layout_storage_split_field : forall multi base image field,
  In field (tcb_layout_fields multi) ->
  tcb_layout_storage_rep multi base image |--
  tcb_layout_cell multi base field (image field) **
    tcb_layout_storage_without_field multi base image field.
Proof.
  intros; apply TaskFieldStorage.store_fields_split_field;
    [apply tcb_layout_fields_nodup|assumption].
Qed.

Lemma tcb_layout_storage_merge_field : forall multi base image field,
  In field (tcb_layout_fields multi) ->
  tcb_layout_cell multi base field (image field) **
    tcb_layout_storage_without_field multi base image field |--
  tcb_layout_storage_rep multi base image.
Proof.
  intros; apply TaskFieldStorage.store_fields_merge_field;
    [apply tcb_layout_fields_nodup|assumption].
Qed.

Lemma tcb_layout_storage_merge_updated_field : forall multi base image field value,
  In field (tcb_layout_fields multi) ->
  tcb_layout_cell multi base field value **
    tcb_layout_storage_without_field multi base image field |--
  tcb_layout_storage_rep multi base (tcb_layout_write image field value).
Proof.
  intros; apply TaskFieldStorage.store_fields_merge_updated_field;
    [apply tcb_layout_fields_nodup|assumption].
Qed.

Lemma tcb_layout_no_multi_rep_equiv : forall base image,
  tcb_layout_storage_rep false base image --||--
    tcb64_storage_rep base (tcb_layout_common_image image).
Proof.
  intros; unfold tcb_layout_storage_rep, tcb64_storage_rep, tcb64_fields_rep.
  unfold tcb_layout_fields, tcb_fields; cbn [map firstn skipn app].
  repeat rewrite TaskFieldStorage.store_fields_cons by
    (repeat constructor; simpl; intuition discriminate).
  rewrite !TaskFieldStorage.store_fields_nil.
  split; reflexivity.
Qed.

Definition tcb_layout_without_multi (base : addr) (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec TCBEventMultiRdy
      (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_layout_fields true))) image.

Definition tcb_layout_set_multi (image : TCBLayoutImage) (array ready : addr)
  : TCBLayoutImage :=
  tcb_layout_write (tcb_layout_write image TCBEventMultiPtr (Some array))
    TCBEventMultiRdy (Some ready).

(** The profile fields are in the same object/image as the common TCB fields,
    not an independently owned side record. Other switches retain the selected
    16-bit flags, create-ext, delete, names, one register and zero TLS profile. *)
Definition tcb_profile_fields : list TCBLayoutField :=
  [TCBCtxSwCtr; TCBCyclesTot; TCBCyclesStart; TCBStkBase; TCBStkUsed].

Definition tcb_configured_fields (multi profile : bool) : list TCBLayoutField :=
  map TCBCommonField (firstn 9 tcb_fields) ++
  (if multi then [TCBEventMultiPtr; TCBEventMultiRdy] else []) ++
  map TCBCommonField (firstn 14 (skipn 9 tcb_fields)) ++
  (if profile then tcb_profile_fields else []) ++
  map TCBCommonField (skipn 23 tcb_fields).

Definition tcb_configured_field_offset (multi profile : bool)
  (field : TCBLayoutField) : Z :=
  tcb_layout_field_offset multi field +
  match field with
  | TCBCommonField common =>
      if andb profile (Z.leb 56 (tcb_field_offset common)) then 20 else 0
  | _ => 0
  end.

Lemma tcb_configured_layout_covers_bytes : forall multi profile,
  flat_map (fun field =>
    map (fun n => tcb_configured_field_offset multi profile field + Z.of_nat n)
      (seq 0 (tcb_layout_field_width field))) (tcb_configured_fields multi profile) =
  map Z.of_nat (seq 0 (Z.to_nat (tcb_configured_size multi profile))).
Proof. intros [] []; reflexivity. Qed.

Lemma tcb_configured_fields_nodup : forall multi profile,
  NoDup (tcb_configured_fields multi profile).
Proof. intros [] []; repeat constructor; simpl; intuition discriminate. Qed.

Lemma tcb_configured_common_field_in : forall multi profile field,
  In (TCBCommonField field) (tcb_configured_fields multi profile).
Proof. intros [] [] []; simpl; tauto. Qed.

Lemma tcb_configured_profile_field_in : forall multi field,
  In field tcb_profile_fields -> In field (tcb_configured_fields multi true).
Proof. intros [] field Hin; simpl in *; tauto. Qed.

Definition tcb_configured_storage_rep (multi profile : bool) (base : addr)
  (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (tcb_configured_fields multi profile) image.

Definition tcb_configured_storage_without_field (multi profile : bool) (base : addr)
  (image : TCBLayoutImage) (field : TCBLayoutField) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (remove TCBLayoutField_eq_dec field (tcb_configured_fields multi profile)) image.

Lemma tcb_configured_storage_no_profile : forall multi base image,
  tcb_configured_storage_rep multi false base image = tcb_layout_storage_rep multi base image.
Proof. intros [] base image; reflexivity. Qed.

Lemma tcb_configured_storage_split_field : forall multi profile base image field,
  In field (tcb_configured_fields multi profile) ->
  tcb_configured_storage_rep multi profile base image |--
    tcb_layout_cell multi base field (image field) **
      tcb_configured_storage_without_field multi profile base image field.
Proof.
  intros; apply TaskFieldStorage.store_fields_split_field;
    [apply tcb_configured_fields_nodup|assumption].
Qed.

Lemma tcb_configured_storage_merge_field : forall multi profile base image field,
  In field (tcb_configured_fields multi profile) ->
  tcb_layout_cell multi base field (image field) **
    tcb_configured_storage_without_field multi profile base image field |--
      tcb_configured_storage_rep multi profile base image.
Proof.
  intros; apply TaskFieldStorage.store_fields_merge_field;
    [apply tcb_configured_fields_nodup|assumption].
Qed.

Lemma tcb_configured_storage_merge_updated_field : forall multi profile base image field value,
  In field (tcb_configured_fields multi profile) ->
  tcb_layout_cell multi base field value **
    tcb_configured_storage_without_field multi profile base image field |--
      tcb_configured_storage_rep multi profile base (tcb_layout_write image field value).
Proof.
  intros; apply TaskFieldStorage.store_fields_merge_updated_field;
    [apply tcb_configured_fields_nodup|assumption].
Qed.

Lemma tcb_layout_set_multi_fields : forall image array ready,
  tcb_layout_set_multi image array ready TCBEventMultiPtr = Some array /\
  tcb_layout_set_multi image array ready TCBEventMultiRdy = Some ready /\
  forall field, tcb_layout_set_multi image array ready (TCBCommonField field) =
    image (TCBCommonField field).
Proof. intros; split; [reflexivity|]; split; [reflexivity|]; intros []; reflexivity. Qed.

Lemma tcb_layout_storage_split_multi : forall base image array ready,
  image TCBEventMultiPtr = Some array -> image TCBEventMultiRdy = Some ready ->
  tcb_layout_storage_rep true base image |--
    task_multi_fields_rep base array ready ** tcb_layout_without_multi base image.
Proof.
  intros base image array ready Harray Hready; unfold tcb_layout_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (tcb_layout_fields true) image TCBEventMultiPtr
    (tcb_layout_fields_nodup true) ltac:(simpl; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_layout_fields true)) image TCBEventMultiRdy
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)).
  rewrite Harray, Hready; unfold tcb_layout_without_multi, task_multi_fields_rep.
  cbn [tcb_layout_cell]; entailer!.
Qed.

Lemma tcb_layout_storage_merge_multi : forall base image array ready,
  task_multi_fields_rep base array ready ** tcb_layout_without_multi base image |--
    tcb_layout_storage_rep true base (tcb_layout_set_multi image array ready).
Proof.
  intros base image array ready.
  set (written := tcb_layout_set_multi image array ready).
  destruct (tcb_layout_set_multi_fields image array ready) as [Harray [Hready Hcommon]].
  fold written in Harray, Hready, Hcommon.
  assert (Hrest : tcb_layout_without_multi base written = tcb_layout_without_multi base image).
  { unfold tcb_layout_without_multi, written, tcb_layout_set_multi, tcb_layout_write.
    repeat rewrite TaskFieldStorage.store_fields_update_unlisted by (simpl; intuition discriminate).
    reflexivity. }
  rewrite <- Hrest.
  change ((tcb_layout_cell true base TCBEventMultiPtr (Some array) **
    tcb_layout_cell true base TCBEventMultiRdy (Some ready)) **
    tcb_layout_without_multi base written |-- tcb_layout_storage_rep true base written).
  rewrite <- Harray, <- Hready.
  unfold tcb_layout_without_multi, tcb_layout_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_layout_fields true)) written TCBEventMultiRdy
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (tcb_layout_fields true) written TCBEventMultiPtr
    (tcb_layout_fields_nodup true) ltac:(simpl; tauto)).
  entailer!.
Qed.

(** Removing the two Multi pointers must retain the optional profiling cells
    as well as every common field. *)
Definition tcb_configured_without_multi (profile : bool) (base : addr)
  (image : TCBLayoutImage) : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec TCBEventMultiRdy
      (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true profile))) image.

Lemma tcb_configured_storage_split_multi : forall profile base image array ready,
  image TCBEventMultiPtr = Some array -> image TCBEventMultiRdy = Some ready ->
  tcb_configured_storage_rep true profile base image |--
    task_multi_fields_rep base array ready ** tcb_configured_without_multi profile base image.
Proof.
  intros profile base image array ready Harray Hready; unfold tcb_configured_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (tcb_configured_fields true profile) image TCBEventMultiPtr
    (tcb_configured_fields_nodup true profile) ltac:(destruct profile; simpl; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_split_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true profile)) image TCBEventMultiRdy
    ltac:(destruct profile; repeat constructor; simpl; intuition discriminate)
    ltac:(destruct profile; simpl; tauto)).
  rewrite Harray, Hready; unfold tcb_configured_without_multi, task_multi_fields_rep.
  cbn [tcb_layout_cell]; entailer!.
Qed.

Lemma tcb_configured_storage_merge_multi : forall profile base image array ready,
  task_multi_fields_rep base array ready ** tcb_configured_without_multi profile base image |--
    tcb_configured_storage_rep true profile base (tcb_layout_set_multi image array ready).
Proof.
  intros profile base image array ready.
  set (written := tcb_layout_set_multi image array ready).
  destruct (tcb_layout_set_multi_fields image array ready) as [Harray [Hready Hcommon]].
  fold written in Harray, Hready, Hcommon.
  assert (Hrest : tcb_configured_without_multi profile base written =
    tcb_configured_without_multi profile base image).
  { unfold tcb_configured_without_multi, written, tcb_layout_set_multi, tcb_layout_write.
    repeat rewrite TaskFieldStorage.store_fields_update_unlisted by
      (destruct profile; simpl; intuition discriminate).
    reflexivity. }
  rewrite <- Hrest.
  change ((tcb_layout_cell true base TCBEventMultiPtr (Some array) **
    tcb_layout_cell true base TCBEventMultiRdy (Some ready)) **
    tcb_configured_without_multi profile base written |--
    tcb_configured_storage_rep true profile base written).
  rewrite <- Harray, <- Hready.
  unfold tcb_configured_without_multi, tcb_configured_storage_rep.
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base)
    (remove TCBLayoutField_eq_dec TCBEventMultiPtr (tcb_configured_fields true profile)) written TCBEventMultiRdy
    ltac:(destruct profile; repeat constructor; simpl; intuition discriminate)
    ltac:(destruct profile; simpl; tauto)).
  sep_apply_l_atomic (TaskFieldStorage.store_fields_merge_field _ _ TCBLayoutField_eq_dec
    (tcb_layout_cell true base) (tcb_configured_fields true profile) written TCBEventMultiPtr
    (tcb_configured_fields_nodup true profile) ltac:(destruct profile; simpl; tauto)).
  entailer!.
Qed.
