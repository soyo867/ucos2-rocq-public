(** OSTaskQuery's ordered observations and same-heap byte-copy interface.
    Padding values are observed from their initialized native cells; an
    abstract [None] does not select a default byte. *)
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.array_abstraction.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.VC.code.core.mem_copy_goal_check.
Require Export Ucos2Verify.VC.code.core.spec.mem_copy_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Source/ABI interpretation to be instantiated by the actual selected
    compilation unit.  Numeric partition coverage alone proves none of these
    named-address equalities.  This is a static layout obligation, not a new
    runtime readiness or padding-initialization assumption. *)
Definition task_query_layout (sg : StableGlobVars) : Prop :=
  sizeof_alias_type "os_tcb" = 64 /\
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false /\
  sg.(osKernelConfig).(cfgTaskProfile) = false /\
  (forall tid field, task_slot_in_range sg tid ->
    tcb_field_address (task_slot_addr sg tid) field =
      task_slot_addr sg tid + tcb_field_offset field).

(** Error priority follows the actual C: invalid priority wins over NULL.
    Priority 63 is accepted.  There is no ISR/suspension/scheduler-lock guard. *)
Definition task_query_prefix_error (request output : Z) : option Z :=
  if andb (Z.ltb 63 request) (negb (Z.eqb request 255)) then Some 42
  else if Z.eqb output 0 then Some 9 else None.

Definition task_query_valid_arguments (request output : Z) : Prop :=
  (request <= 63 \/ request = 255) /\ output <> 0.

Lemma task_query_prefix_invalid_priority : forall request output,
  63 < request -> request <> 255 ->
  task_query_prefix_error request output = Some 42.
Proof.
  intros request output Hrange Hself; unfold task_query_prefix_error.
  rewrite (proj2 (Z.ltb_lt _ _) Hrange),
    (proj2 (Z.eqb_neq _ _) Hself); reflexivity.
Qed.

Lemma task_query_prefix_null_output : forall request,
  request <= 63 \/ request = 255 ->
  task_query_prefix_error request 0 = Some 9.
Proof.
  intros request [Hrange|Hself]; unfold task_query_prefix_error.
  - rewrite (proj2 (Z.ltb_ge _ _) Hrange); reflexivity.
  - subst request; reflexivity.
Qed.

Lemma task_query_prefix_valid_output : forall request output,
  request <= 63 \/ request = 255 -> output <> 0 ->
  task_query_prefix_error request output = None.
Proof.
  intros request output Hrequest Houtput; unfold task_query_prefix_error.
  rewrite (proj2 (Z.eqb_neq _ _) Houtput).
  destruct Hrequest as [Hrange|Hself].
  - rewrite (proj2 (Z.ltb_ge _ _) Hrange); reflexivity.
  - subst request; reflexivity.
Qed.

(** SELF admission is an actual reversible readable cut at acquisition.  It
    does not demand that the current pointer denote an entry-state live task,
    and it neither chooses nor restricts the later priority-table result. *)
Definition task_query_current_readable (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (caller : Assertion) (resolved : Z) : Prop :=
  0 <= resolved <= 63 /\ exists residual,
    (UCOS2_raw_rep sg s ** caller |--
      sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(SchedState).(curTaskID) **
      tcb_field_address (encode_task_link sg s.(SchedState).(curTaskID)) TCBPrio
        # UChar |-> resolved ** residual) /\
    (sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg s.(SchedState).(curTaskID) **
      tcb_field_address (encode_task_link sg s.(SchedState).(curTaskID)) TCBPrio
        # UChar |-> resolved ** residual |-- UCOS2_raw_rep sg s ** caller).

Definition task_query_self_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (request : Z) (caller : Assertion) : Prop :=
  request = 255 -> forall acquired,
    critical_region_interval critical sg invocation before acquired ->
    UCOS2_state_inv sg acquired ->
    exists resolved, task_query_current_readable sg acquired caller resolved.

Definition task_query_priority_resolution (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (caller : Assertion) (request resolved : Z) : Prop :=
  (request <> 255 /\ resolved = request) \/
  (request = 255 /\ task_query_current_readable sg s caller resolved).

Lemma task_query_explicit_priority_resolution : forall sg s caller request,
  request <> 255 -> task_query_priority_resolution sg s caller request request.
Proof. intros; left; auto. Qed.

(** The native merge predicates use the selected endian interpretation.
    Address validity and the original value range are retained so that the
    returned byte array reconstructs the SAME typed cell. *)
Definition task_query_word_encoding (width : nat) (p value : Z)
  (bytes : list Z) : Prop :=
  match width, bytes with
  | 1%nat, [byte] => byte = value /\ isvalidptr_char p /\ 0 <= value <= 255
  | 2%nat, [first; second] =>
      merge_short first second value /\ isvalidptr_short p /\ 0 <= value <= 65535
  | 4%nat, [first; second; third; fourth] =>
      merge_int first second third fourth value /\ isvalidptr_int p /\
      0 <= value <= Int.max_unsigned
  | _, _ => False
  end.

Lemma task_query_word_encoding_length : forall width p value bytes,
  task_query_word_encoding width p value bytes ->
  Zlength bytes = Z.of_nat width.
Proof.
  intros width p value bytes Hencoding.
  destruct width as [|[|[|[|[|width]]]]];
    destruct bytes as [|a [|b [|c [|d [|e bytes]]]]];
    cbn [task_query_word_encoding] in Hencoding; try contradiction; reflexivity.
Qed.

Lemma task_query_uchar_bytes : forall p value,
  p # UChar |-> value |--
    EX bytes, coq_prop (task_query_word_encoding 1 p value bytes) &&
      UCharArray.full p 1 bytes.
Proof.
  intros p value; unfold store_uchar; Intros.
  Exists [value].
  unfold task_query_word_encoding, UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  unfold store_uchar; entailer!.
Qed.

Lemma task_query_uint_bytes : forall p value,
  p # UInt |-> value |--
    EX bytes, coq_prop (task_query_word_encoding 4 p value bytes) &&
      UCharArray.full p 4 bytes.
Proof.
  intros p value; unfold store_uint, store_4byte.
  Intros first second third fourth.
  assert (Hmerge : merge_int
    (unsigned_last_nbits first 8) (unsigned_last_nbits second 8)
    (unsigned_last_nbits third 8) (unsigned_last_nbits fourth 8) value).
  { eapply merge_int_eqm; try apply byte_eqm_unsigned_last_8; eassumption. }
  pose proof (unsigned_Lastnbits_range first 8 ltac:(lia)) as Hfirst.
  pose proof (unsigned_Lastnbits_range second 8 ltac:(lia)) as Hsecond.
  pose proof (unsigned_Lastnbits_range third 8 ltac:(lia)) as Hthird.
  pose proof (unsigned_Lastnbits_range fourth 8 ltac:(lia)) as Hfourth.
  sep_apply_l_atomic (store_byte_cast' (p + 3) fourth).
  sep_apply_l_atomic (store_byte_cast' (p + 2) third).
  sep_apply_l_atomic (store_byte_cast' (p + 1) second).
  sep_apply_l_atomic (store_byte_cast' p first).
  Exists [unsigned_last_nbits first 8; unsigned_last_nbits second 8;
    unsigned_last_nbits third 8; unsigned_last_nbits fourth 8].
  unfold task_query_word_encoding, UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  replace (p + 2 * 1) with (p + 2) by lia.
  replace (p + 3 * 1) with (p + 3) by lia.
  unfold store_uchar; entailer!; try assumption.
  all: try solve [sepcon_assoc_change; cancel].
  all: unfold isvalidptr_int, isvalidptr_char in *; cbn in *; lia.
Qed.

Lemma task_query_ushort_bytes : forall p value,
  p # UShort |-> value |--
    EX bytes, coq_prop (task_query_word_encoding 2 p value bytes) &&
      UCharArray.full p 2 bytes.
Proof.
  intros p value; unfold store_ushort, store_2byte.
  Intros first second.
  assert (Hmerge : merge_short
    (unsigned_last_nbits first 8) (unsigned_last_nbits second 8) value).
  { eapply merge_short_eqm; try apply byte_eqm_unsigned_last_8; eassumption. }
  pose proof (unsigned_Lastnbits_range first 8 ltac:(lia)) as Hfirst.
  pose proof (unsigned_Lastnbits_range second 8 ltac:(lia)) as Hsecond.
  sep_apply_l_atomic (store_byte_cast' (p + 1) second).
  sep_apply_l_atomic (store_byte_cast' p first).
  Exists [unsigned_last_nbits first 8; unsigned_last_nbits second 8].
  unfold task_query_word_encoding, UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  unfold store_uchar; entailer!; try assumption; try entailer!;
    unfold isvalidptr_short, isvalidptr_char in *; cbn in *; lia.
Qed.

Lemma task_query_bytes_uint : forall p value bytes,
  task_query_word_encoding 4 p value bytes ->
  UCharArray.full p 4 bytes |-- p # UInt |-> value.
Proof.
  intros p value [|first [|second [|third [|fourth [|extra bytes]]]]]
    Hencoding; cbn [task_query_word_encoding] in Hencoding; try contradiction.
  destruct Hencoding as [Hmerge [Hvalid Hrange]].
  unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  replace (p + 2 * 1) with (p + 2) by lia.
  replace (p + 3 * 1) with (p + 3) by lia.
  unfold store_uchar, store_uint, store_4byte; Intros.
  Exists first second third fourth; entailer!.
Qed.

Lemma task_query_bytes_ushort : forall p value bytes,
  task_query_word_encoding 2 p value bytes ->
  UCharArray.full p 2 bytes |-- p # UShort |-> value.
Proof.
  intros p value [|first [|second [|extra bytes]]] Hencoding;
    cbn [task_query_word_encoding] in Hencoding; try contradiction.
  destruct Hencoding as [Hmerge [Hvalid Hrange]].
  unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1.
  replace (p + 0 * 1) with p by lia.
  replace (p + 1 * 1) with (p + 1) by lia.
  unfold store_uchar, store_ushort, store_2byte; Intros.
  Exists first second; entailer!.
Qed.

Lemma task_query_bytes_uchar : forall p value bytes,
  task_query_word_encoding 1 p value bytes ->
  UCharArray.full p 1 bytes |-- p # UChar |-> value.
Proof.
  intros p value [|byte [|extra bytes]] Hencoding;
    cbn [task_query_word_encoding] in Hencoding; try contradiction.
  destruct Hencoding as [-> _].
  unfold UCharArray.full, store_array.
  cbn [store_array_rec StoreUCharAsElement.storeA].
  change (sizeof(UCHAR)) with 1; replace (p + 0 * 1) with p by lia.
  entailer!.
Qed.

Definition task_query_field_encoding (base : addr) (field : TCBField)
  (observation : option Z) (bytes : list Z) : Prop :=
  exists value,
    (observation = Some value \/
      (observation = None /\ (field = TCBPadding42 \/ field = TCBPadding43))) /\
    task_query_word_encoding (tcb_field_width field)
      (tcb_field_address base field) value bytes.

Lemma task_query_ptr_bytes : forall p value,
  p # Ptr |-> value |--
    EX bytes, coq_prop (task_query_word_encoding 4 p value bytes) &&
      UCharArray.full p 4 bytes.
Proof.
  intros p value.
  sep_apply_l_atomic (store_ptr_store_uint p value eq_refl eq_refl).
  apply task_query_uint_bytes.
Qed.

Lemma task_query_bytes_ptr : forall p value bytes,
  task_query_word_encoding 4 p value bytes ->
  UCharArray.full p 4 bytes |-- p # Ptr |-> value.
Proof.
  intros p value bytes Hencoding.
  sep_apply_l_atomic (task_query_bytes_uint p value bytes Hencoding).
  apply kernel_store_uint_store_ptr.
Qed.

Lemma task_query_reg_single : forall p value,
  UIntArray.full p 1 [value] --||-- p # UInt |-> value.
Proof.
  intros; unfold UIntArray.full, store_array.
  cbn [store_array_rec StoreUIntAsElement.storeA].
  replace (p + 0 * sizeof(UINT)) with p by lia; split; entailer!.
Qed.

Lemma task_query_field_bytes : forall base field observation,
  (observation = None -> field = TCBPadding42 \/ field = TCBPadding43) ->
  tcb_cell base field observation |--
    EX bytes, coq_prop (task_query_field_encoding base field observation bytes) &&
      UCharArray.full (tcb_field_address base field)
        (Z.of_nat (tcb_field_width field)) bytes.
Proof.
  intros base field observation Hinitialized.
  destruct field; destruct observation as [value|];
    cbn [tcb_cell tcb_field_width tcb_padding_cell] in *;
    try (exfalso; specialize (Hinitialized eq_refl); intuition discriminate).
  all: try (rewrite task_query_reg_single).
  all: try (Intros value).
  all: first
    [match goal with |- ?p # Ptr |-> ?v |-- _ =>
      sep_apply_l_atomic (task_query_ptr_bytes p v) end |
     match goal with |- ?p # UInt |-> ?v |-- _ =>
      sep_apply_l_atomic (task_query_uint_bytes p v) end |
     match goal with |- ?p # UShort |-> ?v |-- _ =>
      sep_apply_l_atomic (task_query_ushort_bytes p v) end |
     match goal with |- ?p # UChar |-> ?v |-- _ =>
      sep_apply_l_atomic (task_query_uchar_bytes p v) end].
  all: Intros bytes; Exists bytes; entailer!;
    unfold task_query_field_encoding;
    exists value; split; [auto|assumption].
Qed.

Lemma task_query_bytes_field : forall base field observation bytes,
  task_query_field_encoding base field observation bytes ->
  UCharArray.full (tcb_field_address base field)
    (Z.of_nat (tcb_field_width field)) bytes |--
    tcb_cell base field observation.
Proof.
  intros base field observation bytes [value [Hobservation Hencoding]].
  destruct Hobservation as [Hsome | [Hnone Hpadding]].
  - subst observation; destruct field;
      cbn [tcb_cell tcb_padding_cell tcb_field_width] in *;
      try (rewrite task_query_reg_single);
      first [apply task_query_bytes_ptr | apply task_query_bytes_uint |
        apply task_query_bytes_ushort | apply task_query_bytes_uchar]; assumption.
  - subst observation; destruct Hpadding as [Hpadding | Hpadding];
      subst field; cbn [tcb_cell tcb_field_width] in *;
      sep_apply_l_atomic (task_query_bytes_uchar _ value bytes Hencoding);
      unfold tcb_padding_cell; Exists value; entailer!.
Qed.

Fixpoint task_query_field_arrays (base : addr) (fields : list TCBField)
  (chunks : list (list Z)) : Assertion :=
  match fields, chunks with
  | [], [] => emp
  | field :: rest, chunk :: pieces =>
      UCharArray.full (tcb_field_address base field)
        (Z.of_nat (tcb_field_width field)) chunk **
      task_query_field_arrays base rest pieces
  | _, _ => coq_prop False
  end.

Lemma task_query_fields_open_bytes : forall fields base image,
  NoDup fields ->
  (forall field, In field fields -> image field = None ->
    field = TCBPadding42 \/ field = TCBPadding43) ->
  tcb64_fields_rep base fields image |--
    EX chunks, coq_prop (Forall2
      (fun field chunk => task_query_field_encoding base field (image field) chunk)
      fields chunks) && task_query_field_arrays base fields chunks.
Proof.
  induction fields as [|field rest IH]; intros base image Hnodup Hinitialized.
  - unfold tcb64_fields_rep; rewrite TaskFieldStorage.store_fields_nil.
    Exists []; cbn [task_query_field_arrays]; entailer!; constructor.
  - inversion Hnodup as [|field0 rest0 Hfresh Hrest]; subst.
    unfold tcb64_fields_rep at 1.
    rewrite TaskFieldStorage.store_fields_cons by assumption.
    fold (tcb64_fields_rep base rest image).
    pose proof (task_query_field_bytes base field (image field)
      (Hinitialized field (or_introl eq_refl))) as Hopen.
    rewrite Hopen at 1.
    Intros chunk.
    sep_apply_l_atomic (IH base image Hrest
      (fun other Hin => Hinitialized other (or_intror Hin))).
    Intros pieces; Exists (chunk :: pieces).
    cbn [task_query_field_arrays]; entailer!; constructor; assumption.
Qed.

Lemma task_query_fields_restore_bytes : forall fields chunks base image,
  NoDup fields ->
  Forall2 (fun field chunk => task_query_field_encoding base field (image field) chunk)
    fields chunks ->
  task_query_field_arrays base fields chunks |-- tcb64_fields_rep base fields image.
Proof.
  intros fields chunks base image Hnodup Hencoding; revert Hnodup.
  induction Hencoding as [|field chunk rest pieces Hfield Hpieces IH]; intros Hnodup.
  - cbn [task_query_field_arrays]; unfold tcb64_fields_rep.
    rewrite TaskFieldStorage.store_fields_nil; reflexivity.
  - inversion Hnodup as [|field0 rest0 Hfresh Hrest]; subst.
    cbn [task_query_field_arrays].
    sep_apply_l_atomic (task_query_bytes_field base field (image field) chunk Hfield).
    sep_apply_l_atomic (IH Hrest).
    unfold tcb64_fields_rep; rewrite TaskFieldStorage.store_fields_cons by assumption.
    entailer!.
Qed.

Fixpoint task_query_fields_span (fields : list TCBField) (start finish : Z) : Prop :=
  match fields with
  | [] => start = finish
  | field :: rest => tcb_field_offset field = start /\
      task_query_fields_span rest (start + Z.of_nat (tcb_field_width field)) finish
  end.

Lemma task_query_fields_span_bound : forall fields start finish,
  task_query_fields_span fields start finish -> start <= finish.
Proof.
  induction fields as [|field rest IH]; intros start finish Hspan;
    cbn [task_query_fields_span] in Hspan; [lia|].
  destruct Hspan as [_ Hrest]; specialize (IH _ _ Hrest).
  pose proof (Nat2Z.is_nonneg (tcb_field_width field)); lia.
Qed.

Lemma task_query_arrays_merge : forall fields chunks base start finish,
  task_query_fields_span fields start finish ->
  (forall field, In field fields ->
    tcb_field_address base field = base + tcb_field_offset field) ->
  List.length fields = List.length chunks ->
  task_query_field_arrays base fields chunks |--
    UCharArray.full (base + start) (finish - start) (List.concat chunks).
Proof.
  induction fields as [|field rest IH]; intros chunks base start finish Hspan Hlayout Hlength.
  - destruct chunks; cbn in Hlength; [|discriminate].
    cbn [task_query_fields_span] in Hspan; subst finish.
    replace (start - start) with 0 by lia.
    cbn [task_query_field_arrays List.concat].
    unfold UCharArray.full, store_array; cbn [store_array_rec]; entailer!.
  - destruct chunks as [|chunk pieces]; cbn in Hlength; [discriminate|].
    cbn [task_query_fields_span] in Hspan.
    destruct Hspan as [Hoffset Hrest].
    pose proof (task_query_fields_span_bound _ _ _ Hrest) as Hbound.
    cbn [task_query_field_arrays List.concat].
    sep_apply_l_atomic (IH pieces base
      (start + Z.of_nat (tcb_field_width field)) finish Hrest
      (fun other Hin => Hlayout other (or_intror Hin)) ltac:(lia)).
    rewrite (Hlayout field (or_introl eq_refl)), Hoffset.
    change StoreUCharAsElement.sizeA with 1.
    replace (base + (start + Z.of_nat (tcb_field_width field))) with
      (base + start + Z.of_nat (tcb_field_width field) * 1) by lia.
    replace (finish - (start + Z.of_nat (tcb_field_width field))) with
      ((finish - start) - Z.of_nat (tcb_field_width field)) by lia.
    sep_apply_l_atomic (UCharArray.full_merge_to_full (base + start)
      (Z.of_nat (tcb_field_width field)) (finish - start) chunk (List.concat pieces)
      ltac:(pose proof (Nat2Z.is_nonneg (tcb_field_width field)); lia)).
    entailer!.
Qed.

Lemma task_query_arrays_split : forall fields chunks base image start finish,
  task_query_fields_span fields start finish ->
  (forall field, In field fields ->
    tcb_field_address base field = base + tcb_field_offset field) ->
  Forall2 (fun field chunk => task_query_field_encoding base field (image field) chunk)
    fields chunks ->
  UCharArray.full (base + start) (finish - start) (List.concat chunks) |--
    task_query_field_arrays base fields chunks.
Proof.
  intros fields chunks base image start finish Hspan Hlayout Hencoding.
  revert start finish Hspan Hlayout.
  induction Hencoding as [|field chunk rest pieces Hfield Hpieces IH];
    intros start finish Hspan Hlayout.
  - cbn [task_query_fields_span] in Hspan; subst finish.
    replace (start - start) with 0 by lia.
    cbn [task_query_field_arrays List.concat].
    unfold UCharArray.full, store_array; cbn [store_array_rec]; entailer!.
  - cbn [task_query_fields_span] in Hspan.
    destruct Hspan as [Hoffset Hrest].
    pose proof (task_query_fields_span_bound _ _ _ Hrest) as Hbound.
    destruct Hfield as [value [_ Hword]].
    pose proof (task_query_word_encoding_length _ _ _ _ Hword) as Hchunk.
    cbn [List.concat task_query_field_arrays].
    prop_apply (UCharArray.full_Zlength (base + start) (finish - start)
      (chunk ++ List.concat pieces)); Intros.
    assert (Hpieces_length : Zlength (List.concat pieces) = finish - start - Zlength chunk).
    { rewrite Zlength_app in H; lia. }
    rewrite <- Hchunk in Hbound.
    sep_apply_l_atomic (UCharArray.full_split_to_full (base + start)
      (Zlength chunk) (finish - start) (chunk ++ List.concat pieces) ltac:(lia)).
    rewrite sublist_app_exact1.
    rewrite (sublist_split_app_r _ _ (Zlength chunk) chunk (List.concat pieces))
      by (try reflexivity; lia).
    replace (Zlength chunk - Zlength chunk) with 0 by lia.
    rewrite <- Hpieces_length, sublist_self by reflexivity.
    change StoreUCharAsElement.sizeA with 1.
    rewrite Z.mul_1_r, Hchunk.
    replace (base + start + Z.of_nat (tcb_field_width field)) with
      (base + (start + Z.of_nat (tcb_field_width field))) by lia.
    replace (finish - start - Z.of_nat (tcb_field_width field)) with
      (finish - (start + Z.of_nat (tcb_field_width field))) by lia.
    replace (Zlength (List.concat pieces)) with
      (finish - (start + Z.of_nat (tcb_field_width field))) by lia.
    sep_apply_l_atomic (IH _ _ Hrest
      (fun other Hin => Hlayout other (or_intror Hin))).
    rewrite (Hlayout field (or_introl eq_refl)), Hoffset; entailer!.
Qed.

Definition task_query_image_serialization (base : addr) (image : TCBCommonImage)
  (bytes : list Z) : Prop :=
  exists chunks,
    Forall2 (fun field chunk => task_query_field_encoding base field (image field) chunk)
      tcb_fields chunks /\ bytes = List.concat chunks.

Lemma task_query_tcb_open_bytes : forall base image,
  (forall field, tcb_field_address base field = base + tcb_field_offset field) ->
  (forall field, image field = None -> field = TCBPadding42 \/ field = TCBPadding43) ->
  tcb64_storage_rep base image |--
    EX bytes, coq_prop (task_query_image_serialization base image bytes) &&
      UCharArray.full base 64 bytes.
Proof.
  intros base image Hlayout Hinitialized; unfold tcb64_storage_rep.
  sep_apply_l_atomic (task_query_fields_open_bytes tcb_fields base image
    tcb_fields_nodup (fun field _ => Hinitialized field)).
  Intros chunks; Exists (List.concat chunks).
  sep_apply_l_atomic (task_query_arrays_merge tcb_fields chunks base 0 64
    ltac:(repeat split; reflexivity) (fun field _ => Hlayout field)
    ltac:(eapply Forall2_length; eassumption)).
  replace (base + 0) with base by lia.
  entailer!; exists chunks; auto.
Qed.

Lemma task_query_tcb_restore_bytes : forall base image bytes,
  (forall field, tcb_field_address base field = base + tcb_field_offset field) ->
  task_query_image_serialization base image bytes ->
  UCharArray.full base 64 bytes |-- tcb64_storage_rep base image.
Proof.
  intros base image bytes Hlayout [chunks [Hencoding ->]].
  replace base with (base + 0) at 1 by lia.
  sep_apply_l_atomic (task_query_arrays_split tcb_fields chunks base image 0 64
    ltac:(repeat split; reflexivity) (fun field _ => Hlayout field) Hencoding).
  unfold tcb64_storage_rep.
  apply task_query_fields_restore_bytes; [apply tcb_fields_nodup|exact Hencoding].
Qed.

Lemma task_query_image_serialization_length : forall base image bytes,
  task_query_image_serialization base image bytes -> Zlength bytes = 64.
Proof.
  intros base image bytes [chunks [Hchunks ->]].
  assert (Hlength : forall fields chunks,
    Forall2 (fun field chunk => task_query_field_encoding base field (image field) chunk)
      fields chunks ->
    Zlength (List.concat chunks) = fold_right (fun field total => Z.of_nat (tcb_field_width field) + total) 0 fields).
  { intros fields pieces Hpieces; induction Hpieces; cbn; [reflexivity|].
    rewrite Zlength_app, IHHpieces.
    destruct H as [value [_ Hvalue]].
    rewrite (task_query_word_encoding_length _ _ _ _ Hvalue); reflexivity. }
  rewrite (Hlength _ _ Hchunks); reflexivity.
Qed.

(** The snapshot records concrete encoding witnesses extracted from the native
    source heap.  The residual owns every other original kernel resource. *)
Definition task_query_source_byte_view (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (tid : TaskID) (t : TaskAbstractState)
  (bytes : list Z) : Prop :=
  s.(TskState).(inUsedTaskStates) tid = Some t /\
  task_query_image_serialization (task_slot_addr sg tid) (task_tcb64_image sg t) bytes.

Definition task_query_raw_frame sg s : Assertion :=
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Definition task_query_source_residual sg s tid : Assertion :=
  task_public_storage_without_task sg s.(TskState) tid ** task_query_raw_frame sg s.

Lemma task_query_raw_split : forall sg s,
  UCOS2_raw_rep sg s --||--
    task_public_storage sg s.(TskState) ** task_query_raw_frame sg s.
Proof.
  intros; unfold UCOS2_raw_rep, task_shared_rep, task_query_raw_frame,
    UCOS2_raw_rep_missing_task_storage_sched; split; entailer!.
Qed.

Lemma task_query_source_byte_view_length : forall sg s tid t bytes,
  task_query_source_byte_view sg s tid t bytes -> Zlength bytes = 64.
Proof.
  intros sg s tid t bytes [_ Hbytes].
  exact (task_query_image_serialization_length _ _ _ Hbytes).
Qed.

Lemma task_query_source_open_bytes : forall sg s tid t,
  task_query_layout sg -> task_slot_in_range sg tid ->
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  UCOS2_raw_rep sg s |-- EX bytes,
    coq_prop (task_query_source_byte_view sg s tid t bytes) &&
    (UCharArray.full (task_slot_addr sg tid) 64 bytes ** task_query_source_residual sg s tid).
Proof.
  intros sg s tid t [Hsize [Hmulti [Hprofile Hlayout]]] Hslot Hlookup.
  rewrite task_query_raw_split.
  sep_apply_l_atomic (task_public_storage_split_task sg s.(TskState) tid t Hlookup).
  rewrite (used_task_rep_tcb64 sg tid t Hmulti Hprofile).
  rewrite <- (task_slot_addr_tcb64 sg tid Hmulti Hprofile).
  sep_apply_l_atomic (task_query_tcb_open_bytes (task_slot_addr sg tid)
    (task_tcb64_image sg t) (fun field => Hlayout tid field Hslot)
    ltac:(intros field; destruct field; cbn [task_tcb64_image];
      intros Hnone; try discriminate; auto)).
  Intros bytes; Exists bytes.
  unfold task_query_source_byte_view, task_query_source_residual; entailer!.
Qed.

Lemma task_query_source_byte_view_restore : forall sg s tid t bytes,
  task_query_layout sg -> task_slot_in_range sg tid ->
  task_query_source_byte_view sg s tid t bytes ->
  UCharArray.full (task_slot_addr sg tid) 64 bytes **
    task_query_source_residual sg s tid |--
    UCOS2_raw_rep sg s.
Proof.
  intros sg s tid t bytes [Hsize [Hmulti [Hprofile Hlayout]]] Hslot [Hlookup Hencoding].
  sep_apply_l_atomic (task_query_tcb_restore_bytes (task_slot_addr sg tid)
    (task_tcb64_image sg t) bytes (fun field => Hlayout tid field Hslot) Hencoding).
  rewrite (task_slot_addr_tcb64 sg tid Hmulti Hprofile).
  rewrite <- (used_task_rep_tcb64 sg tid t Hmulti Hprofile).
  unfold task_query_source_residual.
  sep_apply_l_atomic (task_public_storage_merge_task sg s.(TskState) tid t Hlookup).
  rewrite task_query_raw_split; entailer!.
Qed.

(** The protected observation is either an exact error or a complete source
    snapshot.  Neither free nor reserved slots require source bytes. *)
Definition task_query_protected_result (sg : StableGlobVars)
  (acquired : UCOS2_Verify_State) (caller : Assertion) (request error : Z)
  (snapshot : option (list Z)) : Prop :=
  exists resolved, task_query_priority_resolution sg acquired caller request resolved /\
    match acquired.(TskState).(prioTbl) resolved with
    | PTFree => error = 41 /\ snapshot = None
    | PTReserved => error = 67 /\ snapshot = None
    | PTTask tid => error = 0 /\ exists t bytes,
        snapshot = Some bytes /\
        task_query_source_byte_view sg acquired tid t bytes
    end.

Definition task_query_output_result (snapshot : option (list Z))
  (before after : list (option Z)) : Prop :=
  match snapshot with None => after = before | Some bytes => after = map (@Some Z) bytes end.

(** Both critical intervals are real registered environment intervals.  Query
    does not update the acquired kernel.  Release may change it AFTER copying,
    so after need not contain the byte snapshot.  Copied pointer values give
    no ownership of the pointees and do not publish a new kernel task. *)
Definition task_query_call_result (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask request output error : Z)
  (caller : Assertion)
  (before after : UCOS2_Verify_State)
  (old_output new_output : list (option Z)) : Prop :=
  match task_query_prefix_error request output with
  | Some early => error = early /\ after = before /\ new_output = old_output
  | None => exists acquired saved snapshot,
      interrupt_saved_value mask saved /\
      critical_region_interval critical sg invocation before acquired /\
      UCOS2_state_inv sg acquired /\
      task_query_protected_result sg acquired caller request error snapshot /\
      task_query_output_result snapshot old_output new_output /\
      critical_region_interval critical sg invocation acquired after
  end.

Lemma task_query_call_result_early_error :
  forall critical sg invocation mask request output error caller before old_output,
  task_query_prefix_error request output = Some error ->
  task_query_call_result critical sg invocation mask request output error caller
    before before old_output old_output.
Proof. intros; unfold task_query_call_result; rewrite H; auto. Qed.

(** Resolve SELF from its reversible acquired-field view, then observe the
    actual table entry.  A live entry copies the complete byte serialization;
    the two error cases retain every old output byte.  None of these reads
    changes the acquired kernel state. *)
Definition task_query_protected_program (sg : StableGlobVars)
  (caller : Assertion) (request : Z) (old_output : list (option Z))
  : program UCOS2_Verify_State (Z * list (option Z)) :=
  StateRelMonad.bind
    (get (fun s resolved => task_query_priority_resolution sg s caller request resolved))
    (fun resolved => StateRelMonad.bind (get' (fun s => s.(TskState).(prioTbl) resolved))
      (fun entry => match entry with
       | PTFree => StateRelMonad.ret (41, old_output)
       | PTReserved => StateRelMonad.ret (67, old_output)
       | PTTask tid => StateRelMonad.bind
           (get (fun s bytes => exists t, task_query_source_byte_view sg s tid t bytes))
           (fun bytes => StateRelMonad.ret (0, map (@Some Z) bytes))
       end)).

(** The argument checks precede Save.  Acquisition and release are separate
    registered intervals, so the returned kernel need not still contain the
    copied TCB.  The result retains both the C error code and exact output. *)
Definition task_query_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (caller : Assertion)
  (request output : Z) (old_output : list (option Z))
  : program UCOS2_Verify_State (Z * list (option Z)) :=
  match task_query_prefix_error request output with
  | Some early => StateRelMonad.ret (early, old_output)
  | None => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
      (fun _ => StateRelMonad.bind (task_query_protected_program sg caller request old_output)
        (fun result => StateRelMonad.bind
          (update (critical_region_interval critical sg invocation))
          (fun _ => StateRelMonad.ret result)))
  end.

Definition task_query_safe critical sg invocation before caller request output old_output
  (X : Z -> list (option Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_query_program critical sg invocation caller request output old_output)
    (fun result state => X (fst result) (snd result) state).

Lemma task_query_protected_program_iff :
  forall sg caller request old_output before error new_output after,
  task_query_protected_program sg caller request old_output before (error, new_output) after <->
  after = before /\ exists snapshot,
    task_query_protected_result sg before caller request error snapshot /\
    task_query_output_result snapshot old_output new_output.
Proof.
  intros sg caller request old_output before error new_output after; split.
  - intros [resolved [read [[Hresolution Hread]
      [entry [looked [[Hentry Hlooked] Hprogram]]]]]].
    subst read looked entry.
    destruct (before.(TskState).(prioTbl) resolved) as [| |tid] eqn:Hentry.
    + destruct Hprogram as [Hresult Hafter]; inversion Hresult; subst.
      split; [reflexivity|]. exists None; split; [|reflexivity].
      exists resolved; split; [exact Hresolution|rewrite Hentry; auto].
    + destruct Hprogram as [Hresult Hafter]; inversion Hresult; subst.
      split; [reflexivity|]. exists None; split; [|reflexivity].
      exists resolved; split; [exact Hresolution|rewrite Hentry; auto].
    + destruct Hprogram as [bytes [copied [[[t Hbytes] Hcopied] [Hresult Hafter]]]].
      inversion Hresult; subst.
      split; [reflexivity|]. exists (Some bytes); split; [|reflexivity].
      exists resolved; split; [exact Hresolution|].
      rewrite Hentry; split; [reflexivity|]. exists t, bytes; auto.
  - intros [-> [snapshot [[resolved [Hresolution Hresult]] Houtput]]].
    exists resolved, before; split; [split; [exact Hresolution|reflexivity]|].
    exists (before.(TskState).(prioTbl) resolved), before.
    split; [split; reflexivity|].
    destruct (before.(TskState).(prioTbl) resolved) as [| |tid] eqn:Hentry.
    + destruct Hresult as [-> ->]; cbn [task_query_output_result] in Houtput.
      subst new_output; split; reflexivity.
    + destruct Hresult as [-> ->]; cbn [task_query_output_result] in Houtput.
      subst new_output; split; reflexivity.
    + destruct Hresult as [-> [t [bytes [-> Hbytes]]]].
      cbn [task_query_output_result] in Houtput; subst new_output.
      exists bytes, before; split.
      * split; [exists t; exact Hbytes|reflexivity].
      * split; reflexivity.
Qed.

Lemma task_query_call_result_program :
  forall critical sg invocation mask request output error caller before after old_output new_output,
  task_query_call_result critical sg invocation mask request output error caller
    before after old_output new_output ->
  task_query_program critical sg invocation caller request output old_output
    before (error, new_output) after.
Proof.
  intros critical sg invocation mask request output error caller before after old_output new_output Hcall.
  unfold task_query_call_result in Hcall; unfold task_query_program.
  destruct (task_query_prefix_error request output) as [early|].
  - destruct Hcall as [-> [-> ->]]; split; reflexivity.
  - destruct Hcall as [acquired [saved [snapshot
      [Hsaved [Hacquire [Hvalid [Hresult [Houtput Hrelease]]]]]]]].
    exists tt, acquired; split; [exact Hacquire|].
    exists (error, new_output), acquired; split.
    + apply task_query_protected_program_iff; split; [reflexivity|].
      exists snapshot; auto.
    + exists tt, after; split; [exact Hrelease|split; reflexivity].
Qed.

(** The saved word certifies the existing platform record; it is not an
    abstract branch guard or an additional public input condition. *)
Lemma task_query_program_call_result :
  forall critical sg invocation mask saved request output error caller before after old_output new_output,
  UCOS2_state_inv sg before -> interrupt_saved_value mask saved ->
  task_query_program critical sg invocation caller request output old_output
    before (error, new_output) after ->
  task_query_call_result critical sg invocation mask request output error caller
    before after old_output new_output.
Proof.
  intros critical sg invocation mask saved request output error caller before after old_output new_output
    Hbefore Hsaved Hprogram.
  unfold task_query_program in Hprogram; unfold task_query_call_result.
  destruct (task_query_prefix_error request output) as [early|].
  - destruct Hprogram as [Hresult Hafter]; inversion Hresult; subst; auto.
  - destruct Hprogram as [u [acquired [Hacquire [result [released [Hprotected
      [v [returned [Hrelease [Hresult Hafter]]]]]]]]]].
    subst result returned.
    apply task_query_protected_program_iff in Hprotected.
    destruct Hprotected as [-> [snapshot [Hresult Houtput]]].
    exists acquired, saved, snapshot.
    split; [exact Hsaved|]. split; [exact Hacquire|].
    split; [|auto].
    exact (proj1 (critical_region_interval_transports_resources
      critical sg invocation before acquired Hacquire Hbefore)).
Qed.

Lemma task_query_program_call_result_iff :
  forall critical sg invocation mask saved request output error caller before after old_output new_output,
  UCOS2_state_inv sg before -> interrupt_saved_value mask saved ->
  (task_query_program critical sg invocation caller request output old_output
     before (error, new_output) after <->
   task_query_call_result critical sg invocation mask request output error caller
     before after old_output new_output).
Proof.
  intros; split.
  - eapply task_query_program_call_result; eassumption.
  - apply task_query_call_result_program.
Qed.

Lemma task_query_safe_return :
  forall critical sg invocation mask request output error caller before after old_output new_output X,
  task_query_call_result critical sg invocation mask request output error caller
    before after old_output new_output ->
  task_query_safe critical sg invocation before caller request output old_output X ->
  safeExec (fun state => state = after) (StateRelMonad.ret (error, new_output))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation mask request output error caller before after old_output new_output X
    Hcall Hsafe.
  eapply (highstependret_derive
    (task_query_program critical sg invocation caller request output old_output)
    (fun state => state = before) (error, new_output) (fun _ state => state = after)).
  - intros state ->; exists after; split; [|reflexivity].
    eapply task_query_call_result_program; exact Hcall.
  - exact Hsafe.
Qed.

Lemma task_query_protected_free_result : forall sg acquired caller request resolved,
  task_query_priority_resolution sg acquired caller request resolved ->
  acquired.(TskState).(prioTbl) resolved = PTFree ->
  task_query_protected_result sg acquired caller request 41 None.
Proof.
  intros; exists resolved; split; [assumption|rewrite H0; auto].
Qed.

Lemma task_query_protected_reserved_result : forall sg acquired caller request resolved,
  task_query_priority_resolution sg acquired caller request resolved ->
  acquired.(TskState).(prioTbl) resolved = PTReserved ->
  task_query_protected_result sg acquired caller request 67 None.
Proof.
  intros; exists resolved; split; [assumption|rewrite H0; auto].
Qed.

Lemma task_query_protected_snapshot_result :
  forall sg acquired caller request resolved tid t bytes,
  task_query_priority_resolution sg acquired caller request resolved ->
  acquired.(TskState).(prioTbl) resolved = PTTask tid ->
  task_query_source_byte_view sg acquired tid t bytes ->
  task_query_protected_result sg acquired caller request 0 (Some bytes).
Proof.
  intros; exists resolved; split; [assumption|].
  rewrite H0; split; [reflexivity|].
  exists t, bytes; auto.
Qed.

Definition task_query_addresses (sg : StableGlobVars) (current table : Z) : Prop :=
  current = sg.(g_OSTCBCur) /\ table = sg.(g_OSTCBPrioTbl).

Definition task_query_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (s : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg s) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation s).

Definition task_query_save_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (saved : Z) : Assertion :=
  EX acquired, coq_prop
    (interrupt_saved_value mask saved /\
     critical_region_interval critical sg invocation before acquired) &&
    (critical_region_masked platform critical sg invocation origin saved acquired **
     UCOS2_inv sg acquired).

Definition task_query_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (released : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg invocation origin saved released **
    UCOS2_inv sg released.

Definition task_query_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (released : UCOS2_Verify_State) : Assertion :=
  EX after, coq_prop (critical_region_interval critical sg invocation released after) &&
    task_query_closed platform critical sg invocation origin
      (armv7a_irq_fiq_mask saved) after.

(** Materialize facts before their typed cell or invariant is consumed.  These
    are local consequences of existing ownership, not public input conditions. *)
Lemma task_query_request_uchar_bounds : forall p request,
  p # UChar |-> request |--
    coq_prop (0 <= request <= 255) && p # UChar |-> request.
Proof.
  intros p request.
  prop_apply_p (store_uchar_range p request).
  change Byte.max_unsigned with 255; entailer!.
Qed.

Lemma task_query_restore_pre_state_inv :
  forall platform critical sg invocation origin saved acquired,
  task_query_restore_pre platform critical sg invocation origin saved acquired |--
    coq_prop (UCOS2_state_inv sg acquired).
Proof.
  intros; unfold task_query_restore_pre, UCOS2_inv; entailer!.
Qed.

(** The destination protocol is used only after the two argument guards.
    It owns actual mixed bytes, separated from the complete kernel and caller
    frame.  Their observations remain unchanged on either protected error. *)
Definition task_query_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (caller : Assertion) (request output : Z) (old_output : list (option Z)) : Assertion :=
  match task_query_prefix_error request output with
  | Some _ => emp
  | None => coq_prop
      (task_query_layout sg /\
       task_query_self_admission critical sg invocation before request caller /\
       0 <= output /\ output + 64 <= 4294967295) &&
      (task_query_closed platform critical sg invocation origin mask before **
       caller ** UCharArray.mixed_full output 64 old_output)
  end.

Definition task_query_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (caller : Assertion) (request output : Z) (old_output : list (option Z))
  (error : Z) (X : Z -> list (option Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  match task_query_prefix_error request output with
  | Some early => coq_prop (error = early /\
      safeExec (fun state => state = before) (StateRelMonad.ret (error, old_output))
        (fun result state => X (fst result) (snd result) state)) && emp
  | None => EX after new_output, coq_prop
      (task_query_call_result critical sg invocation mask request output error caller
        before after old_output new_output /\
       safeExec (fun state => state = after) (StateRelMonad.ret (error, new_output))
        (fun result state => X (fst result) (snd result) state)) &&
      (task_query_closed platform critical sg invocation origin mask after **
       caller ** UCharArray.mixed_full output 64 new_output)
  end.

Definition task_query_entry_frame (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (caller : Assertion) (request output : Z) (old_output : list (option Z)) : Assertion :=
  coq_prop (task_query_layout sg /\
    task_query_self_admission critical sg invocation before request caller /\
    0 <= output /\ output + 64 <= 4294967295) &&
    (caller ** UCharArray.mixed_full output 64 old_output).

Definition task_query_current_cut (sg : StableGlobVars) (acquired : UCOS2_Verify_State)
  (caller : Assertion) (pointer resolved : Z) (residual : Assertion) : Prop :=
  0 <= resolved <= 63 /\
  pointer = encode_task_link sg acquired.(SchedState).(curTaskID) /\
  (UCOS2_raw_rep sg acquired ** caller |--
    sg.(g_OSTCBCur) # Ptr |-> pointer **
    tcb_field_address pointer TCBPrio # UChar |-> resolved ** residual) /\
  (sg.(g_OSTCBCur) # Ptr |-> pointer **
    tcb_field_address pointer TCBPrio # UChar |-> resolved ** residual |--
    UCOS2_raw_rep sg acquired ** caller).

Definition task_query_current_tail (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (before acquired : UCOS2_Verify_State)
  (caller : Assertion) (request output : Z) (old_output : list (option Z)) : Assertion :=
  coq_prop (UCOS2_state_inv sg acquired /\ task_query_layout sg /\
    task_query_self_admission critical sg invocation before request caller /\
    0 <= output /\ output + 64 <= 4294967295) &&
    (critical_region_masked platform critical sg invocation origin saved acquired **
     UCharArray.mixed_full output 64 old_output).

Definition task_query_table_value (sg : StableGlobVars) (acquired : UCOS2_Verify_State)
  (priority : Z) : Z := prio_tbl_entry_to_addr sg (acquired.(TskState).(prioTbl) priority).

Definition task_query_task_entry (acquired : UCOS2_Verify_State)
  (priority : Z) (tid : TaskID) : Prop :=
  acquired.(TskState).(prioTbl) priority = PTTask tid.

Definition task_query_reserved_entry (acquired : UCOS2_Verify_State)
  (priority : Z) : Prop :=
  acquired.(TskState).(prioTbl) priority = PTReserved.

(** The reserved encoding is classified while the acquired heap is still
    owned.  A live TCB at address one would require its offset-zero pointer
    field at an unaligned address; positivity of the pool base alone would
    not exclude that mathematical encoding. *)
Lemma task_query_reserved_table_entry : forall sg acquired priority,
  task_query_layout sg -> 0 <= priority <= 63 ->
  task_query_table_value sg acquired priority = 1 ->
  UCOS2_inv sg acquired |--
    coq_prop (task_query_reserved_entry acquired priority) && UCOS2_inv sg acquired.
Proof.
  intros sg acquired priority Hlayout Hpriority Hvalue.
  unfold UCOS2_inv at 1; Intros.
  rename H into Hvalid.
  destruct (acquired.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry.
  - unfold task_query_table_value in Hvalue; rewrite Hentry in Hvalue;
      discriminate.
  - unfold task_query_reserved_entry, UCOS2_inv; rewrite Hentry; entailer!.
  - destruct Hlayout as [Hsize [Hmulti [Hprofile Haddresses]]].
    pose proof Hvalid as Hparts.
    destruct Hparts as [Hselected [Htasks [_ [_ [Hcross _]]]]].
    assert (Hnative_priority : task_priority_in_range sg priority).
    { unfold selected_kernel_profile, valid_stable_glob_vars in Hselected.
      unfold task_priority_in_range; intuition lia. }
    destruct Hcross as [[_ [Htable _]] _].
    specialize (Htable priority Hnative_priority); rewrite Hentry in Htable.
    destruct Htable as [t Hlookup].
    assert (Hslot : task_slot_in_range sg tid).
    { apply (proj2 (proj1 (proj1 Htasks) tid)).
      left; exists t; exact Hlookup. }
    unfold task_query_table_value in Hvalue; rewrite Hentry in Hvalue.
    change (task_slot_addr sg tid = 1) in Hvalue.
    rewrite task_query_raw_split.
    sep_apply_l_atomic (task_public_storage_split_task sg acquired.(TskState) tid t Hlookup).
    rewrite (used_task_rep_tcb64 sg tid t Hmulti Hprofile).
    rewrite <- (task_slot_addr_tcb64 sg tid Hmulti Hprofile).
    sep_apply_l_atomic (tcb64_storage_split (task_slot_addr sg tid)
      (task_tcb64_image sg t) TCBStkPtr).
    cbn [tcb_cell task_tcb64_image].
    rewrite (Haddresses tid TCBStkPtr Hslot).
    cbn [tcb_field_offset]; rewrite Z.add_0_r, Hvalue.
    prop_apply_p (valid_store_ptr 1 t.(tcbStkPtr)).
    unfold isvalidptr; Intros.
    destruct H as [[_ [_ Haligned]] _].
    change (1 mod 4 = 0) in Haligned; discriminate.
Qed.

(** Use the actual acquired table binding, including priority aliases.  The
    endpoint comes from the initializer-backed immutable profile, not from
    an extra Query input condition or last-byte ownership. *)
Lemma task_query_acquired_task_slot_bounds : forall sg acquired priority tid,
  UCOS2_state_inv sg acquired -> task_priority_in_range sg priority ->
  task_query_task_entry acquired priority tid ->
  task_slot_in_range sg tid /\
  0 <= task_slot_addr sg tid /\ task_slot_addr sg tid + 64 <= 4294967295.
Proof.
  intros sg acquired priority tid Hvalid Hpriority Hentry.
  destruct Hvalid as [Hprofile [Htasks [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Htable _]] _].
  specialize (Htable priority Hpriority).
  unfold task_query_task_entry in Hentry; rewrite Hentry in Htable.
  destruct Htable as [node Hlookup].
  assert (Hslot : task_slot_in_range sg tid).
  { apply (proj2 (proj1 (proj1 Htasks) tid)).
    left; exists node; exact Hlookup. }
  split; [exact Hslot|].
  apply task_slot_addr_selected_bounds; assumption.
Qed.

Definition task_query_table_tail (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (acquired : UCOS2_Verify_State)
  (priority : Z) : Assertion :=
  coq_prop (UCOS2_state_inv sg acquired) &&
    (critical_region_masked platform critical sg invocation origin saved acquired **
     store_prio_tbl_missing_i sg acquired.(TskState).(prioTbl) priority **
     UCOS2_raw_rep_missing_priority_table sg acquired).

Definition task_query_copy_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (acquired : UCOS2_Verify_State)
  (caller : Assertion) (tid : TaskID) : Assertion :=
  coq_prop (UCOS2_state_inv sg acquired /\ task_query_layout sg /\ task_slot_in_range sg tid) &&
    (critical_region_masked platform critical sg invocation origin saved acquired **
     task_query_source_residual sg acquired tid ** caller).

Definition task_query_success_frame (sg : StableGlobVars) (acquired : UCOS2_Verify_State)
  (caller : Assertion) (request output : Z) (bytes : list Z) : Assertion :=
  coq_prop (task_query_protected_result sg acquired caller request 0 (Some bytes)) &&
    (caller ** UCharArray.mixed_full output 64 (map (@Some Z) bytes)).

Lemma task_query_copy_reclose :
  forall platform critical sg invocation origin saved acquired caller request output
    priority tid t bytes,
  task_query_priority_resolution sg acquired caller request priority ->
  task_query_task_entry acquired priority tid ->
  task_query_source_byte_view sg acquired tid t bytes ->
  mem_copy_post output (task_slot_addr sg tid) 64 bytes **
    task_query_copy_frame platform critical sg invocation origin saved acquired caller tid |--
  task_query_restore_pre platform critical sg invocation origin saved acquired **
    task_query_success_frame sg acquired caller request output bytes.
Proof.
  intros platform critical sg invocation origin saved acquired caller request output
    priority tid t bytes Hresolution Hentry Hbytes.
  unfold task_query_task_entry in Hentry.
  unfold task_query_copy_frame, mem_copy_post.
  Intros.
  sep_apply_l_atomic (task_query_source_byte_view_restore sg acquired tid t bytes
    ltac:(tauto) ltac:(tauto) Hbytes).
  sep_apply_l_atomic (UCharArray.full_to_mixed_full output 64 bytes).
  assert (Hresult : task_query_protected_result sg acquired caller request 0 (Some bytes)).
  { eapply task_query_protected_snapshot_result; eassumption. }
  unfold task_query_restore_pre, task_query_success_frame, UCOS2_inv; entailer!.
Qed.

(** A boundary diagnostic, not a reachable-state or source-bug claim: owning
    the last representable byte alone does not prove MemCopy's final source
    increment.  No extra public source bound is assumed here. *)
Lemma task_query_last_byte_does_not_bound_final_increment :
  0 <= 4294967232 /\ 4294967232 + 63 <= 4294967295 /\
  ~ (4294967232 + 64 <= 4294967295).
Proof. lia. Qed.

Lemma task_query_pool_endpoint_does_not_bound_final_increment :
  kernel_region_valid (4294965888, 64 * (20 + 2)) /\
  0 <= 21 < 20 + 2 /\
  4294965888 + 21 * 64 = 4294967232 /\
  (4294965888 + 21 * 64) mod 4 = 0 /\
  4294965888 + 21 * 64 + 63 <= 4294967295 /\
  ~ (4294965888 + 21 * 64 + 64 <= 4294967295).
Proof. unfold kernel_region_valid; cbn; lia. Qed.

Lemma ptr_array_missing_i_index_in_range__resource_views_and_call_preconditions :
  forall values base index lo hi,
  PtrArray.missing_i base index lo hi values |-- coq_prop (lo <= index < hi).
Proof.
  induction values as [|value values IH]; intros base index lo hi;
    unfold PtrArray.missing_i; cbn [store_array_missing_i_rec].
  - entailer!.
  - Split.
    + Intros.
      prop_apply (PtrArray.seg_length base (lo + 1) hi values).
      Intros; entailer!; lia.
    + Intros.
      prop_apply (IH base index (lo + 1) hi).
      Intros; entailer!; lia.
Qed.
Lemma store_prio_tbl_missing_i_index_in_range__resource_views_and_call_preconditions :
  forall sg table priority,
  Ucos2Verify.lib.array_abstraction.store_prio_tbl_missing_i sg table priority |--
    coq_prop (0 <= priority < 64).
Proof.
  intros; unfold Ucos2Verify.lib.array_abstraction.store_prio_tbl_missing_i.
  apply ptr_array_missing_i_index_in_range__resource_views_and_call_preconditions.
Qed.
Lemma task_query_table_zero_is_free__exact_return_observations :
  forall sg acquired priority,
  UCOS2_state_inv sg acquired -> 0 <= priority <= 63 ->
  task_query_table_value sg acquired priority = 0 ->
  acquired.(TskState).(prioTbl) priority = PTFree.
Proof.
  intros sg acquired priority Hvalid Hpriority Hzero.
  destruct (acquired.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry.
  - reflexivity.
  - unfold task_query_table_value in Hzero; rewrite Hentry in Hzero;
      discriminate.
  - pose proof Hvalid as Hparts.
    destruct Hparts as [Hselected _].
    assert (Hstable : valid_stable_glob_vars sg).
    { unfold selected_kernel_profile in Hselected; tauto. }
    assert (Hnative : task_priority_in_range sg priority).
    { unfold selected_kernel_profile, valid_stable_glob_vars in Hselected.
      unfold task_priority_in_range; intuition lia. }
    assert (Htask : task_query_task_entry acquired priority tid)
      by exact Hentry.
    pose proof (task_query_acquired_task_slot_bounds sg acquired priority tid
      Hvalid Hnative Htask) as [Hslot _].
    pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable
      ltac:(unfold stable_global_addresses; simpl; tauto)) as Hbase.
    unfold task_query_table_value in Hzero; rewrite Hentry in Hzero.
    change (task_slot_addr sg tid = 0) in Hzero.
    unfold task_slot_addr, tcb_configured_size, tcb_layout_size in Hzero.
    unfold task_slot_in_range in Hslot.
    destruct sg.(osKernelConfig).(cfgEventMultiEnabled),
      sg.(osKernelConfig).(cfgTaskProfile); lia.
Qed.
