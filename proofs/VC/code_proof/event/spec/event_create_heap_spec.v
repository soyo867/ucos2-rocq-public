Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_execution Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Import UCOS2_C_Rules ListNotations EventStateDef KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Physical effects of one source ECB field store in the selected ARM32
    little-endian representation. A multi-byte list describes one typed
    store, not separate interruptible C instructions. The caller binds the
    field list to the actual initialization prefix and must provide the
    same private owner at each intervening source/return cut. *)
Definition event_create_field_writes (base : addr) (field : EventField) (stored : Z)
  : list (addr * Mem.byte) :=
  let address := base + event_field_offset field in
  match field with
  | EventPtrField | EventNameField => pointer_store_writes address stored
  | EventCntField => byte_list_writes address [stored mod 256; (stored / 256) mod 256]
  | _ => [(address, stored)]
  end.

Definition event_create_field_value_in_range (field : EventField) (stored : Z) : Prop :=
  0 <= stored < match field with
  | EventPtrField | EventNameField => 4294967296
  | EventCntField => 65536
  | _ => 256
  end.

Lemma event_create_count_store_execution : forall address stored (frame : Assertion) before,
  0 <= stored < 65536 -> (address # UShort |->_ ** frame) before ->
  exists after,
    kernel_heap_execution
      (byte_list_writes address [stored mod 256; (stored / 256) mod 256]) before after /\
    (address # UShort |-> stored ** frame) after.
Proof.
  intros address stored frame before Hrange [cell [rest [Hjoin [[Haddress Hcell] Hrest]]]].
  assert (Hranges : Forall (fun byte => 0 <= byte < 256)
    [stored mod 256; (stored / 256) mod 256]).
  { repeat constructor; apply Z.mod_pos_bound; lia. }
  assert (Hopen : store_2byte_noninit address |-- store_bytes_noninit address 2 ** emp).
  { unfold store_2byte_noninit; cbn [store_bytes_noninit]; entailer!. }
  destruct (byte_list_store_execution [stored mod 256; (stored / 256) mod 256]
    address emp cell Hranges (Hopen cell Hcell)) as [updated [Hrun Hupdated]].
  assert (Hshort : (address # UShort |-> stored) updated).
  { split; [split; [exact Haddress|]; change (stored >= 0 /\ stored <= 65535); lia|].
    exists (stored mod 256), ((stored / 256) mod 256); split.
    - change (stored mod 65536 =
        (stored mod 256) mod 256 + ((stored / 256) mod 256) mod 256 * 256).
      rewrite !Z.mod_mod by lia.
      rewrite (Z.mod_small stored 65536 Hrange).
      assert (Hquotient : 0 <= stored / 256 < 256).
      { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
      rewrite (Z.mod_small (stored / 256) 256 Hquotient).
      pose proof (Z.div_mod stored 256 ltac:(lia)); lia.
    - assert (Hmerge : byte_list_rep address [stored mod 256; (stored / 256) mod 256] ** emp |--
        store_byte address (stored mod 256) ** store_byte (address + 1) ((stored / 256) mod 256)).
      { cbn [byte_list_rep]; entailer!. }
      exact (Hmerge updated Hupdated). }
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [after [Hwhole Hafter]].
  exists after; split; [exact Hwhole|].
  exists updated, rest; split; [exact Hafter|]; split; assumption.
Qed.

Lemma event_create_field_store_execution : forall base field old stored (frame : Assertion) before,
  event_create_field_value_in_range field stored ->
  (event_cell base field old ** frame) before ->
  exists after, kernel_heap_execution (event_create_field_writes base field stored) before after /\
    (event_cell base field (Some stored) ** frame) after.
Proof.
  intros base field old stored frame before Hrange Hpre.
  assert (Hforget : event_cell base field old |-- event_cell base field None).
  { destruct field, old; cbn [event_cell];
      first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr |
        apply store_ushort_undef_store_ushort | entailer!]. }
  assert (Hopen : event_cell base field old ** frame |-- event_cell base field None ** frame).
  { sep_apply_l_atomic Hforget; entailer!. }
  pose proof (Hopen before Hpre) as Howned.
  destruct field; cbn [event_create_field_value_in_range] in Hrange;
    cbn [event_cell event_create_field_writes] in Howned |- *;
    first [eapply framed_uchar_noninit_store_execution | eapply framed_pointer_store_execution |
      eapply event_create_count_store_execution]; eassumption.
Qed.

(** The shared frame is reindexed only after the actual private field
    bytes have been written. Pure lifecycle metadata supplies no memory.
    Both the updated creator image and the one shared program owner remain
    on the same output heap; the caller may compose the next source cut. *)
Lemma event_create_private_field_heap : forall sg state eid allocation field stored before
  (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_create_field_value_in_range field stored ->
  (event_private_storage_rep sg eid allocation ** kernel_program_inv sg state ** frame) before ->
  exists final after,
    (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
      eid = Some final /\
    kernel_heap_execution (event_create_field_writes (event_pool_addr sg eid) field stored) before after /\
    (event_private_storage_rep sg eid final **
     kernel_program_inv sg (replace_EventS
       (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame) after.
Proof.
  intros sg state eid allocation field stored before frame Hget Hfield Hrange Hpre.
  set (final := {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
    eventPrivateGeneration := allocation.(eventPrivateGeneration);
    eventPrivateQueue := allocation.(eventPrivateQueue);
    eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
    eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}).
  assert (Hlookup :
    (event_private_write state.(EventState) eid allocation field (Some stored)).(eventLifecycle).(eventPrivate)
      eid = Some final) by apply kernel_map_set_same.
  assert (Hsplit : event_private_storage_rep sg eid allocation ** kernel_program_inv sg state ** frame |--
    event_cell (event_pool_addr sg eid) field (allocation.(eventPrivateStorage) field) **
    (event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) field ** kernel_program_inv sg state ** frame)).
  { unfold event_private_storage_rep.
    sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) allocation.(eventPrivateStorage) field Hfield); entailer!. }
  destruct (event_create_field_store_execution (event_pool_addr sg eid) field
    (allocation.(eventPrivateStorage) field) stored _ before Hrange (Hsplit before Hpre))
    as [after [Hrun Hafter]].
  assert (Hmerge : event_cell (event_pool_addr sg eid) field (Some stored) **
    (event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
      allocation.(eventPrivateStorage) field ** kernel_program_inv sg state ** frame) |--
    event_private_storage_rep sg eid final **
      kernel_program_inv sg (replace_EventS
        (event_private_write state.(EventState) eid allocation field (Some stored)) state) ** frame).
  { unfold event_private_storage_rep, final; cbn [eventPrivateStorage].
    rewrite !kernel_program_inv_split_unmap.
    sep_apply_l_atomic (event_storage_merge_updated_field sg.(osKernelConfig).(cfgEventNames)
      (event_pool_addr sg eid) allocation.(eventPrivateStorage) field (Some stored) Hfield).
    sep_apply_l_atomic (UCOS2_event_private_write_global_frame sg state eid allocation field (Some stored) Hget).
    entailer!. }
  exists final, after; split; [exact Hlookup|]. split; [exact Hrun|exact (Hmerge after Hafter)].
Qed.

(** Any actual uninterrupted prefix of the existing source field list.
    The source relation contains the stores, not a desired post-invariant.
    For an interrupted execution the caller must compose the individual
    field steps with the actual environment transports; this theorem does
    not silently frame old shared bytes across Restore. *)
Lemma event_create_private_prefix_heap : forall sg eid writes state allocation before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  Forall (fun write => In (fst write) (event_fields sg.(osKernelConfig).(cfgEventNames)) /\
    event_create_field_value_in_range (fst write) (snd write)) writes ->
  (event_private_storage_rep sg eid allocation ** kernel_program_inv sg state ** frame) before ->
  exists final next after,
    event_create_private_stores eid writes state tt next /\
    next.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes (event_pool_addr sg eid) (fst write) (snd write)) writes)
      before after /\
    (event_private_storage_rep sg eid final ** kernel_program_inv sg next ** frame) after.
Proof.
  intros sg eid writes; induction writes as [|[field stored] rest IH];
    intros state allocation before frame Hget Hfields Hpre.
  - exists allocation, state, before; split; [split; reflexivity|].
    split; [exact Hget|]. split; [split; [constructor|split; reflexivity]|exact Hpre].
  - inversion Hfields as [|head tail [Hfield Hrange] Hrest]; subst.
    destruct (event_create_private_field_heap sg state eid allocation field stored before frame
      Hget Hfield Hrange Hpre) as [middle_allocation [middle [Hlookup [Hwrite Hmiddle]]]].
    destruct (IH (replace_EventS
        (event_private_write state.(EventState) eid allocation field (Some stored)) state)
        middle_allocation middle frame Hlookup Hrest Hmiddle)
      as [final [next [after [Htail [Hfinal [Hrun Hafter]]]]]].
    exists final, next, after; split.
    + cbn [event_create_private_stores]; exists allocation; split; assumption.
    + split; [exact Hfinal|]. split; [cbn [flat_map fst snd]; eapply heap_execution_append; eassumption|exact Hafter].
Qed.

Lemma event_create_initialization_fields_in_range : forall named kind count pointer name,
  0 <= kind < 256 -> 0 <= count < 65536 ->
  0 <= pointer < 4294967296 -> 0 <= name < 4294967296 ->
  Forall (fun write => In (fst write) (event_fields named) /\
    event_create_field_value_in_range (fst write) (snd write))
    (event_create_initialization_fields named kind count pointer name).
Proof.
  intros [] kind count pointer name Hkind Hcount Hpointer Hname;
    unfold event_create_initialization_fields; cbn;
    repeat (apply Forall_cons;
      [split; [unfold event_fields; cbn; auto 20|unfold event_create_field_value_in_range; cbn; lia]|]);
    apply Forall_nil.
Qed.

(** Source-order consumer for the Sem/Mbox/Queue initializer. Publication,
    QCB allocation and any intervening calls are separate operations; in
    particular MutexCreate's repaired Type-last order is not this list. *)
Lemma event_create_initialization_heap : forall sg eid kind count pointer name
  state allocation before (frame : Assertion),
  state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  0 <= kind < 256 -> 0 <= count < 65536 ->
  0 <= pointer < 4294967296 -> 0 <= name < 4294967296 ->
  (event_private_storage_rep sg eid allocation ** kernel_program_inv sg state ** frame) before ->
  exists final next after,
    event_create_private_initialization eid sg.(osKernelConfig).(cfgEventNames)
      kind count pointer name state tt next /\
    next.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    kernel_heap_execution
      (flat_map (fun write => event_create_field_writes (event_pool_addr sg eid) (fst write) (snd write))
        (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) kind count pointer name))
      before after /\
    (event_private_storage_rep sg eid final ** kernel_program_inv sg next ** frame) after.
Proof.
  intros sg eid kind count pointer name state allocation before frame Hget Hkind Hcount Hpointer Hname Hpre.
  unfold event_create_private_initialization.
  eapply event_create_private_prefix_heap; [exact Hget| |exact Hpre].
  apply event_create_initialization_fields_in_range; assumption.
Qed.
