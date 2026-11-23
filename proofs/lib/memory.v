Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
From SumLib Require Import ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.error_codes.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** V2.93.01 fixed partitions.  Allocation never introduces an allocator
    header: the first pointer word is a free-list link only while free.
    Membership and unique return are caller protocols, not OSMemPut guards. *)
Definition memory_block_addr (p : MemoryPartitionState) (i : Z) : addr :=
  p.(memBase) + i * p.(memBlockSize).
Definition memory_free_head (p : MemoryPartitionState) (ids : list Z) : addr :=
  match ids with [] => 0 | i :: _ => memory_block_addr p i end.

Definition memory_region_valid (p : MemoryPartitionState) : Prop :=
  0 < p.(memBase) /\ p.(memBase) mod 4 = 0 /\
  4 <= p.(memBlockSize) < 4294967296 /\ p.(memBlockSize) mod 4 = 0 /\
  2 <= p.(memBlockCount) < 4294967296 /\
  p.(memBase) + p.(memBlockSize) * p.(memBlockCount) <= 4294967296.

Definition memory_block_partition (id : MemID) (p : MemoryPartitionState) : Prop :=
  NoDup p.(memFreeBlocks) /\
  (forall i, In i p.(memFreeBlocks) -> 0 <= i < p.(memBlockCount)) /\
  (forall i, (exists l, p.(memAllocatedBlocks) i = Some l) <->
     0 <= i < p.(memBlockCount) /\ ~ In i p.(memFreeBlocks)) /\
  (forall i l, p.(memAllocatedBlocks) i = Some l ->
     l.(loanPartition) = id /\ l.(loanPartitionGeneration) = p.(memGeneration) /\
     l.(loanBlock) = i /\ (l.(loanGeneration) < p.(memNextLoan))%nat).
Definition valid_memory_partition (id : MemID) (p : MemoryPartitionState) : Prop :=
  memory_region_valid p /\ memory_block_partition id p.

Definition memory_partition_initial (generation : nat) (base size count name : Z)
  : MemoryPartitionState :=
  {| memGeneration := generation; memBase := base; memBlockSize := size;
     memBlockCount := count; memFreeBlocks := Zrange 0 count;
     memAllocatedBlocks := fun _ => None; memName := name; memNextLoan := 0 |}.

Lemma memory_partition_initial_partition : forall id generation base size count name,
  memory_block_partition id (memory_partition_initial generation base size count name).
Proof.
  intros; unfold memory_block_partition, memory_partition_initial; simpl.
  split; [apply NoDup_Zrange|]. split.
  - intros; apply In_Zrange; assumption.
  - split.
    + intro i; split.
      * intros [l H]; discriminate.
      * intros [Hrange Hnot]; exfalso; apply Hnot; apply In_Zrange; exact Hrange.
    + intros i l H; discriminate.
Qed.

(** The private prefix counts completed pointer stores, including the
    final NULL store.  Advancing it records a store performed by the C
    loop; it is not an entailment that initializes arbitrary bytes. *)
Definition memory_private_set_prefix (p : MemoryPrivatePartition) (prefix : Z)
  : MemoryPrivatePartition :=
  {| memPrivateSlot := p.(memPrivateSlot);
     memPrivateImage := p.(memPrivateImage); memPrivateBase := p.(memPrivateBase);
     memPrivateExtent := p.(memPrivateExtent); memPrivateBlockSize := p.(memPrivateBlockSize);
     memPrivateBlockCount := p.(memPrivateBlockCount); memPrivateLinkedPrefix := prefix |}.
Definition memory_private_initialization_valid (p : MemoryPrivatePartition) : Prop :=
  memory_region_valid (memory_partition_initial 0 p.(memPrivateBase)
    p.(memPrivateBlockSize) p.(memPrivateBlockCount) p.(memPrivateImage).(memImageName)) /\
  p.(memPrivateExtent) = p.(memPrivateBlockSize) * p.(memPrivateBlockCount) /\
  0 <= p.(memPrivateLinkedPrefix) <= p.(memPrivateBlockCount).
Definition memory_initialize_next_link (p : MemoryPrivatePartition)
  : option ((addr * addr) * MemoryPrivatePartition) :=
  let i := p.(memPrivateLinkedPrefix) in
  if i <? p.(memPrivateBlockCount) then
    Some ((p.(memPrivateBase) + i * p.(memPrivateBlockSize),
      if Z.eqb (i + 1) p.(memPrivateBlockCount) then 0
      else p.(memPrivateBase) + (i + 1) * p.(memPrivateBlockSize)),
      memory_private_set_prefix p (i + 1))
  else None.
Lemma memory_initialize_next_link_preserves_validity : forall p address next post,
  memory_private_initialization_valid p ->
  memory_initialize_next_link p = Some ((address, next), post) ->
  memory_private_initialization_valid post /\
  post.(memPrivateLinkedPrefix) = p.(memPrivateLinkedPrefix) + 1 /\
  post.(memPrivateImage) = p.(memPrivateImage).
Proof.
  intros p address next post [Hr [He Hp]] Hstep; unfold memory_initialize_next_link in Hstep.
  destruct (memPrivateLinkedPrefix p <? memPrivateBlockCount p) eqn:E; [|discriminate].
  apply Z.ltb_lt in E; inversion Hstep; subst address next post.
  split.
  - unfold memory_private_initialization_valid; simpl; split; [exact Hr|]. split; [exact He|lia].
  - split; reflexivity.
Qed.
Lemma memory_initialize_next_link_last_store : forall p,
  p.(memPrivateLinkedPrefix) + 1 = p.(memPrivateBlockCount) ->
  memory_initialize_next_link p = Some
    ((p.(memPrivateBase) + p.(memPrivateLinkedPrefix) * p.(memPrivateBlockSize), 0),
      memory_private_set_prefix p p.(memPrivateBlockCount)).
Proof.
  intros p H; unfold memory_initialize_next_link.
  assert (E : (memPrivateLinkedPrefix p <? memPrivateBlockCount p) = true) by (apply Z.ltb_lt; lia).
  rewrite E, H, Z.eqb_refl; reflexivity.
Qed.
Lemma memory_initialize_complete_has_no_next_store : forall p,
  p.(memPrivateLinkedPrefix) = p.(memPrivateBlockCount) -> memory_initialize_next_link p = None.
Proof. intros; unfold memory_initialize_next_link; rewrite H, Z.ltb_irrefl; reflexivity. Qed.

Lemma memory_create_establishes_partition : forall id generation base size count name,
  memory_region_valid (memory_partition_initial generation base size count name) ->
  valid_memory_partition id (memory_partition_initial generation base size count name).
Proof. intros; split; [assumption|apply memory_partition_initial_partition]. Qed.

(** The source Get reads the head and its old link, then decrements NFree.
    This logical view is refined by that physical step under the partition
    invariant, rather than filtering the step on the desired post-validity. *)
Definition memory_get_partition (id : MemID)
  (p : MemoryPartitionState) : option (MemoryBlockLoan * MemoryPartitionState) :=
  match p.(memFreeBlocks) with
  | [] => None
  | i :: rest =>
    let l := {| loanPartition := id; loanPartitionGeneration := p.(memGeneration);
                loanBlock := i; loanGeneration := p.(memNextLoan) |} in
    Some (l, {| memGeneration := p.(memGeneration); memBase := p.(memBase);
                memBlockSize := p.(memBlockSize); memBlockCount := p.(memBlockCount);
                memFreeBlocks := rest;
                memAllocatedBlocks := kernel_map_set p.(memAllocatedBlocks) i (Some l);
                memName := p.(memName); memNextLoan := S p.(memNextLoan) |})
  end.

Definition memory_put_partition (p : MemoryPartitionState) (i : Z) : MemoryPartitionState :=
  {| memGeneration := p.(memGeneration); memBase := p.(memBase);
     memBlockSize := p.(memBlockSize); memBlockCount := p.(memBlockCount);
     memFreeBlocks := i :: p.(memFreeBlocks);
     memAllocatedBlocks := kernel_map_set p.(memAllocatedBlocks) i None;
     memName := p.(memName); memNextLoan := p.(memNextLoan) |}.

Lemma memory_get_preserves_partition : forall id p l post,
  valid_memory_partition id p -> memory_get_partition id p = Some (l, post) ->
  valid_memory_partition id post.
Proof.
  intros id p l post [Hregion [Hnd [Hrange [Hpartition Hloans]]]] Hget.
  unfold memory_get_partition in Hget.
  destruct (memFreeBlocks p) as [|i rest] eqn:E; [discriminate|].
  inversion Hget; subst; clear Hget; simpl.
  split; [exact Hregion|]. unfold memory_block_partition; simpl.
  inversion Hnd as [|? ? Hnot Hrest]; subst.
  split; [exact Hrest|]. split; [intros; apply Hrange; right; assumption|].
  split.
  - intro j; unfold kernel_map_set; destruct (Z.eq_dec j i) as [->|Hneq].
    + split; [intros _; split; [apply Hrange; left; reflexivity|exact Hnot]|eauto].
    + rewrite Hpartition; simpl; intuition congruence.
  - intros j old Hlookup; unfold kernel_map_set in Hlookup.
    destruct (Z.eq_dec j i) as [->|Hneq].
    + inversion Hlookup; subst; simpl; repeat split; auto; lia.
    + specialize (Hloans j old Hlookup); destruct Hloans as [? [? [? ?]]];
        repeat split; auto; lia.
Qed.

Lemma memory_put_preserves_partition : forall id p i l,
  valid_memory_partition id p -> p.(memAllocatedBlocks) i = Some l ->
  valid_memory_partition id (memory_put_partition p i).
Proof.
  intros id p i l [Hregion [Hnd [Hrange [Hpartition Hloans]]]] Hlookup.
  assert (Hi : 0 <= i < memBlockCount p /\ ~ In i (memFreeBlocks p)).
  { apply (proj1 (Hpartition i)); eauto. }
  split; [exact Hregion|]. unfold memory_block_partition, memory_put_partition; simpl.
  split; [constructor; tauto|]. split.
  - intros j [->|H]; [tauto|apply Hrange; assumption].
  - split.
    + intro j; unfold kernel_map_set; destruct (Z.eq_dec j i) as [->|Hneq].
      * split; [intros [v H]; discriminate|intros [_ H]; exfalso; apply H; auto].
      * rewrite Hpartition; simpl; intuition congruence.
    + intros j v H; unfold kernel_map_set in H.
      destruct (Z.eq_dec j i); [discriminate|apply Hloans; assumption].
Qed.

Lemma memory_get_records_loan : forall id p l post,
  memory_get_partition id p = Some (l, post) ->
  post.(memAllocatedBlocks) l.(loanBlock) = Some l /\
  l.(loanPartition) = id /\ l.(loanPartitionGeneration) = post.(memGeneration) /\
  Z.of_nat (List.length p.(memFreeBlocks)) = Z.of_nat (List.length post.(memFreeBlocks)) + 1.
Proof.
  intros id p l post H; unfold memory_get_partition in H.
  destruct (memFreeBlocks p) as [|i rest]; [discriminate|].
  inversion H; subst; simpl; rewrite kernel_map_set_same; repeat split; auto; lia.
Qed.

Lemma memory_put_removes_loan : forall p i,
  (memory_put_partition p i).(memAllocatedBlocks) i = None.
Proof. intros; apply kernel_map_set_same. Qed.

Module MemoryFieldStorage := FieldStorage Arch32 LittleEndian
  UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules UCOS2_C_Rules.

(** The record remains the sole concrete image.  This finite inventory is
    only a typed-field view for QCP's existing store_map resource algebra. *)
Inductive MemoryControlField :=
  | MCBAddr | MCBFreeList | MCBBlkSize | MCBNBlks | MCBNFree | MCBName.
Definition MemoryControlField_eq_dec : forall x y : MemoryControlField, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition memory_control_fields (c : KernelConfiguration) : list MemoryControlField :=
  [MCBAddr; MCBFreeList; MCBBlkSize; MCBNBlks; MCBNFree] ++
  (if c.(cfgMemoryNames) then [MCBName] else []).

Definition memory_control_value (v : MemoryControlImage) (field : MemoryControlField) : Z :=
  match field with
  | MCBAddr => v.(memImageBase) | MCBFreeList => v.(memImageFree)
  | MCBBlkSize => v.(memImageSize) | MCBNBlks => v.(memImageCount)
  | MCBNFree => v.(memImageNFree) | MCBName => v.(memImageName)
  end.

Definition memory_control_set_field (v : MemoryControlImage) (field : MemoryControlField) (value : Z)
  : MemoryControlImage :=
  {| memImageBase := match field with MCBAddr => value | _ => v.(memImageBase) end;
     memImageFree := match field with MCBFreeList => value | _ => v.(memImageFree) end;
     memImageSize := match field with MCBBlkSize => value | _ => v.(memImageSize) end;
     memImageCount := match field with MCBNBlks => value | _ => v.(memImageCount) end;
     memImageNFree := match field with MCBNFree => value | _ => v.(memImageNFree) end;
     memImageName := match field with MCBName => value | _ => v.(memImageName) end |}.

Definition memory_control_cell (base : addr) (field : MemoryControlField) (value : Z) : Assertion :=
  match field with
  | MCBAddr => &(base # "os_mem" ->ₛ "OSMemAddr") # Ptr |-> value
  | MCBFreeList => &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> value
  | MCBBlkSize => &(base # "os_mem" ->ₛ "OSMemBlkSize") # UInt |-> value
  | MCBNBlks => &(base # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> value
  | MCBNFree => &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> value
  | MCBName => &(base # "os_mem" ->ₛ "OSMemName") # Ptr |-> value
  end.

Definition store_memory_control (sg : StableGlobVars) (base : addr) (v : MemoryControlImage) : Assertion :=
  MemoryFieldStorage.store_fields MemoryControlField_eq_dec (memory_control_cell base)
    (memory_control_fields sg.(osKernelConfig)) (memory_control_value v).

Definition memory_control_without_field (sg : StableGlobVars) (base : addr)
  (v : MemoryControlImage) (field : MemoryControlField) : Assertion :=
  MemoryFieldStorage.store_fields MemoryControlField_eq_dec (memory_control_cell base)
    (remove MemoryControlField_eq_dec field (memory_control_fields sg.(osKernelConfig)))
    (memory_control_value v).

Lemma memory_control_fields_nodup : forall c, NoDup (memory_control_fields c).
Proof.
  intros; unfold memory_control_fields; destruct (cfgMemoryNames c); simpl;
    repeat constructor; simpl; intuition discriminate.
Qed.

Lemma memory_control_set_field_value_eq : forall v field value,
  memory_control_value (memory_control_set_field v field value) =
    field_update MemoryControlField_eq_dec (memory_control_value v) field value.
Proof.
  intros; apply functional_extensionality; intro other; destruct field, other; reflexivity.
Qed.

Lemma store_memory_control_split_field : forall sg base v field,
  In field (memory_control_fields sg.(osKernelConfig)) ->
  store_memory_control sg base v |--
    memory_control_cell base field (memory_control_value v field) **
    memory_control_without_field sg base v field.
Proof.
  intros; apply MemoryFieldStorage.store_fields_split_field;
    [apply memory_control_fields_nodup|assumption].
Qed.

Lemma store_memory_control_merge_field : forall sg base v field,
  In field (memory_control_fields sg.(osKernelConfig)) ->
  memory_control_cell base field (memory_control_value v field) **
    memory_control_without_field sg base v field |-- store_memory_control sg base v.
Proof.
  intros; apply MemoryFieldStorage.store_fields_merge_field;
    [apply memory_control_fields_nodup|assumption].
Qed.

Lemma store_memory_control_merge_updated_field : forall sg base v field value,
  In field (memory_control_fields sg.(osKernelConfig)) ->
  memory_control_cell base field value ** memory_control_without_field sg base v field |--
    store_memory_control sg base (memory_control_set_field v field value).
Proof.
  intros; unfold store_memory_control, memory_control_without_field.
  rewrite memory_control_set_field_value_eq.
  apply MemoryFieldStorage.store_fields_merge_updated_field;
    [apply memory_control_fields_nodup|assumption].
Qed.

Lemma store_memory_control_layout_equiv : forall sg base v,
  store_memory_control sg base v --||-- &(base # "os_mem" ->ₛ "OSMemAddr") # Ptr |-> v.(memImageBase) **
  &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> v.(memImageFree) **
  &(base # "os_mem" ->ₛ "OSMemBlkSize") # UInt |-> v.(memImageSize) **
  &(base # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> v.(memImageCount) **
  &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> v.(memImageNFree) **
  (if sg.(osKernelConfig).(cfgMemoryNames) then
    &(base # "os_mem" ->ₛ "OSMemName") # Ptr |-> v.(memImageName) else emp).
Proof.
  intros; unfold store_memory_control, memory_control_fields.
  destruct (cfgMemoryNames (osKernelConfig sg)); simpl;
    repeat rewrite MemoryFieldStorage.store_fields_cons by (repeat constructor; simpl; intuition discriminate);
    rewrite MemoryFieldStorage.store_fields_nil; unfold memory_control_cell, memory_control_value;
    split; entailer!.
Qed.


Definition memory_partition_image (p : MemoryPartitionState) : MemoryControlImage :=
  {| memImageBase := p.(memBase); memImageFree := memory_free_head p p.(memFreeBlocks);
     memImageSize := p.(memBlockSize); memImageCount := p.(memBlockCount);
     memImageNFree := Z.of_nat (List.length p.(memFreeBlocks)); memImageName := p.(memName) |}.

Definition memory_block_tail (p : MemoryPartitionState) (i : Z) : Assertion :=
  UCharArray.undef_full (memory_block_addr p i + 4) (p.(memBlockSize) - 4).
Definition memory_free_block_rep (p : MemoryPartitionState) (i next : Z) : Assertion :=
  memory_block_addr p i # Ptr |-> next ** memory_block_tail p i.
Definition memory_block_storage (p : MemoryPartitionState) (i : Z) : Assertion :=
  EX first : Z, memory_free_block_rep p i first.

Fixpoint store_memory_free_blocks (p : MemoryPartitionState) (ids : list Z) : Assertion :=
  match ids with
  | [] => emp
  | i :: rest => memory_free_block_rep p i (memory_free_head p rest) **
                  store_memory_free_blocks p rest
  end.

Definition memory_block_loan (p : MemoryPartitionState) (l : MemoryBlockLoan) : Assertion :=
  coq_prop (p.(memAllocatedBlocks) l.(loanBlock) = Some l /\
            l.(loanPartitionGeneration) = p.(memGeneration)) &&
  memory_block_storage p l.(loanBlock).

Definition memory_partition_rep (sg : StableGlobVars) (id : MemID)
  (p : MemoryPartitionState) : Assertion :=
  store_memory_control sg (memory_control_addr sg id) (memory_partition_image p) **
  store_memory_free_blocks p p.(memFreeBlocks).

Lemma store_memory_free_blocks_frame : forall p q ids,
  p.(memBase) = q.(memBase) -> p.(memBlockSize) = q.(memBlockSize) ->
  store_memory_free_blocks p ids = store_memory_free_blocks q ids.
Proof.
  intros p q ids Hb Hs; induction ids as [|i rest IH]; simpl; [reflexivity|].
  unfold memory_free_block_rep, memory_free_head, memory_block_tail, memory_block_addr.
  rewrite Hb, Hs, IH; reflexivity.
Qed.

Lemma memory_get_transfers_block : forall id p l post,
  memory_get_partition id p = Some (l, post) ->
  store_memory_free_blocks p p.(memFreeBlocks) |--
  memory_block_loan post l ** store_memory_free_blocks post post.(memFreeBlocks).
Proof.
  intros id p l post H.
  pose proof (memory_get_records_loan id p l post H) as [Hl [_ [Hg _]]].
  unfold memory_get_partition in H.
  destruct (memFreeBlocks p) as [|i rest] eqn:E; [discriminate|].
  inversion H; subst; clear H; simpl in *.
  unfold memory_block_loan, memory_block_storage; simpl.
  Exists (memory_free_head p rest).
  unfold memory_free_block_rep, memory_block_tail, memory_block_addr; simpl.
  entailer!.
  match goal with
  | |- _ |-- store_memory_free_blocks ?q rest =>
      rewrite (store_memory_free_blocks_frame p q rest eq_refl eq_refl); entailer!
  end.
Qed.

(** This is an after-write reassembly rule: the caller has already stored
    the old free head in the returning block.  It is not an entailment
    which changes bytes without the C store. *)
Lemma memory_put_restores_block : forall p i,
  memory_free_block_rep p i (memory_free_head p p.(memFreeBlocks)) **
  store_memory_free_blocks p p.(memFreeBlocks) |--
  store_memory_free_blocks (memory_put_partition p i)
    (memory_put_partition p i).(memFreeBlocks).
Proof.
  intros; simpl; unfold memory_free_block_rep, memory_free_head,
    memory_block_tail, memory_block_addr; simpl.
  entailer!.
  match goal with
  | |- _ |-- store_memory_free_blocks ?q ?ids =>
      rewrite (store_memory_free_blocks_frame p q ids eq_refl eq_refl); entailer!
  end.
Qed.

(** Literal MCB updates remain total even for a malformed free-list model.
    Permission for the dereference/write is a separate Hoare precondition. *)
Definition memory_get_image (v : MemoryControlImage) (next : addr) : MemoryControlImage :=
  {| memImageBase := v.(memImageBase); memImageFree := next;
     memImageSize := v.(memImageSize); memImageCount := v.(memImageCount);
     memImageNFree := kernel_u32 (v.(memImageNFree) - 1); memImageName := v.(memImageName) |}.
Definition memory_put_image (v : MemoryControlImage) (block : addr) : MemoryControlImage :=
  {| memImageBase := v.(memImageBase); memImageFree := block;
     memImageSize := v.(memImageSize); memImageCount := v.(memImageCount);
     memImageNFree := kernel_u32 (v.(memImageNFree) + 1); memImageName := v.(memImageName) |}.

Definition memory_query_snapshot (v : MemoryControlImage) : list Z :=
  [v.(memImageBase); v.(memImageFree); v.(memImageSize); v.(memImageCount);
   v.(memImageNFree); kernel_u32 (v.(memImageCount) - v.(memImageNFree))].
Lemma memory_query_snapshot_used_count : forall v,
  nth 5 (memory_query_snapshot v) 0 = kernel_u32 (v.(memImageCount) - v.(memImageNFree)).
Proof. reflexivity. Qed.

Definition memory_controls_rep (sg : StableGlobVars) (s : GlobMemoryState) : Assertion :=
  store_map (fun i v => store_memory_control sg (memory_control_addr sg i) v)
    s.(memControlImages).
Definition memory_controls_without (sg : StableGlobVars) (s : GlobMemoryState) (i : MemID)
  : Assertion :=
  store_map_missing_i (fun i v => store_memory_control sg (memory_control_addr sg i) v)
    s.(memControlImages) i.
Definition memory_raw_rep (sg : StableGlobVars) (s : GlobMemoryState) : Assertion :=
  memory_controls_rep sg s **
  store_map (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) s.(memPartitions) **
  sg.(g_OSMemFreeList) # Ptr |->
    (match s.(memFreeControls) with [] => 0 | i :: _ => memory_control_addr sg i end).

Definition memory_control_partition (sg : StableGlobVars) (s : GlobMemoryState) : Prop :=
  NoDup s.(memFreeControls) /\
  (forall i, In i s.(memFreeControls) ->
     0 <= i < sg.(osKernelConfig).(cfgMaxMemPartitions)) /\
  (forall i, 0 <= i < sg.(osKernelConfig).(cfgMaxMemPartitions) ->
     (In i s.(memFreeControls) /\ s.(memPartitions) i = None /\ s.(memPrivateControls) i = None) \/
     (exists p, s.(memPartitions) i = Some p /\ ~ In i s.(memFreeControls) /\ s.(memPrivateControls) i = None) \/
     (exists p, s.(memPrivateControls) i = Some p /\ ~ In i s.(memFreeControls) /\ s.(memPartitions) i = None)).
Definition valid_memory_state (sg : StableGlobVars) (s : GlobMemoryState) : Prop :=
  memory_control_partition sg s /\
  (forall i p, s.(memPartitions) i = Some p ->
     0 <= i < sg.(osKernelConfig).(cfgMaxMemPartitions) /\ valid_memory_partition i p /\
     s.(memControlImages) i = Some (memory_partition_image p)) /\
  (forall i p, s.(memPrivateControls) i = Some p -> s.(memControlImages) i = None) /\
  (forall i, s.(memPrivateControls) i = None ->
     ((exists v, s.(memControlImages) i = Some v) <->
       0 <= i < sg.(osKernelConfig).(cfgMaxMemPartitions))) /\
  (forall pre i rest, s.(memFreeControls) = pre ++ i :: rest ->
     exists v, s.(memControlImages) i = Some v /\
       v.(memImageFree) = match rest with [] => 0 | j :: _ => memory_control_addr sg j end) /\
  (forall i p, s.(memPrivateControls) i = Some p ->
     0 <= i < sg.(osKernelConfig).(cfgMaxMemPartitions) /\ p.(memPrivateSlot) = i /\
     s.(memPartitions) i = None /\ ~ In i s.(memFreeControls)).
Definition memory_disabled : GlobMemoryState :=
  {| memPartitions := fun _ => None; memFreeControls := []; memControlImages := fun _ => None;
     memPrivateControls := fun _ => None; memNextGeneration := 0 |}.
Definition valid_memory_configuration (sg : StableGlobVars) (s : GlobMemoryState) : Prop :=
  if sg.(osKernelConfig).(cfgMemoryEnabled) then valid_memory_state sg s else s = memory_disabled.
Definition memory_configured_rep (sg : StableGlobVars) (s : GlobMemoryState) : Assertion :=
  if sg.(osKernelConfig).(cfgMemoryEnabled) then memory_raw_rep sg s else emp.
Definition memory_inv (sg : StableGlobVars) (s : GlobMemoryState) : Assertion :=
  coq_prop (valid_memory_configuration sg s) && memory_configured_rep sg s.
Lemma memory_disabled_configuration_valid : forall sg,
  sg.(osKernelConfig).(cfgMemoryEnabled) = false -> valid_memory_configuration sg memory_disabled.
Proof. intros; unfold valid_memory_configuration; rewrite H; reflexivity. Qed.

Lemma memory_controls_split_control : forall sg s i v,
  s.(memControlImages) i = Some v ->
  memory_controls_rep sg s |-- store_memory_control sg (memory_control_addr sg i) v **
    memory_controls_without sg s i.
Proof.
  intros; unfold memory_controls_rep, memory_controls_without.
  sep_apply_l_atomic (store_map_split
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) i v _ H); entailer!.
Qed.

Lemma memory_controls_merge_updated_control : forall sg s post i v,
  post.(memControlImages) i = Some v ->
  (forall j, j <> i -> s.(memControlImages) j = post.(memControlImages) j) ->
  store_memory_control sg (memory_control_addr sg i) v ** memory_controls_without sg s i |--
  memory_controls_rep sg post.
Proof.
  intros sg s post i v H Hframe; unfold memory_controls_rep, memory_controls_without.
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) _ _ i Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) i v _ H); entailer!.
Qed.

Definition memory_initial_image (sg : StableGlobVars) (name : addr) (i : MemID) : MemoryControlImage :=
  {| memImageBase := 0;
     memImageFree := match kernel_list_next (Zrange 0 sg.(osKernelConfig).(cfgMaxMemPartitions)) i with
       | None => 0 | Some j => memory_control_addr sg j end;
     memImageSize := 0; memImageCount := 0; memImageNFree := 0; memImageName := name |}.
Definition memory_initial (sg : StableGlobVars) (name : addr) : GlobMemoryState :=
  {| memPartitions := fun _ => None;
     memFreeControls := Zrange 0 sg.(osKernelConfig).(cfgMaxMemPartitions);
     memControlImages := fun i =>
       if andb (0 <=? i) (i <? sg.(osKernelConfig).(cfgMaxMemPartitions))
       then Some (memory_initial_image sg name i) else None;
     memPrivateControls := fun _ => None; memNextGeneration := 0 |}.

Lemma memory_initial_valid : forall sg name, valid_memory_state sg (memory_initial sg name).
Proof.
  intros sg name; unfold valid_memory_state, memory_initial; simpl.
  split.
  - unfold memory_control_partition; simpl; split; [apply NoDup_Zrange|]. split.
    + intros; apply In_Zrange; assumption.
    + intros i Hi; left; split; [apply In_Zrange; exact Hi|auto].
  - split; [intros; discriminate|]. split; [intros; discriminate|]. split.
    + intros i _; destruct (andb (0 <=? i) (i <? cfgMaxMemPartitions (osKernelConfig sg))) eqn:E.
      * apply Bool.andb_true_iff in E; destruct E as [Hlo Hhi].
        apply Z.leb_le in Hlo; apply Z.ltb_lt in Hhi; split; [intros; lia|eauto].
      * split; [intros [v H]; discriminate|]. intros [Hlo Hhi].
        assert (andb (0 <=? i) (i <? cfgMaxMemPartitions (osKernelConfig sg)) = true)
          by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        congruence.
    + split.
      * intros pre i rest Hlist.
        assert (Hi : 0 <= i < cfgMaxMemPartitions (osKernelConfig sg)).
        { apply In_Zrange; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
        assert (Hb : andb (0 <=? i) (i <? cfgMaxMemPartitions (osKernelConfig sg)) = true)
          by (apply Bool.andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        rewrite Hb; exists (memory_initial_image sg name i); split; [reflexivity|].
        unfold memory_initial_image; simpl; rewrite Hlist, kernel_list_next_at.
        -- destruct rest; reflexivity.
        -- pose proof (NoDup_Zrange 0 (cfgMaxMemPartitions (osKernelConfig sg))) as Hnd.
           rewrite Hlist in Hnd; exact Hnd.
      * intros; discriminate.
Qed.

Lemma memory_initial_has_control : forall sg name,
  0 < sg.(osKernelConfig).(cfgMaxMemPartitions) ->
  exists v, (memory_initial sg name).(memControlImages) 0 = Some v.
Proof.
  intros sg name H; unfold memory_initial; simpl.
  assert (Hlt : (0 <? cfgMaxMemPartitions (osKernelConfig sg)) = true) by (apply Z.ltb_lt; lia).
  rewrite Hlt; eauto.
Qed.

Lemma memory_free_count_in_range : forall id p,
  valid_memory_partition id p -> 0 <= Z.of_nat (List.length p.(memFreeBlocks)) <= p.(memBlockCount).
Proof.
  intros id p [Hr [Hnd [Hrange [Hp Hl]]]].
  eapply kernel_pool_free_count_bound with (used := p.(memAllocatedBlocks)).
  - unfold memory_region_valid in Hr; lia.
  - split; [exact Hnd|]. split; assumption.
Qed.

Lemma memory_get_refines_control_image : forall id p l post,
  valid_memory_partition id p -> memory_get_partition id p = Some (l, post) ->
  memory_get_image (memory_partition_image p) (memory_free_head post post.(memFreeBlocks)) =
  memory_partition_image post.
Proof.
  intros id p l post Hv Hget.
  pose proof (memory_free_count_in_range id p Hv) as Hcount.
  destruct Hv as [Hregion _]; unfold memory_region_valid in Hregion.
  unfold memory_get_partition in Hget; destruct (memFreeBlocks p) as [|i rest] eqn:E; [discriminate|].
  inversion Hget; subst; clear Hget.
  unfold memory_get_image, memory_partition_image; f_equal.
  change (kernel_u32 (Z.of_nat (List.length (memFreeBlocks p)) - 1) = Z.of_nat (List.length rest)).
  rewrite E.
  change (kernel_u32 (Z.of_nat (S (List.length rest)) - 1) = Z.of_nat (List.length rest)).
  change (0 <= Z.of_nat (S (List.length rest)) <= memBlockCount p) in Hcount.
  rewrite Nat2Z.inj_succ in Hcount |- *.
  replace (Z.succ (Z.of_nat (List.length rest)) - 1) with (Z.of_nat (List.length rest)) by lia.
  apply kernel_u32_identity; lia.
Qed.

(** OS_MemInit publishes every MCB in a free chain.  Create removes an MCB
    inside its first critical section, then initializes both that MCB and
    the caller's arena privately before publication.  Neither region is
    simultaneously owned by the global invariant during this phase. *)
Definition memory_reserve_control (s : GlobMemoryState)
  (base extent size count : Z) : option (MemoryPrivatePartition * GlobMemoryState) :=
  match s.(memFreeControls) with
  | [] => None
  | i :: rest => match s.(memControlImages) i with
    | None => None
    | Some old =>
      let private := {| memPrivateSlot := i;
        memPrivateImage := old; memPrivateBase := base; memPrivateExtent := extent;
        memPrivateBlockSize := size; memPrivateBlockCount := count; memPrivateLinkedPrefix := 0 |} in
      Some (private, {| memPartitions := s.(memPartitions); memFreeControls := rest;
        memControlImages := kernel_map_set s.(memControlImages) i None;
        memPrivateControls := kernel_map_set s.(memPrivateControls) i (Some private);
        memNextGeneration := s.(memNextGeneration) |})
    end
  end.
Definition memory_private_control_rep (sg : StableGlobVars) (p : MemoryPrivatePartition) : Assertion :=
  store_memory_control sg (memory_control_addr sg p.(memPrivateSlot)) p.(memPrivateImage).
Definition memory_private_arena_rep (p : MemoryPrivatePartition) : Assertion :=
  UCharArray.undef_full p.(memPrivateBase) p.(memPrivateExtent).
Lemma memory_reserve_excludes_global_control : forall s base extent size count private post,
  memory_reserve_control s base extent size count = Some (private, post) ->
  post.(memControlImages) private.(memPrivateSlot) = None /\
  post.(memPrivateControls) private.(memPrivateSlot) = Some private.
Proof.
  intros s base extent size count private post H; unfold memory_reserve_control in H.
  destruct (memFreeControls s) as [|i rest]; [discriminate|].
  destruct (memControlImages s i); [|discriminate].
  inversion H; subst; simpl; split; apply kernel_map_set_same.
Qed.
Definition memory_publish_control (s : GlobMemoryState) (private : MemoryPrivatePartition)
  : GlobMemoryState :=
  let i := private.(memPrivateSlot) in
  let p := memory_partition_initial s.(memNextGeneration) private.(memPrivateBase)
    private.(memPrivateBlockSize) private.(memPrivateBlockCount) private.(memPrivateImage).(memImageName) in
  {| memPartitions := kernel_map_set s.(memPartitions) i (Some p);
     memFreeControls := s.(memFreeControls);
     memControlImages := kernel_map_set s.(memControlImages) i (Some (memory_partition_image p));
     memPrivateControls := kernel_map_set s.(memPrivateControls) i None;
     memNextGeneration := S s.(memNextGeneration) |}.
Lemma memory_publish_initializes_partition : forall s private,
  exists p, (memory_publish_control s private).(memPartitions) private.(memPrivateSlot) = Some p /\
    memory_block_partition private.(memPrivateSlot) p /\
    (memory_publish_control s private).(memPrivateControls) private.(memPrivateSlot) = None.
Proof.
  intros; unfold memory_publish_control; simpl; rewrite kernel_map_set_same.
  eexists; split; [reflexivity|]. split; [apply memory_partition_initial_partition|apply kernel_map_set_same].
Qed.

(** The public argument guards are deliberately weaker than the caller's
    storage protocol.  In particular, the source checks base alignment but
    does not check stride alignment, total extent, or Put membership. *)
Definition memory_create_argument_error (c : KernelConfiguration) (base count size : Z)
  : option OSErrCode :=
  if c.(cfgArgumentChecks) then
    if Z.eqb base 0 then Some OS_ERR_MEM_INVALID_ADDR else
    if negb (Z.eqb (base mod 4) 0) then Some OS_ERR_MEM_INVALID_ADDR else
    if count <? 2 then Some OS_ERR_MEM_INVALID_BLKS else
    if size <? 4 then Some OS_ERR_MEM_INVALID_SIZE else None
  else None.
Definition memory_get_guard (c : KernelConfiguration) (pmem : addr) (v : MemoryControlImage)
  : option OSErrCode :=
  if andb c.(cfgArgumentChecks) (Z.eqb pmem 0) then Some OS_ERR_MEM_INVALID_PMEM else
  if Z.eqb v.(memImageNFree) 0 then Some OS_ERR_MEM_NO_FREE_BLKS else None.
Definition memory_put_guard (c : KernelConfiguration) (pmem block : addr) (v : MemoryControlImage)
  : option OSErrCode :=
  if andb c.(cfgArgumentChecks) (Z.eqb pmem 0) then Some OS_ERR_MEM_INVALID_PMEM else
  if andb c.(cfgArgumentChecks) (Z.eqb block 0) then Some OS_ERR_MEM_INVALID_PBLK else
  if v.(memImageCount) <=? v.(memImageNFree) then Some OS_ERR_MEM_FULL else None.
Lemma memory_create_guard_does_not_check_stride_alignment :
  memory_create_argument_error selected_kernel_configuration 4096 2 5 = None.
Proof. reflexivity. Qed.
Lemma memory_put_guard_does_not_check_membership : forall p block v,
  p <> 0 -> block <> 0 -> v.(memImageNFree) < v.(memImageCount) ->
  memory_put_guard selected_kernel_configuration p block v = None.
Proof.
  intros p block v Hp Hb Hn; unfold memory_put_guard; simpl.
  destruct (Z.eqb p 0) eqn:Ep; [apply Z.eqb_eq in Ep; contradiction|].
  destruct (Z.eqb block 0) eqn:Eb; [apply Z.eqb_eq in Eb; contradiction|].
  destruct (memImageCount v <=? memImageNFree v) eqn:En; [apply Z.leb_le in En; lia|reflexivity].
Qed.

Definition memory_replace_partition (s : GlobMemoryState) (i : MemID) (p : MemoryPartitionState)
  : GlobMemoryState :=
  {| memPartitions := kernel_map_set s.(memPartitions) i (Some p);
     memFreeControls := s.(memFreeControls);
     memControlImages := kernel_map_set s.(memControlImages) i (Some (memory_partition_image p));
     memPrivateControls := s.(memPrivateControls); memNextGeneration := s.(memNextGeneration) |}.
Lemma memory_replace_partition_preserves_validity : forall sg s i old p,
  valid_memory_state sg s -> s.(memPartitions) i = Some old -> valid_memory_partition i p ->
  valid_memory_state sg (memory_replace_partition s i p).
Proof.
  intros sg s i old p [Hpool [Hparts [Hprivateimage [Hdomain [Hlinks Hprivate]]]]] Hold Hp.
  destruct Hpool as [Hnd [Hrange Hslots]].
  destruct (Hparts i old Hold) as [Hi [Hvalid Himage]].
  assert (Hslot : ~ In i (memFreeControls s) /\ memPrivateControls s i = None).
  { destruct (Hslots i Hi) as [[_ [H _]]|[[q [H [Hnot Hpriv]]]|[q [_ [_ H]]]]].
    - congruence.
    - split; assumption.
    - congruence. }
  destruct Hslot as [Hnot Hpriv].
  unfold valid_memory_state, memory_replace_partition; simpl.
  split.
  - unfold memory_control_partition; simpl; split; [exact Hnd|]. split; [exact Hrange|].
    intros j Hj; destruct (Z.eq_dec j i) as [->|Hne].
    + right; left; exists p; rewrite kernel_map_set_same; auto.
    + rewrite kernel_map_set_other by exact Hne; apply Hslots; exact Hj.
  - split.
    + intros j q H; unfold kernel_map_set in H; destruct (Z.eq_dec j i) as [->|Hne].
      * inversion H; subst q; split; [exact Hi|]. split; [exact Hp|apply kernel_map_set_same].
      * destruct (Hparts j q H) as [Hj [Hq Hv]]; split; [exact Hj|]. split; [exact Hq|].
        rewrite kernel_map_set_other by exact Hne; exact Hv.
    + split.
      * intros j q H; assert (Hne : j <> i) by (intro E; subst; congruence).
        rewrite kernel_map_set_other by exact Hne; eapply Hprivateimage; eauto.
      * split.
        -- intros j Hnone; destruct (Z.eq_dec j i) as [->|Hne].
           ++ rewrite kernel_map_set_same; split; [intros; exact Hi|eauto].
           ++ rewrite kernel_map_set_other by exact Hne; apply Hdomain; exact Hnone.
        -- split.
           ++ intros pre j rest Hlist.
              assert (Hne : j <> i).
              { intro E; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
              destruct (Hlinks pre j rest Hlist) as [v [Hv Hnext]].
              exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Hv|exact Hnext].
           ++ intros j q H; assert (Hne : j <> i) by (intro E; subst; congruence).
              destruct (Hprivate j q H) as [Hj [Hslot [Hnone Hfree]]].
              split; [exact Hj|]. split; [exact Hslot|]. split; [|exact Hfree].
              rewrite kernel_map_set_other by exact Hne; exact Hnone.
Qed.
Definition memory_get (s : GlobMemoryState) (i : MemID)
  : option (MemoryBlockLoan * GlobMemoryState) :=
  match s.(memPartitions) i with
  | None => None
  | Some p => match memory_get_partition i p with
    | None => None | Some (loan, post) => Some (loan, memory_replace_partition s i post) end
  end.
Definition memory_put (s : GlobMemoryState) (i block : Z) : option GlobMemoryState :=
  match s.(memPartitions) i with
  | None => None | Some p => Some (memory_replace_partition s i (memory_put_partition p block)) end.
Lemma memory_get_preserves_state_validity : forall sg s i loan post,
  valid_memory_state sg s -> memory_get s i = Some (loan, post) -> valid_memory_state sg post.
Proof.
  intros sg s i loan post Hv H; unfold memory_get in H.
  destruct (memPartitions s i) as [p|] eqn:E; [|discriminate].
  destruct (memory_get_partition i p) as [[l q]|] eqn:Eg; [|discriminate].
  inversion H; subst; eapply memory_replace_partition_preserves_validity; eauto.
  eapply memory_get_preserves_partition; [|exact Eg].
  destruct Hv as [_ [Hparts _]]; exact (proj1 (proj2 (Hparts i p E))).
Qed.
Lemma memory_put_preserves_state_validity : forall sg s i block p loan post,
  valid_memory_state sg s -> s.(memPartitions) i = Some p -> p.(memAllocatedBlocks) block = Some loan ->
  memory_put s i block = Some post -> valid_memory_state sg post.
Proof.
  intros sg s i block p loan post Hv Ep El H; unfold memory_put in H; rewrite Ep in H.
  inversion H; subst; eapply memory_replace_partition_preserves_validity; eauto.
  eapply memory_put_preserves_partition; [|exact El].
  destruct Hv as [_ [Hparts _]]; exact (proj1 (proj2 (Hparts i p Ep))).
Qed.
Lemma memory_put_refines_control_image : forall id p i loan,
  valid_memory_partition id p -> p.(memAllocatedBlocks) i = Some loan ->
  memory_put_image (memory_partition_image p) (memory_block_addr p i) =
  memory_partition_image (memory_put_partition p i).
Proof.
  intros id p i loan Hv Hl.
  pose proof (memory_put_preserves_partition id p i loan Hv Hl) as Hpost.
  pose proof (memory_free_count_in_range id (memory_put_partition p i) Hpost) as Hcount.
  destruct Hv as [Hregion _]; unfold memory_region_valid in Hregion.
  unfold memory_put_image, memory_partition_image; f_equal.
  change (kernel_u32 (Z.of_nat (List.length (memFreeBlocks p)) + 1) =
    Z.of_nat (S (List.length (memFreeBlocks p)))).
  change (0 <= Z.of_nat (S (List.length (memFreeBlocks p))) <= memBlockCount p) in Hcount.
  rewrite Nat2Z.inj_succ in Hcount |- *.
  rewrite kernel_u32_identity; lia.
Qed.

Lemma memory_reserve_preserves_state_validity : forall sg s base extent size count private post,
  valid_memory_state sg s ->
  memory_reserve_control s base extent size count = Some (private, post) ->
  valid_memory_state sg post.
Proof.
  intros sg s base extent size count private post Hv Hstep.
  destruct Hv as [[Hnd [Hrange Hslots]] [Hparts [Hprivateimage [Hdomain [Hlinks Hprivate]]]]].
  unfold memory_reserve_control in Hstep.
  destruct (memFreeControls s) as [|i rest] eqn:E; [discriminate|].
  destruct (memControlImages s i) as [old|] eqn:Ei; [|discriminate].
  inversion Hstep; subst private post; clear Hstep.
  inversion Hnd as [|? ? Hnot Hrest]; subst.
  assert (Hi : 0 <= i < cfgMaxMemPartitions (osKernelConfig sg)) by (apply Hrange; left; reflexivity).
  assert (Hslot : memPartitions s i = None /\ memPrivateControls s i = None).
  { destruct (Hslots i Hi) as [[_ H]|[[p [_ [H _]]]|[p [_ [H _]]]]]; [exact H|exfalso;apply H;left;reflexivity|exfalso;apply H;left;reflexivity]. }
  destruct Hslot as [Hnone Hprivate_none].
  unfold valid_memory_state; simpl; split.
  - unfold memory_control_partition; simpl; split; [exact Hrest|]. split.
    + intros j Hj; apply Hrange; right; exact Hj.
    + intros j Hj; destruct (Z.eq_dec j i) as [->|Hne].
      * right; right; eexists; rewrite kernel_map_set_same; auto.
      * rewrite kernel_map_set_other by exact Hne.
        destruct (Hslots j Hj) as [[Hin [Hp Hpr]]|[[p [Hp [Hnotj Hpr]]]|[p [Hpr [Hnotj Hp]]]]].
        -- left; split; [simpl in Hin; intuition congruence|auto].
        -- right; left; exists p; split; [exact Hp|]. split; [intro Hin; apply Hnotj; right; exact Hin|exact Hpr].
        -- right; right; exists p; split; [exact Hpr|]. split; [intro Hin; apply Hnotj; right; exact Hin|exact Hp].
  - split.
    + intros j p Hp; assert (Hne : j <> i) by (intro Heq; subst; congruence).
      destruct (Hparts j p Hp) as [Hj [Hvp Him]]. split; [exact Hj|]. split; [exact Hvp|].
      rewrite kernel_map_set_other by exact Hne; exact Him.
    + split.
      * intros j p Hp; unfold kernel_map_set in Hp; destruct (Z.eq_dec j i) as [->|Hne].
        -- apply kernel_map_set_same.
        -- rewrite kernel_map_set_other by exact Hne; eapply Hprivateimage; eauto.
      * split.
        -- intros j Hp; unfold kernel_map_set in Hp; destruct (Z.eq_dec j i) as [->|Hne]; [discriminate|].
           rewrite kernel_map_set_other by exact Hne; apply Hdomain; exact Hp.
        -- split.
           ++ intros pre j suffix Hlist.
              assert (Hne : j <> i).
              { intro Heq; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
              destruct (Hlinks (i :: pre) j suffix ltac:(simpl; rewrite Hlist; reflexivity)) as [v [Him Hnext]].
              exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Him|exact Hnext].
           ++ intros j p Hp; unfold kernel_map_set in Hp; destruct (Z.eq_dec j i) as [->|Hne].
              ** inversion Hp; subst p; simpl; auto.
              ** destruct (Hprivate j p Hp) as [Hj [Hslot [Hpart Hfree]]].
                 split; [exact Hj|]. split; [exact Hslot|]. split; [exact Hpart|].
                 intro Hin; apply Hfree; right; exact Hin.
Qed.
Lemma memory_controls_merge_control : forall sg s i v,
  s.(memControlImages) i = Some v ->
  store_memory_control sg (memory_control_addr sg i) v ** memory_controls_without sg s i |--
    memory_controls_rep sg s.
Proof.
  intros; unfold memory_controls_rep, memory_controls_without.
  sep_apply_l_atomic (store_map_merge
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) i v _ H); entailer!.
Qed.

Lemma memory_publish_preserves_state_validity : forall sg s private,
  valid_memory_state sg s ->
  s.(memPrivateControls) private.(memPrivateSlot) = Some private ->
  memory_region_valid (memory_partition_initial s.(memNextGeneration)
    private.(memPrivateBase) private.(memPrivateBlockSize) private.(memPrivateBlockCount)
    private.(memPrivateImage).(memImageName)) ->
  valid_memory_state sg (memory_publish_control s private).
Proof.
  intros sg s private [[Hnd [Hrange Hslots]]
    [Hparts [Hprivateimage [Hdomain [Hlinks Hprivate]]]]] Hlookup Hregion.
  destruct (Hprivate _ _ Hlookup) as [Hi [Hslot [Hnone Hnot]]].
  unfold valid_memory_state, memory_publish_control; simpl.
  split.
  - unfold memory_control_partition; simpl; split; [exact Hnd|]. split; [exact Hrange|].
    intros j Hj; destruct (Z.eq_dec j (memPrivateSlot private)) as [->|Hne].
    + right; left; eexists; rewrite !kernel_map_set_same; auto.
    + rewrite !kernel_map_set_other by exact Hne; apply Hslots; exact Hj.
  - split.
    + intros j p Hp; unfold kernel_map_set in Hp.
      destruct (Z.eq_dec j (memPrivateSlot private)) as [->|Hne].
      * inversion Hp; subst p; split; [exact Hi|]. split.
        -- apply memory_create_establishes_partition; exact Hregion.
        -- apply kernel_map_set_same.
      * destruct (Hparts j p Hp) as [Hj [Hvalid Himage]].
        split; [exact Hj|]. split; [exact Hvalid|].
        rewrite kernel_map_set_other by exact Hne; exact Himage.
    + split.
      * intros j p Hp; unfold kernel_map_set in Hp.
        destruct (Z.eq_dec j (memPrivateSlot private)) as [->|Hne]; [discriminate|].
        rewrite kernel_map_set_other by exact Hne; eapply Hprivateimage; eauto.
      * split.
        -- intros j Hp; destruct (Z.eq_dec j (memPrivateSlot private)) as [->|Hne].
           ++ rewrite kernel_map_set_same; split; [intros; exact Hi|eauto].
           ++ rewrite kernel_map_set_other in Hp |- * by exact Hne; apply Hdomain; exact Hp.
        -- split.
           ++ intros pre j rest Hlist.
              assert (Hne : j <> memPrivateSlot private).
              { intro Heq; subst j; apply Hnot; rewrite Hlist; apply in_or_app; right; left; reflexivity. }
              destruct (Hlinks pre j rest Hlist) as [v [Himage Hnext]].
              exists v; split; [rewrite kernel_map_set_other by exact Hne; exact Himage|exact Hnext].
           ++ intros j p Hp; unfold kernel_map_set in Hp.
              destruct (Z.eq_dec j (memPrivateSlot private)) as [->|Hne]; [discriminate|].
              destruct (Hprivate j p Hp) as [Hj [Hslotj [Hpart Hfree]]].
              split; [exact Hj|]. split; [exact Hslotj|]. split; [|exact Hfree].
              rewrite kernel_map_set_other by exact Hne; exact Hpart.
Qed.

Lemma memory_reserve_transfers_control : forall sg s base extent size count private post,
  memory_reserve_control s base extent size count = Some (private, post) ->
  memory_controls_rep sg s |--
    memory_private_control_rep sg private ** memory_controls_rep sg post.
Proof.
  intros sg s base extent size count private post Hstep.
  unfold memory_reserve_control in Hstep.
  destruct (memFreeControls s) as [|i rest]; [discriminate|].
  destruct (memControlImages s i) as [old|] eqn:E; [|discriminate].
  inversion Hstep; subst private post; unfold memory_controls_rep, memory_private_control_rep; simpl.
  sep_apply_l_atomic (store_map_split
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) i old _ E).
  assert (Hframe : forall j, j <> i ->
    memControlImages s j = kernel_map_set (memControlImages s) i None j).
  { intros; symmetry; apply kernel_map_set_other; assumption. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) _ _ i Hframe)).
  sep_apply_l_atomic (store_map_missing_equiv_store_map
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) _ i
    (kernel_map_set_same _ (memControlImages s) i None)); entailer!.
Qed.

(** Publication consumes the fully written MCB.  The arena's free-block
    cells are a separate premise, so no initialization store is hidden
    in a spatial entailment. *)
Lemma memory_publish_merges_control : forall sg s private,
  s.(memControlImages) private.(memPrivateSlot) = None ->
  store_memory_control sg (memory_control_addr sg private.(memPrivateSlot))
    (memory_partition_image (memory_partition_initial s.(memNextGeneration)
      private.(memPrivateBase) private.(memPrivateBlockSize) private.(memPrivateBlockCount)
      private.(memPrivateImage).(memImageName))) ** memory_controls_rep sg s |--
  memory_controls_rep sg (memory_publish_control s private).
Proof.
  intros sg s private Hnone; unfold memory_controls_rep, memory_publish_control; simpl.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) _ _ Hnone).
  assert (Hframe : forall j, j <> memPrivateSlot private -> memControlImages s j =
    kernel_map_set (memControlImages s) (memPrivateSlot private)
      (Some (memory_partition_image (memory_partition_initial (memNextGeneration s)
        (memPrivateBase private) (memPrivateBlockSize private) (memPrivateBlockCount private)
        (memImageName (memPrivateImage private))))) j).
  { intros; symmetry; apply kernel_map_set_other; assumption. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) _ _ _ Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun i v => store_memory_control sg (memory_control_addr sg i) v)
    (memPrivateSlot private)
    (memory_partition_image (memory_partition_initial (memNextGeneration s)
      (memPrivateBase private) (memPrivateBlockSize private) (memPrivateBlockCount private)
      (memImageName (memPrivateImage private)))) _
    (kernel_map_set_same _ (memControlImages s) (memPrivateSlot private) _)); entailer!.
Qed.

Lemma memory_arena_bytes_to_link_word : forall p,
  p mod 4 = 0 -> UCharArray.undef_full p 4 |-- p # Ptr |->_ .
Proof.
  intros p Halign.
  unfold UCharArray.undef_full, store_undef_array; simpl.
  unfold StoreUCharAsElement.undefstoreA; simpl.
  unfold undef_store_uchar, undef_store_ptr, store_4byte_noninit, isvalidptr; simpl.
  entailer!.
  all: unfold isvalidptr_char in *; simpl in *.
  - rewrite Z.add_0_r; entailer!.
  - lia.
  - change (p + 4 - 1 <= addr_max_unsigned); lia.
Qed.

(** This assertion is a byte-layout view of the local Create progress.
    QCP's existing iter_sepcon owns the completed blocks; its ordinary
    undef array owns the suffix that has not yet received link stores. *)
Definition memory_private_linked_block_rep (p : MemoryPrivatePartition) (i : Z) : Assertion :=
  (p.(memPrivateBase) + i * p.(memPrivateBlockSize)) # Ptr |->
    (if Z.eqb (i + 1) p.(memPrivateBlockCount) then 0
      else p.(memPrivateBase) + (i + 1) * p.(memPrivateBlockSize)) **
  UCharArray.undef_full (p.(memPrivateBase) + i * p.(memPrivateBlockSize) + 4) (p.(memPrivateBlockSize) - 4).

Definition memory_private_linked_prefix_rep (p : MemoryPrivatePartition) : Assertion :=
  iter_sepcon (map (memory_private_linked_block_rep p) (Zrange 0 p.(memPrivateLinkedPrefix))) **
  UCharArray.undef_full (p.(memPrivateBase) + p.(memPrivateLinkedPrefix) * p.(memPrivateBlockSize))
    ((p.(memPrivateBlockCount) - p.(memPrivateLinkedPrefix)) * p.(memPrivateBlockSize)).

Lemma memory_private_prefix_publish_eq : forall s private prefix,
  memory_publish_control s (memory_private_set_prefix private prefix) = memory_publish_control s private.
Proof. reflexivity. Qed.

Lemma memory_private_linked_block_prefix_frame : forall private prefix i,
  memory_private_linked_block_rep (memory_private_set_prefix private prefix) i =
    memory_private_linked_block_rep private i.
Proof. reflexivity. Qed.

Lemma memory_private_arena_starts_linked_prefix : forall p,
  p.(memPrivateLinkedPrefix) = 0 ->
  p.(memPrivateExtent) = p.(memPrivateBlockSize) * p.(memPrivateBlockCount) ->
  memory_private_arena_rep p |-- memory_private_linked_prefix_rep p.
Proof.
  intros p Hp He; unfold memory_private_arena_rep, memory_private_linked_prefix_rep.
  rewrite Hp; simpl; rewrite He.
  replace (memPrivateBase p + 0 * memPrivateBlockSize p) with (memPrivateBase p) by lia.
  replace ((memPrivateBlockCount p - 0) * memPrivateBlockSize p)
    with (memPrivateBlockSize p * memPrivateBlockCount p) by lia.
  rewrite <- derivable1_iter_sepcon_r; simpl.
  rewrite Z.add_0_r; entailer!.
Qed.

Lemma memory_private_current_link_aligned : forall p,
  memory_private_initialization_valid p ->
  (p.(memPrivateBase) + p.(memPrivateLinkedPrefix) * p.(memPrivateBlockSize)) mod 4 = 0.
Proof.
  intros p [Hr _]; unfold memory_region_valid, memory_partition_initial in Hr; simpl in Hr.
  destruct Hr as [_ [Hb [_ [Hs _]]]].
  rewrite Z.add_mod, Z.mul_mod, Hb, Hs by lia; rewrite Z.mul_0_r; reflexivity.
Qed.

Lemma memory_initialize_next_link_addresses_in_range : forall p address next post,
  memory_private_initialization_valid p -> memory_initialize_next_link p = Some ((address, next), post) ->
  0 < address /\ address + 4 <= 4294967296 /\ address mod 4 = 0 /\ 0 <= next < 4294967296.
Proof.
  intros p address next post Hvalid Hstep.
  pose proof (memory_private_current_link_aligned p Hvalid) as Ha.
  destruct Hvalid as [Hr [He Hp]]; unfold memory_region_valid, memory_partition_initial in Hr; simpl in Hr.
  destruct Hr as [Hb [Hab [Hsize [Has [Hcount Hend]]]]].
  unfold memory_initialize_next_link in Hstep.
  destruct (memPrivateLinkedPrefix p <? memPrivateBlockCount p) eqn:E; [|discriminate].
  apply Z.ltb_lt in E; inversion Hstep; subst address next post.
  split; [nia|]; split; [nia|]; split; [exact Ha|].
  destruct (Z.eqb (memPrivateLinkedPrefix p + 1) (memPrivateBlockCount p)) eqn:Elast;
    [split; lia|apply Z.eqb_neq in Elast; split; nia].
Qed.

Definition memory_private_next_link_frame (p : MemoryPrivatePartition) : Assertion :=
  iter_sepcon (map (memory_private_linked_block_rep p) (Zrange 0 p.(memPrivateLinkedPrefix))) **
  UCharArray.undef_full (p.(memPrivateBase) + p.(memPrivateLinkedPrefix) * p.(memPrivateBlockSize) + 4)
    (p.(memPrivateBlockSize) - 4) **
  UCharArray.undef_full (p.(memPrivateBase) + (p.(memPrivateLinkedPrefix) + 1) * p.(memPrivateBlockSize))
    ((p.(memPrivateBlockCount) - p.(memPrivateLinkedPrefix) - 1) * p.(memPrivateBlockSize)).

Lemma memory_private_linked_prefix_split_next_word : forall p,
  memory_private_initialization_valid p -> p.(memPrivateLinkedPrefix) < p.(memPrivateBlockCount) ->
  memory_private_linked_prefix_rep p |--
    (p.(memPrivateBase) + p.(memPrivateLinkedPrefix) * p.(memPrivateBlockSize)) # Ptr |->_ **
    memory_private_next_link_frame p.
Proof.
  intros p Hvalid Hlt.
  pose proof (memory_private_current_link_aligned p Hvalid) as Halign.
  destruct Hvalid as [Hr [He Hp]].
  unfold memory_region_valid, memory_partition_initial in Hr; simpl in Hr.
  destruct Hr as [Hb [Hab [Hsize [Has [Hcount Hend]]]]].
  unfold memory_private_linked_prefix_rep, memory_private_next_link_frame.
  sep_apply_l_atomic (UCharArray.undef_full_split_to_undef_full
    (memPrivateBase p + memPrivateLinkedPrefix p * memPrivateBlockSize p)
    (memPrivateBlockSize p) ((memPrivateBlockCount p - memPrivateLinkedPrefix p) * memPrivateBlockSize p) ltac:(nia)).
  sep_apply_l_atomic (UCharArray.undef_full_split_to_undef_full
    (memPrivateBase p + memPrivateLinkedPrefix p * memPrivateBlockSize p) 4 (memPrivateBlockSize p) ltac:(lia)).
  sep_apply_l_atomic (memory_arena_bytes_to_link_word _ Halign).
  replace ((memPrivateBlockCount p - memPrivateLinkedPrefix p) * memPrivateBlockSize p - memPrivateBlockSize p)
    with ((memPrivateBlockCount p - memPrivateLinkedPrefix p - 1) * memPrivateBlockSize p) by ring.
  entailer!.
  change (sizeof(UCHAR)) with 1.
  replace (memPrivateBase p + memPrivateLinkedPrefix p * memPrivateBlockSize p + memPrivateBlockSize p * 1)
    with (memPrivateBase p + (memPrivateLinkedPrefix p + 1) * memPrivateBlockSize p) by ring.
  replace (memPrivateBase p + memPrivateLinkedPrefix p * memPrivateBlockSize p + 4 * 1)
    with (memPrivateBase p + memPrivateLinkedPrefix p * memPrivateBlockSize p + 4) by ring.
  entailer!.
Qed.

Lemma memory_private_linked_prefix_merge_next_word : forall p address next post,
  memory_private_initialization_valid p -> memory_initialize_next_link p = Some ((address, next), post) ->
  address # Ptr |-> next ** memory_private_next_link_frame p |-- memory_private_linked_prefix_rep post.
Proof.
  intros p address next post Hvalid Hstep.
  destruct Hvalid as [Hr [He Hp]].
  unfold memory_initialize_next_link in Hstep.
  destruct (memPrivateLinkedPrefix p <? memPrivateBlockCount p) eqn:E; [|discriminate].
  apply Z.ltb_lt in E; inversion Hstep; subst address next post.
  unfold memory_private_next_link_frame, memory_private_linked_prefix_rep.
  change (memory_private_linked_block_rep (memory_private_set_prefix p (memPrivateLinkedPrefix p + 1)))
    with (memory_private_linked_block_rep p).
  cbv beta iota zeta delta [memory_private_set_prefix memPrivateBase memPrivateBlockSize
    memPrivateBlockCount memPrivateLinkedPrefix].
  fold (memPrivateBase p) (memPrivateBlockSize p) (memPrivateBlockCount p) (memPrivateLinkedPrefix p).
  assert (Hindices : Zrange 0 (memPrivateLinkedPrefix p + 1) = Zrange 0 (memPrivateLinkedPrefix p) ++ [memPrivateLinkedPrefix p]).
  { unfold Zrange; rewrite !Z.sub_0_r, Z2Nat.inj_add by lia.
    rewrite Zrange_aux_app, Z2Nat.id by lia; rewrite Z.add_0_l; reflexivity. }
  rewrite Hindices, map_app.
  rewrite <- derivable1_sepcon_iter_sepcon1.
  replace ((memPrivateBlockCount p - (memPrivateLinkedPrefix p + 1)) * memPrivateBlockSize p)
    with ((memPrivateBlockCount p - memPrivateLinkedPrefix p - 1) * memPrivateBlockSize p) by ring.
  rewrite <- (derivable1_iter_sepcon_r [memory_private_linked_block_rep p (memPrivateLinkedPrefix p)]); simpl.
  unfold memory_private_linked_block_rep; entailer!.
Qed.

Lemma memory_initialized_range_to_free_blocks : forall p generation n low,
  p.(memPrivateBlockCount) = low + Z.of_nat n ->
  iter_sepcon (map (memory_private_linked_block_rep p) (Zrange_aux low n)) |--
    store_memory_free_blocks (memory_partition_initial generation p.(memPrivateBase)
      p.(memPrivateBlockSize) p.(memPrivateBlockCount) p.(memPrivateImage).(memImageName)) (Zrange_aux low n).
Proof.
  intros p generation n; induction n as [|n IH]; intros low Hcount.
  - simpl; rewrite derivable1_iter_sepcon_l; simpl; entailer!.
  - change (iter_sepcon ([memory_private_linked_block_rep p low] ++
      map (memory_private_linked_block_rep p) (Zrange_aux (low + 1) n)) |--
      memory_free_block_rep (memory_partition_initial generation (memPrivateBase p) (memPrivateBlockSize p)
        (memPrivateBlockCount p) (memImageName (memPrivateImage p))) low
        (memory_free_head (memory_partition_initial generation (memPrivateBase p) (memPrivateBlockSize p)
          (memPrivateBlockCount p) (memImageName (memPrivateImage p))) (Zrange_aux (low + 1) n)) **
      store_memory_free_blocks (memory_partition_initial generation (memPrivateBase p) (memPrivateBlockSize p)
        (memPrivateBlockCount p) (memImageName (memPrivateImage p))) (Zrange_aux (low + 1) n)).
    rewrite derivable1_sepcon_iter_sepcon2.
    sep_apply_l_atomic (IH (low + 1) ltac:(rewrite Nat2Z.inj_succ in Hcount; lia)).
    rewrite derivable1_iter_sepcon_l; simpl.
    assert (Hnext : (if Z.eqb (low + 1) (memPrivateBlockCount p) then 0
        else memPrivateBase p + (low + 1) * memPrivateBlockSize p) =
      memory_free_head (memory_partition_initial generation (memPrivateBase p) (memPrivateBlockSize p)
        (memPrivateBlockCount p) (memImageName (memPrivateImage p))) (Zrange_aux (low + 1) n)).
    { destruct n as [|n]; simpl in Hcount |- *.
      - assert (E : (low + 1 =? memPrivateBlockCount p) = true) by (apply Z.eqb_eq; lia).
        rewrite E; reflexivity.
      - assert (E : (low + 1 =? memPrivateBlockCount p) = false) by (apply Z.eqb_neq; lia).
        rewrite E; reflexivity. }
    unfold memory_private_linked_block_rep; rewrite Hnext.
    unfold memory_free_block_rep, memory_block_tail, memory_block_addr; simpl; entailer!.
Qed.

Lemma memory_private_linked_prefix_completed : forall p generation,
  memory_private_initialization_valid p -> p.(memPrivateLinkedPrefix) = p.(memPrivateBlockCount) ->
  memory_private_linked_prefix_rep p |--
    store_memory_free_blocks (memory_partition_initial generation p.(memPrivateBase)
      p.(memPrivateBlockSize) p.(memPrivateBlockCount) p.(memPrivateImage).(memImageName))
      (Zrange 0 p.(memPrivateBlockCount)).
Proof.
  intros p generation [_ [_ Hp]] Hdone.
  unfold memory_private_linked_prefix_rep; rewrite Hdone, Z.sub_diag, Z.mul_0_l.
  sep_apply_l_atomic (proj1 (UCharArray.undef_full_empty
    (memPrivateBase p + memPrivateBlockCount p * memPrivateBlockSize p))).
  unfold Zrange; rewrite Z.sub_0_r.
  sep_apply_l_atomic (memory_initialized_range_to_free_blocks p generation (Z.to_nat (memPrivateBlockCount p)) 0
    ltac:(rewrite Z2Nat.id by lia; lia)); entailer!.
Qed.

(** Both the MCB fields and every arena link have already been stored at
    this cutpoint.  The reservation descriptor stays unchanged in the
    private registry while local prefix progress advances. *)
Lemma memory_publish_reconstructs_raw_rep : forall sg s private,
  memory_private_initialization_valid private ->
  s.(memControlImages) private.(memPrivateSlot) = None -> s.(memPartitions) private.(memPrivateSlot) = None ->
  store_memory_control sg (memory_control_addr sg private.(memPrivateSlot))
    (memory_partition_image (memory_partition_initial s.(memNextGeneration) private.(memPrivateBase)
      private.(memPrivateBlockSize) private.(memPrivateBlockCount) private.(memPrivateImage).(memImageName))) **
  memory_private_linked_prefix_rep (memory_private_set_prefix private private.(memPrivateBlockCount)) **
    memory_raw_rep sg s |-- memory_raw_rep sg (memory_publish_control s private).
Proof.
  intros sg s private Hinit Hnone Hpartnone.
  set (partition := memory_partition_initial s.(memNextGeneration) private.(memPrivateBase)
    private.(memPrivateBlockSize) private.(memPrivateBlockCount) private.(memPrivateImage).(memImageName)).
  assert (Hcompleted : memory_private_initialization_valid
    (memory_private_set_prefix private private.(memPrivateBlockCount))).
  { destruct Hinit as [Hr [He Hp]]; unfold memory_private_initialization_valid; simpl.
    split; [exact Hr|]; split; [exact He|lia]. }
  pose proof (memory_private_linked_prefix_completed
    (memory_private_set_prefix private private.(memPrivateBlockCount)) s.(memNextGeneration) Hcompleted eq_refl) as Hblocks.
  change (memory_private_linked_prefix_rep (memory_private_set_prefix private private.(memPrivateBlockCount)) |--
    store_memory_free_blocks partition partition.(memFreeBlocks)) in Hblocks.
  unfold memory_raw_rep.
  sep_apply_l_atomic Hblocks.
  pose proof (memory_publish_merges_control sg s private Hnone) as Hcontrol.
  fold partition in Hcontrol.
  sep_apply Hcontrol.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) s.(memPartitions) private.(memPrivateSlot) Hpartnone).
  assert (Hframe : forall j, j <> private.(memPrivateSlot) ->
    s.(memPartitions) j = (memory_publish_control s private).(memPartitions) j).
  { intros; change (memPartitions s j = kernel_map_set (memPartitions s) (memPrivateSlot private) (Some partition) j).
    symmetry; apply kernel_map_set_other; assumption. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) s.(memPartitions)
      (memory_publish_control s private).(memPartitions) private.(memPrivateSlot) Hframe)).
  assert (Hnew : (memory_publish_control s private).(memPartitions) private.(memPrivateSlot) = Some partition)
    by (apply kernel_map_set_same).
  sep_apply_l_atomic (store_map_merge (fun _ p => store_memory_free_blocks p p.(memFreeBlocks))
    private.(memPrivateSlot) partition (memory_publish_control s private).(memPartitions) Hnew).
  change ((memory_publish_control s private).(memFreeControls)) with s.(memFreeControls); entailer!.
Qed.

(** OSMemCreate writes these five MCB fields after its arena loop, with
    interrupts restored.  It does not write OSMemName. *)
Definition memory_create_control_writes (p : MemoryPrivatePartition) : list (MemoryControlField * Z) :=
  [(MCBAddr, p.(memPrivateBase)); (MCBFreeList, p.(memPrivateBase));
   (MCBNFree, p.(memPrivateBlockCount)); (MCBNBlks, p.(memPrivateBlockCount));
   (MCBBlkSize, p.(memPrivateBlockSize))].

Definition memory_create_control_image (p : MemoryPrivatePartition) : MemoryControlImage :=
  fold_left (fun image write => memory_control_set_field image (fst write) (snd write))
    (memory_create_control_writes p) p.(memPrivateImage).

Lemma memory_create_control_writes_are_present : forall c p field value,
  In (field, value) (memory_create_control_writes p) -> In field (memory_control_fields c).
Proof.
  intros c p field value H; unfold memory_create_control_writes in H;
    simpl in H; destruct H as [H|[H|[H|[H|[H|H]]]]];
    try contradiction; inversion H; subst field;
    unfold memory_control_fields; apply in_or_app; left; simpl; tauto.
Qed.

Lemma memory_create_control_image_name_eq : forall p,
  (memory_create_control_image p).(memImageName) = p.(memPrivateImage).(memImageName).
Proof. reflexivity. Qed.

Lemma memory_create_control_values_in_range : forall p field value,
  memory_private_initialization_valid p ->
  In (field, value) (memory_create_control_writes p) -> 0 <= value < 4294967296.
Proof.
  intros p field value [Hr _] Hwrite.
  unfold memory_region_valid, memory_partition_initial in Hr; simpl in Hr.
  destruct Hr as [Hb [Hab [Hsize [Has [Hcount Hend]]]]].
  unfold memory_create_control_writes in Hwrite; simpl in Hwrite.
  destruct Hwrite as [H|[H|[H|[H|[H|H]]]]];
    try contradiction; inversion H; subst value; nia.
Qed.

Lemma memory_get_image_fields_eq : forall v next,
  memory_get_image v next =
    memory_control_set_field (memory_control_set_field v MCBFreeList next)
      MCBNFree (kernel_u32 (v.(memImageNFree) - 1)).
Proof. reflexivity. Qed.

Lemma memory_put_image_fields_eq : forall v block,
  memory_put_image v block =
    memory_control_set_field (memory_control_set_field v MCBFreeList block)
      MCBNFree (kernel_u32 (v.(memImageNFree) + 1)).
Proof. reflexivity. Qed.

Lemma memory_create_control_image_partition_eq : forall p generation,
  0 < p.(memPrivateBlockCount) ->
  memory_create_control_image p =
    memory_partition_image (memory_partition_initial generation p.(memPrivateBase)
      p.(memPrivateBlockSize) p.(memPrivateBlockCount) p.(memPrivateImage).(memImageName)).
Proof.
  intros p generation Hcount.
  unfold memory_create_control_image, memory_create_control_writes; simpl.
  unfold memory_partition_image, memory_partition_initial; simpl.
  assert (Hlength : Z.of_nat (List.length (Zrange 0 (memPrivateBlockCount p))) = memPrivateBlockCount p).
  { rewrite kernel_zrange_length, Z2Nat.id by lia; lia. }
  rewrite Hlength.
  assert (Hhead : memory_free_head
    {| memGeneration := generation; memBase := memPrivateBase p; memBlockSize := memPrivateBlockSize p;
       memBlockCount := memPrivateBlockCount p; memFreeBlocks := Zrange 0 (memPrivateBlockCount p);
       memAllocatedBlocks := fun _ => None; memName := memImageName (memPrivateImage p); memNextLoan := O |}
    (Zrange 0 (memPrivateBlockCount p)) = memPrivateBase p).
  { unfold memory_free_head, Zrange; rewrite Z.sub_0_r.
    destruct (Z.to_nat (memPrivateBlockCount p)) as [|n] eqn:E.
    - pose proof (Z2Nat.id (memPrivateBlockCount p) ltac:(lia)) as Hnat.
      rewrite E in Hnat; simpl in Hnat; lia.
    - simpl; unfold memory_block_addr; simpl; lia. }
  rewrite Hhead; reflexivity.
Qed.

Definition memory_raw_rep_without_free_root (sg : StableGlobVars) (s : GlobMemoryState) : Assertion :=
  memory_controls_rep sg s **
  store_map (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) s.(memPartitions).

Lemma memory_reserve_root_values_eq : forall sg s base extent size count private post,
  valid_memory_state sg s ->
  memory_reserve_control s base extent size count = Some (private, post) ->
  (match s.(memFreeControls) with [] => 0 | i :: _ => memory_control_addr sg i end) =
    memory_control_addr sg private.(memPrivateSlot) /\
  private.(memPrivateImage).(memImageFree) =
    (match post.(memFreeControls) with [] => 0 | i :: _ => memory_control_addr sg i end).
Proof.
  intros sg s base extent size count private post Hv Hstep.
  destruct Hv as [_ [_ [_ [_ [Hlinks _]]]]].
  unfold memory_reserve_control in Hstep.
  destruct (memFreeControls s) as [|i rest] eqn:E; [discriminate|].
  destruct (memControlImages s i) as [old|] eqn:Ei; [|discriminate].
  inversion Hstep; subst private post; simpl.
  destruct (Hlinks [] i rest eq_refl) as [v [Ev Hnext]].
  rewrite Ei in Ev; inversion Ev; subst v; split; [reflexivity|exact Hnext].
Qed.

Lemma memory_reserve_split_free_root : forall sg s base extent size count private post,
  valid_memory_state sg s ->
  memory_reserve_control s base extent size count = Some (private, post) ->
  memory_raw_rep sg s |--
    sg.(g_OSMemFreeList) # Ptr |-> memory_control_addr sg private.(memPrivateSlot) **
    memory_raw_rep_without_free_root sg s.
Proof.
  intros sg s base extent size count private post Hv Hstep.
  pose proof (proj1 (memory_reserve_root_values_eq sg s base extent size count private post Hv Hstep)) as Hroot.
  unfold memory_raw_rep, memory_raw_rep_without_free_root; rewrite Hroot; entailer!.
Qed.

(** The global-root store has occurred; its new value is the next link
    read from the original MCB.  No MCB field or arena byte is rewritten
    by this spatial transfer into private ownership. *)
Lemma memory_reserve_reconstructs_raw_rep : forall sg s base extent size count private post,
  valid_memory_state sg s ->
  memory_reserve_control s base extent size count = Some (private, post) ->
  sg.(g_OSMemFreeList) # Ptr |-> private.(memPrivateImage).(memImageFree) **
    memory_raw_rep_without_free_root sg s |--
    memory_private_control_rep sg private ** memory_raw_rep sg post.
Proof.
  intros sg s base extent size count private post Hv Hstep.
  pose proof (proj2 (memory_reserve_root_values_eq sg s base extent size count private post Hv Hstep)) as Hroot.
  unfold memory_raw_rep_without_free_root, memory_raw_rep.
  sep_apply_l_atomic (memory_reserve_transfers_control sg s base extent size count private post Hstep).
  assert (Hparts : post.(memPartitions) = s.(memPartitions)).
  { unfold memory_reserve_control in Hstep.
    destruct (memFreeControls s) as [|i rest]; [discriminate|].
    destruct (memControlImages s i); [|discriminate].
    inversion Hstep; reflexivity. }
  rewrite Hroot, Hparts; entailer!.
Qed.

(** Runtime operations do not reinitialize an existing partition.  This
    source-operation classification is separate from validity and from a
    client's generic Task/Event certificate.  In particular OS_MemInit's
    boot reset is not one of these runtime operations. *)
Definition memory_partition_geometry_eq (before after : MemoryPartitionState) : Prop :=
  before.(memGeneration) = after.(memGeneration) /\
  before.(memBase) = after.(memBase) /\
  before.(memBlockSize) = after.(memBlockSize) /\
  before.(memBlockCount) = after.(memBlockCount).

Lemma memory_partition_geometry_eq_refl : forall p, memory_partition_geometry_eq p p.
Proof. intros; repeat split; reflexivity. Qed.

Lemma memory_partition_geometry_eq_trans : forall p q r,
  memory_partition_geometry_eq p q -> memory_partition_geometry_eq q r ->
  memory_partition_geometry_eq p r.
Proof. unfold memory_partition_geometry_eq; intros; intuition congruence. Qed.

(** NameSet changes the name only. The relation below is a shape of an
    actual name store, not a claim that a C NameSet implementation has been
    verified. Its other fields are the old fields, including allocation
    identities. Existing operations and records retain their statements. *)
Definition memory_partition_set_name (p : MemoryPartitionState) (name : addr)
  : MemoryPartitionState :=
  {| memGeneration := p.(memGeneration); memBase := p.(memBase);
     memBlockSize := p.(memBlockSize); memBlockCount := p.(memBlockCount);
     memFreeBlocks := p.(memFreeBlocks); memAllocatedBlocks := p.(memAllocatedBlocks);
     memName := name; memNextLoan := p.(memNextLoan) |}.

Lemma memory_partition_set_name_image_eq : forall p name,
  memory_partition_image (memory_partition_set_name p name) =
    memory_control_set_field (memory_partition_image p) MCBName name.
Proof. intros; reflexivity. Qed.

Inductive memory_runtime_step : GlobMemoryState -> GlobMemoryState -> Prop :=
| MemoryRuntimeFramesPartitions : forall before after,
    after.(memPartitions) = before.(memPartitions) ->
    memory_runtime_step before after
| MemoryRuntimeGet : forall before id loan after,
    memory_get before id = Some (loan, after) -> memory_runtime_step before after
| MemoryRuntimePut : forall before id block after,
    memory_put before id block = Some after -> memory_runtime_step before after
| MemoryRuntimeReserve : forall before base extent size count private after,
    memory_reserve_control before base extent size count = Some (private, after) ->
    memory_runtime_step before after
| MemoryRuntimePublish : forall before private,
    before.(memPartitions) private.(memPrivateSlot) = None ->
    memory_runtime_step before (memory_publish_control before private)
| MemoryRuntimeSetName : forall before id p name,
    before.(memPartitions) id = Some p ->
    memory_runtime_step before
      (memory_replace_partition before id (memory_partition_set_name p name)).

Lemma memory_runtime_publish_from_reservation : forall sg before private,
  valid_memory_state sg before ->
  before.(memPrivateControls) private.(memPrivateSlot) = Some private ->
  memory_runtime_step before (memory_publish_control before private).
Proof.
  intros sg before private [_ [_ [_ [_ [_ Hprivate]]]]] Hlookup.
  apply MemoryRuntimePublish.
  exact (proj1 (proj2 (proj2 (Hprivate _ _ Hlookup)))).
Qed.

Lemma memory_get_partition_geometry_eq : forall id p loan post,
  memory_get_partition id p = Some (loan, post) -> memory_partition_geometry_eq p post.
Proof.
  intros id p loan post Hget; unfold memory_get_partition in Hget.
  destruct (memFreeBlocks p); [discriminate|].
  inversion Hget; repeat split; reflexivity.
Qed.

Lemma memory_runtime_step_preserves_partition_geometry : forall before after id p,
  memory_runtime_step before after -> before.(memPartitions) id = Some p ->
  exists q, after.(memPartitions) id = Some q /\ memory_partition_geometry_eq p q.
Proof.
  intros before after id p Hstep Hlookup; destruct Hstep.
  - rewrite H; exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
  - unfold memory_get in H.
    destruct (memPartitions before id0) as [old|] eqn:Hold; [|discriminate].
    destruct (memory_get_partition id0 old) as [[l post]|] eqn:Hget; [|discriminate].
    inversion H; subst; clear H; simpl.
    destruct (Z.eq_dec id id0) as [->|Hne].
    + assert (p = old) by congruence; subst p.
      exists post; split; [apply kernel_map_set_same|].
      eapply memory_get_partition_geometry_eq; eassumption.
    + rewrite kernel_map_set_other by exact Hne.
      exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
  - unfold memory_put in H.
    destruct (memPartitions before id0) as [old|] eqn:Hold; [|discriminate].
    inversion H; subst; clear H; simpl.
    destruct (Z.eq_dec id id0) as [->|Hne].
    + assert (p = old) by congruence; subst p.
      exists (memory_put_partition old block); split; [apply kernel_map_set_same|].
      repeat split; reflexivity.
    + rewrite kernel_map_set_other by exact Hne.
      exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
  - unfold memory_reserve_control in H.
    destruct (memFreeControls before) as [|head rest]; [discriminate|].
    destruct (memControlImages before head); [|discriminate].
    inversion H; subst; exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
  - simpl; assert (Hne : id <> memPrivateSlot private) by (intro E; subst; congruence).
    rewrite kernel_map_set_other by exact Hne.
    exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
  - simpl; destruct (Z.eq_dec id id0) as [->|Hne].
    + assert (p = p0) by congruence; subst p.
      exists (memory_partition_set_name p0 name); split; [apply kernel_map_set_same|].
      repeat split; reflexivity.
    + rewrite kernel_map_set_other by exact Hne.
      exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
Qed.

Lemma memory_partition_geometry_block_addr_eq : forall p q block,
  memory_partition_geometry_eq p q -> memory_block_addr p block = memory_block_addr q block.
Proof. unfold memory_partition_geometry_eq, memory_block_addr; intros; intuition congruence. Qed.

Lemma memory_partition_geometry_block_storage_eq : forall p q block,
  memory_partition_geometry_eq p q -> memory_block_storage p block = memory_block_storage q block.
Proof.
  intros p q block [_ [Hb [Hs _]]].
  unfold memory_block_storage, memory_free_block_rep, memory_block_tail, memory_block_addr.
  rewrite Hb, Hs; reflexivity.
Qed.

Lemma memory_allocated_block_in_range : forall id p block loan,
  valid_memory_partition id p -> p.(memAllocatedBlocks) block = Some loan ->
  0 <= block < p.(memBlockCount).
Proof.
  intros id p block loan [_ [_ [_ [Hpartition _]]]] Hlookup.
  exact (proj1 (proj1 (Hpartition block) (ex_intro _ loan Hlookup))).
Qed.

(** A caller that supplies no block storage can use the full-error branch
    when other clients do not allocate from this particular partition.
    Other partitions, names and control reservations remain unrestricted.
    This is an operation-level rely, not a future acquired-state premise. *)
Inductive memory_runtime_without_get_at (protected : MemID)
  : GlobMemoryState -> GlobMemoryState -> Prop :=
| MemoryNoGetFrames : forall before after,
    after.(memPartitions) = before.(memPartitions) ->
    memory_runtime_without_get_at protected before after
| MemoryNoGetOther : forall before id loan after,
    id <> protected -> memory_get before id = Some (loan, after) ->
    memory_runtime_without_get_at protected before after
| MemoryNoGetPut : forall before id block after,
    memory_put before id block = Some after ->
    memory_runtime_without_get_at protected before after
| MemoryNoGetReserve : forall before base extent size count private after,
    memory_reserve_control before base extent size count = Some (private, after) ->
    memory_runtime_without_get_at protected before after
| MemoryNoGetPublish : forall before private,
    before.(memPartitions) private.(memPrivateSlot) = None ->
    memory_runtime_without_get_at protected before (memory_publish_control before private)
| MemoryNoGetSetName : forall before id p name,
    before.(memPartitions) id = Some p ->
    memory_runtime_without_get_at protected before
      (memory_replace_partition before id (memory_partition_set_name p name)).

Lemma memory_runtime_without_get_at_runtime_step : forall id before after,
  memory_runtime_without_get_at id before after -> memory_runtime_step before after.
Proof.
  intros id before after Hstep; destruct Hstep;
    eauto using MemoryRuntimeFramesPartitions, MemoryRuntimeGet, MemoryRuntimePut,
      MemoryRuntimeReserve, MemoryRuntimePublish, MemoryRuntimeSetName.
Qed.

Lemma memory_runtime_without_get_at_preserves_full : forall id before after p,
  memory_runtime_without_get_at id before after -> before.(memPartitions) id = Some p ->
  p.(memBlockCount) <= Z.of_nat (List.length p.(memFreeBlocks)) ->
  exists q, after.(memPartitions) id = Some q /\
    q.(memBlockCount) <= Z.of_nat (List.length q.(memFreeBlocks)).
Proof.
  intros id before after p Hstep Hlookup Hfull; destruct Hstep.
  - rewrite H; exists p; auto.
  - unfold memory_get in H0.
    destruct (memPartitions before id0) as [old|] eqn:Hold; [|discriminate].
    destruct (memory_get_partition id0 old) as [[l post]|] eqn:Hget; [|discriminate].
    inversion H0; subst; simpl.
    rewrite kernel_map_set_other by congruence; exists p; auto.
  - unfold memory_put in H.
    destruct (memPartitions before id0) as [old|] eqn:Hold; [|discriminate].
    inversion H; subst; simpl.
    destruct (Z.eq_dec id id0) as [->|Hne].
    + assert (p = old) by congruence; subst p.
      exists (memory_put_partition old block); split; [apply kernel_map_set_same|].
      simpl; lia.
    + rewrite kernel_map_set_other by exact Hne; exists p; auto.
  - unfold memory_reserve_control in H.
    destruct (memFreeControls before) as [|head rest]; [discriminate|].
    destruct (memControlImages before head); [|discriminate].
    inversion H; subst; exists p; auto.
  - simpl; rewrite kernel_map_set_other by (intro E; subst; congruence).
    exists p; auto.
  - simpl; destruct (Z.eq_dec id id0) as [->|Hne].
    + assert (p = p0) by congruence; subst p.
      exists (memory_partition_set_name p0 name); split; [apply kernel_map_set_same|exact Hfull].
    + rewrite kernel_map_set_other by exact Hne; exists p; auto.
Qed.
