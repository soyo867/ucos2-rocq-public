Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.memory.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Source/os_mem.c: OSMemGet removes a head block and updates two MCB
    fields. OSMemPut first writes the old head into the returning block,
    then updates those two fields. These are success-segment resource
    bridges, not whole API specs. Put's membership/unique-return obligation
    comes from the caller's current allocation and actual block ownership,
    not a new C guard. No entailment below performs a store. *)

Definition memory_raw_rep_without_partition (sg : StableGlobVars)
  (s : GlobMemoryState) (id : MemID) : Assertion :=
  memory_controls_without sg s id **
  store_map_missing_i (fun _ p => store_memory_free_blocks p p.(memFreeBlocks))
    s.(memPartitions) id **
  sg.(g_OSMemFreeList) # Ptr |->
    (match s.(memFreeControls) with [] => 0 | i :: _ => memory_control_addr sg i end).

Lemma memory_raw_rep_split_partition : forall sg s id p,
  valid_memory_state sg s -> s.(memPartitions) id = Some p ->
  memory_raw_rep sg s |-- memory_partition_rep sg id p **
    memory_raw_rep_without_partition sg s id.
Proof.
  intros sg s id p [_ [Hparts _]] Hlookup.
  destruct (Hparts id p Hlookup) as [_ [_ Himage]].
  unfold memory_raw_rep, memory_partition_rep, memory_raw_rep_without_partition.
  sep_apply_l_atomic (memory_controls_split_control sg s id (memory_partition_image p) Himage).
  sep_apply_l_atomic (store_map_split
    (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) id p _ Hlookup); entailer!.
Qed.

Lemma memory_raw_rep_merge_updated_partition : forall sg s id p,
  memory_partition_rep sg id p ** memory_raw_rep_without_partition sg s id |--
    memory_raw_rep sg (memory_replace_partition s id p).
Proof.
  intros sg s id p.
  unfold memory_raw_rep, memory_partition_rep, memory_raw_rep_without_partition.
  sepcon_right_assoc.
  sep_apply_l_atomic (memory_controls_merge_updated_control sg s
    (memory_replace_partition s id p) id (memory_partition_image p)
    (kernel_map_set_same _ _ _ _)
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption)).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun _ p => store_memory_free_blocks p p.(memFreeBlocks))
    s.(memPartitions) (kernel_map_set s.(memPartitions) id (Some p)) id
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
  sep_apply_l_atomic (store_map_merge
    (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) id p
    (kernel_map_set s.(memPartitions) id (Some p)) (kernel_map_set_same _ _ _ _)).
  cbn [memory_replace_partition]; entailer!.
Qed.

Definition memory_control_without_free_fields (sg : StableGlobVars) (base : addr)
  (v : MemoryControlImage) : Assertion :=
  &(base # "os_mem" ->ₛ "OSMemAddr") # Ptr |-> v.(memImageBase) **
  &(base # "os_mem" ->ₛ "OSMemBlkSize") # UInt |-> v.(memImageSize) **
  &(base # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> v.(memImageCount) **
  (if sg.(osKernelConfig).(cfgMemoryNames) then
    &(base # "os_mem" ->ₛ "OSMemName") # Ptr |-> v.(memImageName) else emp).

Lemma store_memory_control_split_free_fields : forall sg base v,
  store_memory_control sg base v |--
  &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> v.(memImageFree) **
  &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> v.(memImageNFree) **
  memory_control_without_free_fields sg base v.
Proof.
  intros; rewrite store_memory_control_layout_equiv;
    unfold memory_control_without_free_fields; entailer!.
Qed.

Lemma store_memory_control_merge_updated_free_fields : forall sg base before after,
  before.(memImageBase) = after.(memImageBase) ->
  before.(memImageSize) = after.(memImageSize) ->
  before.(memImageCount) = after.(memImageCount) ->
  before.(memImageName) = after.(memImageName) ->
  &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> after.(memImageFree) **
  &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> after.(memImageNFree) **
  memory_control_without_free_fields sg base before |-- store_memory_control sg base after.
Proof.
  intros sg base before after Hb Hs Hc Hn; rewrite store_memory_control_layout_equiv.
  unfold memory_control_without_free_fields; rewrite Hb, Hs, Hc, Hn; entailer!.
Qed.

(** Get has already stored the next pointer and decremented the count.
    The old free-block heap still contains the returned block; this theorem
    transfers it to the caller instead of silently dropping it from the pool. *)
Lemma memory_get_reconstructs_raw_rep : forall sg s id p loan post,
  valid_memory_partition id p -> memory_get_partition id p = Some (loan, post) ->
  store_memory_control sg (memory_control_addr sg id)
    (memory_get_image (memory_partition_image p) (memory_free_head post post.(memFreeBlocks))) **
  store_memory_free_blocks p p.(memFreeBlocks) **
  memory_raw_rep_without_partition sg s id |--
    memory_block_loan post loan ** memory_raw_rep sg (memory_replace_partition s id post).
Proof.
  intros sg s id p loan post Hvalid Hget.
  rewrite (memory_get_refines_control_image id p loan post Hvalid Hget).
  sep_apply_l_atomic (memory_get_transfers_block id p loan post Hget).
  sep_apply_r_atomic (memory_raw_rep_merge_updated_partition sg s id post).
  unfold memory_partition_rep; entailer!.
Qed.

(** The first pointer word has the old free head, as written by Put.
    Arbitrary payload permissions are not a substitute for this post-store
    assertion. MCB fields likewise carry their actual unsigned updates. *)
Lemma memory_put_reconstructs_raw_rep : forall sg s id p block loan,
  valid_memory_partition id p -> p.(memAllocatedBlocks) block = Some loan ->
  store_memory_control sg (memory_control_addr sg id)
    (memory_put_image (memory_partition_image p) (memory_block_addr p block)) **
  memory_free_block_rep p block (memory_free_head p p.(memFreeBlocks)) **
  store_memory_free_blocks p p.(memFreeBlocks) **
  memory_raw_rep_without_partition sg s id |--
    memory_raw_rep sg (memory_replace_partition s id (memory_put_partition p block)).
Proof.
  intros sg s id p block loan Hvalid Hloan.
  rewrite (memory_put_refines_control_image id p block loan Hvalid Hloan).
  sep_apply_l_atomic (memory_put_restores_block p block).
  sep_apply_r_atomic (memory_raw_rep_merge_updated_partition sg s id (memory_put_partition p block)).
  unfold memory_partition_rep; entailer!.
Qed.

Lemma memory_get_resources_merge : forall sg s id p loan post,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  UCOS2_state_inv sg s -> s.(MemoryState).(memPartitions) id = Some p ->
  memory_get_partition id p = Some (loan, post) ->
  store_memory_control sg (memory_control_addr sg id)
    (memory_get_image (memory_partition_image p) (memory_free_head post post.(memFreeBlocks))) **
  store_memory_free_blocks p p.(memFreeBlocks) **
  memory_raw_rep_without_partition sg s.(MemoryState) id **
  UCOS2_raw_rep_missing_memory sg s |--
    memory_block_loan post loan **
    UCOS2_inv sg (replace_MemoryS (memory_replace_partition s.(MemoryState) id post) s).
Proof.
  intros sg s id p loan post Henabled Hvalid Hlookup Hget.
  assert (Hmemory : valid_memory_state sg s.(MemoryState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_memory_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  assert (Hpart : valid_memory_partition id p).
  { destruct Hmemory as [_ [Hparts _]]; exact (proj1 (proj2 (Hparts id p Hlookup))). }
  assert (Hpost : UCOS2_state_inv sg
    (replace_MemoryS (memory_replace_partition s.(MemoryState) id post) s)).
  { eapply UCOS2_memory_get_preserves_validity; [exact Henabled|exact Hvalid|].
    unfold memory_get; rewrite Hlookup, Hget; reflexivity. }
  sep_apply_l_atomic (memory_get_reconstructs_raw_rep sg s.(MemoryState) id p loan post Hpart Hget).
  pose proof (UCOS2_inv_merge_updated_memory sg s
    (replace_MemoryS (memory_replace_partition s.(MemoryState) id post) s) Hpost eq_refl) as Hmerge.
  cbn [replace_MemoryS] in Hmerge; unfold memory_configured_rep in Hmerge; rewrite Henabled in Hmerge.
  sep_apply_r_atomic Hmerge; entailer!.
Qed.

(** The caller's block and the current free list are disjoint physical
    storage. This fact is independent of any historical loan identity. *)
Lemma memory_block_storage_excludes_free_block : forall p block ids,
  In block ids ->
  memory_block_storage p block ** store_memory_free_blocks p ids |-- coq_prop False.
Proof.
  intros p block ids Hin; induction ids as [|i rest IH]; [contradiction|].
  simpl in Hin; simpl store_memory_free_blocks.
  destruct Hin as [<-|Hin].
  - unfold memory_block_storage; Intros first.
    unfold memory_free_block_rep.
    sepcon_right_assoc.
    sep_apply_l_atomic (dup_store_ptr (memory_block_addr p i) first (memory_free_head p rest)).
    entailer!.
  - sep_apply_l_atomic (IH Hin); entailer!.
Qed.

Lemma memory_block_storage_current_allocation : forall id p block,
  valid_memory_partition id p -> 0 <= block < p.(memBlockCount) ->
  memory_block_storage p block ** store_memory_free_blocks p p.(memFreeBlocks) |--
    coq_prop (exists loan, p.(memAllocatedBlocks) block = Some loan) &&
    (memory_block_storage p block ** store_memory_free_blocks p p.(memFreeBlocks)).
Proof.
  intros id p block [_ [_ [_ [Hpartition _]]]] Hrange.
  destruct (in_dec Z.eq_dec block (memFreeBlocks p)) as [Hin|Hnot].
  - prop_apply (memory_block_storage_excludes_free_block p block (memFreeBlocks p) Hin).
    Intros; contradiction.
  - assert (Hloan : exists loan, memAllocatedBlocks p block = Some loan).
    { apply (proj2 (Hpartition block)); split; assumption. }
    entailer!.
Qed.

Lemma memory_historical_block_current_allocation : forall id historical current block loan,
  valid_memory_partition id historical -> valid_memory_partition id current ->
  historical.(memAllocatedBlocks) block = Some loan ->
  memory_partition_geometry_eq historical current ->
  memory_block_storage historical block ** store_memory_free_blocks current current.(memFreeBlocks) |--
    coq_prop (exists current_loan, current.(memAllocatedBlocks) block = Some current_loan) &&
    (memory_block_storage current block ** store_memory_free_blocks current current.(memFreeBlocks)).
Proof.
  intros id historical current block loan Hhistorical Hcurrent Hlookup Hgeometry.
  rewrite (memory_partition_geometry_block_storage_eq historical current block Hgeometry).
  apply memory_block_storage_current_allocation with (id := id); [exact Hcurrent|].
  pose proof (memory_allocated_block_in_range id historical block loan Hhistorical Hlookup) as Hrange.
  destruct Hgeometry as [_ [_ [_ Hcount]]]; rewrite <- Hcount; exact Hrange.
Qed.

Lemma memory_put_resources_merge : forall sg s id p block loan,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  UCOS2_state_inv sg s -> s.(MemoryState).(memPartitions) id = Some p ->
  p.(memAllocatedBlocks) block = Some loan ->
  store_memory_control sg (memory_control_addr sg id)
    (memory_put_image (memory_partition_image p) (memory_block_addr p block)) **
  memory_free_block_rep p block (memory_free_head p p.(memFreeBlocks)) **
  store_memory_free_blocks p p.(memFreeBlocks) **
  memory_raw_rep_without_partition sg s.(MemoryState) id **
  UCOS2_raw_rep_missing_memory sg s |--
    UCOS2_inv sg (replace_MemoryS
      (memory_replace_partition s.(MemoryState) id (memory_put_partition p block)) s).
Proof.
  intros sg s id p block loan Henabled Hvalid Hlookup Hloan.
  assert (Hmemory : valid_memory_state sg s.(MemoryState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_memory_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  assert (Hpart : valid_memory_partition id p).
  { destruct Hmemory as [_ [Hparts _]]; exact (proj1 (proj2 (Hparts id p Hlookup))). }
  assert (Hpost : UCOS2_state_inv sg (replace_MemoryS
    (memory_replace_partition s.(MemoryState) id (memory_put_partition p block)) s)).
  { eapply UCOS2_memory_put_preserves_validity;
      [exact Henabled|exact Hvalid|exact Hlookup|exact Hloan|].
    unfold memory_put; rewrite Hlookup; reflexivity. }
  sep_apply_l_atomic (memory_put_reconstructs_raw_rep sg s.(MemoryState) id p block loan Hpart Hloan).
  pose proof (UCOS2_inv_merge_updated_memory sg s (replace_MemoryS
    (memory_replace_partition s.(MemoryState) id (memory_put_partition p block)) s) Hpost eq_refl) as Hmerge.
  cbn [replace_MemoryS] in Hmerge; unfold memory_configured_rep in Hmerge; rewrite Henabled in Hmerge.
  sep_apply_r_atomic Hmerge; entailer!.
Qed.
