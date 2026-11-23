Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.memory Require Import mem_get_goal.
From Ucos2Verify.VC.code.memory Require Import mem_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.memory.spec.mem_get_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSMemGet_return_wit_1 : OSMemGet_return_wit_1.
Proof.
  left; intros.
  assert (Hprogram : mem_get_program critical sg invocation view pe before
    mem_get_empty_outcome current).
  { eapply mem_get_program_restored with (entry := entry_2) (checkpoint := entry_2);
      eassumption. }
  pose proof (mem_get_safe_return _ _ _ _ _ _ _ _ X Hprogram PreH26) as Hsafe.
  unfold mem_get_api_post; Exists mem_get_empty_outcome current.
  subst perr_pre; cbn [mem_get_pointer mem_get_error mem_get_empty_outcome]; entailer!.
Qed.

Lemma proof_of_OSMemGet_return_wit_2 : OSMemGet_return_wit_2.
Proof.
  left; intros.
  assert (Hprogram : mem_get_program critical sg invocation view pe before
    (mem_get_access_outcome access) current).
  { eapply mem_get_program_restored with (entry := entry_2)
      (checkpoint := mem_get_access_checkpoint entry_2 access); eassumption. }
  pose proof (mem_get_safe_return _ _ _ _ _ _ _ _ X Hprogram PreH29) as Hsafe.
  unfold mem_get_api_post; Exists (mem_get_access_outcome access) current.
  subst perr_pre; rewrite PreH5; entailer!.
Qed.

Lemma proof_of_OSMemGet_return_wit_3 : OSMemGet_return_wit_3.
Proof.
  left; intros; subst pmem_pre pe perr_pre.
  pose proof (mem_get_program_null critical sg invocation view before) as Hprogram.
  pose proof (mem_get_safe_return _ _ _ _ _ _ _ _ X Hprogram PreH6) as Hsafe.
  unfold mem_get_api_post; Exists mem_get_null_outcome before.
  cbn [mem_get_input_resources mem_get_outcome_resources mem_get_pointer
    mem_get_error mem_get_null_outcome]; entailer!.
Qed.

Lemma proof_of_OSMemGet_which_implies_wit_1 : OSMemGet_which_implies_wit_1.
Proof.
  left; intros.
  destruct (mem_get_call_domain_acquired critical sg invocation view pe before entry_2
    PreH3 PreH1 PreH4) as [access Haccess].
  Exists access entry_2; entailer!.
  destruct view as [image next|id], access as [observed link|current p];
    cbn [mem_get_access_matches] in Haccess; try contradiction.
  - destruct Haccess as [<- <-].
    unfold mem_get_input_resources; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    cbn [mem_get_access_image mem_get_control_frame].
    sep_apply (store_memory_control_split_free_fields sg pe image); entailer!.
  - destruct Haccess as [-> [-> Hlookup]].
    destruct PreH2 as [_ [Henabled _]].
    assert (Hmemory : valid_memory_state sg (MemoryState entry_2)).
    { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
        valid_memory_configuration in PreH5; rewrite Henabled in PreH5; tauto. }
    unfold mem_get_input_resources; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    cbn [mem_get_access_image mem_get_control_frame].
    rewrite (UCOS2_inv_split_memory sg entry_2).
    unfold memory_configured_rep; rewrite Henabled; Intros.
    sep_apply (memory_raw_rep_split_partition sg (MemoryState entry_2) current p Hmemory Hlookup).
    unfold memory_partition_rep.
    sep_apply (store_memory_control_split_free_fields sg (memory_control_addr sg current)
      (memory_partition_image p)); entailer!.
Qed.

Lemma proof_of_OSMemGet_which_implies_wit_2 : OSMemGet_which_implies_wit_2.
Proof.
  left; intros; subst pblk.
  destruct access as [image next|id p].
  - cbn [mem_get_control_frame mem_get_success_frame mem_get_access_image
      mem_get_access_next] in *.
    unfold mem_get_raw_head; rewrite (proj2 (Z.ltb_lt _ _) PreH2); entailer!.
  - cbn [mem_get_control_frame mem_get_success_frame mem_get_access_image
      mem_get_access_next] in *.
    unfold memory_partition_image in *; cbn in PreH2 |- *.
    destruct (memFreeBlocks p) as [|block rest] eqn:Hblocks; [cbn in PreH2; lia|].
    cbn [store_memory_free_blocks memory_free_head tl].
    unfold memory_free_block_rep; entailer!.
Qed.

Lemma proof_of_OSMemGet_which_implies_wit_3 : OSMemGet_which_implies_wit_3.
Proof.
  left; intros.
  assert (Hprotected : mem_get_protected sg view pe entry
    (mem_get_access_outcome access) (mem_get_access_checkpoint entry access)).
  { exists access; repeat split; assumption || reflexivity. }
  assert (Hresult : memImageFree (mem_get_access_image access) =
    mem_get_pointer (mem_get_access_outcome access) /\
    mem_get_error (mem_get_access_outcome access) = 0).
  { destruct access as [image next|id p].
    - cbn [mem_get_access_image] in PreH8.
      cbn [mem_get_access_image mem_get_access_outcome].
      rewrite (proj2 (Z.ltb_lt _ _) PreH8); split; reflexivity.
    - change (0 < Z.of_nat (List.length (memFreeBlocks p))) in PreH8.
      cbn [mem_get_access_image mem_get_access_outcome].
      unfold memory_get_partition.
      destruct (memFreeBlocks p) as [|block rest] eqn:Hblocks;
        [cbn in PreH8; lia|].
      split; [|reflexivity].
      change (memory_free_head p (memFreeBlocks p) = memory_free_head p (block :: rest)).
      rewrite Hblocks; reflexivity. }
  destruct Hresult as [Hpointer Herror].
  assert (Hcheckpoint : UCOS2_state_inv sg (mem_get_access_checkpoint entry access)).
  { destruct access as [image next|id p]; cbn [mem_get_access_checkpoint]; [exact PreH4|].
    destruct (memory_get_partition id p) as [[loan post]|] eqn:Hget; [|exact PreH4].
    destruct view as [image next|current]; cbn [mem_get_access_matches] in PreH6;
      [contradiction|].
    destruct PreH6 as [-> [_ Hlookup]].
    eapply UCOS2_memory_get_preserves_validity; [exact (proj1 (proj2 PreH2))|exact PreH4|].
    unfold memory_get; rewrite Hlookup, Hget; reflexivity. }
  unfold mbox_accept_cpu_restore_pre; entailer!.
  assert (Hrange : 0 <= memImageNFree (mem_get_access_image access) - 1 < 4294967296).
  { change (memImageNFree (mem_get_access_image access) <= 4294967295) in PreH9; lia. }
  pose proof (store_memory_control_merge_updated_free_fields sg pe
    (mem_get_access_image access)
    (memory_get_image (mem_get_access_image access) (mem_get_access_next access))
    eq_refl eq_refl eq_refl eq_refl) as Hfields.
  cbn [memImageFree memImageNFree memory_get_image] in Hfields.
  rewrite (kernel_resources.kernel_u32_identity _ Hrange) in Hfields.
  destruct view as [image next|id], access as [observed link|current p];
    cbn [mem_get_access_matches] in PreH6; try contradiction.
  - destruct PreH6 as [<- <-].
    cbn [mem_get_access_image mem_get_access_next] in PreH8, Hfields.
    cbn [mem_get_success_frame mem_get_access_checkpoint mem_get_access_image mem_get_access_next].
    unfold mem_get_outcome_resources; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    cbn; unfold mem_get_raw_after, mem_get_raw_head;
      rewrite (proj2 (Z.ltb_lt _ _) PreH8).
    sep_apply Hfields; subst pblk; entailer!.
  - destruct PreH6 as [-> [-> Hlookup]].
    change (0 < Z.of_nat (List.length (memFreeBlocks p))) in PreH8.
    destruct (memFreeBlocks p) as [|block rest] eqn:Hblocks; [cbn in PreH8; lia|].
    destruct (memory_get_partition current p) as [[loan post]|] eqn:Hget.
    2: { unfold memory_get_partition in Hget; rewrite Hblocks in Hget; discriminate. }
    assert (Hnext : memory_free_head post (memFreeBlocks post) = memory_free_head p rest).
    { unfold memory_get_partition in Hget; rewrite Hblocks in Hget; inversion Hget; reflexivity. }
    cbn [mem_get_success_frame mem_get_access_checkpoint mem_get_access_outcome
      mem_get_access_image mem_get_access_next] in *.
    rewrite Hget.
    unfold mem_get_outcome_resources; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    cbn; rewrite Hblocks; cbn [tl].
    cbn [memImageNFree memory_partition_image] in Hfields.
    rewrite Hblocks in Hfields; cbn [tl] in Hfields.
    pose proof (memory_get_resources_merge sg entry current p loan post
      (proj1 (proj2 PreH2)) PreH4 Hlookup Hget) as Hmerge.
    rewrite Hnext in Hmerge.
    R_sepcon_lift' (memory_block_loan post loan).
    sep_apply_r_atomic Hmerge.
    sepcon_right_assoc.
    sep_apply_r_atomic Hfields.
    rewrite Hblocks; cbn [store_memory_free_blocks].
    unfold memory_free_block_rep; subst pblk.
    cbn [memImageFree memory_partition_image]; rewrite Hblocks; cbn [memory_free_head]; entailer!.
Qed.

Lemma proof_of_OSMemGet_which_implies_wit_4 : OSMemGet_which_implies_wit_4.
Proof.
  left; intros.
  assert (Hempty : memImageNFree (mem_get_access_image access) = 0) by lia.
  assert (Hprotected : mem_get_protected sg view pe entry mem_get_empty_outcome entry).
  { exists access; split; [exact PreH6|].
    destruct access as [image next|id p].
    - cbn [mem_get_access_image] in Hempty.
      cbn [mem_get_access_outcome mem_get_access_checkpoint]; rewrite Hempty; split; reflexivity.
    - change (Z.of_nat (List.length (memFreeBlocks p)) = 0) in Hempty.
      cbn [mem_get_access_outcome mem_get_access_checkpoint]; unfold memory_get_partition.
      destruct (memFreeBlocks p); [split; reflexivity|cbn in Hempty; lia]. }
  unfold mbox_accept_cpu_restore_pre; entailer!.
  destruct view as [image next|id], access as [observed link|current p];
    cbn [mem_get_access_matches] in PreH6; try contradiction.
  - destruct PreH6 as [<- <-].
    cbn [mem_get_access_image] in Hempty.
    cbn [mem_get_control_frame mem_get_access_image].
    unfold mem_get_outcome_resources; rewrite (proj2 (Z.eqb_neq _ _) PreH1).
    cbn; unfold mem_get_raw_after, mem_get_raw_head; rewrite Hempty; cbn.
    pose proof (store_memory_control_merge_updated_free_fields sg pe image image
      eq_refl eq_refl eq_refl eq_refl) as Hfields.
    rewrite Hempty in Hfields; sep_apply_r_atomic Hfields; entailer!.
  - destruct PreH6 as [-> [-> Hlookup]].
    destruct PreH2 as [_ [Henabled _]].
    assert (Hmemory : valid_memory_state sg (MemoryState entry)).
    { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
        valid_memory_configuration in PreH4; rewrite Henabled in PreH4; tauto. }
    assert (Himage : memControlImages (MemoryState entry) current = Some (memory_partition_image p)).
    { destruct Hmemory as [_ [Hparts _]]; exact (proj2 (proj2 (Hparts current p Hlookup))). }
    cbn [mem_get_control_frame mem_get_access_image].
    unfold mem_get_outcome_resources; rewrite (proj2 (Z.eqb_neq _ _) PreH1); cbn.
    sep_apply (store_memory_control_merge_updated_free_fields sg (memory_control_addr sg current)
      (memory_partition_image p) (memory_partition_image p) eq_refl eq_refl eq_refl eq_refl).
    pose proof (UCOS2_inv_merge_updated_memory sg entry entry PreH4 eq_refl) as Hmerge.
    unfold memory_configured_rep in Hmerge; rewrite Henabled in Hmerge.
    sep_apply_r_atomic Hmerge.
    unfold memory_raw_rep_without_partition, memory_raw_rep.
    sepcon_right_assoc.
    sep_apply_r_atomic (memory_controls_merge_control sg (MemoryState entry) current
      (memory_partition_image p) Himage).
    sepcon_right_assoc.
    sep_apply_r_atomic (store_map_merge (fun _ p => store_memory_free_blocks p (memFreeBlocks p))
      current p (memPartitions (MemoryState entry)) Hlookup); entailer!.
Qed.

