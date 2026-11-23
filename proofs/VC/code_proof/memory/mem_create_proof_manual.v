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
From Ucos2Verify.VC.code.memory Require Import mem_create_goal.
From Ucos2Verify.VC.code.memory Require Import mem_create_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.memory.spec.mem_create_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSMemCreate_entail_wit_1 : OSMemCreate_entail_wit_1.
Proof.
  left; intros.
  prop_apply (valid_store_ptr (&("addr")) addr_pre); Intros.
  prop_apply (store_uint_range (&("nblks")) nblks_pre); Intros.
  prop_apply (store_uint_range (&("blksize")) blksize_pre); Intros.
  destruct H as [_ Hptr].
  change (0 <= addr_pre <= 4294967295) in Hptr.
  change (0 <= nblks_pre <= 4294967295) in H0.
  change (0 <= blksize_pre <= 4294967295) in H1.
  unfold mem_create_arguments_in_range.
  entailer!; lia.
Qed.

Lemma proof_of_OSMemCreate_entail_wit_2 : OSMemCreate_entail_wit_2.
Proof.
  right; intros; subst addr_pre nblks_pre blksize_pre.
  unfold mem_create_arguments_in_range in PreH5.
  assert (Hb : kernel_resources.kernel_u32 base = base)
    by (apply kernel_resources.kernel_u32_identity; lia).
  assert (Hn : kernel_resources.kernel_u32 count = count)
    by (apply kernel_resources.kernel_u32_identity; lia).
  assert (Hs : kernel_resources.kernel_u32 size = size)
    by (apply kernel_resources.kernel_u32_identity; lia).
  assert (Ha : base mod 4 = 0).
  { pose proof (mem_create_alignment_guard_mod base) as Halign.
    rewrite Hb in Halign; change (Z.land base 3 = 0) in PreH3; lia. }
  entailer!; unfold mem_create_arguments_valid.
  apply mem_create_argument_error_none_iff.
  rewrite Hb, Hn, Hs; change (size >= 4) in PreH1; repeat split; try assumption; lia.
Qed.

Lemma proof_of_OSMemCreate_entail_wit_3 : OSMemCreate_entail_wit_3.
Proof.
  left; intros.
  prop_apply (valid_store_ptr (&("OSMemFreeList")) (mem_create_free_head sg entry)); Intros.
  prop_apply (store_uint_range (&("cpu_sr")) retval); Intros.
  destruct H as [_ Hptr].
  change (0 <= mem_create_free_head sg entry <= 4294967295) in Hptr.
  change (0 <= retval <= 4294967295) in H0.
  entailer!; lia.
Qed.

Lemma proof_of_OSMemCreate_entail_wit_4_1 : OSMemCreate_entail_wit_4_1.
Proof.
  right; intros.
  Exists (replace_MemoryS post entry) (Some private).
  unfold mbox_accept_cpu_restore_pre, mem_create_selected_pointer,
    mem_create_selected_resources.
  assert (Hfacts : mem_create_acquire_facts critical sg invocation mode base count size
    before entry (Some private) (replace_MemoryS post entry)).
  { unfold mem_create_acquire_facts; split; [exact PreH9|].
    split; [exact PreH10|]. split.
    - right; exists private, post; split; [exact (proj1 PreH1)|auto].
    - exists post; auto. }
  entailer!.
Qed.

Lemma proof_of_OSMemCreate_entail_wit_4_2 : OSMemCreate_entail_wit_4_2.
Proof.
  right; intros.
  pose proof (proj1 (mem_create_free_head_zero_iff__entry_reservation sg entry
    PreH7 PreH12) PreH1) as Hempty.
  assert (Hfacts : mem_create_acquire_facts critical sg invocation mode base count size
    before entry None entry).
  { unfold mem_create_acquire_facts; split; [exact PreH8|].
    split; [exact PreH9|]. split; [left; auto|exact I]. }
  assert (Haccess : mem_create_byte_access
    (mem_create_detached_resources sg entry None mode base count size caller_frame) output).
  { eapply mem_create_byte_access_consequence; [|exact PreH11].
    unfold mem_create_detached_resources, mem_create_selected_resources,
      mem_create_entry_resources; entailer!. }
  Exists entry (None : MemCreateSelection).
  unfold mbox_accept_cpu_restore_pre, mem_create_selected_pointer,
    mem_create_selected_resources.
  entailer!.
  pose proof (ucos2_verify_inv.UCOS2_inv_merge_updated_memory sg entry entry PreH12 eq_refl) as Hmerge.
  unfold memory_configured_rep in Hmerge.
  destruct PreH7 as [_ [Henabled _]]; rewrite Henabled in Hmerge.
  sep_apply_r_atomic Hmerge.
  unfold mem_create_root_frame, memory_raw_rep_without_free_root,
    memory_raw_rep, mem_create_free_head; rewrite <- PreH6; entailer!.
Qed.

Lemma proof_of_OSMemCreate_entail_wit_5 : OSMemCreate_entail_wit_5.
Proof.
  right; intros.
  destruct PreH6 as [Hregion _].
  unfold memory_region_valid, memory_partition_initial in Hregion; simpl in Hregion.
  assert (Hcount : 2 <= count < 4294967296) by (rewrite <- PreH4; tauto).
  assert (Hlast : unsigned_last_nbits (count - 1) 32 = count - 1).
  { apply unsigned_last_nbits_eq; change (0 <= count - 1 < 4294967296); lia. }
  entailer!.
Qed.

Lemma proof_of_OSMemCreate_entail_wit_6 : OSMemCreate_entail_wit_6.
Proof.
  right; intros; unfold mem_create_loop_state; entailer!.
Qed.

Lemma proof_of_OSMemCreate_return_wit_1 : OSMemCreate_return_wit_1.
Proof.
  left; intros.
  pose proof (mem_create_api_return_from_byte platform critical sg invocation origin mask mode
    base count size output before (memory_control_addr sg (memPrivateSlot private))
    (mem_create_publish_state current private) 0 caller_frame X PreH2 PreH8) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSMemCreate_return_wit_2 : OSMemCreate_return_wit_2.
Proof.
  left; intros.
  pose proof (mem_create_api_return_from_byte platform critical sg invocation origin mask mode
    base count size output before 0 current 90 caller_frame X PreH2 PreH10) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSMemCreate_return_wit_3 : OSMemCreate_return_wit_3.
Proof.
  left; intros; subst perr_pre blksize_pre nblks_pre addr_pre.
  assert (Hbase : kernel_resources.kernel_u32 base = base).
  { apply kernel_resources.kernel_u32_identity; unfold mem_create_arguments_in_range in PreH5; lia. }
  assert (Hcount : kernel_resources.kernel_u32 count = count).
  { apply kernel_resources.kernel_u32_identity; unfold mem_create_arguments_in_range in PreH5; lia. }
  assert (Hsize : kernel_resources.kernel_u32 size = size).
  { apply kernel_resources.kernel_u32_identity; unfold mem_create_arguments_in_range in PreH5; lia. }
  assert (Halign : kernel_resources.kernel_u32 base mod 4 = 0).
  { rewrite <- mem_create_alignment_guard_mod, Hbase.
    change (Z.land base 3 = 0) in PreH3; exact PreH3. }
  assert (Herror : mem_create_argument_error base count size = Some error_codes.OS_ERR_MEM_INVALID_SIZE).
  { apply mem_create_argument_error_size; [rewrite Hbase; exact PreH4|exact Halign|
      rewrite Hcount; lia|rewrite Hsize; change (size < 4) in PreH1; exact PreH1]. }
  pose proof (mem_create_program_argument_return critical sg invocation base count size
    (mem_create_private_return critical sg invocation) before _ Herror) as Hprogram.
  pose proof (mem_create_api_return_from_byte platform critical sg invocation origin mask mode
    base count size output before 0 before 92 caller_frame X Hprogram PreH21) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSMemCreate_return_wit_4 : OSMemCreate_return_wit_4.
Proof.
  left; intros; subst perr_pre blksize_pre nblks_pre addr_pre.
  assert (Hbase : kernel_resources.kernel_u32 base = base).
  { apply kernel_resources.kernel_u32_identity; unfold mem_create_arguments_in_range in PreH4; lia. }
  assert (Hcount : kernel_resources.kernel_u32 count = count).
  { apply kernel_resources.kernel_u32_identity; unfold mem_create_arguments_in_range in PreH4; lia. }
  assert (Halign : kernel_resources.kernel_u32 base mod 4 = 0).
  { rewrite <- mem_create_alignment_guard_mod, Hbase.
    change (Z.land base 3 = 0) in PreH2; exact PreH2. }
  assert (Herror : mem_create_argument_error base count size = Some error_codes.OS_ERR_MEM_INVALID_BLKS).
  { apply mem_create_argument_error_count; [rewrite Hbase; exact PreH3|exact Halign|
      rewrite Hcount; exact PreH1]. }
  pose proof (mem_create_program_argument_return critical sg invocation base count size
    (mem_create_private_return critical sg invocation) before _ Herror) as Hprogram.
  pose proof (mem_create_api_return_from_byte platform critical sg invocation origin mask mode
    base count size output before 0 before 91 caller_frame X Hprogram PreH20) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSMemCreate_return_wit_5 : OSMemCreate_return_wit_5.
Proof.
  left; intros; subst perr_pre blksize_pre nblks_pre addr_pre.
  assert (Hbase : kernel_resources.kernel_u32 base = base).
  { apply kernel_resources.kernel_u32_identity; unfold mem_create_arguments_in_range in PreH3; lia. }
  assert (Halign : kernel_resources.kernel_u32 base mod 4 <> 0).
  { rewrite <- mem_create_alignment_guard_mod, Hbase.
    change (Z.land base 3 <> 0) in PreH1; exact PreH1. }
  assert (Herror : mem_create_argument_error base count size = Some error_codes.OS_ERR_MEM_INVALID_ADDR).
  { apply mem_create_argument_error_alignment; [rewrite Hbase; exact PreH2|exact Halign]. }
  pose proof (mem_create_program_argument_return critical sg invocation base count size
    (mem_create_private_return critical sg invocation) before _ Herror) as Hprogram.
  pose proof (mem_create_api_return_from_byte platform critical sg invocation origin mask mode
    base count size output before 0 before 98 caller_frame X Hprogram PreH19) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSMemCreate_return_wit_6 : OSMemCreate_return_wit_6.
Proof.
  left; intros; subst perr_pre blksize_pre nblks_pre addr_pre base.
  pose proof (mem_create_program_argument_return critical sg invocation 0 count size
    (mem_create_private_return critical sg invocation) before _
    (mem_create_argument_error_null count size)) as Hprogram.
  pose proof (mem_create_api_return_from_byte platform critical sg invocation origin mask mode
    0 count size output before 0 before 98 caller_frame X Hprogram PreH18) as Hreturn.
  sep_apply_r_atomic Hreturn; entailer!.
Qed.

Lemma proof_of_OSMemCreate_partial_solve_wit_12_pure : OSMemCreate_partial_solve_wit_12_pure.
Proof.
  right; intros; change (sizeof(UCHAR)) with 1; entailer!; ring.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_1 : OSMemCreate_which_implies_wit_1.
Proof.
  left; intros.
  rewrite mutex_query_spec.mutex_query_closed_equiv.
  change (mem_create_byte_access
    (UCOS2_inv sg before ** mem_create_input_resources mode base count size ** caller_frame) output) in PreH1.
  unfold mem_create_return_resources, mem_create_retained_resources; cbn [Z.eqb].
  cancel (interrupt_platform_running platform invocation origin mask).
  sep_apply_r_atomic (mem_create_byte_access_split _ _ PreH1); entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_2 : OSMemCreate_which_implies_wit_2.
Proof.
  exact proof_of_OSMemCreate_which_implies_wit_1.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_3 : OSMemCreate_which_implies_wit_3.
Proof.
  exact proof_of_OSMemCreate_which_implies_wit_1.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_4 : OSMemCreate_which_implies_wit_4.
Proof.
  exact proof_of_OSMemCreate_which_implies_wit_1.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_5 : OSMemCreate_which_implies_wit_5.
Proof.
  right; intros.
  assert (Hbefore : mem_create_byte_access
    (UCOS2_inv sg before ** emp **
      (mem_create_input_resources mode base count size ** caller_frame)) output).
  { eapply mem_create_byte_access_consequence; [|exact PreH6].
    unfold mem_create_entry_resources; entailer!. }
  pose proof (mem_create_interval_preserves_output_access critical sg invocation output
    (mem_create_input_resources mode base count size ** caller_frame) emp before entry
    (PreH5 PreH3) PreH4 Hbefore) as Hentry.
  assert (Haccess : mem_create_byte_access
    (mem_create_entry_resources sg entry mode base count size caller_frame) output).
  { eapply mem_create_byte_access_consequence; [|exact Hentry].
    unfold mem_create_entry_resources; entailer!. }
  rewrite (ucos2_verify_inv.UCOS2_inv_split_memory sg entry).
  unfold memory_configured_rep; destruct PreH2 as [_ [Henabled _]]; rewrite Henabled.
  Intros; unfold memory_raw_rep, mem_create_root_frame,
    memory_raw_rep_without_free_root, mem_create_free_head.
  rewrite <- PreH1; entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_6 : OSMemCreate_which_implies_wit_6.
Proof.
  left; intros; subst pmem.
  pose proof (mem_create_memory_valid__entry_reservation sg entry PreH5 PreH6) as Hmemory.
  assert (Hnonempty : memFreeControls (MemoryState entry) <> nil).
  { intro Hempty; apply PreH2; unfold mem_create_free_head; rewrite Hempty; reflexivity. }
  unfold mem_create_call_domain in PreH7; rewrite PreH9 in PreH7.
  destruct PreH7 as [Hprotocol Hdomain].
  assert (Hmode : mode = MemCreateArena).
  { destruct mode; [reflexivity|].
    pose proof (mem_create_source_interval_preserves_empty_controls critical sg invocation
      before entry Hprotocol PreH8 Hdomain); contradiction. }
  subst mode.
  destruct (mem_create_reserve_nonempty sg (MemoryState entry) (kernel_resources.kernel_u32 base)
    (kernel_resources.kernel_u32 count) (kernel_resources.kernel_u32 size)
    Hmemory Hnonempty) as [private [post Hreserve]].
  destruct (mem_create_reserve_facts__entry_reservation sg entry base count size private post
    PreH5 PreH6 PreH10 Hdomain Hreserve) as [Hfacts Himage].
  pose proof (proj1 (memory_reserve_root_values_eq sg (MemoryState entry)
    (kernel_resources.kernel_u32 base)
    (kernel_resources.kernel_u32 size * kernel_resources.kernel_u32 count)
    (kernel_resources.kernel_u32 size) (kernel_resources.kernel_u32 count)
    private post Hmemory Hreserve)) as Hroot.
  change (mem_create_free_head sg entry = memory_control_addr sg (memPrivateSlot private)) in Hroot.
  Exists post private; entailer!.
  unfold mem_create_root_frame, memory_raw_rep_without_free_root, mem_create_head_field_frame.
  sep_apply_l_atomic (memory_controls_split_control sg (MemoryState entry)
    (memPrivateSlot private) (memPrivateImage private) Himage).
  sep_apply_l_atomic (store_memory_control_split_field sg
    (memory_control_addr sg (memPrivateSlot private)) (memPrivateImage private) MCBFreeList
    ltac:(unfold memory_control_fields; simpl; auto)).
  cbn [memory_control_cell memory_control_value]; rewrite Hroot; entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_7 : OSMemCreate_which_implies_wit_7.
Proof.
  right; intros.
  destruct PreH3 as [Hchecks [Henabled Hnames]].
  pose proof PreH5 as [Hreserve [Hpost [Hinit [Hbase [Hsize [Hcount [Hprefix Haddress]]]]]]].
  assert (Hmemory : valid_memory_state sg (MemoryState entry)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_memory_configuration in PreH4;
      rewrite Henabled in PreH4; tauto. }
  pose proof (memory_reserve_root_values_eq sg (MemoryState entry) (Ucos2Verify.lib.kernel_resources.kernel_u32 base)
    (Ucos2Verify.lib.kernel_resources.kernel_u32 size * Ucos2Verify.lib.kernel_resources.kernel_u32 count)
    (Ucos2Verify.lib.kernel_resources.kernel_u32 size) (Ucos2Verify.lib.kernel_resources.kernel_u32 count)
    private post Hmemory Hreserve) as [Hroot Hnext].
  set (rest := memory_raw_rep_without_free_root sg (MemoryState entry) **
    UCOS2_raw_rep_missing_memory sg entry ** mem_create_input_resources mode base count size ** caller_frame).
  assert (Hfold : sg.(g_OSMemFreeList) # Ptr |-> memory_control_addr sg private.(memPrivateSlot) **
    rest |-- mem_create_entry_resources sg entry mode base count size caller_frame).
  { unfold rest, mem_create_entry_resources.
    pose proof (UCOS2_inv_merge_updated_memory sg entry entry PreH4 eq_refl) as Hmerge.
    unfold memory_configured_rep in Hmerge; rewrite Henabled in Hmerge.
    unfold memory_raw_rep in Hmerge; rewrite Hroot in Hmerge.
    unfold memory_raw_rep_without_free_root.
    sepcon_right_assoc.
    sep_apply_r_atomic Hmerge; entailer!. }
  assert (Hsplit : mem_create_detached_resources sg (replace_MemoryS post entry)
    (mem_create_selection private) mode base count size caller_frame |--
    sg.(g_OSMemFreeList) # Ptr |-> private.(memPrivateImage).(memImageFree) ** rest).
  { unfold mem_create_detached_resources, mem_create_selection, mem_create_selected_resources, rest.
    rewrite (UCOS2_inv_split_memory sg (replace_MemoryS post entry)); Intros.
    cbn [replace_MemoryS] in *.
    unfold memory_configured_rep; rewrite Henabled.
    sep_apply (mem_create_reserved_resources_restore__private_initialization sg (MemoryState entry)
      (Ucos2Verify.lib.kernel_resources.kernel_u32 base)
      (Ucos2Verify.lib.kernel_resources.kernel_u32 size * Ucos2Verify.lib.kernel_resources.kernel_u32 count)
      (Ucos2Verify.lib.kernel_resources.kernel_u32 size) (Ucos2Verify.lib.kernel_resources.kernel_u32 count)
      private post Hmemory Hreserve); entailer!. }
  assert (Haccess : mem_create_byte_access (mem_create_detached_resources sg (replace_MemoryS post entry)
    (mem_create_selection private) mode base count size caller_frame) output).
  { eapply mem_create_byte_access_consequence; [exact Hsplit|].
    eapply mem_create_byte_access_ptr_replace__private_initialization
      with (old := memory_control_addr sg private.(memPrivateSlot)).
    - change (0 <= memory_control_addr sg (memPrivateSlot private) /\
        memory_control_addr sg (memPrivateSlot private) <= 4294967295); lia.
    - eapply mem_create_byte_access_consequence; [exact Hfold|exact PreH6]. }
  assert (Hvalid : UCOS2_state_inv sg (replace_MemoryS post entry)).
  { eapply mem_create_reserve_preserves_global_validity; eassumption. }
  assert (Himage : (MemoryState entry).(memControlImages) private.(memPrivateSlot) =
    Some private.(memPrivateImage)).
  { unfold memory_reserve_control in Hreserve.
    destruct (memFreeControls (MemoryState entry)); [discriminate|].
    destruct (memControlImages (MemoryState entry) m) eqn:E; [|discriminate].
    inversion Hreserve; subst; exact E. }
  rewrite PreH1, PreH2.
  unfold mem_create_head_field_frame.
  sepcon_right_assoc.
  pose proof (store_memory_control_merge_field sg (memory_control_addr sg private.(memPrivateSlot))
    private.(memPrivateImage) MCBFreeList ltac:(unfold memory_control_fields; simpl; auto)) as Hfield.
  cbn [memory_control_cell memory_control_value] in Hfield.
  sep_apply Hfield.
  sep_apply (memory_controls_merge_control sg (MemoryState entry) private.(memPrivateSlot)
    private.(memPrivateImage) Himage).
  pose proof (mem_create_reserve_resources_merge sg entry (Ucos2Verify.lib.kernel_resources.kernel_u32 base)
    (Ucos2Verify.lib.kernel_resources.kernel_u32 size * Ucos2Verify.lib.kernel_resources.kernel_u32 count)
    (Ucos2Verify.lib.kernel_resources.kernel_u32 size) (Ucos2Verify.lib.kernel_resources.kernel_u32 count)
    private post Henabled PreH4 Hreserve) as Hmerge.
  unfold memory_raw_rep_without_free_root in Hmerge.
  lazymatch type of Hmerge with ?P |-- ?Q =>
    lazymatch goal with |- ?L |-- _ =>
      assert (Horder : L |-- P ** (mem_create_input_resources mode base count size ** caller_frame))
        by entailer!;
      rewrite Horder, Hmerge; entailer!
    end
  end.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_8 : OSMemCreate_which_implies_wit_8.
Proof.
  left; intros; subst pmem.
  destruct selected as [private|].
  - destruct PreH3 as [_ [_ [_ [post [_ [Hreserve _]]]]]].
    destruct Hreserve as [_ [_ [_ [_ [_ [_ [_ Hpositive]]]]]]].
    simpl in PreH2; exfalso; lia.
  - destruct PreH3 as [Hargs [Hentry [Hacquire _]]].
    destruct Hacquire as [[Hempty [_ Hcheckpoint]]|[private [post [_ [Hnone _]]]]];
      [subst checkpoint|discriminate].
    assert (Hprogram : mem_create_kernel_program critical sg invocation base count size
      before (mem_create_outcome 0 90) current).
    { eapply mem_create_program_empty_return; eassumption. }
    pose proof (mem_create_interval_preserves_output_access critical sg invocation output
      (mem_create_input_resources mode base count size ** caller_frame) emp entry current
      (PreH5 Hargs) PreH4 PreH6) as Hcurrent.
    assert (Haccess : mem_create_byte_access
      (mem_create_return_resources sg mode base count size 0 current caller_frame) output).
    { eapply mem_create_byte_access_consequence; [|exact Hcurrent].
      unfold mem_create_return_resources, mem_create_retained_resources; simpl; entailer!. }
    rewrite mutex_query_closed_equiv.
    unfold mem_create_selected_resources; simpl.
    entailer!.
    sep_apply_r_atomic (mem_create_byte_access_split
      (mem_create_return_resources sg mode base count size 0 current caller_frame) output Haccess).
    unfold mem_create_return_resources, mem_create_retained_resources; simpl; entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_9 : OSMemCreate_which_implies_wit_9.
Proof.
  left; intros.
  destruct selected as [private|]; [|simpl in PreH2; contradiction].
  destruct PreH4 as [Hargs [Hentry [Hacquire [post [Hmode [Hreservation Hcheckpoint]]]]]].
  subst mode checkpoint; simpl in PreH2; subst pmem.
  unfold mem_create_call_domain in PreH6; rewrite Hargs in PreH6.
  destruct Hreservation as [Hreserve [Hpost [Hinit [Hb [Hs [Hn [Hprefix Haddr]]]]]]].
  assert (Hreservation : mem_create_reservation sg base count size entry private post)
    by (unfold mem_create_reservation; tauto).
  pose proof (mem_create_interval_preserves_output_access critical sg invocation output
    (mem_create_input_resources MemCreateArena base count size ** caller_frame)
    (memory_private_control_rep sg private) (replace_MemoryS post entry) current
    (PreH7 Hargs) PreH5 PreH8) as Haccess.
  pose proof (mem_create_input_prefix_zero_equiv__entry_reservation private base count size
    Hargs Hb Hn Hs Hinit) as Hprefix_equiv.
  assert (Hcursor : mem_create_byte_access
    (mem_create_cursor_resources sg current private 0 caller_frame) output).
  { eapply mem_create_byte_access_consequence; [|exact Haccess].
    unfold mem_create_cursor_resources; rewrite <- Hprefix_equiv; entailer!. }
  rewrite mutex_query_closed_equiv.
  unfold mem_create_selected_resources.
  sep_apply_l_atomic (mem_create_reservation_after_restore critical sg invocation base count size
    entry private post current PreH3 Hreservation (proj1 PreH6) PreH5).
  Intros.
  assert (Hhistory : mem_create_private_history critical sg invocation base count size
    before current private).
  { unfold mem_create_private_history; split; [exact Hargs|].
    exists entry, post; tauto. }
  Exists private; unfold mem_create_loop_state; entailer!.
  unfold mem_create_cursor_resources.
  rewrite <- Hprefix_equiv; entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_10 : OSMemCreate_which_implies_wit_10.
Proof.
  left; intros.
  unfold mem_create_loop_state; Intros.
  assert (Haccess : mem_create_byte_access
    (mem_create_cursor_resources sg current private (i+1) caller_frame) output).
  { eapply mem_create_byte_access_consequence with
      (second := mem_create_cursor_resources sg current private i caller_frame).
    - unfold mem_create_cursor_resources.
      sep_apply_l_atomic (mem_create_linked_prefix_forget_last__private_initialization
        private i PreH8 ltac:(rewrite PreH6; lia)); entailer!.
    - tauto. }
  unfold mem_create_cursor_resources, mem_create_loop_resources.
  pose proof (memory_private_linked_prefix_split_next_word (memory_private_set_prefix private i)
    (mem_create_prefix_valid private i PreH8 ltac:(rewrite PreH6; lia))
    ltac:(simpl; rewrite PreH6; lia)) as Hsplit.
  cbn [memory_private_set_prefix memPrivateBase memPrivateLinkedPrefix memPrivateBlockSize] in Hsplit.
  rewrite PreH5, PreH7 in Hsplit.
  sep_apply_l_atomic Hsplit; subst plink; entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_11 : OSMemCreate_which_implies_wit_11.
Proof.
  right; intros; subst plink pblk.
  rewrite <- PreH3, <- PreH5.
  unfold mem_create_loop_resources, mem_create_cursor_resources.
  sep_apply_l_atomic (mem_create_loop_store_merge private i PreH6 ltac:(rewrite PreH4; lia)).
  entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_12 : OSMemCreate_which_implies_wit_12.
Proof.
  left; intros.
  assert (Hi : i = count-1) by lia; subst i.
  assert (Hcount : 2 <= count).
  { destruct PreH8 as [Hr _]; unfold memory_region_valid, memory_partition_initial in Hr;
      simpl in Hr; rewrite <- PreH6; lia. }
  unfold mem_create_loop_state; Intros.
  assert (Haccess : mem_create_byte_access
    (mem_create_cursor_resources sg current private count caller_frame) output).
  { eapply mem_create_byte_access_consequence with
      (second := mem_create_cursor_resources sg current private (count-1) caller_frame).
    - unfold mem_create_cursor_resources.
      replace count with ((count-1)+1) at 1 by lia.
      sep_apply_l_atomic (mem_create_linked_prefix_forget_last__private_initialization
        private (count-1) PreH8 ltac:(rewrite PreH6; lia)); entailer!.
    - tauto. }
  unfold mem_create_cursor_resources, mem_create_loop_resources.
  pose proof (memory_private_linked_prefix_split_next_word (memory_private_set_prefix private (count-1))
    (mem_create_prefix_valid private (count-1) PreH8 ltac:(rewrite PreH6; lia))
    ltac:(simpl; rewrite PreH6; lia)) as Hsplit.
  cbn [memory_private_set_prefix memPrivateBase memPrivateLinkedPrefix memPrivateBlockSize] in Hsplit.
  rewrite PreH5, PreH7 in Hsplit.
  sep_apply_l_atomic Hsplit; subst plink; entailer!.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_13 : OSMemCreate_which_implies_wit_13.
Proof.
  right; intros; subst pmem plink.
  destruct PreH7 as [Hchecks [Henabled Hnames]].
  assert (Htransport : memory_private_control_rep sg private |--
    coq_prop (mem_create_byte_access (mem_create_initialized_resources sg current private caller_frame) output)).
  { intros old_heap Hold.
    eapply mem_create_byte_access_consequence with
      (second := store_memory_control sg (memory_control_addr sg private.(memPrivateSlot))
        (memory_create_control_image private) **
        (UCOS2_inv sg current ** memory_private_linked_prefix_rep
          (memory_private_set_prefix private private.(memPrivateBlockCount)) ** caller_frame)).
    - unfold mem_create_initialized_resources; entailer!.
    - eapply mem_create_byte_access_control_replace__private_initialization
        with (old := private.(memPrivateImage)) (old_heap := old_heap); [exact Hnames|exact Hold|].
      eapply mem_create_byte_access_consequence; [|exact PreH8].
      unfold mem_create_cursor_resources, memory_private_control_rep; rewrite PreH4; entailer!. }
  unfold mem_create_loop_resources, mem_create_control_write_frame.
  pose proof (mem_create_tail_null_store_merge private PreH6) as Htail.
  rewrite PreH3, PreH4, PreH5 in Htail.
  sep_apply Htail.
  prop_apply Htransport; Intros.
  unfold memory_private_control_rep; rewrite store_memory_control_layout_equiv, Hnames.
  entailer!.
  rewrite PreH4; reflexivity.
Qed.

Lemma proof_of_OSMemCreate_which_implies_wit_14 : OSMemCreate_which_implies_wit_14.
Proof.
  left; intros; subst pmem mode.
  destruct PreH7 as [Hchecks [Henabled Hnames]].
  destruct PreH8 as [Hargs [entry [post [Henter [Hreservation [Hrestore Hlookup]]]]]].
  destruct Hreservation as [Hreserve [Hpost [Hinit [Hbase [Hsize [Hcount [Hprefix Haddress]]]]]]].
  assert (Hprogram : mem_create_kernel_program critical sg invocation base count size before
    (mem_create_outcome (memory_control_addr sg private.(memPrivateSlot)) 0)
    (mem_create_publish_state current private)).
  { unfold mem_create_kernel_program, mem_create_outcome.
    eapply mem_create_program_private_return with (entry := entry) (private := private)
      (post := post) (restored := current);
      eassumption || apply mem_create_private_return_reflexive. }
  assert (Hnonzero : memory_control_addr sg private.(memPrivateSlot) <> 0) by lia.
  assert (Hpublish : mem_create_initialized_resources sg current private caller_frame |--
    mem_create_return_resources sg MemCreateArena base count size
      (memory_control_addr sg private.(memPrivateSlot)) (mem_create_publish_state current private) caller_frame).
  { unfold mem_create_initialized_resources, mem_create_return_resources, mem_create_retained_resources.
    rewrite (proj2 (Z.eqb_neq _ _) Hnonzero).
    assert (Hvalid_ent : UCOS2_inv sg current |-- coq_prop (UCOS2_state_inv sg current)).
    { unfold UCOS2_inv; entailer!. }
    prop_apply Hvalid_ent; Intros.
    unfold mem_create_publish_state.
    sep_apply (mem_create_publish_resources_merge sg current private Henabled ltac:(tauto) Hlookup PreH6).
    entailer!. }
  assert (Hfinish : mem_create_initialized_resources sg current private caller_frame |--
    output # UChar |->_ ** mem_create_output_residual
      (mem_create_return_resources sg MemCreateArena base count size
        (memory_control_addr sg private.(memPrivateSlot)) (mem_create_publish_state current private) caller_frame) output).
  { sep_apply_l_atomic (mem_create_byte_access_split
      (mem_create_initialized_resources sg current private caller_frame) output PreH9).
    sep_apply_l_atomic (mem_create_output_residual_consequence__private_initialization _ _ output Hpublish).
    entailer!. }
  entailer!.
  sep_apply_r_atomic Hfinish.
  unfold mem_create_initialized_resources, mem_create_control_write_frame.
  rewrite store_memory_control_layout_equiv, Hnames.
  cbn [memory_create_control_image memory_create_control_writes fold_left fst snd memory_control_set_field
    memImageBase memImageFree memImageSize memImageCount memImageNFree memImageName].
  try rewrite PreH3; try rewrite PreH4; try rewrite PreH5; entailer!.
Qed.

