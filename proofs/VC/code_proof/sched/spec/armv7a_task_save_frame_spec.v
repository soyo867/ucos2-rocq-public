Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules ListNotations KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Ordinary-memory projection of the selected ARMv7-A/GNU non-VFP
    OSCtxSw save prefix. Unlike the IRQ entry, the source stores LR twice,
    then one R0--R12 group, then the corrected CPSR. The group lists keep
    increasing register/address order; they are not sixteen fictional
    single-register pushes. These lemmas do not create CPU continuations
    or prove the ISA, CLREX, TCB-SP write, hook, or eventual C return. *)

Lemma armv7a_frame_store_words_execution : forall words address (frame : Assertion) before,
  Forall (fun value => 0 <= value < 4294967296) words ->
  (UIntArray.undef_full address (Zlength words) ** frame) before ->
  exists after,
    kernel_heap_execution (armv7a_frame_store_words address words) before after /\
    (UIntArray.mixed_full address (Zlength words) (map (@Some Z) words) ** frame) after.
Proof.
  induction words as [|word rest IH]; intros address frame before Hranges Hbefore.
  - exists before; split; [split; [constructor|split; reflexivity]|].
    assert (Hempty : UIntArray.undef_full address 0 ** frame |--
      UIntArray.mixed_full address 0 [] ** frame).
    { rewrite UIntArray.undef_full_empty, UIntArray.mixed_full_empty; entailer!. }
    exact (Hempty before Hbefore).
  - inversion Hranges as [|word0 rest0 Hword Hrest]; subst.
    rewrite Zlength_cons in *.
    pose proof (Zlength_nonneg rest) as Hnonneg.
    assert (Hsplit : UIntArray.undef_full address (Zlength rest + 1) ** frame |--
      address # UInt |->_ ** (UIntArray.undef_full (address + 4) (Zlength rest) ** frame)).
    { sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full address 1
        (Zlength rest + 1) ltac:(lia)).
      rewrite sizeof_uint; replace (address + 1 * 4) with (address + 4) by ring.
      replace (Zlength rest + 1 - 1) with (Zlength rest) by lia.
      sep_apply_l_atomic (task_stack_undef_single_cell address); entailer!. }
    destruct (task_stack_uint_store_execution address word
      (UIntArray.undef_full (address + 4) (Zlength rest) ** frame) before Hword
      (Hsplit before Hbefore)) as [middle [Hhead Hmiddle]].
    assert (Horder : address # UInt |-> word **
      (UIntArray.undef_full (address + 4) (Zlength rest) ** frame) |--
      UIntArray.undef_full (address + 4) (Zlength rest) ** (address # UInt |-> word ** frame))
      by entailer!.
    destruct (IH (address + 4) (address # UInt |-> word ** frame) middle Hrest
      (Horder middle Hmiddle)) as [after [Htail Hafter]].
    exists after; split.
    + cbn [armv7a_frame_store_words]; eapply heap_execution_append; eassumption.
    + assert (Hmerge : UIntArray.mixed_full (address + 4) (Zlength rest)
        (map (@Some Z) rest) ** (address # UInt |-> word ** frame) |--
        UIntArray.mixed_full address (Zlength rest + 1)
          (map (@Some Z) (word :: rest)) ** frame).
      { sep_apply_l_atomic (task_stack_cell_mixed_single address word).
        pose proof (UIntArray.mixed_full_merge_to_mixed_full address 1 (Zlength rest + 1)
          [Some word] (map (@Some Z) rest) ltac:(lia)) as Hjoin.
        rewrite sizeof_uint in Hjoin.
        replace (address + 1 * 4) with (address + 4) in Hjoin by ring.
        replace (Zlength rest + 1 - 1) with (Zlength rest) in Hjoin by lia.
        sep_apply_l_atomic Hjoin; entailer!. }
      exact (Hmerge after Hafter).
Qed.

Definition armv7a_task_frame_store_writes (sp cpsr : Z) (registers : list Z) (lr : Z) :=
  pointer_store_writes (sp + 60) lr ++
  pointer_store_writes (sp + 56) lr ++
  armv7a_frame_store_words (sp + 4) registers ++
  pointer_store_writes sp cpsr.

Lemma armv7a_task_frame_store_execution : forall sp cpsr registers lr (frame : Assertion) before,
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  (UIntArray.undef_full sp 16 ** frame) before ->
  exists after,
    kernel_heap_execution (armv7a_task_frame_store_writes sp cpsr registers lr) before after /\
    (UIntArray.mixed_full sp 16 (map (@Some Z) (cpsr :: registers ++ [lr; lr])) ** frame) after.
Proof.
  intros sp cpsr registers lr frame before Hlength Hcpsr Hlr Hranges Hbefore.
  assert (Hzlength : Zlength registers = 13) by (rewrite Zlength_correct, Hlength; reflexivity).
  assert (Hsplit : UIntArray.undef_full sp 16 ** frame |--
    (sp + 60) # UInt |->_ ** ((sp + 56) # UInt |->_ **
      (UIntArray.undef_full (sp + 4) 13 ** (sp # UInt |->_ ** frame)))).
  { sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 15 16 ltac:(lia)).
    sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 14 15 ltac:(lia)).
    sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 1 14 ltac:(lia)).
    rewrite sizeof_uint.
    replace (sp + 15 * 4) with (sp + 60) by ring.
    replace (sp + 14 * 4) with (sp + 56) by ring.
    replace (sp + 1 * 4) with (sp + 4) by ring.
    replace (16 - 15) with 1 by lia; replace (15 - 14) with 1 by lia.
    replace (14 - 1) with 13 by lia.
    sep_apply_l_atomic (task_stack_undef_single_cell (sp + 60)).
    sep_apply_l_atomic (task_stack_undef_single_cell (sp + 56)).
    sep_apply_l_atomic (task_stack_undef_single_cell sp); entailer!. }
  destruct (task_stack_uint_store_execution (sp + 60) lr _ before Hlr
    (Hsplit before Hbefore)) as [pc_heap [Hpc Hpc_heap]].
  assert (Hlr_input : (sp + 60) # UInt |-> lr ** ((sp + 56) # UInt |->_ **
      (UIntArray.undef_full (sp + 4) 13 ** (sp # UInt |->_ ** frame))) |--
    (sp + 56) # UInt |->_ ** (UIntArray.undef_full (sp + 4) 13 **
      (sp # UInt |->_ ** ((sp + 60) # UInt |-> lr ** frame)))) by entailer!.
  destruct (task_stack_uint_store_execution (sp + 56) lr _ pc_heap Hlr
    (Hlr_input pc_heap Hpc_heap)) as [lr_heap [Hlr_run Hlr_heap]].
  assert (Hregister_input : (sp + 56) # UInt |-> lr **
      (UIntArray.undef_full (sp + 4) 13 **
       (sp # UInt |->_ ** ((sp + 60) # UInt |-> lr ** frame))) |--
    UIntArray.undef_full (sp + 4) (Zlength registers) **
      (sp # UInt |->_ ** ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> lr ** frame)))).
  { rewrite Hzlength; entailer!. }
  destruct (armv7a_frame_store_words_execution registers (sp + 4) _ lr_heap Hranges
    (Hregister_input lr_heap Hlr_heap)) as [register_heap [Hregister_run Hregister_heap]].
  rewrite Hzlength in Hregister_heap.
  assert (Hcpsr_input : UIntArray.mixed_full (sp + 4) 13 (map (@Some Z) registers) **
      (sp # UInt |->_ ** ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> lr ** frame))) |--
    sp # UInt |->_ ** (UIntArray.mixed_full (sp + 4) 13 (map (@Some Z) registers) **
      ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> lr ** frame)))) by entailer!.
  destruct (task_stack_uint_store_execution sp cpsr _ register_heap Hcpsr
    (Hcpsr_input register_heap Hregister_heap)) as [after [Hcpsr_run Hafter]].
  exists after; split.
  - unfold armv7a_task_frame_store_writes.
    eapply heap_execution_append; [exact Hpc|].
    eapply heap_execution_append; [exact Hlr_run|].
    eapply heap_execution_append; eassumption.
  - assert (Hmerge : sp # UInt |-> cpsr **
      (UIntArray.mixed_full (sp + 4) 13 (map (@Some Z) registers) **
       ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> lr ** frame))) |--
      UIntArray.mixed_full sp 16 (map (@Some Z) (cpsr :: registers ++ [lr; lr])) ** frame).
    { sep_apply_l_atomic (task_stack_cell_mixed_single sp cpsr).
      sep_apply_l_atomic (task_stack_cell_mixed_single (sp + 56) lr).
      sep_apply_l_atomic (task_stack_cell_mixed_single (sp + 60) lr).
      pose proof (UIntArray.mixed_full_merge_to_mixed_full sp 1 14
        [Some cpsr] (map (@Some Z) registers) ltac:(lia)) as Hhead.
      rewrite sizeof_uint in Hhead.
      replace (sp + 1 * 4) with (sp + 4) in Hhead by ring.
      replace (14 - 1) with 13 in Hhead by lia.
      pose proof (UIntArray.mixed_full_merge_to_mixed_full sp 14 15
        ([Some cpsr] ++ map (@Some Z) registers) [Some lr] ltac:(lia)) as Hlink.
      rewrite sizeof_uint in Hlink.
      replace (sp + 14 * 4) with (sp + 56) in Hlink by ring.
      replace (15 - 14) with 1 in Hlink by lia.
      pose proof (UIntArray.mixed_full_merge_to_mixed_full sp 15 16
        (([Some cpsr] ++ map (@Some Z) registers) ++ [Some lr]) [Some lr] ltac:(lia)) as Hpc_merge.
      rewrite sizeof_uint in Hpc_merge.
      replace (sp + 15 * 4) with (sp + 60) in Hpc_merge by ring.
      replace (16 - 15) with 1 in Hpc_merge by lia.
      replace (map (@Some Z) (cpsr :: registers ++ [lr; lr])) with
        ((([Some cpsr] ++ map (@Some Z) registers) ++ [Some lr]) ++ [Some lr])
        by (cbn [map]; rewrite map_app; cbn [map]; repeat rewrite <- app_assoc; reflexivity).
      sep_apply_r_atomic Hpc_merge.
      sepcon_assoc_change; sep_apply_r_atomic Hlink.
      sepcon_assoc_change; sep_apply_r_atomic Hhead; entailer!. }
    exact (Hmerge after Hafter).
Qed.

(** The source's TST LR,#1; ORRNE R0,R0,#0x20. This is the saved word,
    not an assertion that the currently executing CPU has changed mode. *)
Definition armv7a_task_saved_cpsr (cpsr lr : Z) : Z :=
  if Z.eqb (Z.land lr 1) 0 then cpsr else Z.lor cpsr 32.

Lemma armv7a_task_saved_cpsr_in_range : forall cpsr lr,
  0 <= cpsr < 4294967296 -> 0 <= armv7a_task_saved_cpsr cpsr lr < 4294967296.
Proof.
  intros cpsr lr Hcpsr; unfold armv7a_task_saved_cpsr.
  destruct (Z.eqb (Z.land lr 1) 0); [exact Hcpsr|].
  apply (bitmap_lor_in_range 32); cbn; lia.
Qed.

Definition armv7a_task_save_writes (old_sp cpsr : Z) (registers : list Z) (lr : Z) :=
  armv7a_task_frame_store_writes (old_sp - 64) (armv7a_task_saved_cpsr cpsr lr) registers lr.

(** A descriptor of the words just written. Constructing this record is
    not ownership of an invocation or a platform execution permission. *)
Definition armv7a_task_save_image (call : OsSchedCallContext)
  (old_sp cpsr : Z) (registers : list Z) (lr : Z) (fragments : TaskStackFragments)
  : Armv7aContinuation :=
  {| armv7a_continuation_call := Some call;
     armv7a_continuation_stack := call.(os_sched_call_stack);
     armv7a_continuation_sp := old_sp - 64;
     armv7a_continuation_fragments := fragments;
     armv7a_continuation_cpsr := armv7a_task_saved_cpsr cpsr lr;
     armv7a_continuation_registers := registers;
     armv7a_continuation_lr := lr;
     armv7a_continuation_pc := lr |}.

Lemma armv7a_task_save_image_binding : forall call old_sp cpsr registers lr fragments,
  List.length registers = 13%nat ->
  armv7a_continuation_binding (armv7a_task_save_image call old_sp cpsr registers lr fragments).
Proof. intros; split; [assumption|reflexivity]. Qed.

Lemma armv7a_task_frame_fragment_array : forall region first words,
  task_stack_fragments_rep region [(first, first + 16, words)] --||--
  UIntArray.mixed_full (region.(stackRegionBase) + first * sizeof(UINT)) 16 words.
Proof.
  intros; unfold task_stack_fragments_rep, iter_sepcon.
  cbn [map fold_left task_stack_fragment_rep].
  rewrite UIntArray.mixed_seg_0_shift.
  replace (first + 16 - first) with 16 by lia.
  change (emp ** UIntArray.mixed_full (region.(stackRegionBase) + first * sizeof(UINT))
    16 words --||-- UIntArray.mixed_full (region.(stackRegionBase) + first * sizeof(UINT)) 16 words).
  split; entailer!.
Qed.

(** Prefix and suffix are existing fragments, not newly owned gaps.
    Borrowed intervals remain absent; only this owned sixteen-word slice
    is overwritten, so callers need not own an unfragmented whole stack. *)
Lemma armv7a_task_frame_fragments_split : forall region prefix suffix first words,
  task_stack_fragments_rep region (prefix ++ [(first, first + 16, words)] ++ suffix) --||--
  UIntArray.mixed_full (region.(stackRegionBase) + first * sizeof(UINT)) 16 words **
    (task_stack_fragments_rep region prefix ** task_stack_fragments_rep region suffix).
Proof.
  intros; rewrite !task_stack_fragments_rep_app, armv7a_task_frame_fragment_array.
  split; entailer!.
Qed.

Lemma armv7a_task_frame_update_preserves_fragment_bounds :
  forall prefix suffix first old_words new_words limit lower,
  task_stack_fragments_in_range limit lower
    (prefix ++ [(first, first + 16, old_words)] ++ suffix) ->
  task_stack_fragments_in_range limit lower
    (prefix ++ [(first, first + 16, new_words)] ++ suffix).
Proof.
  induction prefix as [|[[lo hi] words] rest IH]; intros; cbn in *; [tauto|].
  destruct H as [Hlo [Hhi Hrest]]; split; [exact Hlo|].
  split; [exact Hhi|]; eapply IH; exact Hrest.
Qed.

Lemma armv7a_task_save_fragment_execution :
  forall call old_sp cpsr registers lr prefix suffix first old_words (frame : Assertion) before,
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  old_sp - 64 = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) +
    first * sizeof(UINT) ->
  (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
    (prefix ++ [(first, first + 16, old_words)] ++ suffix) ** frame) before ->
  let words := armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr] in
  let fragments := prefix ++ [(first, first + 16, map (@Some Z) words)] ++ suffix in
  let saved := armv7a_task_save_image call old_sp cpsr registers lr fragments in
  exists after,
    kernel_heap_execution (armv7a_task_save_writes old_sp cpsr registers lr) before after /\
    (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** frame) after /\
    armv7a_continuation_restore_reads saved after /\
    exists residual : Assertion,
      task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) |--
      UIntArray.mixed_full saved.(armv7a_continuation_sp) 16
        (map (@Some Z) (armv7a_continuation_words saved)) ** residual.
Proof.
  intros call old_sp cpsr registers lr prefix suffix first old_words frame before
    Hlength Hcpsr Hlr Hranges Hsp Hbefore.
  cbn zeta.
  set (region := call.(os_sched_call_stack).(stackLeaseRegion)).
  change (old_sp - 64 = region.(stackRegionBase) + first * sizeof(UINT)) in Hsp.
  set (words := armv7a_task_saved_cpsr cpsr lr :: registers ++ [lr; lr]).
  set (residual := task_stack_fragments_rep region prefix ** task_stack_fragments_rep region suffix).
  assert (Howned : task_stack_fragments_rep region
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) ** frame |--
    UIntArray.undef_full (old_sp - 64) 16 ** (residual ** frame)).
  { rewrite armv7a_task_frame_fragments_split, <- Hsp.
    sep_apply_l_atomic (UIntArray.mixed_full_to_undef_full (old_sp - 64) 16 old_words).
    unfold residual; entailer!. }
  destruct (armv7a_task_frame_store_execution (old_sp - 64)
    (armv7a_task_saved_cpsr cpsr lr) registers lr (residual ** frame) before Hlength
    (armv7a_task_saved_cpsr_in_range cpsr lr Hcpsr) Hlr Hranges
    (Howned before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : UIntArray.mixed_full (old_sp - 64) 16 (map (@Some Z) words) **
      (residual ** frame) |--
    task_stack_fragments_rep region
      (prefix ++ [(first, first + 16, map (@Some Z) words)] ++ suffix) ** frame).
  { rewrite armv7a_task_frame_fragments_split, <- Hsp; unfold residual; entailer!. }
  split; [exact (Hmerge after Hafter)|].
  split.
  - split; [apply armv7a_task_save_image_binding; exact Hlength|].
    cbn [armv7a_task_save_image armv7a_continuation_sp armv7a_continuation_words
      armv7a_continuation_cpsr armv7a_continuation_registers armv7a_continuation_lr
      armv7a_continuation_pc].
    apply (armv7a_frame_array_reads words (old_sp - 64) (residual ** frame) after).
    assert (Hzlength : Zlength words = 16).
    { unfold words; rewrite Zlength_correct; cbn [List.length].
      rewrite List.length_app, Hlength; reflexivity. }
    rewrite Hzlength; exact Hafter.
  - exists residual.
    change (task_stack_fragments_rep region
      (prefix ++ [(first, first + 16, map (@Some Z) words)] ++ suffix) |--
      UIntArray.mixed_full (old_sp - 64) 16 (map (@Some Z) words) ** residual).
    rewrite armv7a_task_frame_fragments_split, <- Hsp; reflexivity.
Qed.
