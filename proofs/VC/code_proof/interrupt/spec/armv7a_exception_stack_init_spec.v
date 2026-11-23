Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_clear_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_clear_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations KernelHeapStorage KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Pinned ARMv7-A/os_cpu_c.c, OSInitHookBegin, lines 95--101.
    The OS_CPU_GLOBALS translation unit actually allocates ExceptStk and
    its Base cell through the ORIGINAL port header. The prepared GNU-only
    verification input deliberately has extern declarations instead.

    This is the masked initializer PREFIX: size-- / *pstk++=0, followed by
    Base=&ExceptStk[size] and the OS_STK pointer cast of Base&0xfffffff8.
    Its resource input is the real array and pointer cell, not their address
    labels. The default header has 1024 words, despite its older 128-word
    comment. The parameterized region below retains other explicit sizes.
    DRegCntGet and the following counter stores are outside this prefix.
    No boot mask, IRQ execution permission, or new platform ABI is created. *)
Definition armv7a_exception_stack_aligned_top (region : TaskStackRegion) : addr :=
  (task_stack_region_end region / 8) * 8.

Definition armv7a_exception_stack_initialized (region : TaskStackRegion)
  (base_cell : addr) : Assertion :=
  base_cell # Ptr |-> armv7a_exception_stack_aligned_top region **
  task_stack_fragments_rep region
    (task_stack_complete_fragments region
      (repeat (Some 0) (Z.to_nat region.(stackRegionWords)))).

Definition armv7a_exception_stack_init_writes (region : TaskStackRegion)
  (base_cell : addr) : list (addr * Mem.byte) :=
  task_stack_clear_writes region.(stackRegionBase) (Z.to_nat region.(stackRegionWords)) ++
  pointer_store_writes base_cell (task_stack_region_end region) ++
  pointer_store_writes base_cell (Z.land (task_stack_region_end region) 4294967288).

Lemma armv7a_exception_stack_aligned_top_source_mask : forall region,
  valid_task_stack_region region ->
  armv7a_exception_stack_aligned_top region =
    Z.land (task_stack_region_end region) 4294967288.
Proof.
  intros region [Hsize [Hbase [Halign Hend]]].
  assert (Hrange : 0 <= task_stack_region_end region < 4294967296).
  { unfold task_stack_region_end in *; rewrite sizeof_uint in *; lia. }
  unfold armv7a_exception_stack_aligned_top.
  replace 4294967288 with (Z.land (Z.ones 32) (Z.lnot (Z.ones 3))) by reflexivity.
  rewrite task_stack_init_clear_low_bits by lia; reflexivity.
Qed.

Lemma armv7a_exception_stack_aligned_top_bounds : forall region,
  valid_task_stack_region region ->
  0 <= armv7a_exception_stack_aligned_top region <= task_stack_region_end region /\
  task_stack_region_end region < armv7a_exception_stack_aligned_top region + 8 /\
  armv7a_exception_stack_aligned_top region mod 8 = 0.
Proof.
  intros region [Hsize [Hbase [Halign Hend]]].
  assert (Hnonnegative : 0 <= task_stack_region_end region).
  { unfold task_stack_region_end; rewrite sizeof_uint; lia. }
  pose proof (Z.div_mod (task_stack_region_end region) 8 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (task_stack_region_end region) 8 ltac:(lia)) as Hmod.
  assert (Hquotient : 0 <= task_stack_region_end region / 8) by (apply Z.div_pos; lia).
  unfold armv7a_exception_stack_aligned_top.
  split; [split; lia|]. split; [lia|apply Z.mod_mul; lia].
Qed.

(** Reuse the already proved identical incrementing typed-zero loop; the
    hook does not call OS_TaskStkClr or acquire its option guards. The two
    subsequent Base writes and the intervening actual load are retained.
    Complete fragments are the SAME array bytes, not a second stack owner. *)
Lemma armv7a_exception_stack_init_store_execution :
  forall region base_cell initial (frame : Assertion) before,
  valid_task_stack_region region ->
  (task_stack_storage region initial ** (base_cell # Ptr |->_ ** frame)) before ->
  exists cleared based after,
    kernel_heap_execution
      (task_stack_clear_writes region.(stackRegionBase) (Z.to_nat region.(stackRegionWords)))
      before cleared /\
    kernel_heap_execution (pointer_store_writes base_cell (task_stack_region_end region)) cleared based /\
    pointer_load base_cell (task_stack_region_end region) based /\
    kernel_heap_execution
      (pointer_store_writes base_cell (Z.land (task_stack_region_end region) 4294967288)) based after /\
    kernel_heap_execution (armv7a_exception_stack_init_writes region base_cell) before after /\
    (armv7a_exception_stack_initialized region base_cell ** frame) after.
Proof.
  intros region base_cell initial frame before Hvalid Hbefore.
  assert (Hlength : Zlength initial = region.(stackRegionWords)).
  { destruct Hbefore as [owned [rest [Hjoin [Hstack Hrest]]]].
    exact (task_stack_storage_length region initial owned Hstack). }
  assert (Hcount : List.length initial = Z.to_nat region.(stackRegionWords)).
  { rewrite <- Hlength, Zlength_correct, Nat2Z.id; reflexivity. }
  assert (Hend : 0 <= task_stack_region_end region < 4294967296).
  { destruct Hvalid as [Hsize [Hbase [Halign Hend]]].
    unfold task_stack_region_end in *; rewrite sizeof_uint in *; lia. }
  destruct (armv7a_exception_stack_aligned_top_bounds region Hvalid)
    as [[Htop0 Htopend] [Hnear Halign]].
  assert (Hclear_pre : (UIntArray.mixed_full region.(stackRegionBase) (Zlength initial) initial **
    (base_cell # Ptr |->_ ** frame)) before).
  { unfold task_stack_storage in Hbefore; rewrite Hlength; exact Hbefore. }
  destruct (task_stack_clear_store_execution 3 region.(stackRegionBase) initial
    (base_cell # Ptr |->_ ** frame) before eq_refl Hclear_pre)
    as [cleared [Hscalar [Hclear Hcleared]]].
  rewrite Hcount in Hclear.
  assert (Horder : UIntArray.mixed_full region.(stackRegionBase) (Zlength initial)
      (repeat (Some 0) (List.length initial)) ** (base_cell # Ptr |->_ ** frame) |--
    base_cell # Ptr |->_ **
      (task_stack_storage region (repeat (Some 0) (Z.to_nat region.(stackRegionWords))) ** frame)).
  { unfold task_stack_storage; rewrite Hlength, Hcount; entailer!. }
  destruct (framed_pointer_store_execution base_cell (task_stack_region_end region)
    (task_stack_storage region (repeat (Some 0) (Z.to_nat region.(stackRegionWords))) ** frame)
    cleared Hend (Horder cleared Hcleared)) as [based [Hbasewrite Hbased]].
  pose proof (framed_pointer_store_load base_cell (task_stack_region_end region) _ based Hbased) as Hread.
  assert (Hforget : base_cell # Ptr |-> task_stack_region_end region **
      (task_stack_storage region (repeat (Some 0) (Z.to_nat region.(stackRegionWords))) ** frame) |--
    base_cell # Ptr |->_ **
      (task_stack_storage region (repeat (Some 0) (Z.to_nat region.(stackRegionWords))) ** frame)).
  { sep_apply_l_atomic (store_ptr_undef_store_ptr base_cell (task_stack_region_end region)); entailer!. }
  destruct (framed_pointer_store_execution base_cell (armv7a_exception_stack_aligned_top region)
    (task_stack_storage region (repeat (Some 0) (Z.to_nat region.(stackRegionWords))) ** frame)
    based ltac:(lia) (Hforget based Hbased)) as [after [Halignwrite Hafter]].
  assert (Hsourcewrite : kernel_heap_execution
    (pointer_store_writes base_cell (Z.land (task_stack_region_end region) 4294967288)) based after).
  { rewrite <- armv7a_exception_stack_aligned_top_source_mask by exact Hvalid; exact Halignwrite. }
  exists cleared, based, after.
  split; [exact Hclear|]. split; [exact Hbasewrite|]. split; [exact Hread|].
  split; [exact Hsourcewrite|]. split.
  - unfold armv7a_exception_stack_init_writes.
    eapply heap_execution_append; [exact Hclear|].
    eapply heap_execution_append; [exact Hbasewrite|exact Hsourcewrite].
  - assert (Hpack : base_cell # Ptr |-> armv7a_exception_stack_aligned_top region **
        (task_stack_storage region (repeat (Some 0) (Z.to_nat region.(stackRegionWords))) ** frame) |--
      armv7a_exception_stack_initialized region base_cell ** frame).
    { unfold armv7a_exception_stack_initialized.
      rewrite task_stack_fragments_rep_complete; entailer!. }
    exact (Hpack after Hafter).
Qed.

(** Connect the produced owners to a SUPPLIED actual execution endpoint,
    and expose the pointer load used by the non-nested IRQ stack switch.
    Further handler pushes/calls consume this storage under their own
    contracts; this lemma does not pretend they preserve its zero values. *)
Lemma armv7a_exception_stack_init_source_post :
  forall region base_cell initial (frame : Assertion) before after,
  valid_task_stack_region region ->
  (task_stack_storage region initial ** (base_cell # Ptr |->_ ** frame)) before ->
  kernel_heap_execution (armv7a_exception_stack_init_writes region base_cell) before after ->
  pointer_load base_cell (armv7a_exception_stack_aligned_top region) after /\
  (armv7a_exception_stack_initialized region base_cell ** frame) after.
Proof.
  intros region base_cell initial frame before after Hvalid Hpre Hactual.
  destruct (armv7a_exception_stack_init_store_execution region base_cell initial frame before Hvalid Hpre)
    as [cleared [based [produced [Hclear [Hbase [Hread [Halign [Hrun Hpost]]]]]]]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; split; [|exact Hpost].
  assert (Horder : armv7a_exception_stack_initialized region base_cell ** frame |--
    base_cell # Ptr |-> armv7a_exception_stack_aligned_top region **
      (task_stack_fragments_rep region (task_stack_complete_fragments region
        (repeat (Some 0) (Z.to_nat region.(stackRegionWords)))) ** frame)).
  { unfold armv7a_exception_stack_initialized; entailer!. }
  exact (framed_pointer_store_load base_cell (armv7a_exception_stack_aligned_top region)
    _ after (Horder after Hpost)).
Qed.
