Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.armv7a_task_save_frame_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules ListNotations KernelHeapStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Ordinary-memory projection of OS_CPU_ARM_ExceptHndlr in the selected
    ARMv7-A/GNU non-VFP port. Keep its actual five store groups: PC, LR,
    R4--R12, copied R0--R3, SPSR. This is not the task-switch save, whose
    two last words are both LR. The exception-bank reads and CPU exchange
    remain at the existing explicit architecture boundary. *)
Lemma armv7a_irq_frame_store_execution : forall saved (frame : Assertion) before,
  armv7a_continuation_binding saved ->
  0 <= saved.(armv7a_continuation_cpsr) < 4294967296 ->
  0 <= saved.(armv7a_continuation_lr) < 4294967296 ->
  0 <= saved.(armv7a_continuation_pc) < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296)
    saved.(armv7a_continuation_registers) ->
  (UIntArray.undef_full saved.(armv7a_continuation_sp) 16 ** frame) before ->
  exists after,
    kernel_heap_execution (armv7a_continuation_save_writes saved) before after /\
    (UIntArray.mixed_full saved.(armv7a_continuation_sp) 16
      (map (@Some Z) (armv7a_continuation_words saved)) ** frame) after.
Proof.
  intros saved frame before [Hlength Hbinding] Hcpsr Hlr Hpc Hranges Hbefore.
  set (sp := saved.(armv7a_continuation_sp)) in *.
  set (registers := saved.(armv7a_continuation_registers)) in *.
  set (cpsr := saved.(armv7a_continuation_cpsr)) in *.
  set (lr := saved.(armv7a_continuation_lr)) in *.
  set (pc := saved.(armv7a_continuation_pc)) in *.
  assert (Hfirst_length : Zlength (firstn 4 registers) = 4).
  { rewrite Zlength_correct, firstn_length, Hlength; reflexivity. }
  assert (Hlast_length : Zlength (skipn 4 registers) = 9).
  { rewrite Zlength_correct, skipn_length, Hlength; reflexivity. }
  assert (Hparts : Forall (fun value => 0 <= value < 4294967296) (firstn 4 registers) /\
    Forall (fun value => 0 <= value < 4294967296) (skipn 4 registers)).
  { rewrite <- Forall_app, firstn_skipn; exact Hranges. }
  destruct Hparts as [Hfirst_range Hlast_range].
  assert (Hsplit : UIntArray.undef_full sp 16 ** frame |--
    (sp + 60) # UInt |->_ ** ((sp + 56) # UInt |->_ **
      (UIntArray.undef_full (sp + 20) 9 **
       (UIntArray.undef_full (sp + 4) 4 ** (sp # UInt |->_ ** frame))))).
  { sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 15 16 ltac:(lia)).
    sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 14 15 ltac:(lia)).
    sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 5 14 ltac:(lia)).
    sep_apply_l_atomic (UIntArray.undef_full_split_to_undef_full sp 1 5 ltac:(lia)).
    rewrite sizeof_uint.
    replace (sp + 15 * 4) with (sp + 60) by ring.
    replace (sp + 14 * 4) with (sp + 56) by ring.
    replace (sp + 5 * 4) with (sp + 20) by ring.
    replace (sp + 1 * 4) with (sp + 4) by ring.
    replace (16 - 15) with 1 by lia; replace (15 - 14) with 1 by lia.
    replace (14 - 5) with 9 by lia; replace (5 - 1) with 4 by lia.
    sep_apply_l_atomic (task_stack_undef_single_cell (sp + 60)).
    sep_apply_l_atomic (task_stack_undef_single_cell (sp + 56)).
    sep_apply_l_atomic (task_stack_undef_single_cell sp); entailer!. }
  destruct (task_stack_uint_store_execution (sp + 60) pc _ before Hpc
    (Hsplit before Hbefore)) as [pc_heap [Hpc_run Hpc_heap]].
  assert (Hlr_input : (sp + 60) # UInt |-> pc ** ((sp + 56) # UInt |->_ **
      (UIntArray.undef_full (sp + 20) 9 **
       (UIntArray.undef_full (sp + 4) 4 ** (sp # UInt |->_ ** frame)))) |--
    (sp + 56) # UInt |->_ ** (UIntArray.undef_full (sp + 20) 9 **
      (UIntArray.undef_full (sp + 4) 4 **
       (sp # UInt |->_ ** ((sp + 60) # UInt |-> pc ** frame))))) by entailer!.
  destruct (task_stack_uint_store_execution (sp + 56) lr _ pc_heap Hlr
    (Hlr_input pc_heap Hpc_heap)) as [lr_heap [Hlr_run Hlr_heap]].
  assert (Hlast_input : (sp + 56) # UInt |-> lr **
      (UIntArray.undef_full (sp + 20) 9 **
       (UIntArray.undef_full (sp + 4) 4 **
        (sp # UInt |->_ ** ((sp + 60) # UInt |-> pc ** frame)))) |--
    UIntArray.undef_full (sp + 20) (Zlength (skipn 4 registers)) **
      (UIntArray.undef_full (sp + 4) 4 **
       (sp # UInt |->_ ** ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> pc ** frame))))).
  { rewrite Hlast_length; entailer!. }
  destruct (armv7a_frame_store_words_execution (skipn 4 registers) (sp + 20) _ lr_heap
    Hlast_range (Hlast_input lr_heap Hlr_heap)) as [last_heap [Hlast_run Hlast_heap]].
  rewrite Hlast_length in Hlast_heap.
  assert (Hfirst_input : UIntArray.mixed_full (sp + 20) 9 (map (@Some Z) (skipn 4 registers)) **
      (UIntArray.undef_full (sp + 4) 4 **
       (sp # UInt |->_ ** ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> pc ** frame)))) |--
    UIntArray.undef_full (sp + 4) (Zlength (firstn 4 registers)) **
      (UIntArray.mixed_full (sp + 20) 9 (map (@Some Z) (skipn 4 registers)) **
       (sp # UInt |->_ ** ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> pc ** frame))))).
  { rewrite Hfirst_length; entailer!. }
  destruct (armv7a_frame_store_words_execution (firstn 4 registers) (sp + 4) _ last_heap
    Hfirst_range (Hfirst_input last_heap Hlast_heap)) as [register_heap [Hfirst_run Hregister_heap]].
  rewrite Hfirst_length in Hregister_heap.
  assert (Hcpsr_input : UIntArray.mixed_full (sp + 4) 4 (map (@Some Z) (firstn 4 registers)) **
      (UIntArray.mixed_full (sp + 20) 9 (map (@Some Z) (skipn 4 registers)) **
       (sp # UInt |->_ ** ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> pc ** frame)))) |--
    sp # UInt |->_ ** (UIntArray.mixed_full (sp + 4) 4 (map (@Some Z) (firstn 4 registers)) **
      (UIntArray.mixed_full (sp + 20) 9 (map (@Some Z) (skipn 4 registers)) **
       ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> pc ** frame))))) by entailer!.
  destruct (task_stack_uint_store_execution sp cpsr _ register_heap Hcpsr
    (Hcpsr_input register_heap Hregister_heap)) as [after [Hcpsr_run Hafter]].
  exists after; split.
  - unfold armv7a_continuation_save_writes.
    eapply heap_execution_append; [exact Hpc_run|].
    eapply heap_execution_append; [exact Hlr_run|].
    eapply heap_execution_append; [exact Hlast_run|].
    eapply heap_execution_append; eassumption.
  - assert (Hregisters_merge : UIntArray.mixed_full (sp + 4) 4 (map (@Some Z) (firstn 4 registers)) **
      UIntArray.mixed_full (sp + 20) 9 (map (@Some Z) (skipn 4 registers)) |--
      UIntArray.mixed_full (sp + 4) 13 (map (@Some Z) registers)).
    { pose proof (UIntArray.mixed_full_merge_to_mixed_full (sp + 4) 4 13
        (map (@Some Z) (firstn 4 registers)) (map (@Some Z) (skipn 4 registers)) ltac:(lia)) as Hmerge.
      rewrite sizeof_uint in Hmerge.
      replace (sp + 4 + 4 * 4) with (sp + 20) in Hmerge by ring.
      replace (13 - 4) with 9 in Hmerge by lia.
      rewrite <- map_app, firstn_skipn in Hmerge; exact Hmerge. }
    assert (Hmerge : sp # UInt |-> cpsr **
      (UIntArray.mixed_full (sp + 4) 4 (map (@Some Z) (firstn 4 registers)) **
       (UIntArray.mixed_full (sp + 20) 9 (map (@Some Z) (skipn 4 registers)) **
        ((sp + 56) # UInt |-> lr ** ((sp + 60) # UInt |-> pc ** frame)))) |--
      UIntArray.mixed_full sp 16 (map (@Some Z) (cpsr :: registers ++ [lr; pc])) ** frame).
    { sep_apply_l_atomic Hregisters_merge.
      sep_apply_l_atomic (task_stack_cell_mixed_single sp cpsr).
      sep_apply_l_atomic (task_stack_cell_mixed_single (sp + 56) lr).
      sep_apply_l_atomic (task_stack_cell_mixed_single (sp + 60) pc).
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
        (([Some cpsr] ++ map (@Some Z) registers) ++ [Some lr]) [Some pc] ltac:(lia)) as Hpc_merge.
      rewrite sizeof_uint in Hpc_merge.
      replace (sp + 15 * 4) with (sp + 60) in Hpc_merge by ring.
      replace (16 - 15) with 1 in Hpc_merge by lia.
      replace (map (@Some Z) (cpsr :: registers ++ [lr; pc])) with
        ((([Some cpsr] ++ map (@Some Z) registers) ++ [Some lr]) ++ [Some pc])
        by (cbn [map]; rewrite map_app; cbn [map]; repeat rewrite <- app_assoc; reflexivity).
      sep_apply_r_atomic Hpc_merge.
      sepcon_assoc_change; sep_apply_r_atomic Hlink.
      sepcon_assoc_change; sep_apply_r_atomic Hhead; entailer!. }
    exact (Hmerge after Hafter).
Qed.

(** Computed descriptor of this source save, not an additional CPU token.
    The caller retains the exact prefix/suffix fragments it already owned;
    a borrowed hole is never filled in by this construction. *)
Definition armv7a_irq_save_image (call : OsSchedCallContext)
  (sp cpsr : Z) (registers : list Z) (lr pc : Z) (fragments : TaskStackFragments)
  : Armv7aContinuation :=
  {| armv7a_continuation_call := Some call;
     armv7a_continuation_stack := call.(os_sched_call_stack);
     armv7a_continuation_sp := sp;
     armv7a_continuation_fragments := fragments;
     armv7a_continuation_cpsr := cpsr;
     armv7a_continuation_registers := registers;
     armv7a_continuation_lr := lr;
     armv7a_continuation_pc := pc |}.

Lemma armv7a_irq_save_image_binding : forall call sp cpsr registers lr pc fragments,
  List.length registers = 13%nat ->
  armv7a_continuation_binding (armv7a_irq_save_image call sp cpsr registers lr pc fragments).
Proof. intros; split; [assumption|reflexivity]. Qed.

Lemma armv7a_irq_save_image_frame_slice : forall call sp cpsr registers lr pc prefix suffix first,
  sp = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  armv7a_task_frame_slice (armv7a_irq_save_image call sp cpsr registers lr pc
    (prefix ++ [(first, first + 16, map (@Some Z) (cpsr :: registers ++ [lr; pc]))] ++ suffix)).
Proof.
  intros call sp cpsr registers lr pc prefix suffix first Hsp.
  exists (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) prefix **
    task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion) suffix).
  cbn [armv7a_irq_save_image armv7a_continuation_stack armv7a_continuation_sp
    armv7a_continuation_fragments armv7a_continuation_words armv7a_continuation_cpsr
    armv7a_continuation_registers armv7a_continuation_lr armv7a_continuation_pc].
  rewrite armv7a_task_frame_fragments_split, Hsp; reflexivity.
Qed.

Lemma armv7a_irq_save_fragment_execution :
  forall call sp cpsr registers lr pc prefix suffix first old_words (frame : Assertion) before,
  List.length registers = 13%nat ->
  0 <= cpsr < 4294967296 -> 0 <= lr < 4294967296 -> 0 <= pc < 4294967296 ->
  Forall (fun value => 0 <= value < 4294967296) registers ->
  sp = call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionBase) + first * sizeof(UINT) ->
  (task_stack_fragments_rep call.(os_sched_call_stack).(stackLeaseRegion)
    (prefix ++ [(first, first + 16, old_words)] ++ suffix) ** frame) before ->
  let fragments := prefix ++ [(first, first + 16,
    map (@Some Z) (cpsr :: registers ++ [lr; pc]))] ++ suffix in
  let saved := armv7a_irq_save_image call sp cpsr registers lr pc fragments in
  exists after,
    kernel_heap_execution (armv7a_continuation_save_writes saved) before after /\
    (task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** frame) after /\
    armv7a_continuation_restore_reads saved after /\ armv7a_task_frame_slice saved.
Proof.
  intros call sp cpsr registers lr pc prefix suffix first old_words frame before
    Hlength Hcpsr Hlr Hpc Hranges Hsp Hbefore; cbn zeta.
  set (region := call.(os_sched_call_stack).(stackLeaseRegion)).
  set (words := cpsr :: registers ++ [lr; pc]).
  set (fragments := prefix ++ [(first, first + 16, map (@Some Z) words)] ++ suffix).
  set (saved := armv7a_irq_save_image call sp cpsr registers lr pc fragments).
  set (residual := task_stack_fragments_rep region prefix ** task_stack_fragments_rep region suffix).
  assert (Hbinding : armv7a_continuation_binding saved)
    by (apply armv7a_irq_save_image_binding; exact Hlength).
  assert (Hslice : armv7a_task_frame_slice saved)
    by (apply armv7a_irq_save_image_frame_slice; exact Hsp).
  assert (Howned : task_stack_fragments_rep region
      (prefix ++ [(first, first + 16, old_words)] ++ suffix) ** frame |--
    UIntArray.undef_full sp 16 ** (residual ** frame)).
  { rewrite armv7a_task_frame_fragments_split; unfold region; rewrite <- Hsp.
    sep_apply_l_atomic (UIntArray.mixed_full_to_undef_full sp 16 old_words).
    unfold residual; entailer!. }
  destruct (armv7a_irq_frame_store_execution saved (residual ** frame) before
    Hbinding Hcpsr Hlr Hpc Hranges (Howned before Hbefore)) as [after [Hrun Hafter]].
  assert (Hmerge : UIntArray.mixed_full sp 16 (map (@Some Z) words) ** (residual ** frame) |--
    task_stack_fragments_rep region fragments ** frame).
  { unfold fragments; rewrite armv7a_task_frame_fragments_split; unfold region; rewrite <- Hsp.
    unfold residual; entailer!. }
  pose proof (Hmerge after Hafter) as Hfinal.
  exists after; split; [exact Hrun|]. split; [exact Hfinal|].
  split; [eapply armv7a_task_frame_slice_restore_reads; eassumption|exact Hslice].
Qed.
