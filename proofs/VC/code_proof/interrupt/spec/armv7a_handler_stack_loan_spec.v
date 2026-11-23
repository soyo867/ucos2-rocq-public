Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The two words retained by the assembly caller of OS_CPU_ExceptHndlr.
    They belong to the caller's frame, not to the region loaned to C.
    The port resource always keeps its ORIGINAL handler-record index. *)
Definition armv7a_handler_scratch (address alignment lr : Z) : Assertion :=
  address # Ptr |-> alignment ** (address + 4) # Ptr |-> lr.

Definition armv7a_handler_stack_remainder region prefix suffix : Assertion :=
  task_stack_fragments_rep region prefix ** task_stack_fragments_rep region suffix.

Lemma armv7a_handler_stack_split_scratch : forall region prefix suffix first,
  task_stack_fragments_rep region (prefix ++ [(first, first + 2, [None; None])] ++ suffix)
  --||--
  (region.(stackRegionBase) + first * sizeof(UINT)) # UInt |->_ **
  ((region.(stackRegionBase) + first * sizeof(UINT) + 4) # UInt |->_ **
    armv7a_handler_stack_remainder region prefix suffix).
Proof.
  intros region prefix suffix first.
  rewrite task_stack_fragments_rep_app.
  change (task_stack_fragments_rep region prefix **
    iter_sepcon (task_stack_fragment_rep region (first, first + 2, [None; None]) ::
      map (task_stack_fragment_rep region) suffix) --||--
    (region.(stackRegionBase) + first * sizeof(UINT)) # UInt |->_ **
    ((region.(stackRegionBase) + first * sizeof(UINT) + 4) # UInt |->_ **
      armv7a_handler_stack_remainder region prefix suffix)).
  rewrite TaskFieldStorage.iter_sepcon_cons_equiv.
  unfold task_stack_fragment_rep, UIntArray.mixed_seg.
  cbn [store_array_rec UIntArray.mixedstoreA StoreUIntAsElement.undefstoreA].
  rewrite sizeof_uint.
  replace (stackRegionBase region + (first + 1) * 4) with
    (stackRegionBase region + first * 4 + 4) by ring.
  unfold armv7a_handler_stack_remainder, task_stack_fragments_rep.
  split; entailer!.
Qed.

(** Actual stores establish the protected values. The input words can be
    unspecified, but the output words must not be forgotten before POP. *)
Lemma armv7a_handler_scratch_push_source : forall address alignment lr (frame : Assertion) before,
  0 <= alignment < 4294967296 -> 0 <= lr < 4294967296 ->
  (address # UInt |->_ ** ((address + 4) # UInt |->_ ** frame)) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes address alignment ++ pointer_store_writes (address + 4) lr)
      before after /\ (armv7a_handler_scratch address alignment lr ** frame) after.
Proof.
  intros address alignment lr frame before Halign Hlr Hpre.
  assert (Hinput : address # UInt |->_ ** ((address + 4) # UInt |->_ ** frame) |--
    address # Ptr |->_ ** ((address + 4) # Ptr |->_ ** frame)).
  { rewrite (proj1 (kernel_undef_store_uint_ptr_equiv address)),
      (proj1 (kernel_undef_store_uint_ptr_equiv (address + 4))); reflexivity. }
  destruct (framed_pointer_store_execution address alignment _ before Halign (Hinput before Hpre))
    as [middle [Hfirst Hmiddle]].
  assert (Horder : address # Ptr |-> alignment ** ((address + 4) # Ptr |->_ ** frame) |--
    (address + 4) # Ptr |->_ ** (address # Ptr |-> alignment ** frame)) by entailer!.
  destruct (framed_pointer_store_execution (address + 4) lr _ middle Hlr (Horder middle Hmiddle))
    as [after [Hsecond Hafter]].
  exists after; split; [eapply heap_execution_append; eassumption|].
  assert (Hfinish : (address + 4) # Ptr |-> lr ** (address # Ptr |-> alignment ** frame) |--
    armv7a_handler_scratch address alignment lr ** frame)
    by (unfold armv7a_handler_scratch; entailer!).
  exact (Hfinish after Hafter).
Qed.

Lemma armv7a_handler_scratch_pop_reads : forall address alignment lr (frame : Assertion) heap,
  (armv7a_handler_scratch address alignment lr ** frame) heap ->
  pointer_load address alignment heap /\ pointer_load (address + 4) lr heap.
Proof.
  intros address alignment lr frame heap Hpre; split.
  - eapply framed_pointer_store_load.
    assert (Horder : armv7a_handler_scratch address alignment lr ** frame |--
      address # Ptr |-> alignment ** ((address + 4) # Ptr |-> lr ** frame))
      by (unfold armv7a_handler_scratch; entailer!).
    exact (Horder heap Hpre).
  - eapply framed_pointer_store_load.
    assert (Horder : armv7a_handler_scratch address alignment lr ** frame |--
      (address + 4) # Ptr |-> lr ** (address # Ptr |-> alignment ** frame))
      by (unfold armv7a_handler_scratch; entailer!).
    exact (Horder heap Hpre).
Qed.

Lemma armv7a_handler_stack_merge_scratch : forall region prefix suffix first alignment lr,
  armv7a_handler_scratch (region.(stackRegionBase) + first * sizeof(UINT)) alignment lr **
    armv7a_handler_stack_remainder region prefix suffix |--
  task_stack_fragments_rep region (prefix ++ [(first, first + 2, [None; None])] ++ suffix).
Proof.
  intros; unfold armv7a_handler_scratch.
  sep_apply_l_atomic (store_ptr_store_uint (region.(stackRegionBase) + first * sizeof(UINT)) alignment
    eq_refl eq_refl).
  sep_apply_l_atomic (store_ptr_store_uint (region.(stackRegionBase) + first * sizeof(UINT) + 4) lr
    eq_refl eq_refl).
  sep_apply_l_atomic (store_uint_undef_store_uint (region.(stackRegionBase) + first * sizeof(UINT)) alignment).
  sep_apply_l_atomic (store_uint_undef_store_uint (region.(stackRegionBase) + first * sizeof(UINT) + 4) lr).
  rewrite <- (proj2 (armv7a_handler_stack_split_scratch region prefix suffix first)); entailer!.
Qed.

(** This is the explicitly selected, refined BSP private resource. C may
    use the loaned remainder; it must return that SAME assertion and the actual
    execution resource. The two assembly scratch words are not loaned.
    A remainder containing Some values requires those values to survive;
    freely writable temporary words must instead be represented by None.
    Nothing derives this contract from the old whole-fragments instance. *)
Definition armv7a_handler_stack_loan (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (handler : OsIntExitCallContext)
  (remainder : Assertion) (_ : RestoreHandlerCall) (local : KernelRestoreCursor * Z) : Assertion :=
  interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin)
    (armv7a_irq_fiq_mask (fst local).(kernel_restore_current_cpsr)) **
  port.(os_int_exit_handler_running) handler ** remainder.

Definition armv7a_handler_stack_loan_contract platform port handler remainder local_step normal_return : Prop :=
  RestoreHandlerContract (armv7a_handler_stack_loan platform port handler remainder)
    local_step normal_return /\
  (forall sg cursor before returned after,
    normal_return sg cursor before returned after ->
    snd returned.(restore_handler_local) = snd cursor.(restore_handler_local)).

Lemma armv7a_frame_word_reads_in_range : forall words sp heap,
  armv7a_frame_word_reads sp words heap ->
  Forall (fun word => 0 <= word < 4294967296) words.
Proof.
  induction words as [|word words IH]; intros sp heap Hreads; constructor.
  - exact (proj1 (proj1 Hreads)).
  - eapply IH; exact (proj2 Hreads).
Qed.

