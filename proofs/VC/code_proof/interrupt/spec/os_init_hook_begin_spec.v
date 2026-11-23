Require Export Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Export AUXLib.ListLib.
From SimpleC.SL Require Export Mem SeparationLogic.
Require Export Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_clear_spec.
Require Export Ucos2Verify.VC.code.interrupt.spec.armv7a_exception_stack_init_spec.

Export UCOS2_C_Rules TaskStateDef.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Internal boot helper for the pinned V2.93.01 ARMv7-A port.  The
    region is the single original OS_CPU_GLOBALS exception-stack allocation,
    not a new stack owner.  Source annotation binds its base and each scalar
    cell to the actual C symbols, including the port-private UShort OSTmrCtr.

    The caller supplies its serialized, masked boot context in [frame].
    The selected A32 NoVFP DRegCntGet boundary is MOV R0,#0; BX LR:
    it returns zero and preserves that exact memory/ABI/mask frame.
    Neither that boundary nor this helper creates a mask or IRQ permission.
    Public OSInit must compose this local contract at its real boot state. *)
Definition os_init_hook_begin_region (base : addr) : TaskStackRegion :=
  {| stackRegionBase := base; stackRegionWords := 1024;
     stackRegionGrowsDown := true |}.

Definition os_init_hook_begin_pre (base base_cell dreg_cell timer_cell : addr)
  (initial : list (option Z)) (frame : Assertion) : Assertion :=
  coq_prop (valid_task_stack_region (os_init_hook_begin_region base)) &&
  (task_stack_storage (os_init_hook_begin_region base) initial **
   base_cell # Ptr |->_ ** dreg_cell # UInt |->_ **
   timer_cell # UShort |->_ ** frame).

Definition os_init_hook_begin_post (base base_cell dreg_cell timer_cell : addr)
  (frame : Assertion) : Assertion :=
  armv7a_exception_stack_initialized (os_init_hook_begin_region base) base_cell **
  dreg_cell # UInt |-> 0 ** timer_cell # UShort |-> 0 ** frame.

(** The residual really omits the current word.  Its zero replacement is
    supplied only by the actual C store, then folded by the existing
    task_stack_clear_rep_merge_zero_cell theorem. *)
Definition os_init_hook_begin_stack_cell_rest (base : addr)
  (initial : list (option Z)) (done : Z) : Assertion :=
  UIntArray.mixed_missing_i base done 0 (Zlength initial)
    (task_stack_clear_words initial done).

Lemma os_init_hook_begin_region_valid_iff : forall base,
  valid_task_stack_region (os_init_hook_begin_region base) <->
  0 < base /\ base mod 4 = 0 /\ base + 4096 <= 4294967295.
Proof.
  intros base.
  change ((0 < 1024 <= 4294967295 /\ 0 < base /\
           base mod sizeof(UINT) = 0 /\ base + 1024 * sizeof(UINT) <= 4294967295)
          <-> (0 < base /\ base mod 4 = 0 /\ base + 4096 <= 4294967295)).
  rewrite sizeof_uint; intuition lia.
Qed.

Lemma os_init_hook_begin_aligned_top_eq : forall base,
  armv7a_exception_stack_aligned_top (os_init_hook_begin_region base) =
  ((base + 4096) / 8) * 8.
Proof.
  intros base.
  change (((base + 1024 * sizeof(UINT)) / 8) * 8 =
          ((base + 4096) / 8) * 8).
  rewrite sizeof_uint; reflexivity.
Qed.
