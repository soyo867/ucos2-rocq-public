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
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected V2.93.01 OS_TaskStkClr, Source/os_task.c:1364--1395:
    STK_CHK is tested before STK_CLR; growth=1 executes size-- followed by
    *pbos++=0. Each four-byte list below is ONE typed OS_STK store. We do
    not impose an evaluation order between the store and postincrement
    within that C full-expression. The loop has no other calls/writes.
    This is its local heap projection, not arbitrary IRQ-frame transport. *)
Fixpoint task_stack_clear_writes (cursor : Z) (count : nat)
  : list (Mem.addr * Mem.byte) :=
  match count with
  | O => []
  | S rest => pointer_store_writes cursor 0 ++
      task_stack_clear_writes (cursor + sizeof(UINT)) rest
  end.

Inductive task_stack_clear_heap_steps : nat ->
  TaskStackClearLoopState -> model -> TaskStackClearLoopState -> model -> Prop :=
| TaskStackClearHeapZero : forall state heap,
    task_stack_clear_heap_steps O state heap state heap
| TaskStackClearHeapSucc : forall count state next final before middle after,
    task_stack_clear_step state next ->
    kernel_heap_execution (pointer_store_writes state.(stackClearCursor) 0) before middle ->
    task_stack_clear_heap_steps count next middle final after ->
    task_stack_clear_heap_steps (S count) state before final after.

Lemma task_stack_clear_heap_steps_scalar : forall count state before final after,
  task_stack_clear_heap_steps count state before final after ->
  task_stack_clear_steps count state final.
Proof. intros; induction H; [constructor|econstructor; eassumption]. Qed.

Lemma task_stack_clear_heap_steps_writes : forall count state before final after,
  task_stack_clear_heap_steps count state before final after ->
  kernel_heap_execution (task_stack_clear_writes state.(stackClearCursor) count) before after.
Proof.
  intros count state before final after Hsteps; induction Hsteps.
  - split; [constructor|split; reflexivity].
  - destruct H as [Hpositive ->].
    cbn [task_stack_clear_writes task_stack_clear_store_advance
      task_stack_clear_decrement stackClearCursor] in *.
    eapply heap_execution_append; eassumption.
Qed.

(** Unlike the old value-image transformer, this consumes the old/undefined
    cell and obtains the written zero from the checked typed-store writer. *)
Lemma task_stack_clear_heap_step_execution : forall bottom initial done (frame : Assertion) before,
  0 <= done < Zlength initial ->
  (task_stack_clear_rep bottom initial done ** frame) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes (bottom + done * sizeof(UINT)) 0) before after /\
    (task_stack_clear_rep bottom initial (done + 1) ** frame) after.
Proof.
  intros bottom initial done frame before Hdone Hbefore.
  assert (Hsplit : task_stack_clear_rep bottom initial done ** frame |--
    (bottom + done * sizeof(UINT)) # UInt |->_ **
    (UIntArray.mixed_missing_i bottom done 0 (Zlength initial)
      (task_stack_clear_words initial done) ** frame)).
  { sep_apply_l_atomic (task_stack_clear_rep_split_cell bottom initial done Hdone).
    sep_apply_l_atomic (UIntArray.mixedstoreA_to_undefstoreA bottom done
      (Znth done (task_stack_clear_words initial done) None)).
    unfold StoreUIntAsElement.undefstoreA; entailer!. }
  destruct (task_stack_uint_store_execution (bottom + done * sizeof(UINT)) 0
    (UIntArray.mixed_missing_i bottom done 0 (Zlength initial)
      (task_stack_clear_words initial done) ** frame) before ltac:(lia)
    (Hsplit before Hbefore)) as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : (bottom + done * sizeof(UINT)) # UInt |-> 0 **
    (UIntArray.mixed_missing_i bottom done 0 (Zlength initial)
      (task_stack_clear_words initial done) ** frame) |--
    task_stack_clear_rep bottom initial (done + 1) ** frame).
  { sep_apply_l_atomic (task_stack_clear_rep_merge_zero_cell bottom initial done Hdone); entailer!. }
  exact (Hmerge after Hafter).
Qed.

Lemma task_stack_clear_heap_steps_exist : forall count bottom initial done (frame : Assertion) before,
  0 <= done -> done + Z.of_nat count <= Zlength initial ->
  (task_stack_clear_rep bottom initial done ** frame) before ->
  exists after,
    task_stack_clear_heap_steps count (task_stack_clear_frontier bottom initial done) before
      (task_stack_clear_frontier bottom initial (done + Z.of_nat count)) after /\
    (task_stack_clear_rep bottom initial (done + Z.of_nat count) ** frame) after.
Proof.
  induction count as [|count IH]; intros bottom initial done frame before Hdone Hbound Hbefore.
  - replace (done + Z.of_nat 0) with done by lia.
    exists before; split; [constructor|exact Hbefore].
  - rewrite Nat2Z.inj_succ in Hbound |- *.
    destruct (task_stack_clear_heap_step_execution bottom initial done frame before
      ltac:(lia) Hbefore) as [middle [Hhead Hmiddle]].
    destruct (IH bottom initial (done + 1) frame middle ltac:(lia) ltac:(lia) Hmiddle)
      as [after [Htail Hafter]].
    replace (done + Z.succ (Z.of_nat count)) with (done + 1 + Z.of_nat count) by lia.
    exists after; split; [|exact Hafter].
    econstructor; [apply task_stack_clear_step_frontier; lia|exact Hhead|exact Htail].
Qed.

Definition task_stack_clear_heap_result (options : Z)
  (state : TaskStackClearLoopState) (before : model)
  (final : TaskStackClearLoopState) (after : model) : Prop :=
  if Z.eqb (Z.land options 1) 0 then final = state /\ after = before
  else if Z.eqb (Z.land options 2) 0 then final = state /\ after = before
  else exists count,
    task_stack_clear_heap_steps count state before final after /\ final.(stackClearRemaining) = 0.

Lemma task_stack_clear_heap_result_scalar : forall options state before final after,
  task_stack_clear_heap_result options state before final after ->
  task_stack_clear_result options state final.
Proof.
  intros options state before final after Hresult.
  unfold task_stack_clear_heap_result in Hresult; unfold task_stack_clear_result.
  destruct (Z.eqb (Z.land options 1) 0); [tauto|].
  destruct (Z.eqb (Z.land options 2) 0); [tauto|].
  destruct Hresult as [count [Hsteps Hzero]].
  exists count; split; [eapply task_stack_clear_heap_steps_scalar; exact Hsteps|exact Hzero].
Qed.

Lemma task_stack_clear_heap_result_disabled : forall options state heap,
  task_stack_clear_enabled options = false ->
  task_stack_clear_heap_result options state heap state heap.
Proof.
  intros options state heap Hdisabled.
  unfold task_stack_clear_enabled in Hdisabled; unfold task_stack_clear_heap_result.
  destruct (Z.eqb (Z.land options 1) 0); [split; reflexivity|].
  destruct (Z.eqb (Z.land options 2) 0); [split; reflexivity|discriminate].
Qed.

Lemma task_stack_clear_heap_zero_size : forall options bottom words heap,
  task_stack_clear_heap_result options (task_stack_clear_initial bottom 0 words) heap
    (task_stack_clear_initial bottom 0 words) heap.
Proof.
  intros; unfold task_stack_clear_heap_result.
  destruct (Z.eqb (Z.land options 1) 0); [split; reflexivity|].
  destruct (Z.eqb (Z.land options 2) 0); [split; reflexivity|].
  exists O; split; [constructor|reflexivity].
Qed.

Lemma task_stack_clear_store_execution : forall options bottom initial (frame : Assertion) before,
  task_stack_clear_enabled options = true ->
  (UIntArray.mixed_full bottom (Zlength initial) initial ** frame) before ->
  exists after,
    task_stack_clear_heap_result options
      (task_stack_clear_initial bottom (Zlength initial) initial) before
      (task_stack_clear_frontier bottom initial (Zlength initial)) after /\
    kernel_heap_execution (task_stack_clear_writes bottom (List.length initial)) before after /\
    (UIntArray.mixed_full bottom (Zlength initial)
      (repeat (Some 0) (List.length initial)) ** frame) after.
Proof.
  intros options bottom initial frame before Henabled Hbefore.
  destruct (task_stack_clear_heap_steps_exist (List.length initial) bottom initial 0 frame before
    ltac:(lia) ltac:(rewrite Zlength_correct; lia) Hbefore) as [after [Hsteps Hafter]].
  replace (0 + Z.of_nat (List.length initial)) with (Zlength initial) in Hsteps, Hafter
    by (rewrite Zlength_correct; lia).
  rewrite task_stack_clear_frontier_initial in Hsteps.
  exists after; split.
  - unfold task_stack_clear_heap_result.
    apply task_stack_clear_enabled_iff in Henabled; destruct Henabled as [Hcheck Hclear].
    apply Z.eqb_neq in Hcheck; apply Z.eqb_neq in Hclear; rewrite Hcheck, Hclear.
    exists (List.length initial); split; [exact Hsteps|cbn; lia].
  - split.
    + exact (task_stack_clear_heap_steps_writes _ _ _ _ _ Hsteps).
    + unfold task_stack_clear_rep in Hafter.
      rewrite task_stack_clear_words_complete in Hafter; exact Hafter.
Qed.

(** The final postincrement forms exactly one-past, not a store there.
    These are flat 32-bit arithmetic bounds; the same-array allocation/
    provenance obligation is not generated from them. The established
    valid region already includes this end bound. No growth=0 claim. *)
Lemma task_stack_clear_region_cursor_bounds : forall region initial done,
  valid_task_stack_region region -> region.(stackRegionWords) = Zlength initial ->
  0 <= done <= Zlength initial ->
  0 <= (task_stack_clear_frontier region.(stackRegionBase) initial done).(stackClearRemaining)
    <= 4294967295 /\
  0 <= (task_stack_clear_frontier region.(stackRegionBase) initial done).(stackClearCursor)
    <= 4294967295 /\
  (done < Zlength initial ->
    region.(stackRegionBase) <= region.(stackRegionBase) + done * sizeof(UINT) /\
    region.(stackRegionBase) + done * sizeof(UINT) + sizeof(UINT) <= task_stack_region_end region).
Proof.
  intros region initial done [Hwords [Hbase [Halign Hend]]] Hsize Hdone.
  unfold task_stack_region_end in *; cbn [task_stack_clear_frontier stackClearRemaining stackClearCursor].
  rewrite sizeof_uint in *; repeat split; intros; lia.
Qed.

(** Root's actual static arrays can supply this generic input; no bootstrap
    ghost or fresh buffer is needed. The lower/upper lists are AFTER clear,
    and the shared intermediate heap is explicit. Ext argument equality
    binds the first call to this actual region. This local two-call memory
    projection is not whole Create/OSInit or an open-IRQ framing theorem. *)
Lemma task_create_stack_clear_init_store_execution :
  forall region args options task_return initial lower upper (frame : Assertion) before,
  task_create_stack_clear_args true args =
    Some (region.(stackRegionBase), region.(stackRegionWords), options) ->
  task_stack_clear_enabled options = true ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  region.(stackRegionWords) = Zlength initial ->
  repeat (Some 0) (List.length initial) = lower ++ repeat (Some 0) 16 ++ upper ->
  0 <= args.(createEntry) < 4294967296 ->
  0 <= args.(createArgument) < 4294967296 -> 0 <= task_return < 4294967296 ->
  (task_stack_storage region initial ** frame) before ->
  exists middle after,
    task_stack_clear_heap_result options
      (task_stack_clear_initial region.(stackRegionBase) region.(stackRegionWords) initial) before
      (task_stack_clear_frontier region.(stackRegionBase) initial region.(stackRegionWords)) middle /\
    kernel_heap_execution (task_stack_clear_writes region.(stackRegionBase) (List.length initial))
      before middle /\
    kernel_heap_execution
      (task_stack_init_no_vfp_writes args.(createStackTop) args.(createEntry)
        args.(createArgument) task_return) middle after /\
    kernel_heap_execution
      (task_stack_clear_writes region.(stackRegionBase) (List.length initial) ++
       task_stack_init_no_vfp_writes args.(createStackTop) args.(createEntry)
         args.(createArgument) task_return) before after /\
    (task_stack_storage region
      (task_create_stack_image TaskStackNoVFP args task_return lower upper) ** frame) after.
Proof.
  intros region args options task_return initial lower upper frame before
    Hargs Henabled Hlayout Hsize Hzeros Hentry Harg Hreturn Hbefore.
  unfold task_stack_storage in Hbefore; rewrite Hsize in Hbefore.
  destruct (task_stack_clear_store_execution options region.(stackRegionBase) initial frame before
    Henabled Hbefore) as [middle [Hclear [Hclearwrites Hmiddle]]].
  assert (Hinput : (task_stack_storage region (lower ++ repeat (Some 0) 16 ++ upper) ** frame) middle).
  { unfold task_stack_storage; rewrite Hsize, <- Hzeros; exact Hmiddle. }
  destruct (task_create_stack_init_store_execution region args task_return lower
    (repeat (Some 0) 16) upper frame middle Hlayout eq_refl Hentry Harg Hreturn Hinput)
    as [after [Hinit Hafter]].
  exists middle, after; split; [rewrite Hsize; exact Hclear|].
  split; [exact Hclearwrites|]. split; [exact Hinit|].
  split; [eapply heap_execution_append; eassumption|exact Hafter].
Qed.
