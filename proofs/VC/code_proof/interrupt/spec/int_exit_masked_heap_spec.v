Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Import UCOS2_C_Rules KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/os_core.c:701-706, as called by the selected exception wrapper
    AFTER MSR CPSR_c masks both IRQ and FIQ. These are the actual memory
    reads and guarded counter store. Nested Save/Restore have their existing
    external masked contract; this fragment does not prove that contract,
    the whole C interpreter, handler execution or the exception return.

    In particular [observed] is constrained by the OSRunning byte read on
    THIS heap, not chosen from an earlier interrupt-entry snapshot. *)
Inductive os_int_exit_masked_counter_fragment (sg : StableGlobVars)
  : model -> bool -> model -> Prop :=
| OsIntExitMaskedInactive : forall heap,
    uchar_load sg.(g_OSRunning) 0 heap ->
    os_int_exit_masked_counter_fragment sg heap false heap
| OsIntExitMaskedActive : forall before nesting after,
    uchar_load sg.(g_OSRunning) 1 before ->
    uchar_load sg.(g_OSIntNesting) nesting before ->
    kernel_heap_execution
      (if 0 <? nesting then [(sg.(g_OSIntNesting), nesting - 1)] else []) before after ->
    os_int_exit_masked_counter_fragment sg before true after.

Lemma os_int_exit_raw_running_load : forall sg state heap,
  UCOS2_raw_rep sg state heap ->
  uchar_load sg.(g_OSRunning) (if state.(SchedState).(isRunning) then 1 else 0) heap.
Proof.
  intros sg state heap Hraw.
  eapply framed_uchar_store_load.
  exact (proj1 (UCOS2_raw_rep_split_running sg state) heap Hraw).
Qed.

Lemma os_int_exit_raw_nesting_load : forall sg state heap,
  UCOS2_raw_rep sg state heap -> uchar_load sg.(g_OSIntNesting) state.(IntrState).(intNesting) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_raw_rep sg state |--
    sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
    (sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) **
     UCOS2_raw_rep_missing_interrupt sg state)).
  { rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
    cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hraw).
Qed.

Lemma os_int_exit_raw_lock_load : forall sg state heap,
  UCOS2_raw_rep sg state heap -> uchar_load sg.(g_OSLockNesting) state.(IntrState).(lockNesting) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hsplit : UCOS2_raw_rep sg state |--
    sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) **
    (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
     UCOS2_raw_rep_missing_interrupt sg state)).
  { rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
    cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!. }
  eapply framed_uchar_store_load; exact (Hsplit heap Hraw).
Qed.

Lemma os_int_exit_masked_counter_observation : forall sg state before observed after,
  UCOS2_raw_rep sg state before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  observed = state.(SchedState).(isRunning) /\
  kernel_heap_execution (os_int_exit_counter_heap_writes sg observed state) before after.
Proof.
  intros sg state before observed after Hraw Hsource.
  pose proof (os_int_exit_raw_running_load sg state before Hraw) as Hrunning.
  destruct Hsource as [heap Hread|heap nesting final Hread Hnest Hrun].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hrunning) as Hvalue.
    destruct state.(SchedState).(isRunning); [discriminate|].
    split; [reflexivity|]. split; [constructor|split; reflexivity].
  - pose proof (uchar_load_deterministic _ _ _ _ Hread Hrunning) as Hvalue.
    pose proof (uchar_load_deterministic _ _ _ _ Hnest
      (os_int_exit_raw_nesting_load sg state heap Hraw)) as Hcount.
    destruct state.(SchedState).(isRunning); [|discriminate].
    split; [reflexivity|]. subst nesting; exact Hrun.
Qed.

Lemma os_int_exit_masked_counter_raw_post : forall sg state heap,
  UCOS2_raw_rep sg state heap ->
  exists final,
    os_int_exit_masked_counter_fragment sg heap state.(SchedState).(isRunning) final /\
    UCOS2_raw_rep sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) final.
Proof.
  intros sg state heap Hraw.
  pose proof (os_int_exit_raw_running_load sg state heap Hraw) as Hread.
  destruct state.(SchedState).(isRunning) eqn:Hrunning.
  - destruct (os_int_exit_counter_heap_raw_post sg true state heap Hraw)
      as [final [Hrun Hpost]].
    exists final; split; [|exact Hpost].
    eapply OsIntExitMaskedActive; [exact Hread|eapply os_int_exit_raw_nesting_load; exact Hraw|exact Hrun].
  - exists heap; split; [constructor; exact Hread|].
    unfold os_int_exit_counter_state, interrupt_exit_state; rewrite replace_IntrS_put_back; exact Hraw.
Qed.

(** Preservation for an ACTUAL supplied final heap, not just existence of
    a convenient new heap. Both old selected and joint-feature validity
    are unchanged by an interrupt-counter-only update. *)
Lemma os_int_exit_masked_counter_raw_preservation : forall sg state before observed after,
  UCOS2_raw_rep sg state before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  UCOS2_raw_rep sg (os_int_exit_counter_state observed state) after.
Proof.
  intros sg state before observed after Hraw Hsource.
  destruct (os_int_exit_masked_counter_observation sg state before observed after Hraw Hsource)
    as [_ Hrun].
  eapply os_int_exit_counter_heap_raw_preservation; eassumption.
Qed.

Lemma os_int_exit_masked_counter_preserves_inv : forall sg state before observed after,
  UCOS2_inv sg state before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  UCOS2_inv sg (os_int_exit_counter_state observed state) after.
Proof.
  intros sg state before observed after [Hvalid Hraw] Hsource.
  split; [exact Hvalid|eapply os_int_exit_masked_counter_raw_preservation; eassumption].
Qed.

Lemma os_int_exit_masked_counter_preserves_full_inv : forall sg state before observed after,
  UCOS2_full_inv sg state before ->
  os_int_exit_masked_counter_fragment sg before observed after ->
  UCOS2_full_inv sg (os_int_exit_counter_state observed state) after.
Proof.
  intros sg state before observed after [Hvalid Hraw] Hsource.
  split; [exact Hvalid|eapply os_int_exit_masked_counter_raw_preservation; eassumption].
Qed.

Lemma os_int_exit_masked_counter_fragment_frame : forall sg before observed after frame whole,
  os_int_exit_masked_counter_fragment sg before observed after ->
  join before frame whole ->
  exists final, os_int_exit_masked_counter_fragment sg whole observed final /\ join after frame final.
Proof.
  intros sg before observed after frame whole Hsource Hjoin.
  destruct Hsource as [heap Hread|heap nesting final Hread Hnest Hrun].
  - exists whole; split; [constructor; eapply uchar_load_frame; eassumption|exact Hjoin].
  - destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin) as [result [Hwhole Hfinal]].
    exists result; split; [|exact Hfinal].
    eapply OsIntExitMaskedActive;
      [eapply uchar_load_frame; eassumption|eapply uchar_load_frame; eassumption|exact Hwhole].
Qed.

(** The following reads preserve the C short-circuit order: no counter or
    lock read on the inactive path, and no lock read when the post-decrement
    nesting value is nonzero. Scheduling paths are NOT excluded from the
    general OSIntExit model; they are simply outside this fragment. *)
Inductive os_int_exit_masked_no_schedule_fragment (sg : StableGlobVars)
  : model -> model -> Prop :=
| OsIntExitMaskedNoRunning : forall before after,
    os_int_exit_masked_counter_fragment sg before false after ->
    os_int_exit_masked_no_schedule_fragment sg before after
| OsIntExitMaskedStillNested : forall before after nesting,
    os_int_exit_masked_counter_fragment sg before true after ->
    uchar_load sg.(g_OSIntNesting) nesting after -> nesting <> 0 ->
    os_int_exit_masked_no_schedule_fragment sg before after
| OsIntExitMaskedLocked : forall before after locks,
    os_int_exit_masked_counter_fragment sg before true after ->
    uchar_load sg.(g_OSIntNesting) 0 after ->
    uchar_load sg.(g_OSLockNesting) locks after -> locks <> 0 ->
    os_int_exit_masked_no_schedule_fragment sg before after.

Lemma os_int_exit_masked_no_schedule_raw_post : forall sg state heap,
  UCOS2_raw_rep sg state heap ->
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    kernel_heap_execution (os_int_exit_counter_heap_writes sg state.(SchedState).(isRunning) state) heap final /\
    UCOS2_raw_rep sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) final.
Proof.
  intros sg state heap Hraw Hnoschedule.
  destruct (os_int_exit_masked_counter_raw_post sg state heap Hraw) as [final [Hsource Hpost]].
  destruct (os_int_exit_masked_counter_observation sg state heap _ final Hraw Hsource) as [_ Hrun].
  exists final; split; [|split; assumption].
  destruct state.(SchedState).(isRunning) eqn:Hrunning.
  - pose proof (os_int_exit_raw_nesting_load sg _ final Hpost) as Hnest.
    pose proof (os_int_exit_raw_lock_load sg _ final Hpost) as Hlock.
    set (nesting := (interrupt_exit_state true state.(IntrState)).(intNesting)) in *.
    change (uchar_load sg.(g_OSIntNesting) nesting final) in Hnest.
    destruct (Z.eq_dec nesting 0) as [Hzero|Hnonzero].
    + eapply OsIntExitMaskedLocked; [exact Hsource|rewrite <- Hzero; exact Hnest|exact Hlock|].
      intro HzeroLock.
      unfold interrupt_exit_requests_schedule in Hnoschedule.
      change ((Z.eqb nesting 0 && Z.eqb state.(IntrState).(lockNesting) 0)%bool = false) in Hnoschedule.
      assert (Hlocks : (interrupt_exit_state true state.(IntrState)).(lockNesting) = state.(IntrState).(lockNesting)).
      { unfold interrupt_exit_state; destruct (0 <? state.(IntrState).(intNesting)); reflexivity. }
      change ((interrupt_exit_state true state.(IntrState)).(lockNesting) = 0) in HzeroLock.
      rewrite Hlocks in HzeroLock; rewrite Hzero, HzeroLock in Hnoschedule; discriminate.
    + eapply OsIntExitMaskedStillNested; eassumption.
  - apply OsIntExitMaskedNoRunning; exact Hsource.
Qed.

Lemma os_int_exit_masked_no_schedule_fragment_frame : forall sg before after frame whole,
  os_int_exit_masked_no_schedule_fragment sg before after -> join before frame whole ->
  exists final, os_int_exit_masked_no_schedule_fragment sg whole final /\ join after frame final.
Proof.
  intros sg before after frame whole Hsource Hjoin.
  destruct Hsource as [before after Hcounter|before after nesting Hcounter Hnest Hnonzero|
    before after locks Hcounter Hnest Hlock Hnonzero];
    destruct (os_int_exit_masked_counter_fragment_frame sg _ _ _ _ _ Hcounter Hjoin)
      as [final [Hsource Hafter]]; exists final; split; try exact Hafter.
  - apply OsIntExitMaskedNoRunning; exact Hsource.
  - eapply OsIntExitMaskedStillNested;
      [exact Hsource|eapply uchar_load_frame; eassumption|exact Hnonzero].
  - eapply OsIntExitMaskedLocked;
      [exact Hsource|eapply uchar_load_frame; eassumption|
       eapply uchar_load_frame; eassumption|exact Hnonzero].
Qed.

(** A concrete whole-heap producer retaining the SAME disjoint caller's
    resources. In a wrapper application [frame] can own the existing CPU,
    handler-stack and linear continuation resources; none is manufactured
    from a pure descriptor. This proves the masked memory segment only. *)
Lemma os_int_exit_masked_no_schedule_frame_post : forall sg state (frame : Assertion) heap,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (UCOS2_inv sg state ** frame) heap ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) final.
Proof.
  intros sg state frame heap Hnoschedule [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  destruct (os_int_exit_masked_no_schedule_raw_post sg state owned Hraw Hnoschedule)
    as [after [Hsource [Hrun Hpost]]].
  destruct (os_int_exit_masked_no_schedule_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]. split; [split; assumption|exact Hframe].
Qed.

Lemma os_int_exit_masked_no_schedule_full_frame_post : forall sg state (frame : Assertion) heap,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (UCOS2_full_inv sg state ** frame) heap ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    (UCOS2_full_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) final.
Proof.
  intros sg state frame heap Hnoschedule [owned [rest [Hjoin [[Hvalid Hraw] Hframe]]]].
  destruct (os_int_exit_masked_no_schedule_raw_post sg state owned Hraw Hnoschedule)
    as [after [Hsource [Hrun Hpost]]].
  destruct (os_int_exit_masked_no_schedule_fragment_frame sg owned after rest heap Hsource Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, rest; split; [exact Hfinal|]. split; [split; assumption|exact Hframe].
Qed.

(** Consumer of the real first-level entry resource bundle, at the masked
    cut after the handler. The intervening handler must supply this actual
    cut; this lemma does not assume it is identical to the entry snapshot.
    The OSRunning read chooses the current branch, and the actual counter
    write retains the same saved bytes and original return escrow. *)
Lemma armv7a_irq_no_schedule_heap_post : forall external platform port sg context state heap,
  os_int_exit_saved_exception_binding context state ->
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (UCOS2_inv sg state ** armv7a_irq_handler_frame external platform port context) heap ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    os_int_exit_saved_exception_binding context
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) /\
    (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      armv7a_irq_handler_frame external platform port context) final.
Proof.
  intros external platform port sg context state heap Hsaved Hnoschedule Hheap.
  destruct (os_int_exit_masked_no_schedule_frame_post sg state _ heap Hnoschedule Hheap)
    as [final [Hsource Hpost]].
  exists final; split; [exact Hsource|]. split; [exact Hsaved|exact Hpost].
Qed.
