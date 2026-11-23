Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual Source/os_core.c OSIntEnter store footprint, with the
    selected disabled trace macro.  Both no-write branches are retained.
    Its documented caller has already disabled interrupts; this lemma is
    the physical effect of that source segment, not an ARM entry proof. *)
Definition os_int_enter_heap_writes (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) : list (Mem.addr * Mem.byte) :=
  if entry.(SchedState).(isRunning) then
    if entry.(IntrState).(intNesting) <? 255 then
      [(sg.(g_OSIntNesting), entry.(IntrState).(intNesting) + 1)]
    else []
  else [].

Lemma os_int_enter_source_heap_raw_post : forall sg entry heap,
  UCOS2_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    UCOS2_raw_rep sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap Hraw.
  unfold os_int_enter_heap_writes.
  destruct entry.(SchedState).(isRunning) eqn:Hrunning.
  - destruct (entry.(IntrState).(intNesting) <? 255) eqn:Hbelow.
    + apply Z.ltb_lt in Hbelow.
      assert (Hsplit : UCOS2_raw_rep sg entry |--
        coq_prop (interrupt_in_range entry.(IntrState)) &&
        (sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
         (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
          UCOS2_raw_rep_missing_interrupt sg entry))).
      { rewrite (UCOS2_raw_rep_split_module sg entry InterruptModule).
        cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!. }
      destruct (Hsplit heap Hraw) as [Hrange Hcells].
      change (interrupt_in_range entry.(IntrState)) in Hrange.
      assert (Hstored : 0 <= entry.(IntrState).(intNesting) + 1 < 256)
        by (unfold interrupt_in_range in Hrange; lia).
      destruct (kernel_heap_framed_uchar_store _ _ _ _ _ Hstored Hcells)
        as [final [Hrun Hfinal]].
      exists final; split; [exact Hrun|].
      assert (Hmerge :
        sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) + 1) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_raw_rep_missing_interrupt sg entry) |--
        UCOS2_raw_rep sg (os_int_enter_state entry)).
      { unfold os_int_enter_state.
        rewrite (UCOS2_raw_rep_split_module sg _ InterruptModule).
        change (sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) + 1) **
          (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
           UCOS2_raw_rep_missing_interrupt sg entry) |--
          interrupt_inv sg
            (interrupt_enter_state entry.(SchedState).(isRunning) entry.(IntrState)) **
          UCOS2_raw_rep_missing_interrupt sg entry).
        unfold interrupt_enter_state; rewrite Hrunning.
        assert (Hlt : (entry.(IntrState).(intNesting) <? 255) = true)
          by (apply Z.ltb_lt; exact Hbelow).
        rewrite Hlt.
        eapply derivable1_trans.
        2: { apply derivable1_sepcon_mono; [apply interrupt_inv_merge_counters|reflexivity]. }
        unfold store_int_state; cbn; entailer!. }
      exact (Hmerge final Hfinal).
    + exists heap; split; [split; [constructor|split; reflexivity]|].
      unfold os_int_enter_state, interrupt_enter_state; rewrite Hrunning, Hbelow.
      rewrite replace_IntrS_put_back; exact Hraw.
  - exists heap; split; [split; [constructor|split; reflexivity]|].
    rewrite (os_int_enter_not_running_no_effect entry Hrunning).
    exact Hraw.
Qed.

(** The producer describes the actual after heap of the same write
    execution, not just a conveniently chosen valid existential state. *)
Lemma os_int_enter_source_heap_raw_preservation : forall sg entry heap final,
  UCOS2_raw_rep sg entry heap ->
  kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final ->
  UCOS2_raw_rep sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap final Hraw Hrun.
  destruct (os_int_enter_source_heap_raw_post sg entry heap Hraw)
    as [produced [Hproduced Hpost]].
  assert (produced = final) by
    (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

(** The memory producer is profile independent.  Pure endpoint validity
    is transported separately, so the same producer serves the retained
    64-byte profile and the joint Multi/Names/Profile representation. *)
Lemma os_int_enter_source_heap_post : forall sg entry heap,
  UCOS2_inv sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    UCOS2_inv sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap [Hvalid Hraw].
  destruct (os_int_enter_source_heap_raw_post sg entry heap Hraw)
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  split; [apply os_int_enter_preserves_validity; exact Hvalid|exact Hpost].
Qed.

Lemma os_int_enter_source_heap_full_profile_post : forall sg entry heap,
  UCOS2_full_inv sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    UCOS2_full_inv sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap [Hvalid Hraw].
  destruct (os_int_enter_source_heap_raw_post sg entry heap Hraw)
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|].
  split; [exact Hvalid|exact Hpost].
Qed.

Lemma os_int_enter_source_heap_full_profile_preservation : forall sg entry heap final,
  UCOS2_full_inv sg entry heap ->
  kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final ->
  UCOS2_full_inv sg (os_int_enter_state entry) final.
Proof.
  intros sg entry heap final [Hvalid Hraw] Hrun.
  split; [exact Hvalid|].
  eapply os_int_enter_source_heap_raw_preservation; eassumption.
Qed.

(** A real interrupt-source producer for the environment heap.  The
    private caller bytes remain separate while OSIntNesting changes in the
    shared heap.  No raw post-heap or post-invariant premise is supplied. *)
Lemma os_int_enter_source_heap_frames_private : forall sg entry (private : Assertion) heap,
  (UCOS2_inv sg entry ** private) heap ->
  exists final,
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    (UCOS2_inv sg (os_int_enter_state entry) ** private) final.
Proof.
  intros sg entry private heap [shared [local [Hjoin [Hinv Hprivate]]]].
  destruct (os_int_enter_source_heap_post sg entry shared Hinv)
    as [after [Hrun Hpost]].
  destruct (kernel_heap_execution_frame _ _ _ _ _ Hrun Hjoin)
    as [final [Hwhole Hfinal]].
  exists final; split; [exact Hwhole|].
  exists after, local; split; [exact Hfinal|]; split; assumption.
Qed.
