Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSIntExit's counter prefix, Source/os_core.c:701-706.  On the
    true branch entry is AFTER the real Save; observed is the outer
    OSRunning read, not a silently refreshed observation.  The endpoint
    is before scheduler preparation, Restore, and exception return.
    Their resources and effects are not supplied by this memory lemma. *)
Definition os_int_exit_counter_state (observed : bool)
  (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_IntrS (interrupt_exit_state observed entry.(IntrState)) entry.

Definition os_int_exit_counter_heap_writes (sg : StableGlobVars)
  (observed : bool) (entry : UCOS2_Verify_State) : list (Mem.addr * Mem.byte) :=
  if observed then
    if 0 <? entry.(IntrState).(intNesting) then
      [(sg.(g_OSIntNesting), entry.(IntrState).(intNesting) - 1)]
    else []
  else [].

Lemma os_int_exit_counter_heap_raw_post : forall sg observed entry heap,
  UCOS2_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final /\
    UCOS2_raw_rep sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg [] entry heap Hraw; unfold os_int_exit_counter_heap_writes.
  - destruct (0 <? entry.(IntrState).(intNesting)) eqn:Hpositive.
    + assert (Hsplit : UCOS2_raw_rep sg entry |--
        (sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
         (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
          UCOS2_raw_rep_missing_interrupt sg entry))).
      { rewrite (UCOS2_raw_rep_split_module sg entry InterruptModule).
        cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!. }
      pose proof (Hsplit heap Hraw) as Hcells.
      destruct Hcells as [cell [rest [Hjoin [Hcell Hrest]]]].
      pose proof (store_uchar_range _ _ cell Hcell) as Hrange.
      change (0 <= entry.(IntrState).(intNesting) <= 255) in Hrange.
      assert (Hstored : 0 <= entry.(IntrState).(intNesting) - 1 < 256)
        by (apply Z.ltb_lt in Hpositive; lia).
      destruct (kernel_heap_framed_uchar_store _ _ _ _ _ Hstored (Hsplit heap Hraw))
        as [final [Hrun Hfinal]].
      exists final; split; [exact Hrun|].
      assert (Hmerge :
        sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) - 1) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_raw_rep_missing_interrupt sg entry) |--
        UCOS2_raw_rep sg (os_int_exit_counter_state true entry)).
      { unfold os_int_exit_counter_state.
        rewrite (UCOS2_raw_rep_split_module sg _ InterruptModule).
        change (sg.(g_OSIntNesting) # UChar |-> (entry.(IntrState).(intNesting) - 1) **
          (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
           UCOS2_raw_rep_missing_interrupt sg entry) |--
          interrupt_inv sg (interrupt_exit_state true entry.(IntrState)) **
          UCOS2_raw_rep_missing_interrupt sg entry).
        unfold interrupt_exit_state; rewrite Hpositive.
        eapply derivable1_trans.
        2: { apply derivable1_sepcon_mono; [apply interrupt_inv_merge_counters|reflexivity]. }
        unfold store_int_state; cbn; entailer!. }
      exact (Hmerge final Hfinal).
    + exists heap; split; [split; [constructor|split; reflexivity]|].
      unfold os_int_exit_counter_state, interrupt_exit_state; rewrite Hpositive.
      rewrite replace_IntrS_put_back; exact Hraw.
  - exists heap; split; [split; [constructor|split; reflexivity]|].
    unfold os_int_exit_counter_state, interrupt_exit_state.
    rewrite replace_IntrS_put_back; exact Hraw.
Qed.

Lemma os_int_exit_counter_heap_raw_preservation : forall sg observed entry heap final,
  UCOS2_raw_rep sg entry heap ->
  kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final ->
  UCOS2_raw_rep sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg observed entry heap final Hraw Hrun.
  destruct (os_int_exit_counter_heap_raw_post sg observed entry heap Hraw)
    as [produced [Hproduced Hpost]].
  assert (produced = final) by
    (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Lemma os_int_exit_counter_heap_full_profile_post : forall sg observed entry heap,
  UCOS2_full_inv sg entry heap ->
  exists final,
    kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final /\
    UCOS2_full_inv sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg observed entry heap [Hvalid Hraw].
  destruct (os_int_exit_counter_heap_raw_post sg observed entry heap Hraw)
    as [final [Hrun Hpost]].
  exists final; split; [exact Hrun|]; split; assumption.
Qed.

(** Coupling to the EXISTING source-control model.  This binds the same
    before/after counter state to real memory, not a second arbitrary
    state trace.  KernelControlExit stops before dispatch/exception return;
    the context descriptor below is not an owned CPU continuation. *)
Lemma os_int_exit_control_heap_post : forall sg observed handler context entry heap,
  UCOS2_full_inv sg entry heap ->
  exists final,
    kernel_control_step (KernelExitInterrupt observed)
      (KernelInterrupt handler context) entry.(IntrState) context
      (os_int_exit_counter_state observed entry).(IntrState)
      (interrupt_exit_requests_schedule observed entry.(IntrState)) /\
    kernel_heap_execution (os_int_exit_counter_heap_writes sg observed entry) heap final /\
    UCOS2_full_inv sg (os_int_exit_counter_state observed entry) final.
Proof.
  intros sg observed handler context entry heap Hinv.
  destruct (os_int_exit_counter_heap_full_profile_post sg observed entry heap Hinv)
    as [final [Hrun Hpost]].
  exists final; split; [constructor|]; split; assumption.
Qed.

Lemma os_int_enter_control_heap_post : forall sg handler context entry heap,
  UCOS2_full_inv sg entry heap ->
  exists final,
    kernel_control_step (KernelEnterInterrupt handler entry.(SchedState).(isRunning))
      context entry.(IntrState) (KernelInterrupt handler context)
      (os_int_enter_state entry).(IntrState) false /\
    kernel_heap_execution (os_int_enter_heap_writes sg entry) heap final /\
    UCOS2_full_inv sg (os_int_enter_state entry) final.
Proof.
  intros sg handler context entry heap Hinv.
  destruct (os_int_enter_source_heap_full_profile_post sg entry heap Hinv)
    as [final [Hrun Hpost]].
  exists final; split; [constructor|]; split; assumption.
Qed.
