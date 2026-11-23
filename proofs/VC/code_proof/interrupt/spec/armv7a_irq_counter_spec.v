Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_execution.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** ARMv7-A/GNU/os_cpu_a_vfp-none.S:478-482 increments the byte directly;
    it does NOT call OSIntEnter.  ADD followed by STRB has the effect below,
    including wrapping at 255.  The separate documented nesting protocol
    rules out that wrap for a well-nested execution, not for the definition
    of the instruction effect.  IRQ/FIQ are already masked at this cut.

    These are proofs about the explicit memory-effect contract for that
    assembly segment, not an ARM instruction-semantics/refinement proof.
    Stack saves, CPU ownership and dispatch/return remain separate. *)
Definition armv7a_irq_entry_counter_state (entry : UCOS2_Verify_State)
  : UCOS2_Verify_State :=
  if entry.(SchedState).(isRunning) then
    replace_IntrS
      {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
         lockNesting := entry.(IntrState).(lockNesting) |} entry
  else entry.

Definition armv7a_irq_entry_counter_heap_writes (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) : list (Mem.addr * Mem.byte) :=
  if entry.(SchedState).(isRunning) then
    [(sg.(g_OSIntNesting), (entry.(IntrState).(intNesting) + 1) mod 256)]
  else [].

Lemma armv7a_irq_entry_counter_heap_raw_post : forall sg entry heap,
  UCOS2_raw_rep sg entry heap ->
  exists final,
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg entry) heap final /\
    UCOS2_raw_rep sg (armv7a_irq_entry_counter_state entry) final.
Proof.
  intros sg entry heap Hraw.
  unfold armv7a_irq_entry_counter_heap_writes, armv7a_irq_entry_counter_state.
  destruct entry.(SchedState).(isRunning) eqn:Hrunning.
  - assert (Hsplit : UCOS2_raw_rep sg entry |--
      sg.(g_OSIntNesting) # UChar |-> entry.(IntrState).(intNesting) **
      (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
       UCOS2_raw_rep_missing_interrupt sg entry)).
    { rewrite (UCOS2_raw_rep_split_module sg entry InterruptModule).
      cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state; entailer!. }
    assert (Hbyte : 0 <= (entry.(IntrState).(intNesting) + 1) mod 256 < 256)
      by (apply Z.mod_pos_bound; lia).
    destruct (kernel_heap_framed_uchar_store _ _ _ _ _ Hbyte (Hsplit heap Hraw))
      as [final [Hrun Hpost]].
    exists final; split; [exact Hrun|].
    assert (Hmerge :
      sg.(g_OSIntNesting) # UChar |-> ((entry.(IntrState).(intNesting) + 1) mod 256) **
      (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
       UCOS2_raw_rep_missing_interrupt sg entry) |--
      UCOS2_raw_rep sg (replace_IntrS
        {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
           lockNesting := entry.(IntrState).(lockNesting) |} entry)).
    { rewrite (UCOS2_raw_rep_split_module sg _ InterruptModule).
      change (sg.(g_OSIntNesting) # UChar |-> ((entry.(IntrState).(intNesting) + 1) mod 256) **
        (sg.(g_OSLockNesting) # UChar |-> entry.(IntrState).(lockNesting) **
         UCOS2_raw_rep_missing_interrupt sg entry) |--
        interrupt_inv sg
          {| intNesting := (entry.(IntrState).(intNesting) + 1) mod 256;
             lockNesting := entry.(IntrState).(lockNesting) |} **
        UCOS2_raw_rep_missing_interrupt sg entry).
      eapply derivable1_trans.
      2: { apply derivable1_sepcon_mono; [apply interrupt_inv_merge_counters|reflexivity]. }
      unfold store_int_state; cbn; entailer!. }
    exact (Hmerge final Hpost).
  - exists heap; split; [split; [constructor|split; reflexivity]|exact Hraw].
Qed.

Lemma armv7a_irq_entry_counter_heap_raw_preservation : forall sg entry heap final,
  UCOS2_raw_rep sg entry heap ->
  kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg entry) heap final ->
  UCOS2_raw_rep sg (armv7a_irq_entry_counter_state entry) final.
Proof.
  intros sg entry heap final Hraw Hactual.
  destruct (armv7a_irq_entry_counter_heap_raw_post sg entry heap Hraw)
    as [produced [Hrun Hpost]].
  assert (produced = final) by
    (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Lemma armv7a_irq_entry_counter_eq_c_entry : forall entry,
  (entry.(SchedState).(isRunning) = true -> 0 <= entry.(IntrState).(intNesting) < 255) ->
  armv7a_irq_entry_counter_state entry = os_int_enter_state entry.
Proof.
  intros entry Hbound; unfold armv7a_irq_entry_counter_state, os_int_enter_state,
    interrupt_enter_state.
  destruct entry.(SchedState).(isRunning) eqn:Hrunning.
  - specialize (Hbound eq_refl).
    assert (Hlt : (entry.(IntrState).(intNesting) <? 255) = true)
      by (apply Z.ltb_lt; lia).
    rewrite Hlt, Z.mod_small by lia; reflexivity.
  - symmetry; apply replace_IntrS_put_back.
Qed.

(** A concrete consumer of the C/port equivalence: the existing source
    control rule and full representation describe the SAME actual heap
    after this port effect.  The depth bound comes from the documented
    paired-entry protocol.  It is not inferred from an arbitrary token. *)
Lemma armv7a_irq_entry_control_heap_post : forall sg handler context entry heap,
  UCOS2_full_inv sg entry heap ->
  kernel_interrupt_nesting_agrees entry.(SchedState).(isRunning) context entry.(IntrState) ->
  (entry.(SchedState).(isRunning) = true -> (kernel_interrupt_depth context < 255)%nat) ->
  exists final,
    kernel_control_step (KernelEnterInterrupt handler entry.(SchedState).(isRunning))
      context entry.(IntrState) (KernelInterrupt handler context)
      (armv7a_irq_entry_counter_state entry).(IntrState) false /\
    kernel_heap_execution (armv7a_irq_entry_counter_heap_writes sg entry) heap final /\
    UCOS2_full_inv sg (armv7a_irq_entry_counter_state entry) final.
Proof.
  intros sg handler context entry heap [Hvalid Hraw] Hagrees Hdepth.
  assert (Heq : armv7a_irq_entry_counter_state entry = os_int_enter_state entry).
  { apply armv7a_irq_entry_counter_eq_c_entry; intro Hrunning.
    specialize (Hagrees Hrunning); specialize (Hdepth Hrunning); lia. }
  destruct (armv7a_irq_entry_counter_heap_raw_post sg entry heap Hraw)
    as [final [Hrun Hpost]].
  exists final; split.
  - rewrite Heq; constructor.
  - split; [exact Hrun|]. split; [rewrite Heq; exact Hvalid|exact Hpost].
Qed.
