Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This caller already owns the open ISR region. Nested Save/Restore only
    exchange their approved platform tokens; the inside and kernel owners
    remain physical frames of those calls. *)
Definition time_tick_sched_owned platform critical sg invocation origin region_entry
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin 192 **
  critical_region_inside critical sg invocation region_entry **
  UCOS2_inv sg state ** unmap_table_rep sg.

Definition time_tick_sched_interrupt_frame sg (state : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSLockNesting) # UChar |-> os_sched_locks state **
  UCOS2_raw_rep_missing_interrupt sg state.

Lemma time_tick_sched_split_interrupt : forall sg state,
  UCOS2_inv sg state |--
  coq_prop (UCOS2_state_inv sg state /\ 0 <= os_sched_ints state <= 255) &&
  (sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
    time_tick_sched_interrupt_frame sg state).
Proof.
  intros; rewrite UCOS2_inv_split_interrupt.
  unfold interrupt_inv, store_int_state, os_sched_ints, os_sched_locks,
    time_tick_sched_interrupt_frame.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) state.(IntrState).(intNesting)).
  entailer!.
Qed.

Lemma time_tick_sched_merge_interrupt : forall sg state,
  UCOS2_state_inv sg state ->
  sg.(g_OSIntNesting) # UChar |-> os_sched_ints state **
    time_tick_sched_interrupt_frame sg state |-- UCOS2_inv sg state.
Proof.
  intros sg state Hvalid; rewrite UCOS2_inv_split_interrupt.
  unfold time_tick_sched_interrupt_frame, os_sched_ints, os_sched_locks.
  pose proof (interrupt_inv_merge_counters sg state.(IntrState)) as Hmerge.
  unfold store_int_state in Hmerge; sep_apply Hmerge.
  entailer!.
Qed.
