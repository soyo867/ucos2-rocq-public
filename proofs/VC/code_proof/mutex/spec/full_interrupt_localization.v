Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A complete-invariant residual for the one concrete byte updated by
    OSIntNesting.  The residual intentionally retains the complete current
    Task/Scheduler/Event/Queue/Flag/Memory/Timer/Statistics/Control/Names
    owners through [UCOS2_raw_rep_missing_interrupt]; it is not the historical
    verification slice and does not project away any module state. *)
Definition UCOS2_inv_without_os_int_nesting
  (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  UCOS2_raw_rep_missing_interrupt sg s.

Definition UCOS2_inv_os_int_nesting_cell
  (sg : StableGlobVars) (intr : Glob_InterruptAbstractState) : Assertion :=
  sg.(g_OSIntNesting) # UChar |-> intr.(intNesting).

Lemma interrupt_inv_split_os_int_nesting_cell : forall sg s,
  interrupt_inv sg s |--
    UCOS2_inv_os_int_nesting_cell sg s **
    interrupt_inv_no_int_nesting sg s.
Proof.
  intros sg s.
  unfold UCOS2_inv_os_int_nesting_cell,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  entailer!.
Qed.

Lemma UCOS2_inv_split_os_int_nesting : forall sg s,
  UCOS2_inv sg s --||--
    coq_prop (UCOS2_state_inv sg s) &&
    (UCOS2_inv_os_int_nesting_cell sg s.(IntrState) **
     UCOS2_inv_without_os_int_nesting sg s).
Proof.
  intros sg s.
  unfold UCOS2_inv, UCOS2_inv_without_os_int_nesting.
  rewrite (UCOS2_inv_split_interrupt sg s).
  unfold UCOS2_inv_os_int_nesting_cell,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  split; entailer!.
Qed.

Lemma interrupt_inv_merge_os_int_nesting_cell : forall sg old counters,
  interrupt_in_range counters ->
  counters.(lockNesting) = old.(lockNesting) ->
  UCOS2_inv_os_int_nesting_cell sg counters **
  interrupt_inv_no_int_nesting sg old |--
  interrupt_inv sg counters.
Proof.
  intros sg old counters Hrange Hlock.
  unfold UCOS2_inv_os_int_nesting_cell,
    interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  rewrite Hlock.
  entailer!.
Qed.

Lemma UCOS2_inv_merge_updated_os_int_nesting : forall sg s counters,
  UCOS2_state_inv sg s ->
  interrupt_in_range counters ->
  counters.(lockNesting) = s.(IntrState).(lockNesting) ->
  UCOS2_inv_os_int_nesting_cell sg counters **
  UCOS2_inv_without_os_int_nesting sg s |--
  UCOS2_inv sg (replace_IntrS counters s).
Proof.
  intros sg s counters Hvalid Hrange Hlock.
  unfold UCOS2_inv_without_os_int_nesting, UCOS2_inv.
  rewrite (UCOS2_inv_split_interrupt sg (replace_IntrS counters s)).
  rewrite UCOS2_validity_replace_interrupt_eq.
  rewrite UCOS2_raw_rep_missing_interrupt_replace_interrupt_eq.
  simpl.
  sep_apply_l_atomic (interrupt_inv_merge_os_int_nesting_cell
    sg s.(IntrState) counters Hrange Hlock).
  entailer!.
Qed.
