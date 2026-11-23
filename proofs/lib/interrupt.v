Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 2 Task 2.1:InterruptAbstractState 不变式                      *)
(* ================================================================== *)
(* InterruptAbstractState / Glob_InterruptAbstractState / replace_IntrS *)
(* 已在 ucos2_verify_state_def.v 中定义                                 *)

Definition interrupt_in_range (s : InterruptAbstractState) : Prop :=
  0 <= s.(intNesting) /\ 0 <= s.(lockNesting).

Definition store_int_state (sg : StableGlobVars) (s : InterruptAbstractState) : Assertion :=
  (sg.(g_OSIntNesting) # UChar |-> s.(intNesting)) **
  (sg.(g_OSLockNesting) # UChar |-> s.(lockNesting)).

Definition interrupt_inv (sg : StableGlobVars) (s : InterruptAbstractState) : Assertion :=
  coq_prop (interrupt_in_range s) && store_int_state sg s.

Definition interrupt_inv_no_int_nesting
  (sg : StableGlobVars) (s : InterruptAbstractState) : Assertion :=
  coq_prop (interrupt_in_range s) &&
  (sg.(g_OSLockNesting) # UChar |-> s.(lockNesting)).

Definition interrupt_inv_no_nesting_cells
  (s : InterruptAbstractState) : Assertion :=
  coq_prop (interrupt_in_range s).

(* ================================================================== *)
(* Phase 2 Task 2.2:atomic_enter_critical / atomic_exit_critical      *)
(* ================================================================== *)

Definition OS_CPU_SR : Type := Z.

(** [OS_CPU_SR] is the value-level token returned by the method-3
    [OS_CPU_SR_Save] primitive.  Its concrete value is architecture-owned,
    but the selected Arch32 profile guarantees that it is an unsigned
    32-bit value. *)
Definition valid_os_cpu_sr (cpu_sr : OS_CPU_SR) : Prop :=
  0 <= cpu_sr < 4294967296.

(** Mathematical specialization for a maskable, privileged A32 platform.
    These functions are NOT unconditional ARM instruction semantics.  CPSID
    and MSR have privilege/NMFI/security/mode constraints; ordinary MSR does
    not write T.  The source-facing relations below expose the specialization
    conditions.  Instruction refinement, MRS execution-state observations and
    DSB ordering remain architecture obligations; no ISA axiom is added here. *)
Definition armv7a_cpsr_save_direct (cpsr : Z) : OS_CPU_SR * Z :=
  (cpsr, Z.lor cpsr 192).

Definition armv7a_cpsr_restore_direct (current saved : Z) : Z :=
  Z.lor (Z.land current (Z.lnot 223)) (Z.land saved 223).

Lemma armv7a_cpsr_save_returns_exact_word : forall cpsr,
  fst (armv7a_cpsr_save_direct cpsr) = cpsr.
Proof. reflexivity. Qed.

Lemma armv7a_cpsr_save_masks_irq_fiq : forall cpsr,
  Z.testbit (snd (armv7a_cpsr_save_direct cpsr)) 7 = true /\
  Z.testbit (snd (armv7a_cpsr_save_direct cpsr)) 6 = true.
Proof.
  intro cpsr; change (Z.testbit (Z.lor cpsr 192) 7 = true /\
    Z.testbit (Z.lor cpsr 192) 6 = true).
  rewrite !Z.lor_spec.
  change (orb (Z.testbit cpsr 7) true = true /\
    orb (Z.testbit cpsr 6) true = true).
  rewrite !Bool.orb_true_r; split; reflexivity.
Qed.

Record A32InterruptContext : Type := {
  a32Privileged : bool;
  a32NMFI : bool;
  a32FIQWriteAllowed : bool;
  a32Mode : Z;
}.

Definition a32_maskable_context
  (context : A32InterruptContext) (cpsr : Z) : Prop :=
  a32Privileged context = true /\
  a32NMFI context = false /\
  a32FIQWriteAllowed context = true /\
  valid_os_cpu_sr cpsr /\
  Z.testbit cpsr 5 = false /\ Z.testbit cpsr 24 = false /\
  Z.land cpsr 100727808 = 0 /\ (* A32 ITSTATE[7:0], CPSR[26:25,15:10]. *)
  Z.land cpsr 31 = a32Mode context /\
  In (a32Mode context) (17 :: 18 :: 19 :: 22 :: 23 :: 26 :: 27 :: 31 :: nil).

Definition a32_sr_save_source_specialization
  (context : A32InterruptContext) (before saved after : Z) : Prop :=
  a32_maskable_context context before /\
  saved = fst (armv7a_cpsr_save_direct before) /\
  after = snd (armv7a_cpsr_save_direct before).

Definition a32_sr_restore_source_specialization
  (context : A32InterruptContext) (current saved after : Z) : Prop :=
  a32_maskable_context context current /\
  a32_maskable_context context saved /\
  after = armv7a_cpsr_restore_direct current saved.

(** [after] in the two specializations is the internal CPSID/MSR stage,
    not the complete C call-return state.  The following BX LR can switch
    execution state when returning to a Thumb continuation.  A source-level
    return theorem must additionally bind LR, the continuation and its stack;
    these value equations do not choose an ARM-only caller or an FPU variant. *)

Lemma armv7a_cpsr_restore_preserves_t : forall current saved,
  Z.testbit (armv7a_cpsr_restore_direct current saved) 5 = Z.testbit current 5.
Proof.
  intros; unfold armv7a_cpsr_restore_direct.
  rewrite !Z.lor_spec, !Z.land_spec, !Z.lnot_spec by lia.
  change (orb (andb (Z.testbit current 5) true)
    (andb (Z.testbit saved 5) false) =
    Z.testbit current 5).
  rewrite Bool.andb_true_r, Bool.andb_false_r, Bool.orb_false_r; reflexivity.
Qed.

Lemma armv7a_cpsr_restore_irq_fiq_exact : forall current saved,
  Z.testbit (armv7a_cpsr_restore_direct current saved) 7 = Z.testbit saved 7 /\
  Z.testbit (armv7a_cpsr_restore_direct current saved) 6 = Z.testbit saved 6.
Proof.
  intros; unfold armv7a_cpsr_restore_direct.
  rewrite !Z.lor_spec, !Z.land_spec, !Z.lnot_spec by lia.
  change (orb (andb (Z.testbit current 7) false)
    (andb (Z.testbit saved 7) true) = Z.testbit saved 7 /\
    orb (andb (Z.testbit current 6) false)
    (andb (Z.testbit saved 6) true) = Z.testbit saved 6).
  rewrite !Bool.andb_false_r, !Bool.andb_true_r; split; reflexivity.
Qed.

Record InterruptSaveToken : Type := {
  savedCPSR : OS_CPU_SR;
  savedInvocation : nat;
  savedOrigin : TaskInvocationOrigin;
}.

(** Shared external CPU/return resources, indexed by the original
    invocation and IRQ/FIQ mask.  The logical critical-region protocol
    lives in [ucos2_verify_inv]; neither interface asserts an ARM/BSP
    implementation proof.  These declarations are shared by Task and IPC
    clients, not owned by the TCB initializer. *)
Record InterruptPlatformResources : Type := {
  interrupt_platform_running : nat -> TaskInvocationOrigin -> Z -> Assertion;
  interrupt_platform_saved : InterruptSaveToken -> Assertion;
}.

Definition armv7a_irq_fiq_mask (word : Z) : Z := Z.land word 192.

Definition interrupt_saved_value (mask saved : Z) : Prop :=
  valid_os_cpu_sr saved /\ armv7a_irq_fiq_mask saved = mask.

Definition save_token (saved : Z) (invocation : nat)
  (origin : TaskInvocationOrigin) : InterruptSaveToken :=
  {| savedCPSR := saved; savedInvocation := invocation;
     savedOrigin := origin |}.

Definition interrupt_token_for_invocation (st : UCOS2_Verify_State)
  (token : InterruptSaveToken) : Prop :=
  valid_os_cpu_sr token.(savedCPSR) /\
  st.(TskState).(taskLifecycle).(taskInvocations) token.(savedInvocation) =
    Some token.(savedOrigin) /\
  st.(TskState).(taskLifecycle).(taskRetiredInvocations) token.(savedInvocation) = false.

(** Producer-side ownership of the saved interrupt token.  Entering the
    critical section does not change the abstract OS state, while [cpu_sr]
    names the exact value returned to the caller. *)
Definition interrupt_saved_cpu_sr
  (entry critical_entry : UCOS2_Verify_State)
  (cpu_sr : OS_CPU_SR) : Prop :=
  crit_rel_no_os_state_change entry critical_entry /\
  valid_os_cpu_sr cpu_sr.

(** Consumer-side protocol for method-3 restore.  [supplied_cpu_sr] must be
    the very value named by the producer-side token; a merely well-typed but
    unrelated value is not sufficient. *)
Definition interrupt_restore_consumes_saved_cpu_sr
  (entry critical_entry : UCOS2_Verify_State)
  (saved_cpu_sr supplied_cpu_sr : OS_CPU_SR) : Prop :=
  interrupt_saved_cpu_sr entry critical_entry saved_cpu_sr /\
  supplied_cpu_sr = saved_cpu_sr.

Lemma interrupt_restore_consumes_saved_cpu_sr_self :
  forall entry critical_entry saved_cpu_sr,
    interrupt_saved_cpu_sr entry critical_entry saved_cpu_sr ->
    interrupt_restore_consumes_saved_cpu_sr
      entry critical_entry saved_cpu_sr saved_cpu_sr.
Proof.
  intros entry critical_entry saved_cpu_sr Hsaved.
  split; [exact Hsaved | reflexivity].
Qed.

Lemma interrupt_restore_consumes_saved_cpu_sr_exact :
  forall entry critical_entry saved_cpu_sr supplied_cpu_sr,
    interrupt_restore_consumes_saved_cpu_sr
      entry critical_entry saved_cpu_sr supplied_cpu_sr ->
    supplied_cpu_sr = saved_cpu_sr.
Proof.
  intros entry critical_entry saved_cpu_sr supplied_cpu_sr Hconsume.
  exact (proj2 Hconsume).
Qed.

Definition atomic_enter_critical
  : program (StableGlobVars * UCOS2_Verify_State) OS_CPU_SR :=
  fun '(sg1, lvs1) cpu_sr '(sg2, lvs2) =>
    sg1 = sg2 /\ interrupt_saved_cpu_sr lvs1 lvs2 cpu_sr.

Definition atomic_exit_critical (cpu_sr : OS_CPU_SR)
  : program (StableGlobVars * UCOS2_Verify_State) unit :=
  fun '(sg1, lvs1) (_ : unit) '(sg2, lvs2) =>
    sg1 = sg2 /\ lvs1 = lvs2 /\ valid_os_cpu_sr cpu_sr.

(** Round-trip wrapper used by call contracts that still carry the entry
    state and the producer token while the protected body may have changed
    the current OS state. *)
Definition atomic_exit_critical_with_saved
  (entry critical_entry : UCOS2_Verify_State)
  (saved_cpu_sr supplied_cpu_sr : OS_CPU_SR)
  : program (StableGlobVars * UCOS2_Verify_State) unit :=
  fun current (_ : unit) next =>
    interrupt_restore_consumes_saved_cpu_sr
      entry critical_entry saved_cpu_sr supplied_cpu_sr /\
    atomic_exit_critical supplied_cpu_sr current tt next.

(* ================================================================== *)
(* Source-exact interrupt and scheduler-lock nesting stages.            *)
(* ================================================================== *)

(** Source-level byte counters.  The older nonnegative predicate is kept
    as a consequence for existing spatial clients, not as a machine range. *)
Definition interrupt_counters_in_range (s : InterruptAbstractState) : Prop :=
  0 <= s.(intNesting) <= 255 /\ 0 <= s.(lockNesting) <= 255.

Lemma interrupt_counters_in_range_implies_interrupt_in_range : forall s,
  interrupt_counters_in_range s -> interrupt_in_range s.
Proof. intros s H; unfold interrupt_counters_in_range, interrupt_in_range in *; lia. Qed.

Lemma store_int_state_implies_counters_in_range : forall sg s,
  store_int_state sg s |-- coq_prop (interrupt_counters_in_range s).
Proof.
  intros; unfold store_int_state, interrupt_counters_in_range.
  sep_apply_l_atomic (store_uchar_range sg.(g_OSIntNesting) s.(intNesting)).
  sep_apply_l_atomic (store_uchar_range sg.(g_OSLockNesting) s.(lockNesting)).
  entailer!.
Qed.

(** The old nonnegative invariant is already implied by the two actual
    UChar cells.  Reuse this one reconstruction interface for all counter
    operations instead of adding a range premise or a per-API predicate. *)
Lemma interrupt_inv_merge_counters : forall sg s,
  store_int_state sg s |-- interrupt_inv sg s.
Proof.
  intros sg s; unfold interrupt_inv; apply _derivable1_andp_intros.
  - eapply derivable1_trans; [exact (store_int_state_implies_counters_in_range sg s)|].
    apply coq_prop_imply; apply interrupt_counters_in_range_implies_interrupt_in_range.
  - reflexivity.
Qed.

(** os_core.c: OSIntEnter, OSIntExit, OSSchedLock and OSSchedUnlock.
    Running and ISR tests are actual source guards, not validity assumptions.
    [running] is the source observation, not necessarily the running field
    of the later state at which the counters are read.  Function-specific
    observation/Save/Restore boundaries belong to the corresponding spec.
    Exit transformers stop before scheduler/cache/context-switch effects. *)
Definition interrupt_enter_state (running : bool) (s : InterruptAbstractState)
  : InterruptAbstractState :=
  if running then
    if s.(intNesting) <? 255 then
      {| intNesting := s.(intNesting) + 1; lockNesting := s.(lockNesting) |}
    else s
  else s.

Definition interrupt_exit_state (running : bool) (s : InterruptAbstractState)
  : InterruptAbstractState :=
  if running then
    if 0 <? s.(intNesting) then
      {| intNesting := s.(intNesting) - 1; lockNesting := s.(lockNesting) |}
    else s
  else s.

Definition sched_lock_state (running : bool) (s : InterruptAbstractState)
  : InterruptAbstractState :=
  if running then
    if s.(intNesting) =? 0 then
      if s.(lockNesting) <? 255 then
        {| intNesting := s.(intNesting); lockNesting := s.(lockNesting) + 1 |}
      else s
    else s
  else s.

Definition sched_unlock_state (running : bool) (s : InterruptAbstractState)
  : InterruptAbstractState :=
  if running then
    if s.(intNesting) =? 0 then
      if 0 <? s.(lockNesting) then
        {| intNesting := s.(intNesting); lockNesting := s.(lockNesting) - 1 |}
      else s
    else s
  else s.

Definition interrupt_exit_requests_schedule (running : bool)
  (s : InterruptAbstractState) : bool :=
  running && ((interrupt_exit_state running s).(intNesting) =? 0) &&
    (s.(lockNesting) =? 0).

Definition sched_unlock_requests_schedule (running : bool)
  (s : InterruptAbstractState) : bool :=
  running && (s.(intNesting) =? 0) && (s.(lockNesting) =? 1).

Lemma interrupt_enter_preserves_counters_in_range : forall running s,
  interrupt_counters_in_range s ->
  interrupt_counters_in_range (interrupt_enter_state running s).
Proof.
  intros [] [i l] H; unfold interrupt_enter_state, interrupt_counters_in_range in *;
    simpl in *; [destruct (i <? 255) eqn:E|]; simpl in *;
    try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma interrupt_exit_preserves_counters_in_range : forall running s,
  interrupt_counters_in_range s ->
  interrupt_counters_in_range (interrupt_exit_state running s).
Proof.
  intros [] [i l] H; unfold interrupt_exit_state, interrupt_counters_in_range in *;
    simpl in *; [destruct (0 <? i) eqn:E|]; simpl in *;
    try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
Qed.

Lemma sched_lock_preserves_counters_in_range : forall running s,
  interrupt_counters_in_range s ->
  interrupt_counters_in_range (sched_lock_state running s).
Proof.
  intros [] [i l] H; unfold sched_lock_state, interrupt_counters_in_range in *; simpl in *.
  - destruct (i =? 0); [destruct (l <? 255) eqn:E|]; simpl in *;
      try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
  - lia.
Qed.

Lemma sched_unlock_preserves_counters_in_range : forall running s,
  interrupt_counters_in_range s ->
  interrupt_counters_in_range (sched_unlock_state running s).
Proof.
  intros [] [i l] H; unfold sched_unlock_state, interrupt_counters_in_range in *; simpl in *.
  - destruct (i =? 0); [destruct (0 <? l) eqn:E|]; simpl in *;
      try apply Z.ltb_lt in E; try apply Z.ltb_ge in E; lia.
  - lia.
Qed.

Lemma interrupt_exit_requests_schedule_iff : forall running s,
  interrupt_exit_requests_schedule running s = true <->
  running = true /\ (interrupt_exit_state running s).(intNesting) = 0 /\
    s.(lockNesting) = 0.
Proof.
  intros; unfold interrupt_exit_requests_schedule.
  rewrite !Bool.andb_true_iff, !Z.eqb_eq; tauto.
Qed.

Lemma sched_unlock_requests_schedule_iff : forall running s,
  sched_unlock_requests_schedule running s = true <->
  running = true /\ s.(intNesting) = 0 /\ s.(lockNesting) = 1.
Proof.
  intros; unfold sched_unlock_requests_schedule.
  rewrite !Bool.andb_true_iff, !Z.eqb_eq; tauto.
Qed.

Lemma sched_lock_unlock_counters_eq : forall s,
  s.(intNesting) = 0 -> 0 <= s.(lockNesting) < 255 ->
  sched_unlock_state true (sched_lock_state true s) = s.
Proof.
  intros [i l] Hi Hl; simpl in *; subst i.
  unfold sched_lock_state, sched_unlock_state; simpl.
  rewrite (proj2 (Z.ltb_lt l 255) ltac:(lia)); simpl.
  rewrite (proj2 (Z.ltb_lt 0 (l + 1)) ltac:(lia)).
  f_equal; lia.
Qed.

Lemma sched_lock_unlock_saturated :
  sched_unlock_state true
    (sched_lock_state true {| intNesting := 0; lockNesting := 255 |}) =
    {| intNesting := 0; lockNesting := 254 |}.
Proof. reflexivity. Qed.

Lemma interrupt_enter_exit_counters_eq : forall s,
  0 <= s.(intNesting) < 255 ->
  interrupt_exit_state true (interrupt_enter_state true s) = s.
Proof.
  intros [i l] Hi; simpl in *.
  unfold interrupt_enter_state, interrupt_exit_state; simpl.
  rewrite (proj2 (Z.ltb_lt i 255) ltac:(lia)); simpl.
  rewrite (proj2 (Z.ltb_lt 0 (i + 1)) ltac:(lia)).
  f_equal; lia.
Qed.

Lemma interrupt_enter_exit_saturated :
  interrupt_exit_state true
    (interrupt_enter_state true {| intNesting := 255; lockNesting := 0 |}) =
    {| intNesting := 254; lockNesting := 0 |}.
Proof. reflexivity. Qed.

Lemma sched_unlock_zero_does_not_schedule :
  sched_unlock_state true {| intNesting := 0; lockNesting := 0 |} =
    {| intNesting := 0; lockNesting := 0 |} /\
  sched_unlock_requests_schedule true {| intNesting := 0; lockNesting := 0 |} = false.
Proof. split; reflexivity. Qed.

Lemma interrupt_exit_zero_requests_schedule :
  interrupt_exit_state true {| intNesting := 0; lockNesting := 0 |} =
    {| intNesting := 0; lockNesting := 0 |} /\
  interrupt_exit_requests_schedule true {| intNesting := 0; lockNesting := 0 |} = true.
Proof. split; reflexivity. Qed.
