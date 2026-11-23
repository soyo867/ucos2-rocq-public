Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Local Open Scope Z_scope.

(** A source continuation, NOT a new field of any C object or kernel
    abstract state. TaskInvocationOrigin remains the allocation/caller
    origin. An interrupt wraps the suspended continuation; it does not
    become that task just because OSIntNesting happens to be zero.
    Handler labels need not be distinct (the same handler can nest).

    Construction of this descriptor grants no heap or platform token.
    A call-site binding must connect it to the actual saved continuation.
    The approved architecture resources still own the real stacks/masks. *)
Inductive KernelExecutionContext : Type :=
| KernelCaller (invocation : nat) (origin : TaskInvocationOrigin)
| KernelInterrupt (handler : nat) (interrupted : KernelExecutionContext).

Fixpoint kernel_suspended_caller (context : KernelExecutionContext)
  : nat * TaskInvocationOrigin :=
  match context with
  | KernelCaller invocation origin => (invocation, origin)
  | KernelInterrupt _ interrupted => kernel_suspended_caller interrupted
  end.

Fixpoint kernel_interrupt_depth (context : KernelExecutionContext) : nat :=
  match context with
  | KernelCaller _ _ => O
  | KernelInterrupt _ interrupted => S (kernel_interrupt_depth interrupted)
  end.

(** This is execution eligibility only, not a separation-logic permission
    to borrow an object. In particular the suspended caller is NOT the
    currently executing context while an ISR wraps it. Boot is retained. *)
Definition kernel_caller_executing (invocation : nat) (origin : TaskInvocationOrigin)
  (context : KernelExecutionContext) : Prop :=
  context = KernelCaller invocation origin.

Lemma kernel_interrupt_not_caller_executing : forall invocation origin handler interrupted,
  ~ kernel_caller_executing invocation origin (KernelInterrupt handler interrupted).
Proof. intros; unfold kernel_caller_executing; discriminate. Qed.

Lemma kernel_zero_depth_is_caller : forall context,
  kernel_interrupt_depth context = O ->
  exists invocation origin, kernel_caller_executing invocation origin context.
Proof.
  intros [invocation origin|handler interrupted] Hdepth; cbn in Hdepth;
    [eexists; eexists; reflexivity|discriminate].
Qed.

(** Source observations are explicit. For Lock/Unlock/Exit the counter
    state is the protected acquired state (or the no-Save false branch),
    not silently identified with the earlier OSRunning observation.
    Enter pairs a wrapper's entry with OSIntEnter. Exit ends at the C
    counter/scheduling decision, before any dispatch/exception return.
    A true scheduling result must be handled by the existing full scheduler
    or OSIntExit call relation; it is NOT a normal return or a switch. *)
Inductive KernelControlAction : Type :=
| KernelEnterInterrupt (handler : nat) (running_observed : bool)
| KernelExitInterrupt (running_observed : bool)
| KernelLockScheduler (running_observed : bool)
| KernelUnlockScheduler (running_observed : bool).

Inductive kernel_control_step : KernelControlAction ->
  KernelExecutionContext -> InterruptAbstractState ->
  KernelExecutionContext -> InterruptAbstractState -> bool -> Prop :=
| KernelControlEnter : forall handler observed context counters,
    kernel_control_step (KernelEnterInterrupt handler observed) context counters
      (KernelInterrupt handler context) (interrupt_enter_state observed counters) false
| KernelControlExit : forall handler observed interrupted counters,
    kernel_control_step (KernelExitInterrupt observed)
      (KernelInterrupt handler interrupted) counters interrupted
      (interrupt_exit_state observed counters)
      (interrupt_exit_requests_schedule observed counters)
| KernelControlLock : forall observed context counters,
    kernel_control_step (KernelLockScheduler observed) context counters context
      (sched_lock_state observed counters) false
| KernelControlUnlock : forall observed context counters,
    kernel_control_step (KernelUnlockScheduler observed) context counters context
      (sched_unlock_state observed counters)
      (sched_unlock_requests_schedule observed counters).

Lemma kernel_control_step_deterministic : forall action context counters
  continuation1 counters1 schedule1 continuation2 counters2 schedule2,
  kernel_control_step action context counters continuation1 counters1 schedule1 ->
  kernel_control_step action context counters continuation2 counters2 schedule2 ->
  continuation1 = continuation2 /\ counters1 = counters2 /\ schedule1 = schedule2.
Proof. intros; inversion H; inversion H0; subst; repeat split; congruence. Qed.

Lemma kernel_control_step_suspended_caller_eq : forall action context counters
  continuation final scheduling,
  kernel_control_step action context counters continuation final scheduling ->
  kernel_suspended_caller continuation = kernel_suspended_caller context.
Proof. intros; inversion H; reflexivity. Qed.

Lemma kernel_control_step_preserves_counter_range : forall action context counters
  continuation final scheduling,
  kernel_control_step action context counters continuation final scheduling ->
  interrupt_counters_in_range counters -> interrupt_counters_in_range final.
Proof.
  intros action context counters continuation final scheduling Hstep Hrange.
  inversion Hstep; subst.
  - apply interrupt_enter_preserves_counters_in_range; exact Hrange.
  - apply interrupt_exit_preserves_counters_in_range; exact Hrange.
  - apply sched_lock_preserves_counters_in_range; exact Hrange.
  - apply sched_unlock_preserves_counters_in_range; exact Hrange.
Qed.

(** Agreement is a separate source-protocol obligation, not a definition
    of 'ISR' using the C counter. In boot the counter cannot identify the
    context. Saturating C transitions remain in kernel_control_step;
    preservation of depth agreement needs the documented nesting bound. *)
Definition kernel_interrupt_nesting_agrees (running : bool)
  (context : KernelExecutionContext) (counters : InterruptAbstractState) : Prop :=
  running = true -> counters.(intNesting) = Z.of_nat (kernel_interrupt_depth context).

Lemma kernel_interrupt_entry_preserves_nesting_agreement : forall observed handler context counters,
  kernel_interrupt_nesting_agrees observed context counters ->
  (observed = true -> (kernel_interrupt_depth context < 255)%nat) ->
  kernel_interrupt_nesting_agrees observed (KernelInterrupt handler context)
    (interrupt_enter_state observed counters).
Proof.
  intros [] handler context counters Hagrees Hbound; unfold kernel_interrupt_nesting_agrees in *;
    [|discriminate].
  specialize (Hagrees eq_refl); specialize (Hbound eq_refl); intro Htrue.
  unfold interrupt_enter_state; cbn.
  assert (Hlt : (intNesting counters <? 255) = true) by (apply Z.ltb_lt; lia).
  rewrite Hlt.
  change (intNesting counters + 1 = Z.of_nat (S (kernel_interrupt_depth context))).
  rewrite Nat2Z.inj_succ; lia.
Qed.

Lemma kernel_interrupt_exit_preserves_nesting_agreement : forall observed handler context counters,
  kernel_interrupt_nesting_agrees observed (KernelInterrupt handler context) counters ->
  kernel_interrupt_nesting_agrees observed context (interrupt_exit_state observed counters).
Proof.
  intros [] handler context counters Hagrees; unfold kernel_interrupt_nesting_agrees in *;
    [|discriminate].
  specialize (Hagrees eq_refl).
  change (intNesting counters = Z.of_nat (S (kernel_interrupt_depth context))) in Hagrees.
  rewrite Nat2Z.inj_succ in Hagrees; intro Htrue.
  unfold interrupt_exit_state; cbn.
  assert (Hpositive : (0 <? intNesting counters) = true) by (apply Z.ltb_lt; lia).
  rewrite Hpositive; cbn; lia.
Qed.

Lemma kernel_running_zero_nesting_is_caller : forall context counters,
  kernel_interrupt_nesting_agrees true context counters -> counters.(intNesting) = 0 ->
  exists invocation origin, kernel_caller_executing invocation origin context.
Proof.
  intros context counters Hagrees Hzero.
  apply kernel_zero_depth_is_caller.
  specialize (Hagrees eq_refl); lia.
Qed.

Lemma kernel_running_interrupt_nesting_positive : forall handler context counters,
  kernel_interrupt_nesting_agrees true (KernelInterrupt handler context) counters ->
  0 < counters.(intNesting).
Proof.
  intros handler context counters Hagrees; specialize (Hagrees eq_refl).
  change (intNesting counters = Z.of_nat (S (kernel_interrupt_depth context))) in Hagrees.
  rewrite Nat2Z.inj_succ in Hagrees; lia.
Qed.

Lemma kernel_caller_lock_positive : forall invocation origin counters,
  kernel_interrupt_nesting_agrees true (KernelCaller invocation origin) counters ->
  0 <= counters.(lockNesting) ->
  0 < (sched_lock_state true counters).(lockNesting).
Proof.
  intros invocation origin [ints locks] Hagrees Hlocks.
  specialize (Hagrees eq_refl); cbn in Hagrees, Hlocks; subst ints.
  unfold sched_lock_state; cbn.
  destruct (locks <? 255) eqn:E; cbn; [|apply Z.ltb_ge in E]; lia.
Qed.

Lemma kernel_locked_interrupt_exit_no_schedule : forall observed counters,
  counters.(lockNesting) <> 0 -> interrupt_exit_requests_schedule observed counters = false.
Proof.
  intros observed counters Hlocks; unfold interrupt_exit_requests_schedule.
  apply Z.eqb_neq in Hlocks; rewrite Hlocks; apply Bool.andb_false_r.
Qed.

(** A complete matched counter envelope with no body counter writes. This
    is used only after a source-specific body theorem supplies that frame;
    it does not select/filter ISR bodies by the desired final equality.
    The context's actual paired return is explicit, including boot. *)
Lemma kernel_borrowed_interrupt_counter_envelope : forall observed invocation origin handler counters,
  kernel_interrupt_nesting_agrees observed (KernelCaller invocation origin) counters ->
  (observed = true -> counters.(lockNesting) <> 0) ->
  kernel_control_step (KernelEnterInterrupt handler observed)
    (KernelCaller invocation origin) counters
    (KernelInterrupt handler (KernelCaller invocation origin))
    (interrupt_enter_state observed counters) false /\
  kernel_control_step (KernelExitInterrupt observed)
    (KernelInterrupt handler (KernelCaller invocation origin))
    (interrupt_enter_state observed counters)
    (KernelCaller invocation origin) counters false.
Proof.
  intros observed invocation origin handler counters Hagrees Hlocked.
  split; [constructor|].
  assert (Hround : interrupt_exit_state observed (interrupt_enter_state observed counters) = counters).
  { destruct observed; [|reflexivity].
    apply interrupt_enter_exit_counters_eq.
    specialize (Hagrees eq_refl); cbn in Hagrees; lia. }
  assert (Hnoschedule : interrupt_exit_requests_schedule observed
    (interrupt_enter_state observed counters) = false).
  { destruct observed; [|reflexivity].
    apply kernel_locked_interrupt_exit_no_schedule.
    specialize (Hlocked eq_refl).
    unfold interrupt_enter_state; destruct (intNesting counters <? 255); exact Hlocked. }
  pose proof (KernelControlExit handler observed (KernelCaller invocation origin)
    (interrupt_enter_state observed counters)) as Hexit.
  rewrite Hround, Hnoschedule in Hexit; exact Hexit.
Qed.
