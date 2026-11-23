Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.

(** A fresh logical invocation at an ordinary sequential API entry. The
    preceding API has returned; this is not a parked continuation rename,
    nested call, task switch, or allocation of stack bytes. The boundary is
    before the next callee's local stack partition changes. *)
Definition kernel_sequential_call (previous : OsSchedCallContext)
  (invocation : nat) : OsSchedCallContext :=
  {| os_sched_call_invocation := invocation;
     os_sched_call_origin := previous.(os_sched_call_origin);
     os_sched_call_stack := previous.(os_sched_call_stack);
     os_sched_call_fragments := previous.(os_sched_call_fragments) |}.

(** Explicit external application/compiler calling-convention refinement.
    The source relation must be supplied by the linked program's completed
    API return and actual next API entry. There is deliberately no constructor
    deriving an event from arbitrary old/new identifiers. The law exchanges
    one current CPU/architecture owner for one owner with a fresh logical
    label, on the same stack and mask. It produces no kernel state, current
    task, readiness, invariant, reservation or future-call safety fact.

    This is an additional conditional ABI interpretation, not a theorem
    about arbitrary existing opaque resource predicates and not a proof of
    the application/compiler implementation. No C address stores the label.
    Code between the two APIs, interrupts, prologue stores and nested calls
    require their own source steps before/after this single entry cut. *)
Record KernelSequentialCallABI (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) : Type := {
  kernel_sequential_call_source :
    OsSchedCallContext -> nat -> model -> model -> Prop;
  kernel_sequential_call_resources : forall previous invocation mask
    (frame : Assertion) before after,
    kernel_sequential_call_source previous invocation before after ->
    (interrupt_platform_running platform previous.(os_sched_call_invocation)
       previous.(os_sched_call_origin) mask **
     external.(os_sched_arch_running) previous ** frame) before ->
    after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
    (interrupt_platform_running platform invocation previous.(os_sched_call_origin) mask **
     external.(os_sched_arch_running) (kernel_sequential_call previous invocation) ** frame) after
}.

Arguments kernel_sequential_call_source {external platform} _ _ _ _ _.

(** The caller already owns the actual stack bytes. Only the two opaque
    execution owners are interpreted at the observed entry; the byte
    fragments and every disjoint frame are carried once, unchanged. *)
Lemma kernel_sequential_call_owned_entry : forall external platform
  (boundary : KernelSequentialCallABI external platform)
  previous invocation mask before after (frame : Assertion),
  kernel_sequential_call_source boundary previous invocation before after ->
  (kernel_call_execution_owned external platform previous mask ** frame) before ->
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_call_execution_owned external platform
    (kernel_sequential_call previous invocation) mask ** frame) after.
Proof.
  intros external platform boundary previous invocation mask before after frame Hsource Hbefore.
  assert (Hopen : kernel_call_execution_owned external platform previous mask ** frame |--
    interrupt_platform_running platform previous.(os_sched_call_invocation)
      previous.(os_sched_call_origin) mask ** external.(os_sched_arch_running) previous **
    (task_stack_fragments_rep previous.(os_sched_call_stack).(stackLeaseRegion)
       previous.(os_sched_call_fragments) ** frame)).
  { unfold kernel_call_execution_owned, os_sched_context_resources; entailer!. }
  destruct (kernel_sequential_call_resources external platform boundary previous invocation mask
    _ before after Hsource (Hopen before Hbefore)) as [Hmemory Hafter].
  split; [exact Hmemory|].
  match type of Hafter with ?P after => match goal with |- ?Q after =>
    assert (Hclose : P |-- Q) end end.
  { unfold kernel_call_execution_owned, os_sched_context_resources, kernel_sequential_call; entailer!. }
  exact (Hclose after Hafter).
Qed.
