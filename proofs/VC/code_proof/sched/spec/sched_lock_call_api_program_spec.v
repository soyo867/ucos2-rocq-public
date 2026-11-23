Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_call_spec.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Public source-program refinement of the existing OSSchedLock call.
    The platform observation/acquisition/Restore contracts above are unchanged. *)
Definition os_sched_lock_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat)
  : program UCOS2_Verify_State unit :=
  fun before result final =>
    result = tt /\ exists entry,
      os_sched_lock_call_relation critical sg invocation before entry final.

Definition os_sched_lock_continuation (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (X : UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun observed => observed = before)
    (os_sched_lock_program critical sg invocation) (fun _ final => X final).

Definition os_sched_lock_program_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (X : UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (os_sched_lock_continuation critical sg invocation before X) &&
  os_sched_lock_pre platform critical sg invocation origin mask before.

Definition os_sched_lock_program_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (X : UCOS2_Verify_State -> Prop) : Assertion :=
  EX entry, EX final,
    coq_prop (os_sched_lock_call_relation critical sg invocation before entry final /\
      UCOS2_state_inv sg final /\ X final) &&
    (sg.(g_OSRunning) # UChar |-> os_sched_lock_running final **
     os_sched_lock_outside_frame platform critical sg invocation origin mask final).

Lemma os_sched_lock_return_continuation : forall critical sg invocation before X
  entry final,
  os_sched_lock_continuation critical sg invocation before X ->
  os_sched_lock_call_relation critical sg invocation before entry final ->
  X final.
Proof.
  intros critical sg invocation before X entry final
    [observed [Hobserved Hsafe]] Hcall.
  subst observed.
  apply (Hsafe tt final).
  split; [reflexivity|].
  exists entry; exact Hcall.
Qed.

Lemma os_sched_lock_program_pre_open : forall platform critical sg invocation
  origin mask before X,
  os_sched_lock_program_pre platform critical sg invocation origin mask before X |--
  coq_prop (os_sched_lock_continuation critical sg invocation before X) &&
  os_sched_lock_pre platform critical sg invocation origin mask before.
Proof. intros; unfold os_sched_lock_program_pre; entailer!. Qed.

Lemma os_sched_lock_post_program_post : forall platform critical sg invocation
  origin mask before X,
  os_sched_lock_continuation critical sg invocation before X ->
  os_sched_lock_post platform critical sg invocation origin mask before |--
  os_sched_lock_program_post platform critical sg invocation origin mask before X.
Proof.
  intros platform critical sg invocation origin mask before X Hcontinuation.
  unfold os_sched_lock_post, os_sched_lock_program_post.
  intros heap [entry [final [[Hcall Hvalid] Hresources]]].
  exists entry, final.
  split.
  - split; [exact Hcall|].
    split; [exact Hvalid|].
    eapply os_sched_lock_return_continuation; eassumption.
  - exact Hresources.
Qed.

Lemma os_sched_lock_program_not_running_return : forall platform critical sg
  invocation origin mask before X,
  UCOS2_state_inv sg before ->
  os_sched_lock_running before <> 1 ->
  os_sched_lock_continuation critical sg invocation before X ->
  sg.(g_OSRunning) # UChar |-> os_sched_lock_running before **
  os_sched_lock_outside_frame platform critical sg invocation origin mask before |--
  os_sched_lock_program_post platform critical sg invocation origin mask before X.
Proof.
  intros platform critical sg invocation origin mask before X Hvalid Hnotrunning Hsafe
    heap Hresources.
  apply (os_sched_lock_post_program_post platform critical sg invocation origin mask
    before X Hsafe heap).
  apply (os_sched_lock_not_running_return platform critical sg invocation origin mask
    before Hvalid Hnotrunning heap).
  exact Hresources.
Qed.

