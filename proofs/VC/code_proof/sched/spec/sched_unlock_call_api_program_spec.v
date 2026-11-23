Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_call_spec.
Require Import Coq.ZArith.ZArith.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The scheduler acquisition is after the actual decrement and Restore.
    Its acquired state and returned continuation remain those of OS_Sched. *)
Definition os_sched_unlock_call_relation (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (returned : OsSchedCallContext) (final : UCOS2_Verify_State) : Prop :=
  (before.(SchedState).(isRunning) = false /\ returned = context /\ final = before) \/
  (exists entry,
    before.(SchedState).(isRunning) = true /\
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
    if os_sched_unlock_requests entry then
      exists acquired,
        critical_region_interval critical sg context.(os_sched_call_invocation)
          (os_sched_unlock_checkpoint true entry) acquired /\
        os_sched_c_return external critical sg acquired context returned final
    else returned = context /\ final = os_sched_unlock_checkpoint true entry).

Definition os_sched_unlock_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) : program UCOS2_Verify_State unit :=
  fun before result final => result = tt /\ exists returned,
    os_sched_unlock_call_relation external critical sg context before returned final.

Definition os_sched_unlock_continuation (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State)
  (X : UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun observed => observed = before)
    (os_sched_unlock_program external critical sg context) (fun _ final => X final).

Definition os_sched_unlock_program_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (X : UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (os_sched_unlock_continuation external critical sg context before X) &&
  os_sched_unlock_pre external platform critical sg context mask before.

Definition os_sched_unlock_scheduled_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (checkpoint : UCOS2_Verify_State) (X : UCOS2_Verify_State -> Prop) : Assertion :=
  EX acquired, EX final, EX returned,
    coq_prop (critical_region_interval critical sg context.(os_sched_call_invocation)
      checkpoint acquired /\
      os_sched_c_return external critical sg acquired context returned final /\ X final) &&
    (interrupt_platform_running platform context.(os_sched_call_invocation)
       context.(os_sched_call_origin) mask **
     critical_region_outside critical sg context.(os_sched_call_invocation) final **
     os_sched_context_resources external returned ** unmap_table_rep sg).

Definition os_sched_unlock_program_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) (X : UCOS2_Verify_State -> Prop) : Assertion :=
  (coq_prop (before.(SchedState).(isRunning) = false /\
      UCOS2_state_inv sg before /\ X before) &&
    (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
     os_sched_unlock_observation_frame external platform critical sg context mask before)) ||
  (EX entry,
    coq_prop (before.(SchedState).(isRunning) = true /\
      critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
      UCOS2_state_inv sg (os_sched_unlock_checkpoint true entry)) &&
    (if os_sched_unlock_requests entry then
       os_sched_unlock_scheduled_post external platform critical sg context mask
         (os_sched_unlock_checkpoint true entry) X
     else coq_prop (X (os_sched_unlock_checkpoint true entry)) &&
       os_sched_unlock_outside_frame external platform critical sg context mask
         (os_sched_unlock_checkpoint true entry))).

Lemma os_sched_unlock_return_continuation : forall external critical sg context
  before X returned final,
  os_sched_unlock_continuation external critical sg context before X ->
  os_sched_unlock_call_relation external critical sg context before returned final ->
  X final.
Proof.
  intros external critical sg context before X returned final
    [observed [Hobserved Hsafe]] Hcall.
  subst observed.
  apply (Hsafe tt final).
  split; [reflexivity|exists returned; exact Hcall].
Qed.

Lemma os_sched_unlock_program_pre_open : forall external platform critical sg
  context mask before X,
  os_sched_unlock_program_pre external platform critical sg context mask before X |--
  coq_prop (os_sched_unlock_continuation external critical sg context before X) &&
  os_sched_unlock_pre external platform critical sg context mask before.
Proof. intros; unfold os_sched_unlock_program_pre; entailer!. Qed.

Lemma os_sched_unlock_post_program_post : forall external platform critical sg
  context mask before X,
  os_sched_unlock_continuation external critical sg context before X ->
  os_sched_unlock_post external platform critical sg context mask before |--
  os_sched_unlock_program_post external platform critical sg context mask before X.
Proof.
  intros external platform critical sg context mask before X Hsafe heap Hpost.
  destruct Hpost as [[[Hrun Hvalid] Hresources]|
    [entry [[Hrun [Hinterval Hvalid]] Hresources]]].
  - left; split; [|exact Hresources].
    split; [exact Hrun|]. split; [exact Hvalid|].
    apply (os_sched_unlock_return_continuation external critical sg context
      before X context before Hsafe).
    left; exact (conj Hrun (conj eq_refl eq_refl)).
  - right; exists entry; split.
    + exact (conj Hrun (conj Hinterval Hvalid)).
    + destruct (os_sched_unlock_requests entry) eqn:Hrequest.
      * destruct Hresources as [acquired [final [returned
          [[Hacquired Hreturn] Hresources]]]].
        exists acquired, final, returned; split; [|exact Hresources].
        split; [exact Hacquired|]. split; [exact Hreturn|].
        apply (os_sched_unlock_return_continuation external critical sg context
          before X returned final Hsafe).
        right; exists entry; split; [exact Hrun|].
        split; [exact Hinterval|]. rewrite Hrequest.
        exists acquired; exact (conj Hacquired Hreturn).
      * split; [|exact Hresources].
        apply (os_sched_unlock_return_continuation external critical sg context
          before X context (os_sched_unlock_checkpoint true entry) Hsafe).
        right; exists entry; split; [exact Hrun|].
        split; [exact Hinterval|]. rewrite Hrequest.
        exact (conj eq_refl eq_refl).
Qed.

Lemma os_sched_unlock_program_post_base : forall external platform critical sg
  context mask before X,
  os_sched_unlock_program_post external platform critical sg context mask before X |--
  os_sched_unlock_post external platform critical sg context mask before.
Proof.
  intros external platform critical sg context mask before X heap Hpost.
  destruct Hpost as [[[Hrun [Hvalid HX]] Hresources]|
    [entry [Hentry Hresources]]].
  - left; exact (conj (conj Hrun Hvalid) Hresources).
  - right; exists entry; split; [exact Hentry|].
    destruct (os_sched_unlock_requests entry).
    + destruct Hresources as [acquired [final [returned
        [[Hacquired [Hreturn HX]] Hresources]]]].
      exists acquired, final, returned.
      exact (conj (conj Hacquired Hreturn) Hresources).
    + exact (proj2 Hresources).
Qed.
