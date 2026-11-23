Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.VC.code.sched.spec.sched_lock_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Coq.micromega.Lia.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Full OSSchedUnlock C-call specification. Reuse the exact counter
    checkpoint and the verified OS_Sched call contract, including its
    distinct post-Restore acquisition and possible later resumption. *)

Definition os_sched_unlock_running (state : UCOS2_Verify_State) : Z :=
  if state.(SchedState).(isRunning) then 1 else 0.

Definition os_sched_unlock_global_addresses (sg : StableGlobVars)
  (running ints locks high current high_tcb table counter unmap group rows : Z) : Prop :=
  running = sg.(g_OSRunning) /\
  os_sched_global_addresses sg ints locks high current high_tcb table counter unmap group rows.

(** This is the existing OS_Sched resource frame.  In particular, the
    executing continuation fragments are not part of the shared kernel
    invariant; OS_Sched consumes them through its unchanged call contract. *)
Definition os_sched_unlock_outside_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside critical sg context.(os_sched_call_invocation) state **
  os_sched_context_resources external context ** unmap_table_rep sg.

Definition os_sched_unlock_inside_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (saved : Z)
  (entry : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg context.(os_sched_call_invocation)
    context.(os_sched_call_origin) saved entry **
  os_sched_context_resources external context ** unmap_table_rep sg.

(** The closed outside frame above includes the OSRunning byte.  Only this
    residual can be framed beside the explicit pre-Save observation. *)
Definition os_sched_unlock_observation_frame (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside_without_running critical sg context.(os_sched_call_invocation) state **
  os_sched_context_resources external context ** unmap_table_rep sg.

Lemma os_sched_unlock_outside_frame_split_running :
  forall external platform critical sg context mask state,
  os_sched_unlock_outside_frame external platform critical sg context mask state --||--
    (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running state **
     os_sched_unlock_observation_frame external platform critical sg context mask state).
Proof.
  intros; unfold os_sched_unlock_outside_frame, critical_region_outside,
    os_sched_unlock_observation_frame, os_sched_unlock_running.
  split; entailer!.
Qed.

(** A caller obligation only at the actual scheduling call.  Neither the
    ISR guard nor zero/saturated counter inputs are excluded.  The second
    acquisition starts at the unlock checkpoint and is quantified by the
    canonical OS_Sched safety predicate, not identified with that checkpoint. *)
Definition os_sched_unlock_acquire_safety (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State) : Prop :=
  before.(SchedState).(isRunning) = true ->
  forall entry,
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    sched_unlock_requests_schedule true entry.(IntrState) = true ->
    os_sched_acquire_safety external critical sg context (os_sched_unlock_checkpoint true entry).

(** The pre-Save OSRunning read borrows its real typed byte from the region.
    The task-level observation/Save external specialization consumes that
    loan before reopening the complete current kernel representation.  This
    is the same observation/acquisition discipline as OSIntExit, with NO ISR
    frame, exception transfer, or additional platform-running token. *)
Definition os_sched_unlock_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\
    os_sched_unlock_acquire_safety external critical sg context before) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
   os_sched_unlock_observation_frame external platform critical sg context mask before).

Definition os_sched_unlock_body_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  before.(SchedState).(isRunning) = true /\
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  (sched_unlock_requests_schedule true entry.(IntrState) = true ->
    os_sched_acquire_safety external critical sg context (os_sched_unlock_checkpoint true entry)).

Lemma os_sched_unlock_pre_closed_equiv : forall external platform critical sg context mask before,
  os_sched_unlock_pre external platform critical sg context mask before --||--
    coq_prop (UCOS2_state_inv sg before /\
      os_sched_unlock_acquire_safety external critical sg context before) &&
    os_sched_unlock_outside_frame external platform critical sg context mask before.
Proof.
  intros; unfold os_sched_unlock_pre.
  rewrite os_sched_unlock_outside_frame_split_running; split; reflexivity.
Qed.

Definition os_sched_unlock_requests (entry : UCOS2_Verify_State) : bool :=
  sched_unlock_requests_schedule true entry.(IntrState).

Definition os_sched_unlock_counted_locks (entry : UCOS2_Verify_State) : Z :=
  (sched_unlock_state true entry.(IntrState)).(lockNesting).

(** Source-ordered ordinary-return projection.  On 1-to-0 the unchanged
    callee postcondition retains its own acquired state and original-call
    resumption relation.  It does not promise that a context switch occurs,
    that a callback terminates, or that a retired invocation returns.

    The false-running path keeps its unconsumed observation view.  On each
    Save path Restore closes the kernel and returns the same byte inside
    the canonical closed entry.  OS_Sched consumes that whole entry; no
    extra byte is framed through it.  The two layouts are related by the
    actual split lemma above, not by a second independent region handle. *)
Definition os_sched_unlock_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask : Z)
  (before : UCOS2_Verify_State) : Assertion :=
  (coq_prop (before.(SchedState).(isRunning) = false /\ UCOS2_state_inv sg before) &&
    (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
     os_sched_unlock_observation_frame external platform critical sg context mask before)) ||
  (EX entry,
    coq_prop (before.(SchedState).(isRunning) = true /\
      critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
      UCOS2_state_inv sg (os_sched_unlock_checkpoint true entry)) &&
    (if os_sched_unlock_requests entry then
       os_sched_post external platform critical sg context mask
         (os_sched_unlock_checkpoint true entry)
     else os_sched_unlock_outside_frame external platform critical sg context mask
         (os_sched_unlock_checkpoint true entry))).

Lemma os_sched_unlock_acquire_facts : forall external critical sg context mask saved before entry,
  UCOS2_state_inv sg before ->
  os_sched_unlock_acquire_safety external critical sg context before ->
  os_sched_unlock_running before = 1 ->
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
  interrupt_saved_value mask saved ->
  os_sched_unlock_body_facts external critical sg context mask saved before entry.
Proof.
  intros external critical sg context mask saved before entry Hvalid Hsafe Hrun Hinterval Hsaved.
  unfold os_sched_unlock_running in Hrun.
  destruct before.(SchedState).(isRunning) eqn:Hrunning; [|discriminate].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg context.(os_sched_call_invocation) before entry Hinterval Hvalid)) as Hentry.
  unfold os_sched_unlock_body_facts.
  split; [exact Hrunning|]. split; [exact Hinterval|].
  split; [exact Hentry|]. split; [exact Hsaved|].
  exact (Hsafe Hrunning entry Hinterval).
Qed.

(** Old byte ranges are exposed BEFORE the decrement.  The post-write
    UChar cell alone would not bound the overwritten mathematical old value. *)
Lemma os_sched_unlock_split_counters : forall sg entry,
  UCOS2_raw_rep sg entry |--
    coq_prop (0 <= os_sched_ints entry <= 255 /\ 0 <= os_sched_locks entry <= 255) &&
    ((sg.(g_OSIntNesting) # UChar |-> os_sched_ints entry) **
     (sg.(g_OSLockNesting) # UChar |-> os_sched_locks entry) **
     UCOS2_raw_rep_missing_interrupt sg entry).
Proof.
  intros sg entry; rewrite (UCOS2_raw_rep_split_module sg entry InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, store_int_state, os_sched_ints, os_sched_locks,
    UCOS2_raw_rep_missing_interrupt.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) entry.(IntrState).(intNesting)).
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) entry.(IntrState).(lockNesting)).
  entailer!.
Qed.

Lemma os_sched_unlock_positive_counted_locks : forall entry,
  os_sched_ints entry = 0 -> 0 < os_sched_locks entry ->
  os_sched_unlock_counted_locks entry = os_sched_locks entry - 1.
Proof.
  intros entry Hint Hlock; unfold os_sched_unlock_counted_locks, sched_unlock_state.
  unfold os_sched_ints in Hint; unfold os_sched_locks in Hlock |- *.
  rewrite Hint; simpl; rewrite (proj2 (Z.ltb_lt 0 _) Hlock); reflexivity.
Qed.

Lemma os_sched_unlock_merge_counters : forall sg entry,
  UCOS2_state_inv sg entry ->
  (sg.(g_OSIntNesting) # UChar |-> os_sched_ints entry) **
  (sg.(g_OSLockNesting) # UChar |-> os_sched_unlock_counted_locks entry) **
  UCOS2_raw_rep_missing_interrupt sg entry |--
    UCOS2_inv sg (os_sched_unlock_checkpoint true entry).
Proof.
  intros sg entry Hvalid.
  pose proof (os_sched_unlock_merge_inv sg true entry Hvalid) as Hmerge.
  unfold store_int_state in Hmerge.
  assert (Hint : (sched_unlock_state true entry.(IntrState)).(intNesting) =
    entry.(IntrState).(intNesting)).
  { unfold sched_unlock_state; simpl.
    destruct (entry.(IntrState).(intNesting) =? 0);
      [destruct (0 <? entry.(IntrState).(lockNesting))|]; reflexivity. }
  rewrite Hint in Hmerge.
  unfold os_sched_ints, os_sched_unlock_counted_locks.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma os_sched_unlock_sched_pre : forall external platform critical sg context mask entry,
  UCOS2_state_inv sg entry ->
  os_sched_acquire_safety external critical sg context (os_sched_unlock_checkpoint true entry) ->
  os_sched_unlock_outside_frame external platform critical sg context mask
    (os_sched_unlock_checkpoint true entry) |--
  os_sched_pre external platform critical sg context mask (os_sched_unlock_checkpoint true entry).
Proof.
  intros external platform critical sg context mask entry Hvalid Hsafe.
  pose proof (os_sched_unlock_checkpoint_preserves_validity sg true entry Hvalid) as Hpost.
  unfold os_sched_pre, os_sched_unlock_outside_frame; entailer!.
Qed.
