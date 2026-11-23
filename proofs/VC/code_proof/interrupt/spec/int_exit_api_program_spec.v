Require Export Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Coq.ZArith.ZArith.

Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition os_int_exit_program (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext)
  : program UCOS2_Verify_State OsIntExitOutcome :=
  fun before outcome final =>
    os_int_exit_full_call external port critical sg context before outcome /\
    final = os_int_exit_outcome_state before outcome.

Definition os_int_exit_continuation (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext)
  (before : UCOS2_Verify_State)
  (X : OsIntExitOutcome -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun observed => observed = before)
    (os_int_exit_program external port critical sg context) X.

Definition os_int_exit_program_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (mask : Z) (before : UCOS2_Verify_State)
  (X : OsIntExitOutcome -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (os_int_exit_continuation external port critical sg context before X) &&
  os_int_exit_pre external platform port critical sg context mask before.

Definition os_int_exit_program_post (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsIntExitCallContext) (mask : Z)
  (before : UCOS2_Verify_State)
  (X : OsIntExitOutcome -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX entry,
    let final := os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry in
    coq_prop (os_int_exit_return_relation critical sg context before entry /\
      UCOS2_state_inv sg final /\ X (OsIntExitReturned entry) final) &&
    (sg.(g_OSRunning) # UChar |-> os_int_exit_running final **
      os_int_exit_outside_frame platform port critical sg context mask final).

(** The nonlocal C call has no ordinary return. Its original resource-explicit
    transfer post is refined by the same X; no new platform transition is added. *)
Definition os_int_exit_transfer_program_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (port : OsIntExitPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (saved : Z)
  (before entry : UCOS2_Verify_State)
  (X : OsIntExitOutcome -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (before.(SchedState).(isRunning) = true /\
    critical_region_interval critical sg context.(os_int_exit_invocation) before entry /\
    os_int_exit_continuation external port critical sg context before X) &&
  os_int_exit_transfer_pre external platform port critical sg context saved entry.

Definition os_int_exit_transfer_program_post (external : OsSchedExternalResources)
  (port : OsIntExitPlatformResources) (sg : StableGlobVars)
  (context : OsIntExitCallContext) (saved : Z) (entry : UCOS2_Verify_State)
  (transfer : OsIntExitTransfer)
  (X : OsIntExitOutcome -> UCOS2_Verify_State -> Prop) : Assertion :=
  coq_prop (X (OsIntExitExceptionTransferred entry transfer)
    (os_int_exit_installed_state transfer)) &&
  os_int_exit_transfer_post external port sg context saved entry transfer.

Lemma os_int_exit_outcome_continuation : forall external port critical sg context
  before X outcome,
  os_int_exit_continuation external port critical sg context before X ->
  os_int_exit_full_call external port critical sg context before outcome ->
  X outcome (os_int_exit_outcome_state before outcome).
Proof.
  intros external port critical sg context before X outcome
    [observed [Hobserved Hsafe]] Hcall.
  subst observed.
  apply (Hsafe outcome (os_int_exit_outcome_state before outcome)).
  split; [exact Hcall|reflexivity].
Qed.

Lemma os_int_exit_return_continuation : forall external port critical sg context
  before X entry,
  os_int_exit_continuation external port critical sg context before X ->
  os_int_exit_return_relation critical sg context before entry ->
  X (OsIntExitReturned entry)
    (os_int_exit_ready_checkpoint before.(SchedState).(isRunning) entry).
Proof.
  intros external port critical sg context before X entry Hsafe Hreturn.
  exact (os_int_exit_outcome_continuation external port critical sg context
    before X (OsIntExitReturned entry) Hsafe Hreturn).
Qed.

Lemma os_int_exit_transfer_continuation : forall external port critical sg context
  before X entry transfer,
  before.(SchedState).(isRunning) = true ->
  critical_region_interval critical sg context.(os_int_exit_invocation) before entry ->
  os_int_exit_continuation external port critical sg context before X ->
  os_int_exit_transfer_source external port sg context entry transfer ->
  X (OsIntExitExceptionTransferred entry transfer)
    (os_int_exit_installed_state transfer).
Proof.
  intros external port critical sg context before X entry transfer
    Hrunning Hinterval Hsafe Htransfer.
  apply (os_int_exit_outcome_continuation external port critical sg context
    before X (OsIntExitExceptionTransferred entry transfer) Hsafe).
  exact (conj Hrunning (conj Hinterval Htransfer)).
Qed.

Lemma os_int_exit_post_program_post : forall external platform port critical sg
  context mask before X,
  os_int_exit_continuation external port critical sg context before X ->
  os_int_exit_post platform port critical sg context mask before |--
  os_int_exit_program_post platform port critical sg context mask before X.
Proof.
  intros external platform port critical sg context mask before X Hsafe.
  unfold os_int_exit_post, os_int_exit_program_post.
  intros heap [entry [[Hreturn Hvalid] Hresources]].
  exists entry.
  split.
  - split; [exact Hreturn|].
    split; [exact Hvalid|].
    eapply os_int_exit_return_continuation; eassumption.
  - exact Hresources.
Qed.

Lemma os_int_exit_body_transfer_program_pre : forall external platform port critical
  sg context mask saved before entry X,
  os_int_exit_body_facts external port critical sg context mask saved before entry ->
  os_int_exit_continuation external port critical sg context before X ->
  os_int_exit_transfer_pre external platform port critical sg context saved entry |--
  os_int_exit_transfer_program_pre external platform port critical sg context saved
    before entry X.
Proof.
  intros external platform port critical sg context mask saved before entry X
    [Hrunning [Hinterval Hrest]] Hsafe heap Hresources.
  split; [exact (conj Hrunning (conj Hinterval Hsafe))|exact Hresources].
Qed.

Lemma os_int_exit_transfer_program_pre_base : forall external platform port critical
  sg context saved before entry X,
  os_int_exit_transfer_program_pre external platform port critical sg context saved
    before entry X |--
  os_int_exit_transfer_pre external platform port critical sg context saved entry.
Proof. intros; unfold os_int_exit_transfer_program_pre; entailer!. Qed.

Lemma os_int_exit_transfer_post_program_post : forall external port critical sg
  context saved before entry transfer X,
  before.(SchedState).(isRunning) = true ->
  critical_region_interval critical sg context.(os_int_exit_invocation) before entry ->
  os_int_exit_continuation external port critical sg context before X ->
  os_int_exit_transfer_post external port sg context saved entry transfer |--
  os_int_exit_transfer_program_post external port sg context saved entry transfer X.
Proof.
  intros external port critical sg context saved before entry transfer X
    Hrunning Hinterval Hsafe heap Hpost.
  split; [|exact Hpost].
  eapply os_int_exit_transfer_continuation; [exact Hrunning|exact Hinterval|exact Hsafe|].
  exact (proj1 Hpost).
Qed.

(** The nonlocal refinement consumes the same actual cache writes, selected
    parked-stack removal and transferred-control owner as the existing port
    module. The public continuation is not a new platform postcondition. *)
Lemma os_int_exit_transfer_resources_program_post : forall external port critical
  sg context saved before entry transfer X,
  UCOS2_state_inv sg entry ->
  os_int_exit_transfer_source external port sg context entry transfer ->
  before.(SchedState).(isRunning) = true ->
  critical_region_interval critical sg context.(os_int_exit_invocation) before entry ->
  os_int_exit_continuation external port critical sg context before X ->
  task_public_storage sg transfer.(os_int_exit_hooked_state).(TskState) **
  sched_raw_rep sg transfer.(os_int_exit_hooked_state).(TskState)
    (sched_install_selected transfer.(os_int_exit_hooked_state).(SchedState)) **
  UCOS2_raw_rep_missing_task_storage_sched sg transfer.(os_int_exit_hooked_state) **
  task_stack_fragments_rep context.(os_int_exit_handler_stack)
    context.(os_int_exit_handler_fragments) ** unmap_table_rep sg **
  port.(os_int_exit_transferred) context
    (save_token saved context.(os_int_exit_invocation) context.(os_int_exit_origin))
    transfer.(os_int_exit_incoming_stack) transfer.(os_int_exit_incoming_sp)
    transfer.(os_int_exit_incoming_fragments) |--
  os_int_exit_transfer_program_post external port sg context saved entry transfer X.
Proof.
  intros external port critical sg context saved before entry transfer X
    Hvalid Hsource Hrunning Hinterval Hsafe heap Hresources.
  apply (os_int_exit_transfer_post_program_post external port critical sg context
    saved before entry transfer X Hrunning Hinterval Hsafe heap).
  exact (os_int_exit_transfer_resources_merge external port sg context saved
    entry transfer Hvalid Hsource heap Hresources).
Qed.

