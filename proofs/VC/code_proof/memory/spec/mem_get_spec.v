Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.memory.
Require Export Ucos2Verify.lib.memory_execution.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.

Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope Z_scope.

(** Two source-readable inputs.  Raw storage is caller-owned and carries
    the head-word permission only on the positive-count arm.  The pool
    view instead obtains its control and blocks from the acquired kernel.
    In particular raw images are not required to be initialized pools. *)
Inductive MemGetView : Type :=
| MemGetRaw (image : MemoryControlImage) (next : addr)
| MemGetPool (id : MemID).

Inductive MemGetAccess : Type :=
| MemGetRawAccess (image : MemoryControlImage) (next : addr)
| MemGetPoolAccess (id : MemID) (partition : MemoryPartitionState).

Record MemGetOutcome : Type := {
  mem_get_pointer : addr;
  mem_get_error : Z;
  mem_get_released_loan : option (MemoryPartitionState * MemoryBlockLoan)
}.

Definition mem_get_null_outcome : MemGetOutcome :=
  {| mem_get_pointer := 0; mem_get_error := 96; mem_get_released_loan := None |}.
Definition mem_get_empty_outcome : MemGetOutcome :=
  {| mem_get_pointer := 0; mem_get_error := 93; mem_get_released_loan := None |}.

Definition mem_get_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgMemoryEnabled) = true /\
  sg.(osKernelConfig).(cfgMemoryNames) = true.

(** The caller's C-environment protocol, not a CPU promise.  These shapes
    are the canonical runtime Memory transformers: an unchanged module,
    replacement of an existing/allocated slot by Some, private reservation,
    or publication.  None deletes an initialized partition.  OS_MemInit is
    a boot reset and is deliberately not a runtime access step.  NameSet
    has no registered whole-operation transformer here; its future producer
    must establish the same shape from its actual writes. *)
Inductive mem_get_memory_access_step : GlobMemoryState -> GlobMemoryState -> Prop :=
| mem_get_memory_access_unchanged : forall s,
    mem_get_memory_access_step s s
| mem_get_memory_access_replace : forall s id partition,
    mem_get_memory_access_step s (memory_replace_partition s id partition)
| mem_get_memory_access_reserve : forall s base extent size count private post,
    memory_reserve_control s base extent size count = Some (private, post) ->
    mem_get_memory_access_step s post
| mem_get_memory_access_publish : forall s private,
    mem_get_memory_access_step s (memory_publish_control s private).

Lemma mem_get_memory_access_get : forall s id loan post,
  memory_get s id = Some (loan, post) -> mem_get_memory_access_step s post.
Proof.
  intros s id loan post H; unfold memory_get in H.
  destruct (memPartitions s id) as [p|]; [|discriminate].
  destruct (memory_get_partition id p) as [[l q]|]; [|discriminate].
  inversion H; subst; constructor.
Qed.

Lemma mem_get_memory_access_put : forall s id block post,
  memory_put s id block = Some post -> mem_get_memory_access_step s post.
Proof.
  intros s id block post H; unfold memory_put in H.
  destruct (memPartitions s id); [|discriminate].
  inversion H; subst; constructor.
Qed.

Lemma mem_get_memory_access_preserves_lookup : forall before after id previous,
  mem_get_memory_access_step before after ->
  before.(memPartitions) id = Some previous ->
  exists current, after.(memPartitions) id = Some current.
Proof.
  intros before after id previous Hstep Hlookup; destruct Hstep.
  - eauto.
  - unfold memory_replace_partition; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec id id0); eauto.
  - unfold memory_reserve_control in H.
    destruct (memFreeControls s) as [|i rest]; [discriminate|].
    destruct (memControlImages s i); [|discriminate].
    inversion H; subst; simpl; eauto.
  - unfold memory_publish_control; simpl; unfold kernel_map_set.
    destruct (Z.eq_dec id (memPrivateSlot private)); eauto.
Qed.

Definition mem_get_client_access_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) : Prop :=
  forall action before after,
    critical_region_clients critical action ->
    kernel_client_actor action <> Some invocation ->
    kernel_client_step action sg before after ->
    mem_get_memory_access_step before.(MemoryState) after.(MemoryState).

Lemma mem_get_task_creation_access : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  mem_get_memory_access_step before.(MemoryState) after.(MemoryState).
Proof. intros action sg before after [_ [_ ->]]; destruct action; constructor. Qed.

Lemma mem_get_access_protocol_task_creation_clients : forall critical sg invocation,
  (forall action, critical_region_clients critical action -> task_creation_client_family action) ->
  mem_get_client_access_protocol critical sg invocation.
Proof.
  intros critical sg invocation Hfamily action before after Hin Hforeign Hstep.
  destruct (Hfamily action Hin) as [source ->].
  eapply mem_get_task_creation_access; exact Hstep.
Qed.

Lemma mem_get_interval_preserves_lookup : forall critical sg invocation before entry id previous,
  mem_get_client_access_protocol critical sg invocation ->
  critical_region_interval critical sg invocation before entry ->
  before.(MemoryState).(memPartitions) id = Some previous ->
  exists current, entry.(MemoryState).(memPartitions) id = Some current.
Proof.
  intros critical sg invocation before entry id previous Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval; revert previous.
  induction Hinterval as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hlookup.
  - eauto.
  - destruct (mem_get_memory_access_preserves_lookup _ _ id previous
      (Hprotocol action before middle Hin Hforeign Hstep) Hlookup) as [current Hcurrent].
    apply (IH current Hcurrent).
Qed.

Lemma mem_get_initialization_resets_lookup : forall sg name id,
  (memory_initial sg name).(memPartitions) id = None.
Proof. reflexivity. Qed.

Definition mem_get_access_image (access : MemGetAccess) : MemoryControlImage :=
  match access with
  | MemGetRawAccess image _ => image
  | MemGetPoolAccess _ partition => memory_partition_image partition
  end.
Definition mem_get_access_next (access : MemGetAccess) : addr :=
  match access with
  | MemGetRawAccess _ next => next
  | MemGetPoolAccess _ p => memory_free_head p (tl p.(memFreeBlocks))
  end.
Definition mem_get_access_matches (sg : StableGlobVars) (view : MemGetView)
  (pmem : addr) (entry : UCOS2_Verify_State) (access : MemGetAccess) : Prop :=
  match view, access with
  | MemGetRaw image next, MemGetRawAccess observed link => image = observed /\ next = link
  | MemGetPool id, MemGetPoolAccess current p =>
      id = current /\ pmem = memory_control_addr sg id /\
      entry.(MemoryState).(memPartitions) id = Some p
  | _, _ => False
  end.
Definition mem_get_access_outcome (access : MemGetAccess) : MemGetOutcome :=
  match access with
  | MemGetRawAccess image _ =>
      if 0 <? image.(memImageNFree) then
        {| mem_get_pointer := image.(memImageFree); mem_get_error := 0;
           mem_get_released_loan := None |}
      else mem_get_empty_outcome
  | MemGetPoolAccess id p =>
      match memory_get_partition id p with
      | None => mem_get_empty_outcome
      | Some (loan, post) =>
          {| mem_get_pointer := memory_free_head p p.(memFreeBlocks); mem_get_error := 0;
             mem_get_released_loan := Some (post, loan) |}
      end
  end.
Definition mem_get_access_checkpoint (entry : UCOS2_Verify_State)
  (access : MemGetAccess) : UCOS2_Verify_State :=
  match access with
  | MemGetRawAccess _ _ => entry
  | MemGetPoolAccess id p =>
      match memory_get_partition id p with
      | None => entry
      | Some (_, post) => replace_MemoryS (memory_replace_partition entry.(MemoryState) id post) entry
      end
  end.

Definition mem_get_protected (sg : StableGlobVars) (view : MemGetView) (pmem : addr)
  : program UCOS2_Verify_State MemGetOutcome :=
  fun entry outcome checkpoint => exists access,
    mem_get_access_matches sg view pmem entry access /\
    outcome = mem_get_access_outcome access /\ checkpoint = mem_get_access_checkpoint entry access.

Definition mem_get_program (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (view : MemGetView) (pmem : addr)
  : program UCOS2_Verify_State MemGetOutcome :=
  if Z.eqb pmem 0 then StateRelMonad.ret mem_get_null_outcome
  else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (mem_get_protected sg view pmem)
      (fun outcome => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret outcome))).

Definition mem_get_safe critical sg invocation view pmem before
  (X : MemGetOutcome -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (mem_get_program critical sg invocation view pmem) X.
Definition mem_get_return_safe current outcome
  (X : MemGetOutcome -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq current) (StateRelMonad.ret outcome) X.

Lemma mem_get_program_null : forall critical sg invocation view before,
  mem_get_program critical sg invocation view 0 before mem_get_null_outcome before.
Proof. intros; unfold mem_get_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma mem_get_program_restored : forall critical sg invocation view pmem before entry outcome checkpoint current,
  pmem <> 0 -> critical_region_interval critical sg invocation before entry ->
  mem_get_protected sg view pmem entry outcome checkpoint ->
  critical_region_interval critical sg invocation checkpoint current ->
  mem_get_program critical sg invocation view pmem before outcome current.
Proof.
  intros critical sg invocation view pmem before entry outcome checkpoint current Hpmem Hentry Hstep Hcurrent.
  unfold mem_get_program; rewrite (proj2 (Z.eqb_neq _ _) Hpmem).
  unfold StateRelMonad.bind; exists tt, entry; split; [exact Hentry|].
  exists outcome, checkpoint; split; [exact Hstep|].
  exists tt, current; split; [exact Hcurrent|]; split; reflexivity.
Qed.

Lemma mem_get_safe_return : forall critical sg invocation view pmem before outcome current X,
  mem_get_program critical sg invocation view pmem before outcome current ->
  mem_get_safe critical sg invocation view pmem before X ->
  mem_get_return_safe current outcome X.
Proof.
  intros critical sg invocation view pmem before outcome current X Hprogram Hsafe.
  unfold mem_get_safe in Hsafe; unfold mem_get_return_safe.
  eapply (highstependret_derive (mem_get_program critical sg invocation view pmem)
    (eq before) outcome (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Definition mem_get_call_domain (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (view : MemGetView) (pmem : addr) (before : UCOS2_Verify_State) : Prop :=
  pmem = 0 \/ (pmem <> 0 /\ match view with
  | MemGetRaw _ _ => True
  | MemGetPool id => pmem = memory_control_addr sg id /\
      (exists p, before.(MemoryState).(memPartitions) id = Some p) /\
      mem_get_client_access_protocol critical sg invocation
  end).

Definition mem_get_raw_head (image : MemoryControlImage) (next : addr) : Assertion :=
  if 0 <? image.(memImageNFree) then image.(memImageFree) # Ptr |-> next else emp.
Definition mem_get_input_resources (sg : StableGlobVars) (view : MemGetView) (pmem : addr) : Assertion :=
  if Z.eqb pmem 0 then emp else match view with
  | MemGetRaw image next => store_memory_control sg pmem image ** mem_get_raw_head image next
  | MemGetPool _ => emp
  end.

Definition mem_get_control_frame (sg : StableGlobVars) (pmem : addr)
  (entry : UCOS2_Verify_State) (access : MemGetAccess) : Assertion :=
  match access with
  | MemGetRawAccess image next => memory_control_without_free_fields sg pmem image **
      mem_get_raw_head image next ** UCOS2_inv sg entry
  | MemGetPoolAccess id p => memory_control_without_free_fields sg pmem (memory_partition_image p) **
      store_memory_free_blocks p p.(memFreeBlocks) **
      memory_raw_rep_without_partition sg entry.(MemoryState) id ** UCOS2_raw_rep_missing_memory sg entry
  end.

Definition mem_get_success_frame (sg : StableGlobVars) (pmem : addr)
  (entry : UCOS2_Verify_State) (access : MemGetAccess) : Assertion :=
  match access with
  | MemGetRawAccess image _ => memory_control_without_free_fields sg pmem image ** UCOS2_inv sg entry
  | MemGetPoolAccess id p =>
      memory_control_without_free_fields sg pmem (memory_partition_image p) **
      (match p.(memFreeBlocks) with [] => emp | block :: rest =>
        memory_block_tail p block ** store_memory_free_blocks p rest end) **
      memory_raw_rep_without_partition sg entry.(MemoryState) id ** UCOS2_raw_rep_missing_memory sg entry
  end.

Definition mem_get_raw_after (image : MemoryControlImage) (next : addr) : MemoryControlImage :=
  if 0 <? image.(memImageNFree) then memory_get_image image next else image.

(** The initialized loan is indexed by the RELEASE partition returned by
    memory_get_resources_merge.  The physical block is framed through the
    actual Restore.  No equality with the final world's allocation map is
    claimed, and the payload is neither cleared nor initialized. *)
Definition mem_get_outcome_resources (sg : StableGlobVars) (view : MemGetView)
  (pmem : addr) (outcome : MemGetOutcome) : Assertion :=
  if Z.eqb pmem 0 then emp else match view with
  | MemGetRaw image next => store_memory_control sg pmem (mem_get_raw_after image next) **
      mem_get_raw_head image next
  | MemGetPool _ => match outcome.(mem_get_released_loan) with
      | None => emp | Some (partition, loan) => memory_block_loan partition loan end
  end.

Definition mem_get_api_post (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (view : MemGetView) (pmem perr : addr) (before : UCOS2_Verify_State) (pointer : addr)
  (X : MemGetOutcome -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX outcome current, coq_prop (pointer = outcome.(mem_get_pointer) /\
    mem_get_program critical sg invocation view pmem before outcome current /\
    mem_get_return_safe current outcome X) &&
    (mutex_query_closed platform critical sg invocation origin mask current **
     perr # UChar |-> outcome.(mem_get_error) ** mem_get_outcome_resources sg view pmem outcome).

Lemma mem_get_call_domain_acquired : forall critical sg invocation view pmem before entry,
  mem_get_call_domain critical sg invocation view pmem before -> pmem <> 0 ->
  critical_region_interval critical sg invocation before entry ->
  exists access, mem_get_access_matches sg view pmem entry access.
Proof.
  intros critical sg invocation view pmem before entry Hdomain Hpmem Hinterval.
  destruct Hdomain as [Hnull|[_ Hview]]; [contradiction|].
  destruct view as [image next|id].
  - exists (MemGetRawAccess image next); split; reflexivity.
  - destruct Hview as [Haddr [[previous Hlookup] Hprotocol]].
    destruct (mem_get_interval_preserves_lookup critical sg invocation before entry id previous
      Hprotocol Hinterval Hlookup) as [current Hcurrent].
    exists (MemGetPoolAccess id current); simpl; auto.
Qed.

Lemma mem_get_program_has_result : forall critical sg invocation view pmem before,
  mem_get_call_domain critical sg invocation view pmem before ->
  exists outcome current, mem_get_program critical sg invocation view pmem before outcome current.
Proof.
  intros critical sg invocation view pmem before Hdomain.
  destruct (Z.eq_dec pmem 0) as [->|Hpmem].
  - exists mem_get_null_outcome, before; apply mem_get_program_null.
  - assert (Hrefl : critical_region_interval critical sg invocation before before) by constructor.
    destruct (mem_get_call_domain_acquired critical sg invocation view pmem before before
      Hdomain Hpmem Hrefl) as [access Haccess].
    exists (mem_get_access_outcome access), (mem_get_access_checkpoint before access).
    eapply mem_get_program_restored with (entry := before)
      (checkpoint := mem_get_access_checkpoint before access); try assumption; [|constructor].
    exists access; repeat split; assumption || reflexivity.
Qed.
