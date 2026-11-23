Require Export Ucos2Verify.VC.code.queue.spec.q_create_call_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.event Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Exact-state continuation layer for the existing source-ordered Create
    relation.  Its intermediate allocation and current-pool observations
    remain those of q_create_call_relation: in particular the second pool
    is not the first acquisition's snapshot.  No new execution, heap,
    private-ownership or normal-return producer is asserted by this layer.
    The C consumer must supply the SAME observed endpoint and its resources.

    This is additive support for the current migration.  Until that C
    consumer is installed and checked, these lemmas are not an OSQCreate
    implementation proof and do not replace the historical slice contract. *)
Definition q_create_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (start size : Z)
  (slots : list (option addr)) : program UCOS2_Verify_State addr :=
  q_create_call_relation critical sg invocation start size slots 0.

Definition q_create_safe critical sg invocation start size slots before
  (X : addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (q_create_program critical sg invocation start size slots) X.

Lemma q_create_program_isr_return : forall critical sg invocation start size slots before,
  0 < before.(IntrState).(intNesting) ->
  q_create_program critical sg invocation start size slots before 0 before.
Proof.
  intros critical sg invocation start size slots before Hnesting.
  unfold q_create_program, q_create_call_relation.
  rewrite (proj2 (Z.ltb_lt _ _) Hnesting); split; reflexivity.
Qed.

Lemma q_create_program_no_event_return :
  forall critical sg invocation start size slots before entry detached current,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry None detached ->
  critical_region_interval critical sg invocation detached current ->
  q_create_program critical sg invocation start size slots before 0 current.
Proof.
  intros critical sg invocation start size slots before entry detached current
    Hnesting Henter Hallocate Hrestore.
  unfold q_create_program, q_create_call_relation.
  rewrite (proj2 (Z.ltb_ge _ _) Hnesting).
  exists entry, None, detached; auto.
Qed.

Lemma q_create_program_no_queue_return :
  forall critical sg invocation start size slots before entry eid image detached
    resumed free rolled_back current,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry (Some (eid, image)) detached ->
  q_create_private_interval critical sg invocation eid detached resumed ->
  queue_pool_partition sg resumed.(EventState) free ->
  q_create_reserve_critical sg eid free resumed None rolled_back ->
  critical_region_interval critical sg invocation rolled_back current ->
  q_create_program critical sg invocation start size slots before 0 current.
Proof.
  intros critical sg invocation start size slots before entry eid image detached
    resumed free rolled_back current Hnesting Henter Hallocate Hresume Hpool Hreserve Hrestore.
  unfold q_create_program, q_create_call_relation.
  rewrite (proj2 (Z.ltb_ge _ _) Hnesting).
  exists entry, (Some (eid, image)), detached; split; [exact Henter|].
  split; [exact Hallocate|].
  exists resumed, free, None, rolled_back; auto.
Qed.

Lemma q_create_program_published_return :
  forall critical sg invocation start size slots before entry eid image detached
    resumed free qid reserved initialized allocation publication_free,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry (Some (eid, image)) detached ->
  q_create_private_interval critical sg invocation eid detached resumed ->
  queue_pool_partition sg resumed.(EventState) free ->
  q_create_reserve_critical sg eid free resumed (Some qid) reserved ->
  q_create_private_stores_interleaved critical sg invocation eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames)
      2 0 (qcb_addr sg qid) 0) reserved tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  queue_pool_partition sg initialized.(EventState) publication_free ->
  event_name_valid sg initialized.(NameState)
    (q_create_initialized_event allocation qid start size 0) ->
  q_create_program critical sg invocation start size slots before (event_pool_addr sg eid)
    (replace_EventS (queue_publish initialized.(EventState) eid
      (q_create_initialized_event allocation qid start size 0) qid slots) initialized).
Proof.
  intros critical sg invocation start size slots before entry eid image detached
    resumed free qid reserved initialized allocation publication_free
    Hnesting Henter Hallocate Hresume Hpool Hreserve Hstores Hprivate Hpublication Hname.
  unfold q_create_program, q_create_call_relation.
  rewrite (proj2 (Z.ltb_ge _ _) Hnesting).
  exists entry, (Some (eid, image)), detached; split; [exact Henter|].
  split; [exact Hallocate|].
  exists resumed, free, (Some qid), reserved; split; [exact Hresume|].
  split; [exact Hpool|]; split; [exact Hreserve|].
  exists initialized, allocation, publication_free.
  split; [exact Hstores|]. split; [exact Hprivate|].
  split; [exact Hpublication|]. split; [exact Hname|].
  split; reflexivity.
Qed.

(** The SAME arbitrary X observes the actual returned pointer and current
    kernel state, not a LastSeen equivalence class or a protected snapshot.
    A pure program result still does not produce the caller's heap. *)
Lemma q_create_api_safe_return :
  forall critical sg invocation start size slots before current result X,
  q_create_program critical sg invocation start size slots before result current ->
  q_create_safe critical sg invocation start size slots before X ->
  safeExec (eq current) (StateRelMonad.ret result) X.
Proof.
  intros critical sg invocation start size slots before current result X Hprogram Hsafe.
  unfold q_create_safe in Hsafe.
  eapply (highstependret_derive
    (q_create_program critical sg invocation start size slots) (eq before)
    result (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma q_create_program_preserves_validity :
  forall critical sg invocation start size slots before result current,
  UCOS2_state_inv sg before -> 0 < start -> 0 <= size <= 65535 ->
  q_create_program critical sg invocation start size slots before result current ->
  UCOS2_state_inv sg current.
Proof. intros; eapply q_create_call_preserves_validity; eassumption. Qed.

(** ISR rejection occurs before BOTH Saves. Its program endpoint therefore
    stays at the actual observation, independently of possible endpoints
    in the other source branches. *)
Lemma q_create_program_isr_result_iff :
  forall critical sg invocation start size slots before result current,
  0 < before.(IntrState).(intNesting) ->
  (q_create_program critical sg invocation start size slots before result current <->
   result = 0 /\ current = before).
Proof.
  intros critical sg invocation start size slots before result current Hnesting.
  unfold q_create_program, q_create_call_relation.
  rewrite (proj2 (Z.ltb_lt _ _) Hnesting); reflexivity.
Qed.
