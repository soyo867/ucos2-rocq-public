Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The old call program ends at the protected observation.  Error returns
    never call Restore; success preserves that exact observation while the
    actual returned kernel state follows the registered Restore interval. *)
Definition mutex_query_return_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  : program UCOS2_Verify_State Z :=
  fun before code after => exists snapshot,
    mutex_query_call_program critical sg invocation pevent pdata before code snapshot /\
    (if Z.eqb code 0
     then critical_region_interval critical sg invocation snapshot after
     else after = snapshot).

Definition mutex_query_return_post_prop critical sg invocation pevent pdata before code after : Prop :=
  mutex_query_return_program critical sg invocation pevent pdata before code after.

(** Caller-owned output is the protected snapshot, not a fresh query of the
    possibly changed returned state.  The same snapshot is linked to this
    call's original input and to its actual Restore endpoint. *)
Definition mutex_query_return_snapshot (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent pdata : addr)
  (before after : UCOS2_Verify_State) (eid : EventID)
  (current : OSEventAbstractState) (count group : Z) (table : list Z) : Prop :=
  exists snapshot,
    mutex_query_call_program critical sg invocation pevent pdata before 0 snapshot /\
    critical_region_interval critical sg invocation snapshot after /\
    mutex_query_copy_snapshot snapshot eid current count group table.

Lemma mutex_query_return_error : forall critical sg invocation pevent pdata before code after,
  code <> 0 ->
  mutex_query_call_program critical sg invocation pevent pdata before code after ->
  mutex_query_return_program critical sg invocation pevent pdata before code after.
Proof.
  intros; exists after; split; [assumption|].
  assert (Hzero : Z.eqb code 0 = false) by (apply Z.eqb_neq; assumption).
  rewrite Hzero; reflexivity.
Qed.

Lemma mutex_query_return_success : forall critical sg invocation pevent pdata before snapshot after,
  mutex_query_call_program critical sg invocation pevent pdata before 0 snapshot ->
  critical_region_interval critical sg invocation snapshot after ->
  mutex_query_return_program critical sg invocation pevent pdata before 0 after.
Proof. intros; exists snapshot; split; assumption. Qed.

Lemma mutex_query_return_preserves_validity : forall critical sg invocation pevent pdata before code after,
  UCOS2_state_inv sg before ->
  mutex_query_return_program critical sg invocation pevent pdata before code after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pevent pdata before code after Hvalid [snapshot [Hcall Hend]].
  pose proof (mutex_query_call_program_preserves_validity critical sg invocation pevent pdata
    before code snapshot Hvalid Hcall) as Hsnapshot.
  destruct (Z.eqb code 0).
  - exact (proj1 (critical_region_interval_transports_resources
      critical sg invocation snapshot after Hend Hsnapshot)).
  - subst after; exact Hsnapshot.
Qed.

(** Consequence of the existing returned-resource platform boundary.  This
    theorem does not produce an after heap or prove platform instructions:
    the Restore contract must return the physical outside resource at after. *)
Lemma mutex_query_return_restore_consequence :
  forall platform critical sg invocation origin eid mask saved before entry after observed current,
  mutex_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  critical_region_interval critical sg invocation entry after ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation after |--
  mutex_query_closed platform critical sg invocation origin mask after.
Proof.
  intros platform critical sg invocation origin eid mask saved before entry after observed current
    [_ [Hentry [[Hsaved Hmask] _]]] Hinterval.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation entry after Hinterval Hentry)) as Hafter.
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.
