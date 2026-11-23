Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These are the stage-aware interfaces consumed by the actual Del
    annotation carrier. Source coverage is proved separately for each
    concrete Save/Restore/scheduler execution family. In particular a
    contract declaration is not an additional platform behavior law. *)
Definition mutex_del_source_save_pre environment external platform
  (critical : CriticalRegionResources) sg call mask state : Assertion :=
  mutex_del_source_entry environment external platform sg call mask state.

Definition mutex_del_source_restore_pre environment external platform critical
  sg original mask saved acquired checkpoint : Assertion :=
  coq_prop (mutex_del_call_stage original checkpoint) &&
  mutex_del_runtime_restore_pre environment external platform critical sg
    original mask saved acquired checkpoint.

Definition mutex_del_source_return_at environment external platform
  sg original mask returned current : Assertion :=
  coq_prop (mutex_del_call_stage returned current) &&
  mutex_del_runtime_return_at environment external platform sg original mask returned current.

Definition mutex_del_source_return environment external platform sg original mask : Assertion :=
  EX returned current,
    mutex_del_source_return_at environment external platform sg original mask returned current.

(** Del calls OS_Sched only after its real waiting flag requested it.
    That branch excludes the Boot alternative by the critical semantics.
    Readiness is still conditional on the actual nesting guards. *)
Definition mutex_del_source_sched_pre environment external platform
  sg original mask current : Assertion :=
  coq_prop (mutex_del_task_call_stage original current) &&
  mutex_del_runtime_entry environment external platform sg original mask current.

Definition mutex_del_schedule_request (call : OsSchedCallContext) (request : Z) : Prop :=
  request = 1 -> call.(os_sched_call_origin) <> BootInvocation.

Lemma mutex_del_source_save_admission : forall environment external platform critical
  sg call mask state pe eid,
  mutex_del_call_admission call state pe eid ->
  mutex_del_parent_prefix_ok pe state eid ->
  mutex_del_runtime_entry environment external platform sg call mask state |--
  mutex_del_source_save_pre environment external platform critical sg call mask state.
Proof.
  intros environment external platform critical sg call mask state pe eid Hadmission Hprefix.
  unfold mutex_del_source_save_pre, mutex_del_source_entry.
  specialize (Hadmission Hprefix); entailer!.
Qed.

Lemma mutex_del_observation_preserves_call_stage : forall sg eid option result code request
  acquired checkpoint call,
  mutex_del_call_stage call acquired ->
  mutex_del_parent_critical_observation sg eid option result code request acquired checkpoint ->
  mutex_del_call_stage call checkpoint.
Proof.
  intros sg eid option result code request acquired checkpoint call Hstage
    [error [scheduled [Hcritical Hrest]]].
  eapply mutex_del_critical_preserves_call_stage; eassumption.
Qed.

Lemma mutex_del_source_restore_merge : forall environment external platform critical
  sg original mask saved before acquired checkpoint,
  mutex_del_stack_checkpoint sg acquired checkpoint ->
  mutex_del_call_stage original checkpoint ->
  mutex_del_runtime_program_restore_pre platform critical sg original mask saved before acquired checkpoint **
    mutex_del_runtime_acquired environment external platform sg original acquired |--
  mutex_del_source_restore_pre environment external platform critical sg original mask saved acquired checkpoint.
Proof.
  intros; unfold mutex_del_source_restore_pre.
  sep_apply_l_atomic (mutex_del_runtime_program_restore_merge environment external platform
    critical sg original mask saved before acquired checkpoint H).
  entailer!.
Qed.

Lemma mutex_del_source_return_at_forget : forall environment external platform
  sg original mask returned current,
  mutex_del_source_return_at environment external platform sg original mask returned current |--
  mutex_del_runtime_return_at environment external platform sg original mask returned current.
Proof. intros; unfold mutex_del_source_return_at; entailer!. Qed.

Lemma mutex_del_source_return_forget : forall environment external platform sg original mask,
  mutex_del_source_return environment external platform sg original mask |--
  mutex_del_runtime_return environment external platform sg original mask.
Proof.
  intros; unfold mutex_del_source_return, mutex_del_runtime_return; Intros returned current.
  Exists returned current; apply mutex_del_source_return_at_forget.
Qed.

Lemma mutex_del_source_return_open : forall environment external platform sg original mask,
  mutex_del_source_return environment external platform sg original mask |--
  EX returned current,
    coq_prop (kernel_stack_call_same_call returned original) &&
    mutex_del_source_return_at environment external platform sg original mask returned current.
Proof.
  intros; unfold mutex_del_source_return, mutex_del_source_return_at,
    mutex_del_runtime_return_at; Intros returned current selected.
  Exists returned current selected; entailer!.
Qed.

Lemma mutex_del_observation_schedule_request : forall sg eid option result code request
  acquired checkpoint original,
  mutex_del_call_stage original acquired ->
  mutex_del_parent_critical_observation sg eid option result code request acquired checkpoint ->
  mutex_del_schedule_request original request.
Proof.
  intros sg eid option result code request acquired checkpoint original
    Hstage [error [scheduled [Hcritical [Hcode Hrequest]]]] Hrequested Horigin.
  unfold mutex_del_call_stage in Hstage; rewrite Horigin in Hstage.
  pose proof (proj1 (mutex_del_critical_boot_return sg eid option acquired
    (result, (error, scheduled)) checkpoint Hstage Hcritical)) as Hnone.
  simpl in Hnone; subst scheduled; congruence.
Qed.

Lemma mutex_del_source_return_sched_pre : forall environment external platform
  sg original mask returned current,
  mutex_del_schedule_request original 1 ->
  mutex_del_source_return_at environment external platform sg original mask returned current |--
  mutex_del_source_sched_pre environment external platform sg returned mask current.
Proof.
  intros environment external platform sg original mask returned current Hrequest.
  unfold mutex_del_source_return_at; Intros_p Hcurrent.
  assert (Hopen : mutex_del_runtime_return_at environment external platform
      sg original mask returned current |--
    coq_prop (kernel_stack_call_same_call returned original) &&
    mutex_del_runtime_return_at environment external platform sg original mask returned current).
  { unfold mutex_del_runtime_return_at; Intros selected; Exists selected; entailer!. }
  sep_apply_l_atomic Hopen; Intros_p Hsame.
  assert (Htask : mutex_del_task_call_stage returned current).
  { destruct Hsame as [Hi [Ho Hstack]].
    unfold mutex_del_call_stage in Hcurrent.
    destruct returned.(os_sched_call_origin) eqn:Horigin; [|exact Hcurrent].
    exfalso; apply (Hrequest eq_refl); symmetry; exact Ho. }
  unfold mutex_del_source_sched_pre.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_runtime_return_sched_pre.
Qed.
