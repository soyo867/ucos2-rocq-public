Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_source_dispatch_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_unlock_fields_spec.
Require Import Ucos2Verify.lib.kernel_client_invariants.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Coverage of the caller's ACTUAL registry. The CriticalRegionResources
    value, all its clients, spatial resources and existing certificates are
    unchanged. In particular this definition neither widens the registry
    to every source action nor filters an unproved member out of a trace.

    Registration supplies a source classification and its ready proof for
    each member. These are properties of an action's actual source body,
    not requirements about a future Task endpoint. Validity and name-frame
    certificates already belong to the original CriticalRegionResources. *)
Definition tmr_task_registered_source_coverage external (critical : CriticalRegionResources) : Prop :=
  forall action, critical.(critical_region_clients) action ->
    tmr_task_source_client external action /\
    kernel_client_preserves_resources kernel_sched_ready_inv action.

Lemma tmr_task_registered_source_coverage_from_registrations : forall external critical,
  (forall action, critical.(critical_region_clients) action ->
    tmr_task_registered_source_client external action) ->
  tmr_task_registered_source_coverage external critical.
Proof.
  intros external critical Hregistered action Hin.
  destruct (Hregistered action Hin) as [Hsource [_ [_ Hready]]]; split; assumption.
Qed.

Lemma tmr_task_registered_source_coverage_from_sources : forall external critical,
  (forall action, critical.(critical_region_clients) action -> tmr_task_source_client external action) ->
  kernel_sched_ready_clients critical -> tmr_task_registered_source_coverage external critical.
Proof. intros external critical Hsource Hready action Hin; split; auto. Qed.

(** The old certificate package is reusable for a member that the caller
    already registered. This is a statement about that action only; the
    original trace is never reinterpreted under an enlarged registry. *)
Lemma tmr_task_registered_source_member : forall external critical action,
  tmr_task_registered_source_coverage external critical ->
  critical.(critical_region_clients) action -> tmr_task_registered_source_client external action.
Proof.
  intros external critical action Hcoverage Hin.
  destruct (Hcoverage action Hin) as [Hsource Hready].
  split; [exact Hsource|]. split; [exact (critical_region_client_certificates critical action Hin)|].
  split; [|exact Hready].
  intros sg before after Hstep; eapply critical_region_client_name_frame; eassumption.
Qed.

Lemma tmr_task_registered_source_ready_clients : forall external critical,
  tmr_task_registered_source_coverage external critical -> kernel_sched_ready_clients critical.
Proof. intros external critical Hcoverage action Hin; exact (proj2 (Hcoverage action Hin)). Qed.

(** Preserve the caller's registered action family, including its Timer
    source cuts.  The narrower Scheduler-only classification is not required. *)
Lemma tmr_task_registered_source_clients_preserve_initialized : forall external critical sg,
  tmr_task_registered_source_coverage external critical ->
  forall action, critical.(critical_region_clients) action ->
    tmr_task_fields_action_preserves_initialized sg action.
Proof.
  intros external critical sg Hcoverage action Hin.
  eapply tmr_task_source_client_preserves_initialized.
  exact (proj1 (Hcoverage action Hin)).
Qed.

Lemma tmr_task_registered_source_current_clients : forall external critical action,
  tmr_task_registered_source_coverage external critical -> critical.(critical_region_clients) action ->
  kernel_client_preserves_resources os_sched_fields_current_inv action.
Proof.
  intros external critical action Hcoverage Hin sg before after [Hvalid Hcurrent] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action
    (critical_region_client_certificates critical action Hin) sg before after Hvalid Hstep)
    as [Hafter Hframes].
  split; [|exact Hframes]. split; [exact Hafter|].
  eapply tmr_task_source_client_preserves_current_consistency;
    [exact Hvalid|exact (proj1 (Hcoverage action Hin))|exact Hstep|exact Hcurrent].
Qed.

Lemma tmr_task_registered_source_idle_non_idle_clients : forall external critical call action,
  tmr_task_registered_source_coverage external critical -> critical.(critical_region_clients) action ->
  kernel_client_preserves_resources (os_sched_fields_running_idle_non_idle_inv call) action.
Proof.
  intros external critical call action Hcoverage Hin sg before after
    [Hvalid [Hrunning [Hidle Hnonidle]]] Hstep.
  pose proof (proj1 (Hcoverage action Hin)) as Hsource.
  destruct (kernel_client_certificate_preserves_selected_resources action
    (critical_region_client_certificates critical action Hin) sg before after Hvalid Hstep)
    as [Hafter Hframes].
  destruct (tmr_task_source_client_preserves_idle_non_idle external action sg call before after
    Hvalid Hafter Hrunning Hsource Hstep) as [Hidle' Hnonidle'].
  split; [|exact Hframes]. split; [exact Hafter|]. split.
  - rewrite (tmr_task_source_client_running_eq external action sg before after Hvalid Hsource Hstep); exact Hrunning.
  - split; [apply Hidle'; exact Hidle|apply Hnonidle'; exact Hnonidle].
Qed.

Lemma tmr_task_registered_source_clear_clients : forall external critical call action,
  tmr_task_registered_source_coverage external critical -> critical.(critical_region_clients) action ->
  kernel_client_preserves_resources (os_sched_fields_clear_inv call) action.
Proof.
  intros external critical call action Hcoverage Hin sg before after
    [Hvalid [node [Hnode [Hclear Hflag]]]] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action
    (critical_region_client_certificates critical action Hin) sg before after Hvalid Hstep)
    as [Hafter Hframes].
  split; [|exact Hframes]. split; [exact Hafter|].
  eapply tmr_task_source_client_preserves_clear;
    [exact Hvalid|exact (proj1 (Hcoverage action Hin))|exact Hstep|exact Hnode|exact Hclear|exact Hflag].
Qed.

Lemma tmr_task_registered_source_unlock_clients : forall external critical call,
  tmr_task_registered_source_coverage external critical -> tmr_task_unlock_registered_clients critical call.
Proof.
  intros external critical call Hcoverage; split.
  - intros action Hin; eapply tmr_task_registered_source_current_clients; eassumption.
  - split; intros action Hin.
    + eapply tmr_task_registered_source_idle_non_idle_clients; eassumption.
    + eapply tmr_task_registered_source_clear_clients; eassumption.
Qed.

(** A Task-owned caller can discharge the specialized Unlock registration
    part from its existing registry without changing the generic same-X
    safeExec or the real current heap. Only the six current observations
    required by this Task instance remain to be supplied at this call. *)
Lemma tmr_task_registered_source_unlock_pre : forall external environment critical local sg call mask before X,
  tmr_task_registered_source_coverage external critical -> tmr_task_unlock_entry sg call before ->
  os_sched_unlock_fields_pre environment critical local sg call mask before X |--
  tmr_task_unlock_fields_pre environment critical local sg call mask before X.
Proof.
  intros external environment critical local sg call mask before X Hcoverage Hentry heap Howned.
  split; [split; [exact Hentry|eapply tmr_task_registered_source_unlock_clients; exact Hcoverage]|exact Howned].
Qed.
