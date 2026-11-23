Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.Bool.Bool.

(** Proof obligation for a REAL registered client, parameterized by the
    chosen invariant. No operation, endpoint guard, state field or memory
    permission is added. In particular a selected-profile certificate does
    not discharge the full-profile instance. Each source client must prove
    that instance from its actual operations before a full-profile caller
    can use it. This is needed by the names-enabled public Event APIs. *)
Definition kernel_client_preserves_resources
  (invariant : StableGlobVars -> UCOS2_Verify_State -> Prop)
  (action : KernelClientAction) : Prop :=
  forall sg before after,
    invariant sg before -> kernel_client_step action sg before after ->
    invariant sg after /\
    (forall observer, kernel_client_actor action <> Some observer ->
      task_creation_frame observer before.(TskState) after.(TskState)) /\
    (forall observer, kernel_client_event_actor action <> Some observer ->
      event_creation_frame observer before.(EventState) after.(EventState)) /\
    (forall observer origin, kernel_client_stops action observer = false ->
      task_invocation_active before.(TskState) observer origin ->
      task_invocation_active after.(TskState) observer origin).

Lemma kernel_client_certificate_preserves_selected_resources : forall action,
  KernelClientCertificate action ->
  kernel_client_preserves_resources UCOS2_state_inv action.
Proof.
  intros action Hcert sg before after Hvalid Hstep.
  split.
  - eapply kernel_client_preserves_validity; eassumption.
  - split.
    + intros observer Hforeign; eapply kernel_client_frames_creation; eassumption.
    + split.
      * intros observer Hforeign; eapply kernel_client_frames_event_creation; eassumption.
      * intros observer origin Hnormal Hactive.
        eapply kernel_client_preserves_continuation; eassumption.
Qed.

(** The SAME trace carries action identity, task/Event actors and the
    retirement outcome. This theorem cannot invent a source trace, a
    physical after heap, a running token or a restored continuation. *)
Lemma kernel_client_resource_trace_transports_invariant :
  forall invariant clients sg observer event_observer before stopped after,
  (forall action, clients action -> kernel_client_preserves_resources invariant action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  invariant sg before ->
  invariant sg after /\
  task_creation_frame observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation before.(EventState) after.(EventState)) /\
  (stopped = false -> forall origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros invariant clients sg observer event_observer before stopped after Hcert Htrace.
  induction Htrace as [s|action before middle after stopped Hin Hforeign HeventForeign Hstep Htail IH];
    intro Hvalid.
  - split; [exact Hvalid|]. split; [reflexivity|]. split; [intros; reflexivity|auto].
  - destruct (Hcert action Hin sg before middle Hvalid Hstep)
      as [Hmiddle [Htask [Hevent Hactive]]].
    destruct (IH Hmiddle) as [Hafter [Hframe [HeventFrame Hresume]]].
    split; [exact Hafter|]. split.
    + unfold task_creation_frame in *; rewrite Hframe; apply Htask; exact Hforeign.
    + split.
      * intros invocation Hobserver; unfold event_creation_frame in *.
        rewrite (HeventFrame invocation Hobserver); apply Hevent; apply HeventForeign; exact Hobserver.
      * intro Hnormal; apply orb_false_iff in Hnormal; destruct Hnormal as [Hfirst Hrest].
        intros origin Hbefore; apply (Hresume Hrest origin).
        apply (Hactive observer origin Hfirst); exact Hbefore.
Qed.

Lemma kernel_resumption_resource_trace_transports_invariant :
  forall invariant clients sg observer event_observer before stopped after,
  (forall action, clients action -> kernel_client_preserves_resources invariant action) ->
  kernel_resumption_resource_trace clients sg observer event_observer before stopped after ->
  invariant sg before ->
  invariant sg after /\
  task_creation_frame observer before.(TskState) after.(TskState) /\
  (forall invocation, event_observer = Some invocation ->
    event_creation_frame invocation before.(EventState) after.(EventState)) /\
  (stopped = false -> forall origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros invariant clients sg observer event_observer before stopped after Hcert Htrace Hvalid.
  eapply kernel_client_resource_trace_transports_invariant; [exact Hcert| |exact Hvalid].
  apply kernel_resumption_resource_trace_erases; exact Htrace.
Qed.

(** The task-only and critical-region views erase only the Event observer.
    They do not silently change the invariant family. The premise below is
    discharged by source-specific instances, not by the selected64 record. *)
Lemma kernel_client_trace_transports_invariant :
  forall invariant clients sg observer before stopped after,
  (forall action, clients action -> kernel_client_preserves_resources invariant action) ->
  kernel_client_trace clients sg observer before stopped after ->
  invariant sg before ->
  invariant sg after /\
  task_creation_frame observer before.(TskState) after.(TskState) /\
  (stopped = false -> forall origin,
    task_invocation_active before.(TskState) observer origin ->
    task_invocation_active after.(TskState) observer origin).
Proof.
  intros invariant clients sg observer before stopped after Hclients Htrace Hbefore.
  destruct (kernel_client_resource_trace_transports_invariant invariant clients sg
    observer None before stopped after Hclients Htrace Hbefore)
    as [Hafter [Htask [_ Hactive]]].
  split; [exact Hafter|]; split; assumption.
Qed.

Lemma critical_region_interval_transports_invariant :
  forall invariant critical sg invocation before after,
  (forall action, critical_region_clients critical action ->
    kernel_client_preserves_resources invariant action) ->
  critical_region_interval critical sg invocation before after ->
  invariant sg before ->
  invariant sg after /\
  task_creation_frame invocation before.(TskState) after.(TskState) /\
  (forall origin, task_invocation_active before.(TskState) invocation origin ->
    task_invocation_active after.(TskState) invocation origin).
Proof.
  intros invariant critical sg invocation before after Hclients Hinterval Hbefore.
  destruct (kernel_client_trace_transports_invariant invariant
    (critical_region_clients critical) sg invocation before false after Hclients
    (critical_region_interval_raw_trace critical sg invocation before after Hinterval)
    Hbefore) as [Hafter [Htask Hactive]].
  split; [exact Hafter|]; split; [exact Htask|exact (Hactive eq_refl)].
Qed.
