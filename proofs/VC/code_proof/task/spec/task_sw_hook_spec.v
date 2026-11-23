Require Export Ucos2Verify.VC.code.task.spec.app_task_sw_hook_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.

(** Fixed ARMv7-A wrapper: App/CPU/Switch hooks enabled; the selected App
    hook is the independently checked empty leaf; TRACE is disabled and
    OS_CFG_DBG_EN is undefined in the pinned include/profile. The original
    directives remain in the C carrier. This relation belongs only to that
    source instance, and is not a guarantee for arbitrary external hooks. *)
Definition task_sw_hook_step (sg : StableGlobVars)
  (before after : UCOS2_Verify_State) : Prop :=
  app_task_sw_hook_step sg before after.

Lemma task_sw_hook_step_of_app : forall sg before after,
  app_task_sw_hook_step sg before after -> task_sw_hook_step sg before after.
Proof. intros; exact H. Qed.

Definition task_sw_hook_client : KernelClientAction :=
  {| kernel_client_actor := None;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := task_sw_hook_step |}.

Lemma task_sw_hook_client_certificate : KernelClientCertificate task_sw_hook_client.
Proof.
  constructor; cbn; unfold task_sw_hook_step, app_task_sw_hook_step;
    intros; subst; assumption || reflexivity.
Qed.

(** A static selected implementation. The architecture relations are copied
    from the chosen port; dependent continuation ABIs must be constructed
    for this external instance, never silently transported from another. *)
Definition task_sw_hook_external (external : OsSchedExternalResources) : OsSchedExternalResources :=
  {| os_sched_arch_running := external.(os_sched_arch_running);
     os_sched_arch_save_source := external.(os_sched_arch_save_source);
     os_sched_arch_restore_source := external.(os_sched_arch_restore_source);
     os_sched_arch_resume_source := external.(os_sched_arch_resume_source);
     os_sched_hook_action := task_sw_hook_client;
     os_sched_hook_certificate := task_sw_hook_client_certificate |}.

Definition task_sw_hook_source_binding (external : OsSchedExternalResources) : Prop :=
  external.(os_sched_hook_action) = task_sw_hook_client.

Lemma task_sw_hook_external_source_binding : forall external,
  task_sw_hook_source_binding (task_sw_hook_external external).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_external_step : forall external sg state,
  kernel_client_step (task_sw_hook_external external).(os_sched_hook_action) sg state state.
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_external_stops_false : forall external invocation,
  kernel_client_stops (task_sw_hook_external external).(os_sched_hook_action) invocation = false.
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_bound_step : forall external sg before after,
  task_sw_hook_source_binding external -> task_sw_hook_step sg before after ->
  kernel_client_step external.(os_sched_hook_action) sg before after.
Proof. intros external sg before after Hbinding Hstep; unfold task_sw_hook_source_binding in Hbinding.
  rewrite Hbinding; exact Hstep. Qed.

(** Architecture parameters remain exactly the chosen ones. *)
Lemma task_sw_hook_external_arch_running_eq : forall external,
  (task_sw_hook_external external).(os_sched_arch_running) =
    external.(os_sched_arch_running).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_external_arch_save_source_eq : forall external,
  (task_sw_hook_external external).(os_sched_arch_save_source) =
    external.(os_sched_arch_save_source).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_external_arch_restore_source_eq : forall external,
  (task_sw_hook_external external).(os_sched_arch_restore_source) =
    external.(os_sched_arch_restore_source).
Proof. intros; reflexivity. Qed.

Lemma task_sw_hook_external_arch_resume_source_eq : forall external,
  (task_sw_hook_external external).(os_sched_arch_resume_source) =
    external.(os_sched_arch_resume_source).
Proof. intros; reflexivity. Qed.

