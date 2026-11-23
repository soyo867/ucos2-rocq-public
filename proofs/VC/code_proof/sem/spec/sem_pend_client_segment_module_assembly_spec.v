Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_critical_c_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_scoped_c_environment_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_body_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_return_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_selected_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_observed_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_critical_restore_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_c_sequence_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_module_assembly_spec.
Import UCOS2_C_Rules TaskStateDef DeleteComponent CriticalComponent.
Import SelectedEnvironmentCProgram.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Open the Delete producer's one existential once.  Its new outer body
    sequence and the source on that sequence are mapped together; its
    original inner window executions and recycled owner are retained. *)
Lemma sem_pend_module_delete_body :
  forall observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    (source : sem_pend_delete_call_source None observer stored_origin capture body_heap
      restore_selected restore_rely save_selected save_rely restore_stopped save_stopped),
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  inputs.(delete_capture_acquired).(TskState).(taskLifecycle).(taskInvocations) observer = Some stored_origin ->
  exists run : kernel_c_sequence
    (kernel_program_environment_c_step inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) observer stored_origin)
    inputs.(delete_capture_acquired) restore.(delete_restore_before_heap) (task_delete_capture_before_owner inputs)
    (task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped)
    (task_delete_capture_cut capture) body_heap (task_delete_capture_recycled_owner capture),
  sem_pend_client_module_run inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer stored_origin _ _ _ _ _ _ _ run
    inputs.(delete_capture_first).(os_sched_call_origin) capture.(delete_save_returned).(os_sched_call_origin) /\
  task_delete_capture_recycled_owner capture body_heap.
Proof.
  intros observer stored_origin capture body_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped source restore inputs Hregistered.
  destruct (sem_pend_delete_body_call_source None observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped source Hregistered)
    as [body_run [Hsource [Htrace Howner]]].
  exists (sem_pend_module_program_sequence inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer stored_origin _ _ _ _ _ _ _ body_run).
  split; [eapply sem_pend_module_program_observation; eassumption|exact Howner].
Qed.

(** The existing acquired Critical factory has already chosen its literal
    included run.  Keep that very run: no second inclusion or decoder is
    introduced.  The same returned source supplies the observed trace and
    remains paired with the actual API owner, including Generic callers. *)
Lemma sem_pend_module_critical_completion :
  forall environment critical local sg frame call before after observed,
  critical.(critical_region_clients) (sem_pend_critical_call_action call) ->
  kernel_critical_c_completion environment critical local sg frame call before after ->
  exists run : kernel_c_sequence (kernel_program_c_step environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin))
    (kernel_critical_c_entry call) before
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_entry call) ** frame)
    false (kernel_critical_c_returned call) after
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame),
    let included := sem_pend_selected_environment_sequence environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ run in
    sem_pend_client_module_run environment critical sg
      observed.(os_sched_call_invocation) observed.(os_sched_call_origin) _ _ _ _ _ _ _ included
      observed.(os_sched_call_origin) observed.(os_sched_call_origin) /\
    sem_pend_client_return_source environment critical sg observed (kernel_critical_c_entry call)
      observed (kernel_critical_c_returned call) /\
    (kernel_critical_c_owner environment critical local sg call (kernel_critical_c_returned call) ** frame) after.
Proof.
  intros environment critical local sg frame call before after observed Hmember Hcompletion.
  destruct (sem_pend_critical_completion_call_attachment environment critical local sg frame call
    before after observed Hmember Hcompletion) as [run [Hsource [Hcalls [Hreturn Howner]]]].
  exists run; split.
  - split; [exact Hsource|exact (proj1 Hreturn)].
  - exact (conj Hreturn Howner).
Qed.
