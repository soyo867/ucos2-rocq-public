Require Import Coq.ZArith.ZArith Coq.Bool.Bool.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.task.spec.task_del_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_del_c_segment_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_sequence_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_c_program_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_delete_call_source_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_observer_frame_spec.
Import UCOS2_C_Rules TaskStateDef DeleteComponent.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This private factory assembles a new outer sequence at the actual
    capture cut. It never receives or converts the old opaque body proof.
    Each inner joint run is taken unchanged from its indexed attachment,
    together with the original selection/owned witnesses. *)
Local Definition sem_pend_delete_joint_run_source :
  forall event_observer environment critical saved_local sg observer origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped
    (window : task_delete_joint_c_window environment critical saved_local sg
      (kernel_program_c_step environment critical sg observer origin) selected requested rely
      phase loan original before returned after mask before_heap after_heap frame history stopped),
  sem_pend_delete_joint_window_receipt event_observer environment critical saved_local sg observer origin
    selected requested rely phase loan original before returned after mask before_heap after_heap frame history stopped window ->
  exists run : kernel_c_sequence (kernel_program_c_step environment critical sg observer origin)
    before before_heap (task_delete_call_closed environment saved_local phase loan sg original mask before ** frame)
    stopped after after_heap (task_delete_call_closed environment saved_local phase loan sg returned mask after ** frame),
  kernel_program_c_sequence_call_source environment critical sg observer origin event_observer
    _ _ _ _ _ _ _ run.
Proof.
  intros event_observer environment critical saved_local sg observer origin selected requested rely
    phase loan original before returned after mask before_heap after_heap frame history stopped window Hreceipt.
  destruct Hreceipt.
  exists run; assumption.
Defined.

Local Definition sem_pend_delete_restore_run_source :
  forall event_observer observer origin restore selected rely stopped window,
  sem_pend_delete_restore_window_receipt event_observer observer origin restore selected rely stopped window ->
  let inputs := restore.(delete_restore_inputs) in
  exists run : kernel_c_sequence
    (kernel_program_c_step inputs.(delete_capture_environment) inputs.(delete_capture_critical)
      inputs.(delete_capture_globals) observer origin)
    (task_delete_locked inputs.(delete_capture_prepared)) restore.(delete_restore_prepared_heap)
    (task_delete_capture_prepared_owner inputs) stopped
    restore.(delete_restore_between) restore.(delete_restore_middle_heap)
    (task_delete_capture_middle_owner inputs restore.(delete_restore_middle) restore.(delete_restore_between)),
  kernel_program_c_sequence_call_source inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer origin event_observer _ _ _ _ _ _ _ run.
Proof.
  intros event_observer observer origin restore selected rely stopped window Hreceipt inputs.
  destruct Hreceipt as [prefix_heap environment_heap prefix joint suffix Hjoint].
  destruct (sem_pend_delete_joint_run_source event_observer _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ joint Hjoint) as [joint_run Hsource].
  replace stopped with (orb false (orb stopped false)) by (rewrite Bool.orb_false_r; reflexivity).
  eexists; unfold kernel_program_c_sequence_call_source.
  eapply KernelCSourceThen with (first_stopped := false) (last_stopped := orb stopped false)
    (bridge := fun heap owned => owned).
  - apply KernelCSourceAtom; right;
      exact (KernelProgramCDeletePrimitiveSource _ _ _ _ _ _ _ _ _ _ _ _ prefix).
  - eapply KernelCSourceThen with (first_stopped := stopped) (last_stopped := false)
      (bridge := fun heap owned => owned); [exact Hsource|].
    apply KernelCSourceAtom; right;
      exact (KernelProgramCDeletePrimitiveSource _ _ _ _ _ _ _ _ _ _ _ _ suffix).
Defined.

Local Definition sem_pend_delete_save_run_source :
  forall event_observer observer origin capture selected rely stopped window,
  sem_pend_delete_save_window_receipt event_observer observer origin capture selected rely stopped window ->
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  exists run : kernel_c_sequence (task_delete_program_segment observer origin capture)
    restore.(delete_restore_between) restore.(delete_restore_middle_heap)
    (task_delete_capture_middle_owner inputs restore.(delete_restore_middle) restore.(delete_restore_between)) stopped
    capture.(delete_save_resumed) capture.(delete_save_resumed_heap)
    (task_delete_capture_resumed_owner restore capture.(delete_save_saved) capture.(delete_save_returned)
      capture.(delete_save_resumed)),
  kernel_program_c_sequence_call_source inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer origin event_observer _ _ _ _ _ _ _ run.
Proof.
  intros event_observer observer origin capture selected rely stopped window Hreceipt restore inputs.
  destruct Hreceipt as [environment_heap joint suffix saved_restore saved_inputs Hjoint].
  destruct (sem_pend_delete_joint_run_source event_observer _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ joint Hjoint) as [joint_run Hsource].
  replace stopped with (orb stopped false) by apply Bool.orb_false_r.
  eexists; unfold kernel_program_c_sequence_call_source.
  eapply KernelCSourceThen with (first_stopped := stopped) (last_stopped := false)
    (bridge := fun heap owned => owned); [exact Hsource|].
  apply KernelCSourceAtom; right;
    exact (KernelProgramCDeletePrimitiveSource _ _ _ _ _ _ _ _ _ _ _ _ suffix).
Defined.

(** The fixed four-part body is built forward once: actual Prepare,
    original Restore window, original Save window, actual Recycle. The
    dependent result couples this newly assembled run with its own source;
    no proof equality with [sem_pend_delete_call_run] is asserted. *)
Local Definition sem_pend_delete_captured_run_source :
  forall event_observer observer origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    (source : sem_pend_delete_call_source event_observer observer origin capture body_heap
      restore_selected restore_rely save_selected save_rely restore_stopped save_stopped),
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  exists run : kernel_c_sequence (task_delete_program_segment observer origin capture)
    inputs.(delete_capture_acquired) restore.(delete_restore_before_heap)
    (task_delete_capture_before_owner inputs)
    (task_delete_capture_observer_stopped capture origin restore_stopped save_stopped)
    (task_delete_capture_cut capture) body_heap (task_delete_capture_recycled_owner capture),
  kernel_program_c_sequence_call_source inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer origin event_observer _ _ _ _ _ _ _ run.
Proof.
  intros event_observer observer origin capture body_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped source restore inputs.
  destruct (sem_pend_delete_restore_run_source event_observer observer origin restore restore_selected restore_rely
    restore_stopped (sem_pend_delete_restore_window event_observer _ _ _ _ _ _ _ _ _ _ source)
    (sem_pend_delete_restore_receipt event_observer _ _ _ _ _ _ _ _ _ _ source)) as [restore_run Hrestore].
  destruct (sem_pend_delete_save_run_source event_observer observer origin capture save_selected save_rely
    save_stopped (sem_pend_delete_save_window event_observer _ _ _ _ _ _ _ _ _ _ source)
    (sem_pend_delete_save_receipt event_observer _ _ _ _ _ _ _ _ _ _ source)) as [save_run Hsave].
  assert (Hprepare : task_delete_own_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer origin
    inputs.(delete_capture_acquired) restore.(delete_restore_before_heap) (task_delete_capture_before_owner inputs) false
    (task_delete_locked inputs.(delete_capture_prepared)) restore.(delete_restore_prepared_heap)
    (task_delete_capture_prepared_owner inputs)).
  { apply TaskDeleteCPrepare; [repeat split; reflexivity|apply task_delete_restore_capture_prepare_completion]. }
  assert (Hrecycle : task_delete_own_c_segment inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer origin capture.(delete_save_resumed) capture.(delete_save_resumed_heap)
    (task_delete_capture_resumed_owner restore capture.(delete_save_saved) capture.(delete_save_returned) capture.(delete_save_resumed))
    (task_delete_recycle_stops_origin inputs.(delete_capture_tid) origin)
    (task_delete_capture_cut capture) body_heap (task_delete_capture_recycled_owner capture)).
  { apply TaskDeleteCRecycle; [repeat split; reflexivity|].
    exact (sem_pend_delete_body_completed event_observer _ _ _ _ _ _ _ _ _ _ source). }
  pose (prepare_run := KernelCSequenceAtom _ _ _ _ _ _ _ _
    (KernelProgramCDelete _ _ _ _ _ _ _ _ _ _ _ _ Hprepare)).
  pose (recycle_run := KernelCSequenceAtom _ _ _ _ _ _ _ _
    (KernelProgramCDelete _ _ _ _ _ _ _ _ _ _ _ _ Hrecycle)).
  pose (save_tail := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    save_run (fun heap owned => owned) recycle_run).
  pose (restore_tail := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    restore_run (fun heap owned => owned) save_tail).
  pose (body_run := KernelCSequenceThen _ _ _ _ _ _ _ _ _ _ _ _ _
    prepare_run (fun heap owned => owned) restore_tail).
  exists body_run.
  unfold body_run, restore_tail, save_tail, prepare_run, recycle_run, kernel_program_c_sequence_call_source.
  eapply KernelCSourceThen with (first_stopped := false)
    (last_stopped := orb restore_stopped (orb save_stopped (task_delete_recycle_stops_origin inputs.(delete_capture_tid) origin)))
    (bridge := fun heap owned => owned).
  - apply KernelCSourceAtom; right; exact (KernelProgramCDeleteSource _ _ _ _ _ _ _ _ _ _ _ _ Hprepare).
  - eapply KernelCSourceThen with (first_stopped := restore_stopped)
      (last_stopped := orb save_stopped (task_delete_recycle_stops_origin inputs.(delete_capture_tid) origin))
      (bridge := fun heap owned => owned); [exact Hrestore|].
    eapply KernelCSourceThen with (first_stopped := save_stopped)
      (last_stopped := task_delete_recycle_stops_origin inputs.(delete_capture_tid) origin)
      (bridge := fun heap owned => owned); [exact Hsave|].
    apply KernelCSourceAtom; right; exact (KernelProgramCDeleteSource _ _ _ _ _ _ _ _ _ _ _ _ Hrecycle).
Defined.

Lemma sem_pend_delete_body_call_source :
  forall event_observer observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped
    (source : sem_pend_delete_call_source event_observer observer stored_origin capture body_heap
      restore_selected restore_rely save_selected save_rely restore_stopped save_stopped),
  let restore := capture.(delete_save_restore) in
  let inputs := restore.(delete_restore_inputs) in
  inputs.(delete_capture_acquired).(TskState).(taskLifecycle).(taskInvocations) observer = Some stored_origin ->
  exists run : kernel_c_sequence (task_delete_program_segment observer stored_origin capture)
    inputs.(delete_capture_acquired) restore.(delete_restore_before_heap) (task_delete_capture_before_owner inputs)
    (task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped)
    (task_delete_capture_cut capture) body_heap (task_delete_capture_recycled_owner capture),
  kernel_program_c_sequence_call_source inputs.(delete_capture_environment) inputs.(delete_capture_critical)
    inputs.(delete_capture_globals) observer stored_origin event_observer _ _ _ _ _ _ _ run /\
  sem_pend_observed_client_trace inputs.(delete_capture_environment).(task_stack_call_external)
    inputs.(delete_capture_environment).(task_stack_call_port) inputs.(delete_capture_critical).(critical_region_clients)
    inputs.(delete_capture_globals) observer event_observer inputs.(delete_capture_first).(os_sched_call_origin)
    inputs.(delete_capture_acquired) (task_delete_capture_observer_stopped capture stored_origin restore_stopped save_stopped)
    capture.(delete_save_returned).(os_sched_call_origin) (task_delete_capture_cut capture) /\
  task_delete_capture_recycled_owner capture body_heap.
Proof.
  intros event_observer observer stored_origin capture body_heap restore_selected restore_rely save_selected save_rely
    restore_stopped save_stopped source restore inputs Hregistered.
  destruct (sem_pend_delete_captured_run_source event_observer observer stored_origin capture body_heap
    restore_selected restore_rely save_selected save_rely restore_stopped save_stopped source) as [run Hsource].
  exists run; split; [exact Hsource|]; split.
  - eapply SemPendObservedDeleteBody; [exact source|reflexivity|reflexivity|reflexivity|reflexivity|exact Hregistered].
  - exact (proj2 (sem_pend_delete_call_resources event_observer _ _ _ _ _ _ _ _ _ _ source)).
Defined.
