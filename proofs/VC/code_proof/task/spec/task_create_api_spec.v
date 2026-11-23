Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_modular_init_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_runtime_consumer_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_runtime_flow_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_call_protocol_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_modular_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The existing modular CPU contracts retain their source relation and
    the selected C completed-call rely. Context fragments are results of
    these calls, not identified by [same_call]. *)
Definition task_create_save_program environment critical sg original mask
  : program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun before result acquired =>
    kernel_call_save_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg original (fst result)
      mask (snd result) before acquired /\
    task_tcb_init_runtime_history sg original before (fst result) acquired.

Definition task_create_restore_program environment critical sg original
  : program UCOS2_Verify_State OsSchedCallContext :=
  fun released returned current =>
    kernel_resumption_task_source_trace environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical.(critical_region_clients) sg
      original.(os_sched_call_invocation) None original.(os_sched_call_origin)
      released false returned.(os_sched_call_origin) current /\
    task_tcb_init_runtime_history sg original released returned current.

(** StackInit writes the private caller buffer, outside the kernel-state
    projection. Its exact initialized bytes and returned SP remain in the
    checked spatial contract. Only its existing matched environmental
    relation changes the kernel state; no new state-preservation promise
    or physical IRQ trace is added here. *)
Definition task_create_stack_init_program sg args original
  : program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun before result current =>
    snd result = task_stack_init_sp TaskStackNoVFP args.(createStackTop) /\
    task_create_stack_init_entry_preserved sg args original before current /\
    task_tcb_init_stack_source_preserved original before current /\
    task_tcb_init_runtime_history sg original before (fst result) current /\
    before.(NameState) = current.(NameState).

(** This is the pure projection of the already checked TCBInit C summary,
    not an arbitrary state update. [stack_call_result] retains the two
    protected mutations (detach and stack-aware publication), exact
    allocation identity/configured fields, and their established C rely.
    The distinct released/returned states retain the existing return rely;
    publication does not promise child survival at eventual return. *)
Definition task_create_tcb_program critical sg region args task_return lower upper
  initial_name original : program UCOS2_Verify_State (OsSchedCallContext * Z) :=
  fun initial result current => exists released,
    task_tcb_init_stack_call_result critical sg region args task_return lower upper
      initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
      initial (snd result) released /\
    UCOS2_state_inv sg released /\
    task_tcb_init_stack_source_preserved original initial released /\
    task_tcb_init_stack_same_call (fst result) original /\
    task_tcb_init_stack_return_preserved original released current /\
    (snd result = 0 -> current.(SchedState).(readyList) <> []) /\
    task_tcb_init_runtime_history sg original initial (fst result) current /\
    initial.(NameState) = current.(NameState).

(** A name for QCP's opaque annotation type only; the semantics remain the
    existing StateRelMonad over the original kernel state. *)
Definition TaskCreateProgram := program UCOS2_Verify_State Z.

Definition task_create_restore_return_program environment critical sg call error
  : TaskCreateProgram :=
  StateRelMonad.bind (task_create_restore_program environment critical sg call)
    (fun _ => StateRelMonad.ret error).

Definition task_create_rollback_acquired_program environment critical sg args call
  : TaskCreateProgram :=
  StateRelMonad.bind (update' (task_create_stack_rolled_back args))
    (fun _ => task_create_restore_return_program environment critical sg call 66).

Definition task_create_rollback_program environment critical sg args call mask
  : TaskCreateProgram :=
  StateRelMonad.bind (task_create_save_program environment critical sg call mask)
    (fun acquired => task_create_rollback_acquired_program environment critical sg args (fst acquired)).

Definition task_create_schedule_program environment critical sg call mask
  : TaskCreateProgram :=
  StateRelMonad.bind (os_sched_continuation_program environment critical sg call mask)
    (fun _ => StateRelMonad.ret 0).

Definition task_create_tcb_return_program environment critical sg args call mask error
  : TaskCreateProgram :=
  if Z.eqb error 0 then
    StateRelMonad.bind (get' (fun state => state.(SchedState).(isRunning)))
      (fun running => if running then task_create_schedule_program environment critical sg call mask
        else StateRelMonad.ret 0)
  else task_create_rollback_program environment critical sg args call mask.

Definition task_create_initialized_program environment critical sg region args task_return
  lower upper initial_name call mask : TaskCreateProgram :=
  StateRelMonad.bind
    (task_create_tcb_program critical sg region args task_return lower upper initial_name call)
    (fun result => task_create_tcb_return_program environment critical sg args (fst result) mask (snd result)).

Definition task_create_initialize_program environment critical sg region args task_return
  lower upper initial_name call mask : TaskCreateProgram :=
  StateRelMonad.bind (task_create_stack_init_program sg args call)
    (fun result => task_create_initialized_program environment critical sg region args task_return
      lower upper initial_name (fst result) mask).

Definition task_create_reserved_program environment critical sg region args task_return
  lower upper initial_name call mask : TaskCreateProgram :=
  StateRelMonad.bind (task_create_restore_program environment critical sg call)
    (fun returned => task_create_initialize_program environment critical sg region args task_return
      lower upper initial_name returned mask).

Definition task_create_acquired_program environment critical sg region args task_return
  lower upper initial_name original call mask : TaskCreateProgram :=
  StateRelMonad.bind (get' (fun state : UCOS2_Verify_State => state))
    (fun acquired =>
      if Z.ltb 0 (task_create_stack_nesting acquired) then
        task_create_restore_return_program environment critical sg call 60
      else if Z.eqb (task_create_stack_priority sg args acquired) 0 then
        StateRelMonad.bind (update' (task_create_stack_reserved args original))
          (fun _ => task_create_reserved_program environment critical sg region args task_return
            lower upper initial_name call mask)
      else task_create_restore_return_program environment critical sg call 40).

Definition task_create_program environment critical sg region args task_return
  lower upper initial_name call mask : TaskCreateProgram :=
  if Z.ltb 63 (unsigned_last_nbits args.(createPriority) 32) then StateRelMonad.ret 42
  else StateRelMonad.bind (task_create_save_program environment critical sg call mask)
    (fun acquired => task_create_acquired_program environment critical sg region args task_return
      lower upper initial_name call (fst acquired) mask).

Definition task_create_safe (state : UCOS2_Verify_State) (code : TaskCreateProgram)
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun current => current = state) code X.

Definition task_create_api_post environment critical saved_local sg region args task_return
  lower old_frame upper original mask result (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      (result = 0 \/ result = 40 \/ result = 42 \/ result = 60 \/ result = 66) /\
      task_create_safe current (StateRelMonad.ret result) X) &&
    (task_create_continuation_input environment critical saved_local sg returned mask current **
     unmap_table_rep sg **
     (if Z.eq_dec result 0 then emp else
       EX initialized, task_create_stack_failure_buffer region args task_return
         lower old_frame upper initialized)).

Lemma task_create_api_post_weaken : forall environment critical saved_local sg region args task_return
  lower old_frame upper original mask result X,
  task_create_api_post environment critical saved_local sg region args task_return
    lower old_frame upper original mask result X |--
  task_create_continuation_post environment critical saved_local sg region args task_return
    lower old_frame upper original mask result.
Proof.
  intros; unfold task_create_api_post; Intros returned current.
  unfold task_create_continuation_post; Exists returned current; entailer!; tauto.
Qed.

Lemma task_create_bind_safe_step : forall (A : Type) (first : program UCOS2_Verify_State A)
  (next : A -> TaskCreateProgram) before result current X,
  first before result current ->
  task_create_safe before (StateRelMonad.bind first next) X ->
  task_create_safe current (next result) X.
Proof.
  intros A first next before result current X Hstep Hsafe.
  eapply (highstepbind_derive first next (fun state => state = before)
    result (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

Lemma task_create_read_safe_step : forall (A : Type) (read : UCOS2_Verify_State -> A)
  (next : A -> TaskCreateProgram) state X,
  task_create_safe state (StateRelMonad.bind (get' read) next) X ->
  task_create_safe state (next (read state)) X.
Proof.
  intros A read next state X Hsafe.
  eapply (task_create_bind_safe_step A (get' read) next state (read state) state X).
  - split; reflexivity.
  - exact Hsafe.
Qed.

Lemma task_create_update_safe_step : forall update_state (next : TaskCreateProgram) state X,
  task_create_safe state (StateRelMonad.bind (update' update_state) (fun _ => next)) X ->
  task_create_safe (update_state state) next X.
Proof.
  intros update_state next state X Hsafe.
  eapply (task_create_bind_safe_step unit (update' update_state)
    (fun _ => next) state tt (update_state state) X).
  - reflexivity.
  - exact Hsafe.
Qed.

Lemma task_create_result_safe_return : forall code before result current X,
  code before result current -> task_create_safe before code X ->
  task_create_safe current (StateRelMonad.ret result) X.
Proof.
  intros code before result current X Hresult Hsafe.
  eapply (highstependret_derive code (fun state => state = before) result
    (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hresult|reflexivity].
  - exact Hsafe.
Qed.

Lemma task_create_early_safe_return : forall environment critical sg region args task_return
  lower upper initial_name call mask initial X,
  63 < unsigned_last_nbits args.(createPriority) 32 ->
  task_create_safe initial (task_create_program environment critical sg region args task_return
    lower upper initial_name call mask) X ->
  task_create_safe initial (StateRelMonad.ret 42) X.
Proof.
  intros; unfold task_create_program in *.
  rewrite (proj2 (Z.ltb_lt _ _) H) in H0; exact H0.
Qed.

Lemma task_create_save_safe_observation : forall environment critical saved_local sg original
  mask saved before next X,
  task_create_safe before
    (StateRelMonad.bind (task_create_save_program environment critical sg original mask) next) X ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) before acquired /\
      (UCOS2_state_inv sg before -> task_tcb_init_stack_source_preserved original before acquired) /\
      interrupt_saved_value mask saved /\
      kernel_call_normal_return original before returned acquired /\
      kernel_call_control_rely sg before acquired /\
      task_create_safe acquired (next (returned, saved)) X) &&
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      returned saved acquired acquired.
Proof.
  intros environment critical saved_local sg original mask saved before next X Hsafe.
  unfold task_tcb_init_modular_save_output, kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsource : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired) by tauto.
  assert (Hhistory : task_tcb_init_runtime_history sg original before returned acquired)
    by (split; tauto).
  assert (Hnext : task_create_safe acquired (next (returned, saved)) X).
  { eapply (task_create_bind_safe_step _
      (task_create_save_program environment critical sg original mask)
      next before (returned, saved) acquired X); [split; eassumption|exact Hsafe]. }
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsource) as Hinterval.
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  destruct Hsource as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hordinary : UCOS2_state_inv sg before ->
    task_tcb_init_stack_source_preserved original before acquired).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_restore_input_world
    environment critical saved_local sg returned saved acquired acquired)).
  Exists returned acquired; entailer!.
Qed.

Lemma task_create_restore_safe_observation : forall environment critical saved_local sg original
  saved released next X,
  task_create_safe released
    (StateRelMonad.bind (task_create_restore_program environment critical sg original) next) X ->
  task_tcb_init_modular_restore_output environment critical saved_local sg original saved released |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
      (UCOS2_state_inv sg released -> task_tcb_init_stack_source_preserved original released current) /\
      kernel_call_normal_return original released returned current /\
      kernel_call_control_rely sg released current /\
      task_create_safe current (next returned) X) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned
      (armv7a_irq_fiq_mask saved) current.
Proof.
  intros environment critical saved_local sg original saved released next X Hsafe.
  unfold task_tcb_init_modular_restore_output, kernel_call_modular_restore_post; Intros returned current.
  assert (Htrace : kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hnormal : kernel_call_normal_return original released returned current) by tauto.
  assert (Hhistory : task_tcb_init_runtime_history sg original released returned current)
    by (split; tauto).
  assert (Hnext : task_create_safe current (next returned) X).
  { eapply (task_create_bind_safe_step _
      (task_create_restore_program environment critical sg original)
      next released returned current X); [split; eassumption|exact Hsafe]. }
  pose proof (proj1 Hnormal) as Hsame.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hinterval Hcontrol].
  pose proof (task_tcb_init_interval_preserves_call _ _ _ _ _ Hinterval) as Hpreserved.
  assert (Hordinary : UCOS2_state_inv sg released ->
    task_tcb_init_stack_source_preserved original released current).
  { intro Hvalid; eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  sep_apply_l_atomic (proj2 (task_tcb_init_modular_save_input_world
    environment critical saved_local sg returned (armv7a_irq_fiq_mask saved) current)).
  Exists returned current; entailer!.
Qed.

Lemma task_create_save_safe_entry : forall environment critical saved_local sg region args
  task_return lower upper initial_name original mask saved before X,
  0 <= args.(createPriority) <= 63 ->
  task_create_stack_entry sg args initial_name original before ->
  task_create_runtime_call_input args original before ->
  task_create_safe before (task_create_program environment critical sg region args task_return
    lower upper initial_name original mask) X ->
  task_tcb_init_modular_save_output environment critical saved_local sg original mask saved before |--
  EX returned acquired,
    coq_prop (task_create_stack_entry sg args initial_name original acquired /\
      task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      task_create_runtime_call_input args returned acquired /\
      before.(NameState) = acquired.(NameState) /\
      task_create_safe acquired (task_create_acquired_program environment critical sg region args
        task_return lower upper initial_name original returned mask) X) &&
    task_tcb_init_continuation_restore_input environment critical saved_local sg
      returned saved acquired acquired.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    original mask saved before X Hpriority Hentry Hadmit Hsafe.
  unfold task_create_program in Hsafe.
  rewrite unsigned_last_nbits_eq in Hsafe by (change (0 <= args.(createPriority) < 4294967296); lia).
  rewrite (proj2 (Z.ltb_ge _ _) (proj2 Hpriority)) in Hsafe.
  sep_apply_l_atomic (task_create_save_safe_observation environment critical saved_local
    sg original mask saved before _ X Hsafe); Intros returned acquired.
  assert (Hhistory : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    before acquired) by tauto.
  pose proof (task_create_stack_entry_after_call sg args initial_name original
    before acquired Hentry Hhistory) as Hacquired.
  assert (Hvalid : UCOS2_state_inv sg before) by exact (proj1 Hentry).
  pose proof (proj2 (proj2 (proj2 (Hhistory Hvalid)))) as Hnames.
  assert (Hsource : task_tcb_init_stack_source_preserved original before acquired) by tauto.
  assert (Hruntime : task_create_runtime_call_input args returned acquired).
  { eapply (task_create_runtime_call_input_after_return sg args original before returned acquired);
      [exact Hadmit| | |exact Hsource]; tauto. }
  Exists returned acquired; entailer!.
Qed.

Lemma task_create_acquired_isr_safe : forall environment critical sg region args task_return
  lower upper initial_name original call mask acquired X,
  0 < task_create_stack_nesting acquired ->
  task_create_safe acquired (task_create_acquired_program environment critical sg region args
    task_return lower upper initial_name original call mask) X ->
  task_create_safe acquired (task_create_restore_return_program environment critical sg call 60) X.
Proof.
  intros; unfold task_create_acquired_program in H0.
  apply task_create_read_safe_step in H0; cbn in H0.
  rewrite (proj2 (Z.ltb_lt _ _) H) in H0; exact H0.
Qed.

Lemma task_create_acquired_free_safe : forall environment critical sg region args task_return
  lower upper initial_name original call mask acquired X,
  task_create_stack_nesting acquired <= 0 -> task_create_stack_priority sg args acquired = 0 ->
  task_create_safe acquired (task_create_acquired_program environment critical sg region args
    task_return lower upper initial_name original call mask) X ->
  task_create_safe (task_create_stack_reserved args original acquired)
    (task_create_reserved_program environment critical sg region args task_return
      lower upper initial_name call mask) X.
Proof.
  intros; unfold task_create_acquired_program in H1.
  apply task_create_read_safe_step in H1; cbn in H1.
  rewrite (proj2 (Z.ltb_ge _ _) H), H0, Z.eqb_refl in H1.
  exact (task_create_update_safe_step _ _ _ _ H1).
Qed.

Lemma task_create_acquired_occupied_safe : forall environment critical sg region args task_return
  lower upper initial_name original call mask acquired X,
  task_create_stack_nesting acquired <= 0 -> task_create_stack_priority sg args acquired <> 0 ->
  task_create_safe acquired (task_create_acquired_program environment critical sg region args
    task_return lower upper initial_name original call mask) X ->
  task_create_safe acquired (task_create_restore_return_program environment critical sg call 40) X.
Proof.
  intros; unfold task_create_acquired_program in H1.
  apply task_create_read_safe_step in H1; cbn in H1.
  rewrite (proj2 (Z.ltb_ge _ _) H), (proj2 (Z.eqb_neq _ _) H0) in H1; exact H1.
Qed.

Lemma task_create_tcb_running_safe : forall environment critical sg args call mask current X,
  task_create_stack_running current = 1 ->
  task_create_safe current (task_create_tcb_return_program environment critical sg args call mask 0) X ->
  task_create_safe current (task_create_schedule_program environment critical sg call mask) X.
Proof.
  intros; unfold task_create_tcb_return_program in H0; cbn in H0.
  apply task_create_read_safe_step in H0.
  unfold task_create_stack_running in H.
  destruct current.(SchedState).(isRunning); [exact H0|discriminate].
Qed.

Lemma task_create_tcb_stopped_safe : forall environment critical sg args call mask current X,
  task_create_stack_running current <> 1 ->
  task_create_safe current (task_create_tcb_return_program environment critical sg args call mask 0) X ->
  task_create_safe current (StateRelMonad.ret 0) X.
Proof.
  intros; unfold task_create_tcb_return_program in H0; cbn in H0.
  apply task_create_read_safe_step in H0.
  unfold task_create_stack_running in H.
  destruct current.(SchedState).(isRunning); [contradiction|exact H0].
Qed.

Lemma task_create_init_safe_tcb_pre : forall environment critical saved_local sg region args
  task_return lower upper initial_name original mask before returned_sp X,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) before ->
  task_create_runtime_call_input args original before -> task_create_stack_nesting before = 0 ->
  task_create_safe before (task_create_initialize_program environment critical sg region args
    task_return lower upper initial_name original mask) X ->
  task_create_modular_init_output environment critical saved_local sg region args task_return
    lower upper original mask before returned_sp |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      returned_sp = task_stack_init_sp TaskStackNoVFP args.(createStackTop) /\
      task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
        original.(os_sched_call_invocation) original.(os_sched_call_origin) current /\
      task_tcb_init_stack_source_preserved original before current /\
      task_create_runtime_call_input args returned current /\ task_create_stack_nesting current = 0 /\
      before.(NameState) = current.(NameState) /\
      task_create_safe current (task_create_initialized_program environment critical sg region args
        task_return lower upper initial_name returned mask) X) &&
    task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return
      lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
      mask current returned.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    original mask before returned_sp X Hlayout Hentry Hadmit Hnesting Hsafe.
  unfold task_create_modular_init_output; Intros returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hpreserved : task_create_stack_init_entry_preserved sg args original before current) by tauto.
  pose proof (Hpreserved initial_name Hentry) as Hcurrent.
  assert (Hhistory : task_tcb_init_runtime_history sg original before returned current) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved original before current) by tauto.
  pose proof (task_create_runtime_call_input_after_return sg args original before returned current
    Hadmit (proj2 Hhistory) (proj1 Hhistory) Hsource) as Hruntime.
  pose proof (task_create_runtime_nesting_after_return sg before current (proj2 Hhistory) Hnesting) as Hzero.
  sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args task_return
    lower upper returned_sp Hlayout); Intros.
  assert (Hstep : task_create_stack_init_program sg args original before (returned, returned_sp) current)
    by (unfold task_create_stack_init_program; cbn; tauto).
  pose proof (task_create_bind_safe_step _ _ _ before (returned, returned_sp) current X Hstep Hsafe) as Hnext.
  cbn in Hnext; Exists returned current.
  unfold task_tcb_init_continuation_call_pre, task_tcb_init_stack_pre, task_tcb_init_pre,
    task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_continuation_capsules, kernel_call_execution_owned.
  destruct Hsame as [Hi [Ho Hstack]]; rewrite Hi, Ho; entailer!; tauto.
Qed.

Lemma task_create_tcb_safe_success : forall environment critical saved_local sg region args
  task_return lower upper initial_name original mask initial X,
  task_create_runtime_call_input args original initial -> task_create_stack_nesting initial = 0 ->
  task_create_safe initial (task_create_initialized_program environment critical sg region args
    task_return lower upper initial_name original mask) X ->
  task_tcb_init_modular_name_call_post environment critical saved_local sg region args task_return
    lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
    mask initial original 0 |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_source_preserved original initial current /\
      task_create_runtime_call_input args returned current /\ task_create_stack_nesting current = 0 /\
      current.(SchedState).(readyList) <> [] /\
      initial.(NameState) = current.(NameState) /\
      task_create_safe current (task_create_tcb_return_program environment critical sg args returned mask 0) X) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    original mask initial X Hadmit Hnesting Hsafe.
  unfold task_tcb_init_modular_name_call_post; Intros released returned current.
  assert (Hstep : task_create_tcb_program critical sg region args task_return lower upper
    initial_name original initial (returned, 0) current) by (exists released; cbn; tauto).
  pose proof (task_create_bind_safe_step _ _ _ initial (returned, 0) current X Hstep Hsafe) as Hnext.
  cbn in Hnext.
  assert (Hprefix : task_tcb_init_stack_source_preserved original initial released) by tauto.
  assert (Htail : task_tcb_init_stack_source_preserved original released current)
    by (unfold task_tcb_init_stack_return_preserved in *; tauto).
  pose proof (task_tcb_init_stack_source_preserved_trans original initial released current Hprefix Htail) as Hsource.
  assert (Hhistory : task_tcb_init_runtime_history sg original initial returned current) by tauto.
  pose proof (task_create_runtime_call_input_after_return sg args original initial returned current
    Hadmit (proj2 Hhistory) (proj1 Hhistory) Hsource) as Hruntime.
  pose proof (task_create_runtime_nesting_after_return sg initial current (proj2 Hhistory) Hnesting) as Hzero.
  unfold task_tcb_init_stack_buffer_result; destruct (Z.eq_dec 0 66); [discriminate|].
  Exists returned current; entailer!; tauto.
Qed.

Lemma task_create_tcb_safe_no_free : forall environment critical saved_local sg region args task_return
  lower upper initial_name original mask initial X,
  task_create_safe initial (task_create_initialized_program environment critical sg region args
    task_return lower upper initial_name original mask) X ->
  task_tcb_init_modular_name_call_post environment critical saved_local sg region args task_return
    lower upper initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin)
    mask initial original 66 |--
  EX released returned current,
    coq_prop (task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
      original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released /\
      task_tcb_init_stack_same_call returned original /\ UCOS2_state_inv sg current /\
      task_tcb_init_stack_return_preserved original released current /\
      initial.(NameState) = current.(NameState) /\
      task_create_safe current (task_create_rollback_program environment critical sg args returned mask) X) &&
    (task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current **
     task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper)).
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    original mask initial X Hsafe.
  unfold task_tcb_init_modular_name_call_post; Intros released returned current.
  assert (Hstep : task_create_tcb_program critical sg region args task_return lower upper
    initial_name original initial (returned, 66) current) by (exists released; cbn; tauto).
  pose proof (task_create_bind_safe_step _ _ _ initial (returned, 66) current X Hstep Hsafe) as Hnext.
  change (task_create_safe current (task_create_rollback_program environment critical sg args returned mask) X) in Hnext.
  assert (Hresult : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released) by tauto.
  assert (Hraw : task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial 66 released).
  { inversion Hresult; subst; assumption. }
  Exists released returned current.
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
    task_tcb_init_stack_same_call, task_tcb_init_stack_buffer_result.
  destruct (Z.eq_dec 66 66); [|contradiction].
  Intros; unfold task_tcb_init_stack_same_call in *; entailer!; tauto.
Qed.

Definition task_create_schedule_post environment critical saved_local sg original mask X : Assertion :=
  EX scheduled before,
    coq_prop (task_tcb_init_stack_same_call scheduled original /\
      task_create_safe before (task_create_schedule_program environment critical sg scheduled mask) X) &&
    os_sched_continuation_history_return_post environment critical saved_local kernel_program_inv
      sg scheduled mask before.

Lemma task_create_save_safe_no_free : forall environment critical saved_local sg args original
  checkpoint_call mask saved initial released checkpoint X,
  task_tcb_init_stack_same_call checkpoint_call original ->
  task_tcb_init_call_result sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial 66 released ->
  UCOS2_state_inv sg checkpoint ->
  task_tcb_init_stack_return_preserved original released checkpoint ->
  forall create_args,
  task_create_safe checkpoint (task_create_rollback_program environment critical sg create_args checkpoint_call mask) X ->
  task_tcb_init_modular_save_output environment critical saved_local sg
    checkpoint_call mask saved checkpoint |--
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      task_tcb_init_stack_return_preserved original released acquired /\
      task_rollback_guard acquired.(TskState) args.(initPrio) original.(os_sched_call_invocation) /\
      interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
      task_stack_live_coverage acquired.(TskState) (task_stack_call_active_key returned) /\
      task_create_safe acquired (task_create_rollback_acquired_program environment critical sg create_args returned) X) &&
    (critical_region_masked environment.(task_stack_call_platform) critical sg
       original.(os_sched_call_invocation) original.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment returned ** UCOS2_raw_rep sg acquired **
     task_tcb_init_continuation_capsules environment saved_local acquired).
Proof.
  intros environment critical saved_local sg args original checkpoint_call mask saved initial released
    checkpoint X Hsame Hresult Hcheckpoint Hprevious create_args Hsafe.
  pose proof Hsame as [Hinvocation [Horigin Hstack]].
  sep_apply_l_atomic (task_create_save_safe_observation environment critical saved_local sg
    checkpoint_call mask saved checkpoint _ X Hsafe); Intros returned acquired.
  assert (Hlast : task_tcb_init_call_preserved sg checkpoint_call.(os_sched_call_invocation)
    checkpoint acquired) by tauto.
  rewrite Hinvocation in Hlast.
  destruct (Hlast Hcheckpoint) as [Hvalid [Hframe [Hactive Hname]]].
  assert (Hcheckpoint_source : task_tcb_init_stack_source_preserved checkpoint_call checkpoint acquired) by tauto.
  pose proof (task_create_stack_same_call_source_preserved _ _ _ _ Hsame Hcheckpoint_source) as Hordinary.
  assert (Hpreserved : task_tcb_init_stack_return_preserved original released acquired).
  { destruct Hprevious as [Hprevious_frame [Hprevious_active Hprevious_source]].
    split.
    - unfold task_creation_frame in *; congruence.
    - split; [intro Hlive; apply Hactive, Hprevious_active; exact Hlive|].
      eapply task_tcb_init_stack_source_preserved_trans; eassumption. }
  destruct (task_tcb_init_call_no_free_pending_agreement sg args original.(os_sched_call_invocation)
    original.(os_sched_call_origin) initial released Hresult) as [_ [entry [Hentry [Hinv Hempty]]]].
  assert (Hguard : task_rollback_guard acquired.(TskState) args.(initPrio) original.(os_sched_call_invocation)).
  { exists entry; split; [|auto].
    eapply task_creation_frame_lookup; [exact (proj1 Hpreserved)|exact Hentry|exact Hinv]. }
  assert (Hreturned : task_tcb_init_stack_same_call returned checkpoint_call) by tauto.
  destruct Hreturned as [Hreturned_invocation [Hreturned_origin Hreturned_stack]].
  unfold task_tcb_init_continuation_restore_input; Intros.
  Exists returned acquired.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_context, UCOS2_inv.
  rewrite Hreturned_invocation, Hreturned_origin, Hinvocation, Horigin; entailer!; congruence.
Qed.

Lemma task_create_restore_safe_return : forall environment critical saved_local sg region args task_return
  lower old_frame upper original actual mask saved released result initialized X,
  task_tcb_init_stack_same_call actual original -> interrupt_saved_value mask saved ->
  (result = 40 \/ result = 60 \/ result = 66) ->
  task_create_safe released (task_create_restore_return_program environment critical sg actual result) X ->
  task_tcb_init_modular_restore_output environment critical saved_local sg actual saved released **
    unmap_table_rep sg **
    task_create_stack_failure_buffer region args task_return lower old_frame upper initialized |--
  task_create_api_post environment critical saved_local sg region args task_return lower old_frame upper
    original mask result X.
Proof.
  intros environment critical saved_local sg region args task_return lower old_frame upper
    original actual mask saved released result initialized X Hsame Hsaved Hcode Hsafe.
  sep_apply_l_atomic (task_create_restore_safe_observation environment critical saved_local sg
    actual saved released _ X Hsafe); Intros returned current.
  assert (Hreturned : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  unfold task_tcb_init_continuation_save_input, task_create_continuation_input; Intros.
  unfold task_create_api_post; Exists returned current.
  destruct (Z.eq_dec result 0); [lia|]; Exists initialized.
  unfold task_create_continuation_input; rewrite (proj2 Hsaved); entailer!; tauto.
Qed.

Lemma task_create_schedule_safe_return : forall environment critical saved_local sg original mask X
  region args task_return lower old_frame upper,
  task_create_schedule_post environment critical saved_local sg original mask X |--
  task_create_api_post environment critical saved_local sg region args task_return lower old_frame upper
    original mask 0 X.
Proof.
  intros; unfold task_create_schedule_post; Intros scheduled before.
  unfold os_sched_continuation_history_return_post; Intros returned current.
  assert (Hstep : os_sched_continuation_program environment critical sg scheduled mask before returned current).
  { apply os_sched_continuation_program_iff; tauto. }
  assert (Hsafe : task_create_safe before (task_create_schedule_program environment critical sg scheduled mask) X) by tauto.
  pose proof (task_create_bind_safe_step _ _ _ before returned current X Hstep Hsafe) as Hnext.
  assert (Hreturned : task_tcb_init_stack_same_call returned original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  rewrite <- task_create_continuation_input_closed_world.
  unfold task_create_continuation_input; Intros.
  unfold task_create_api_post; Exists returned current.
  destruct (Z.eq_dec 0 0); [|contradiction].
  unfold task_create_continuation_input; entailer!.
Qed.
