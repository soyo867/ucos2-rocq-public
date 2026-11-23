Require Export Ucos2Verify.VC.code.task.spec.task_stk_chk_spec.
Require Export Ucos2Verify.VC.code.time.spec.time_dly_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual returning context indexes the resources at each source cut.
    The old general stack-check contract is unchanged. The extra caller
    frame is ordinary disjoint storage, not a second copy of a stack. *)
Definition task_stk_chk_continuation_frame environment saved_local sg caller state
  (caller_frame : Assertion) : Assertion :=
  task_suspend_call_resources environment saved_local sg caller state ** caller_frame.

Definition task_stk_chk_continuation_masked environment critical sg caller saved acquired : Assertion :=
  critical_region_masked environment.(task_stack_call_platform) critical sg
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) saved acquired.

Definition task_stk_chk_continuation_running environment caller mask : Assertion :=
  interrupt_platform_running environment.(task_stack_call_platform)
    (task_suspend_view caller).(os_execution_invocation)
    (task_suspend_view caller).(os_execution_origin) mask.

Definition task_stk_chk_continuation_acquire_facts environment critical sg original active mask saved
  before acquired : Prop :=
  UCOS2_state_inv sg before /\
  task_suspend_save_observation critical sg original active mask saved before acquired /\
  task_suspend_save_effect environment critical sg original active mask saved before acquired /\
  UCOS2_state_inv sg acquired.

Definition task_stk_chk_continuation_protected environment saved_local sg caller caller_frame
  priority output : program UCOS2_Verify_State TaskStackCheckDecision :=
  fun before decision after =>
    task_stk_chk_protected_program sg
      (task_stk_chk_continuation_frame environment saved_local sg caller before caller_frame)
      priority output before decision after.

Definition task_stk_chk_continuation_scan environment saved_local sg caller caller_frame
  output snapshot : program UCOS2_Verify_State nat :=
  fun before count after =>
    task_stk_chk_scan_program sg
      (task_stk_chk_continuation_frame environment saved_local sg caller before caller_frame)
      output snapshot before count after.

(** Actual Save, protected lookup, actual Restore, and the existing scan.
    Neither CPU call is replaced by task-map equality. The final context
    is retained even on lookup/option errors. Argument errors make no call.
    Output initialization is the same two concrete C stores as before. *)
Definition task_stk_chk_continuation_program environment critical saved_local sg caller mask
  caller_frame priority output : program UCOS2_Verify_State
    ((Z * option TaskStackCheckData) * TaskSuspendCaller) :=
  match task_stack_check_argument_error sg priority output with
  | Some error => StateRelMonad.ret ((encode_os_err_code error, None), caller)
  | None => StateRelMonad.bind (StateRelMonad.ret task_stack_check_zero_data)
      (fun zeroed => StateRelMonad.bind
        (task_suspend_save_program environment critical sg caller mask)
        (fun entered => StateRelMonad.bind
          (task_stk_chk_continuation_protected environment saved_local sg (fst entered)
            caller_frame priority output)
          (fun decision => StateRelMonad.bind
            (task_suspend_restore_program environment critical sg (fst entered))
            (fun returned => match decision with
              | TaskStackCheckError error =>
                  StateRelMonad.ret ((encode_os_err_code error, Some zeroed), returned)
              | TaskStackCheckScan snapshot => StateRelMonad.bind
                  (task_stk_chk_continuation_scan environment saved_local sg returned
                    caller_frame output snapshot)
                  (fun count => StateRelMonad.ret
                    ((0, Some (task_stack_scan_data snapshot.(stackCheckSize) count)), returned))
              end))))
  end.

Definition task_stk_chk_continuation_safe environment critical saved_local sg caller mask
  caller_frame priority output before
  (X : Z -> option TaskStackCheckData -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (task_stk_chk_continuation_program environment critical saved_local sg caller mask
      caller_frame priority output)
    (fun result state => X (fst (fst result)) (snd (fst result)) state).

(** A read-admission predicate supplies a reversible view of existing
    storage only at actual source endpoints. It does not assert a successful
    execution or impose task-map stability. Invalid argument branches need
    no scan view. The acquired SELF byte uses the acquired caller resources;
    the unmasked scan uses the actual returned caller resources. *)
Definition task_stk_chk_continuation_admission environment critical saved_local sg caller mask
  (caller_frame : Assertion) priority output before : Prop :=
  task_stack_check_argument_error sg priority output = None ->
  forall active saved acquired,
    task_suspend_save_effect environment critical sg caller active mask saved before acquired ->
    UCOS2_state_inv sg acquired ->
    (priority = 255 -> exists selected residual,
      task_stk_chk_self_view sg acquired
        (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
        output selected residual) /\
    (forall selected snapshot,
      task_stk_chk_critical sg acquired
        (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
        priority output selected (TaskStackCheckScan snapshot) ->
      forall returned current,
        task_suspend_restore_effect environment critical sg active returned acquired current ->
        UCOS2_state_inv sg current ->
        exists region words count stop residual,
          task_stk_chk_scan_view sg current
            (task_stk_chk_continuation_frame environment saved_local sg returned current caller_frame)
            output snapshot region words count stop residual).

Definition task_stk_chk_continuation_post environment critical saved_local sg caller mask
  caller_frame priority output before error
  (X : Z -> option TaskStackCheckData -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned data current,
    coq_prop (task_stk_chk_continuation_program environment critical saved_local sg caller mask
      caller_frame priority output before ((error, data), returned) current /\
      X error data current) &&
    (task_suspend_closed environment critical saved_local sg returned mask current **
     caller_frame ** task_stk_chk_output_post output data).

Definition task_stk_chk_continuation_error_facts environment critical saved_local sg original active
  mask before caller_frame priority output saved acquired selected error : Prop :=
  task_stk_chk_configuration sg /\ task_stk_chk_valid_arguments priority output /\
  task_stk_chk_continuation_acquire_facts environment critical sg original active mask saved before acquired /\
  exists critical_error, error = encode_os_err_code critical_error /\
    task_stk_chk_critical sg acquired
      (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
      priority output selected (TaskStackCheckError critical_error).

Definition task_stk_chk_continuation_scan_facts environment critical saved_local sg original active returned
  mask before caller_frame priority output saved acquired current selected snapshot region words count stop
  residual : Prop :=
  task_stk_chk_configuration sg /\ task_stk_chk_valid_arguments priority output /\
  task_stk_chk_continuation_acquire_facts environment critical sg original active mask saved before acquired /\
  task_stk_chk_critical sg acquired
    (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
    priority output selected (TaskStackCheckScan snapshot) /\
  task_suspend_restore_observation critical sg active returned acquired current /\
  task_suspend_restore_effect environment critical sg active returned acquired current /\
  UCOS2_state_inv sg current /\
  task_stk_chk_scan_view sg current
    (task_stk_chk_continuation_frame environment saved_local sg returned current caller_frame)
    output snapshot region words count stop residual.

Lemma task_stk_chk_continuation_masked_equiv :
  forall environment critical saved_local sg caller saved acquired current caller_frame,
  (task_suspend_masked environment critical saved_local sg caller saved acquired current ** caller_frame) --||--
  (task_stk_chk_continuation_masked environment critical sg caller saved acquired **
   UCOS2_inv sg current **
   task_stk_chk_continuation_frame environment saved_local sg caller current caller_frame).
Proof.
  intros; unfold task_suspend_masked, task_stk_chk_continuation_masked,
    task_stk_chk_continuation_frame; split; entailer!.
Qed.

Lemma task_stk_chk_continuation_closed_equiv :
  forall environment critical saved_local sg caller mask current caller_frame,
  (task_suspend_closed environment critical saved_local sg caller mask current ** caller_frame) --||--
  (task_stk_chk_continuation_running environment caller mask ** UCOS2_inv sg current **
   task_stk_chk_continuation_frame environment saved_local sg caller current caller_frame).
Proof.
  intros; rewrite time_dly_closed_inv_equiv.
  unfold time_dly_outside_resources, task_stk_chk_continuation_running,
    task_stk_chk_continuation_frame; split; entailer!.
Qed.

Lemma task_stk_chk_continuation_scan_facts_prefix :
  forall environment critical saved_local sg original active returned mask before caller_frame priority
    output saved acquired current selected snapshot region words count stop residual,
  task_stk_chk_continuation_scan_facts environment critical saved_local sg original active returned
    mask before caller_frame priority output saved acquired current selected snapshot region words count stop residual ->
  task_stk_chk_initialized_prefix snapshot region words count stop.
Proof. intros * Hfacts; unfold task_stk_chk_continuation_scan_facts, task_stk_chk_scan_view in Hfacts; tauto. Qed.

Lemma task_stk_chk_continuation_acquire_saved :
  forall environment critical sg original active mask saved before acquired,
  task_stk_chk_continuation_acquire_facts environment critical sg original active mask saved before acquired ->
  interrupt_saved_value mask saved.
Proof.
  intros * [_ [Hobservation _]].
  destruct original, active; cbn [task_suspend_save_observation] in Hobservation; tauto.
Qed.

Lemma task_stk_chk_continuation_save_open :
  forall environment critical saved_local sg original mask saved before caller_frame,
  UCOS2_state_inv sg before ->
  (task_suspend_save_history_post environment critical saved_local sg original mask saved before ** caller_frame) |--
  EX active acquired,
    coq_prop (task_stk_chk_continuation_acquire_facts environment critical sg original active mask saved before acquired) &&
    (task_stk_chk_continuation_masked environment critical sg active saved acquired **
     UCOS2_inv sg acquired **
     task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame).
Proof.
  intros * Hbefore; unfold task_suspend_save_history_post; Intros active acquired.
  rewrite task_stk_chk_continuation_masked_equiv.
  unfold UCOS2_inv; Intros; Exists active acquired.
  unfold task_stk_chk_continuation_acquire_facts; entailer!; tauto.
Qed.

Lemma task_stk_chk_continuation_closed_state :
  forall environment critical saved_local sg caller mask current,
  task_suspend_closed environment critical saved_local sg caller mask current |--
  coq_prop (UCOS2_state_inv sg current) &&
    task_suspend_closed environment critical saved_local sg caller mask current.
Proof. intros; rewrite time_dly_closed_inv_equiv; unfold UCOS2_inv; entailer!. Qed.

Lemma task_stk_chk_continuation_protected_iff :
  forall environment saved_local sg caller caller_frame priority output before decision after,
  task_stk_chk_continuation_protected environment saved_local sg caller caller_frame
    priority output before decision after <->
  after = before /\ exists selected,
    task_stk_chk_critical sg before
      (task_stk_chk_continuation_frame environment saved_local sg caller before caller_frame)
      priority output selected decision.
Proof. intros; apply task_stk_chk_protected_program_iff. Qed.

Lemma task_stk_chk_continuation_scan_iff :
  forall environment saved_local sg caller caller_frame output snapshot before count after,
  task_stk_chk_continuation_scan environment saved_local sg caller caller_frame
    output snapshot before count after <->
  after = before /\ exists region words stop residual,
    task_stk_chk_scan_view sg before
      (task_stk_chk_continuation_frame environment saved_local sg caller before caller_frame)
      output snapshot region words count stop residual.
Proof. intros; apply task_stk_chk_scan_program_iff. Qed.

Lemma task_stk_chk_continuation_program_argument_error :
  forall environment critical saved_local sg caller mask caller_frame priority output before error,
  task_stack_check_argument_error sg priority output = Some error ->
  task_stk_chk_continuation_program environment critical saved_local sg caller mask
    caller_frame priority output before ((encode_os_err_code error, None), caller) before.
Proof. intros; unfold task_stk_chk_continuation_program; rewrite H; split; reflexivity. Qed.

Lemma task_stk_chk_continuation_program_critical_error :
  forall environment critical saved_local sg caller mask caller_frame priority output before
    active saved acquired selected error returned current,
  task_stack_check_argument_error sg priority output = None ->
  task_suspend_save_effect environment critical sg caller active mask saved before acquired ->
  task_stk_chk_critical sg acquired
    (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
    priority output selected (TaskStackCheckError error) ->
  task_suspend_restore_effect environment critical sg active returned acquired current ->
  task_stk_chk_continuation_program environment critical saved_local sg caller mask caller_frame
    priority output before ((encode_os_err_code error, Some task_stack_check_zero_data), returned) current.
Proof.
  intros * Hargs Hsave Hlookup Hrestore.
  unfold task_stk_chk_continuation_program; rewrite Hargs.
  exists task_stack_check_zero_data, before; split; [split; reflexivity|].
  exists (active, saved), acquired; split; [exact Hsave|].
  exists (TaskStackCheckError error), acquired; split.
  - apply task_stk_chk_continuation_protected_iff; split; [reflexivity|eauto].
  - exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma task_stk_chk_continuation_program_scan :
  forall environment critical saved_local sg caller mask caller_frame priority output before
    active saved acquired selected snapshot returned current region words count stop residual,
  task_stack_check_argument_error sg priority output = None ->
  task_suspend_save_effect environment critical sg caller active mask saved before acquired ->
  task_stk_chk_critical sg acquired
    (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
    priority output selected (TaskStackCheckScan snapshot) ->
  task_suspend_restore_effect environment critical sg active returned acquired current ->
  task_stk_chk_scan_view sg current
    (task_stk_chk_continuation_frame environment saved_local sg returned current caller_frame)
    output snapshot region words count stop residual ->
  task_stk_chk_continuation_program environment critical saved_local sg caller mask caller_frame
    priority output before ((0, Some (task_stack_scan_data snapshot.(stackCheckSize) count)), returned) current.
Proof.
  intros * Hargs Hsave Hlookup Hrestore Hview.
  unfold task_stk_chk_continuation_program; rewrite Hargs.
  exists task_stack_check_zero_data, before; split; [split; reflexivity|].
  exists (active, saved), acquired; split; [exact Hsave|].
  exists (TaskStackCheckScan snapshot), acquired; split.
  - apply task_stk_chk_continuation_protected_iff; split; [reflexivity|eauto].
  - exists returned, current; split; [exact Hrestore|].
    exists count, current; split; [|split; reflexivity].
    apply task_stk_chk_continuation_scan_iff; split; [reflexivity|eauto].
Qed.

Lemma task_stk_chk_continuation_safe_result :
  forall environment critical saved_local sg caller mask caller_frame priority output before
    error data returned current X,
  task_stk_chk_continuation_safe environment critical saved_local sg caller mask
    caller_frame priority output before X ->
  task_stk_chk_continuation_program environment critical saved_local sg caller mask
    caller_frame priority output before ((error, data), returned) current ->
  X error data current.
Proof.
  intros * [start [Hstart Hsafe]] Hsource; subst start.
  exact (Hsafe ((error, data), returned) current Hsource).
Qed.

Lemma task_stk_chk_continuation_result_safe_return : forall error data current
  (X : Z -> option TaskStackCheckData -> UCOS2_Verify_State -> Prop),
  X error data current ->
  safeExec (eq current) (StateRelMonad.ret (error, data))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros error data current X Hresult; exists current; split; [reflexivity|].
  intros result state [Hresult_eq Hstate]; subst result state; exact Hresult.
Qed.

Lemma task_stk_chk_continuation_error_finish :
  forall environment critical saved_local sg original active mask before caller_frame priority output
    saved acquired selected error X,
  task_stk_chk_continuation_error_facts environment critical saved_local sg original active
    mask before caller_frame priority output saved acquired selected error ->
  task_stk_chk_continuation_safe environment critical saved_local sg original mask
    caller_frame priority output before X ->
  (task_suspend_restore_history_post environment critical saved_local sg active saved acquired **
   caller_frame ** task_stack_check_data_rep output task_stack_check_zero_data) |--
  task_stk_chk_continuation_post environment critical saved_local sg original mask
    caller_frame priority output before error X.
Proof.
  intros * [Hconfig [Harguments [Hacquire [critical_error [Herror Hcritical]]]]] Hsafe.
  subst error.
  pose proof (task_stk_chk_continuation_acquire_saved _ _ _ _ _ _ _ _ _ Hacquire) as [_ Hmask].
  pose proof Hacquire as [Hbefore [Hsave_observation [Hsave Hacquired]]].
  pose proof (task_stk_chk_valid_arguments_no_error__lookup_and_error_paths
    sg priority output Hconfig Harguments) as Hargs.
  unfold task_suspend_restore_history_post; Intros returned current.
  match goal with H : task_suspend_restore_observation _ _ _ _ _ _ /\
                     task_suspend_restore_effect _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hrestore_observation Hrestore]
  end.
  rewrite Hmask.
  assert (Hsource : task_stk_chk_continuation_program environment critical saved_local sg original mask
    caller_frame priority output before
    ((encode_os_err_code critical_error, Some task_stack_check_zero_data), returned) current).
  { eapply task_stk_chk_continuation_program_critical_error; eassumption. }
  assert (Hresult : X (encode_os_err_code critical_error) (Some task_stack_check_zero_data) current).
  { eapply task_stk_chk_continuation_safe_result; eassumption. }
  unfold task_stk_chk_continuation_post; Exists returned (Some task_stack_check_zero_data) current.
  unfold task_stk_chk_output_post; entailer!.
Qed.

Lemma task_stk_chk_continuation_restore_scan_open :
  forall environment critical saved_local sg original active mask before caller_frame priority output
    saved acquired selected snapshot,
  task_stk_chk_configuration sg ->
  task_stk_chk_valid_arguments priority output ->
  task_stk_chk_continuation_admission environment critical saved_local sg original mask
    caller_frame priority output before ->
  task_stk_chk_continuation_acquire_facts environment critical sg original active mask saved before acquired ->
  task_stk_chk_critical sg acquired
    (task_stk_chk_continuation_frame environment saved_local sg active acquired caller_frame)
    priority output selected (TaskStackCheckScan snapshot) ->
  (task_suspend_restore_history_post environment critical saved_local sg active saved acquired **
   caller_frame ** task_stack_check_data_rep output task_stack_check_zero_data) |--
  EX returned current region words count stop residual,
    coq_prop (task_stk_chk_continuation_scan_facts environment critical saved_local sg original active returned
      mask before caller_frame priority output saved acquired current selected snapshot region words count stop residual) &&
    (task_stk_chk_continuation_running environment returned mask ** UCOS2_inv sg current **
     task_stk_chk_continuation_frame environment saved_local sg returned current caller_frame **
     task_stack_check_data_rep output task_stack_check_zero_data).
Proof.
  intros * Hconfig Harguments Hadmission Hacquire Hcritical.
  pose proof (task_stk_chk_continuation_acquire_saved _ _ _ _ _ _ _ _ _ Hacquire) as [_ Hmask].
  pose proof Hacquire as [Hbefore [Hsave_observation [Hsave Hacquired]]].
  pose proof (task_stk_chk_valid_arguments_no_error__lookup_and_error_paths
    sg priority output Hconfig Harguments) as Hargs.
  unfold task_suspend_restore_history_post; Intros returned current.
  match goal with H : task_suspend_restore_observation _ _ _ _ _ _ /\
                     task_suspend_restore_effect _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hrestore_observation Hrestore]
  end.
  rewrite Hmask.
  sep_apply_l_atomic (task_stk_chk_continuation_closed_state
    environment critical saved_local sg returned mask current).
  Intros.
  match goal with H : UCOS2_state_inv sg current |- _ => rename H into Hcurrent end.
  destruct (proj2 (Hadmission Hargs active saved acquired Hsave Hacquired)
    selected snapshot Hcritical returned current Hrestore Hcurrent) as
    (region & words & count & stop & residual & Hview).
  sep_apply_l_atomic (proj1 (task_stk_chk_continuation_closed_equiv
    environment critical saved_local sg returned mask current caller_frame)).
  Exists returned current region words count stop residual.
  unfold task_stk_chk_continuation_scan_facts; entailer!; tauto.
Qed.
