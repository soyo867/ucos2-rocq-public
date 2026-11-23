Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.lib.time.
Require Export Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Import Ucos2Verify.lib.task_status Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.array_abstraction Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_execution Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTimeDlyResume, V2.93.01: the protected operation uses the priority
    table acquired by Save. NULL and reserved both return 67; delay zero
    returns 80. The success transformer is the shared Time operation.
    This relation intentionally contains no OSRunning or ISR test. *)
Definition time_dly_resume_critical_code (sg : StableGlobVars) (priority : Z)
  (before : UCOS2_Verify_State) (result : Z * bool)
  (after : UCOS2_Verify_State) : Prop :=
  0 <= priority < 63 /\
  match before.(TskState).(prioTbl) priority with
  | PTFree | PTReserved => result = (67, false) /\ after = before
  | PTTask tid => exists old,
      before.(TskState).(inUsedTaskStates) tid = Some old /\
      if Z.eqb old.(dly) 0 then result = (80, false) /\ after = before
      else result = (0, negb (task_is_suspended old.(stat))) /\
        after = time_dly_resume_state sg before tid old
  end.

Lemma time_dly_resume_critical_free : forall sg priority before,
  0 <= priority < 63 -> before.(TskState).(prioTbl) priority = PTFree ->
  time_dly_resume_critical_code sg priority before (67, false) before.
Proof. intros; unfold time_dly_resume_critical_code; rewrite H0; auto. Qed.

Lemma time_dly_resume_critical_reserved : forall sg priority before,
  0 <= priority < 63 -> before.(TskState).(prioTbl) priority = PTReserved ->
  time_dly_resume_critical_code sg priority before (67, false) before.
Proof. intros; unfold time_dly_resume_critical_code; rewrite H0; auto. Qed.

Lemma time_dly_resume_critical_zero_delay : forall sg priority before tid old,
  0 <= priority < 63 -> before.(TskState).(prioTbl) priority = PTTask tid ->
  before.(TskState).(inUsedTaskStates) tid = Some old -> old.(dly) = 0 ->
  time_dly_resume_critical_code sg priority before (80, false) before.
Proof.
  intros sg priority before tid old Hrange Hentry Hnode Hd.
  unfold time_dly_resume_critical_code; rewrite Hentry; split; [exact Hrange|].
  exists old; split; [exact Hnode|].
  rewrite Hd; split; reflexivity.
Qed.

Lemma time_dly_resume_critical_success : forall sg priority before tid old,
  0 <= priority < 63 -> before.(TskState).(prioTbl) priority = PTTask tid ->
  before.(TskState).(inUsedTaskStates) tid = Some old -> old.(dly) <> 0 ->
  time_dly_resume_critical_code sg priority before
    (0, negb (task_is_suspended old.(stat)))
    (time_dly_resume_state sg before tid old).
Proof.
  intros sg priority before tid old Hrange Hentry Hnode Hd.
  unfold time_dly_resume_critical_code; rewrite Hentry; split; [exact Hrange|].
  exists old; split; [exact Hnode|].
  rewrite (proj2 (Z.eqb_neq _ _) Hd); split; reflexivity.
Qed.

Lemma time_dly_resume_critical_preserves_validity : forall sg priority before result after,
  UCOS2_state_inv sg before ->
  time_dly_resume_critical_code sg priority before result after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg priority before result after Hvalid [_ Hstep].
  destruct (before.(TskState).(prioTbl) priority) as [| |tid];
    try (destruct Hstep as [_ ->]; exact Hvalid).
  destruct Hstep as [old [Hnode Hstep]].
  destruct (Z.eqb old.(dly) 0) eqn:Hd; destruct Hstep as [_ ->]; [exact Hvalid|].
  apply Z.eqb_neq in Hd; eapply time_dly_resume_preserves_validity; eassumption.
Qed.

Lemma time_dly_resume_critical_preserves_control : forall sg priority before result after,
  time_dly_resume_critical_code sg priority before result after ->
  after.(IntrState) = before.(IntrState) /\
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning).
Proof.
  intros sg priority before result after [_ Hstep].
  destruct (before.(TskState).(prioTbl) priority) as [| |tid];
    try (destruct Hstep as [_ ->]; split; reflexivity).
  destruct Hstep as [old [Hnode Hstep]].
  destruct (Z.eqb old.(dly) 0); destruct Hstep as [_ ->]; [split; reflexivity|].
  split; [reflexivity|apply sched_wake_by_status_running_eq].
Qed.

Lemma time_dly_resume_critical_preserves_generic_source :
  forall sg priority before result after view,
  time_dly_resume_critical_code sg priority before result after ->
  task_resume_generic_source view before -> task_resume_generic_source view after.
Proof.
  intros sg priority before result after view Hstep Hsource.
  destruct (time_dly_resume_critical_preserves_control _ _ _ _ _ Hstep)
    as [Hintr Hrunning].
  unfold task_resume_generic_source, sched_disabled_entry_source,
    sched_disabled_isr_source in *; rewrite Hintr, Hrunning; exact Hsource.
Qed.

Lemma time_dly_resume_critical_success_ready_nonempty :
  forall sg priority before result after,
  time_dly_resume_critical_code sg priority before result after ->
  snd result = true -> after.(SchedState).(readyList) <> [].
Proof.
  intros sg priority before result after [_ Hstep] Hready.
  destruct (before.(TskState).(prioTbl) priority) as [| |tid];
    try (destruct Hstep as [-> _]; discriminate).
  destruct Hstep as [old [Hnode Hstep]].
  destruct (Z.eqb old.(dly) 0); destruct Hstep as [-> ->]; [discriminate|].
  cbn [snd] in Hready.
  assert (Hmember : In tid
    (sched_wake_by_status sg before.(TskState) before.(SchedState) tid
      (encode_task_status (task_expire_delay old).(stat))).(readyList)).
  { apply (proj2 (sched_wake_by_status_membership sg before.(TskState)
      before.(SchedState) tid (encode_task_status (task_expire_delay old).(stat)) tid)).
    right; split; [reflexivity|].
    change (task_is_suspended (task_expire_delay old).(stat) = false).
    rewrite task_expire_delay_preserves_suspension.
    apply Bool.negb_true_iff in Hready; exact Hready. }
  change ((sched_wake_by_status sg before.(TskState) before.(SchedState) tid
    (encode_task_status (task_expire_delay old).(stat))).(readyList) <> []).
  intro Hempty; rewrite Hempty in Hmember; contradiction.
Qed.

(** Exact source prefix, through the actual Restore endpoint. Save and
    Restore are reused as operations, not as equality of their endpoint
    states. The original/active/returned contexts remain distinct. *)
Definition time_dly_resume_source_history environment critical sg original mask
  priority initial result returned restored : Prop :=
  exists active saved acquired released,
    task_resume_save_program environment critical sg original mask
      initial (active, saved) acquired /\
    time_dly_resume_critical_code sg priority acquired result released /\
    task_resume_restore_program environment critical sg active released returned restored.

Definition time_dly_resume_prefix_program environment critical sg original mask priority
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  if Z.leb 63 priority then StateRelMonad.ret ((42, false), original)
  else StateRelMonad.bind (task_resume_save_program environment critical sg original mask)
    (fun entered => StateRelMonad.bind (time_dly_resume_critical_code sg priority)
      (fun result => StateRelMonad.bind
        (task_resume_restore_program environment critical sg (fst entered))
        (fun returned => StateRelMonad.ret (result, returned)))).

Lemma time_dly_resume_prefix_program_iff :
  forall environment critical sg original mask priority before error schedule returned current,
  time_dly_resume_prefix_program environment critical sg original mask priority
    before ((error, schedule), returned) current <->
  if Z.leb 63 priority then
    error = 42 /\ schedule = false /\ returned = original /\ current = before
  else time_dly_resume_source_history environment critical sg original mask priority
    before (error, schedule) returned current.
Proof.
  intros environment critical sg original mask priority before error schedule returned current.
  unfold time_dly_resume_prefix_program; destruct (Z.leb 63 priority).
  - change ((((error, schedule), returned) = ((42, false), original) /\ before = current) <->
      error = 42 /\ schedule = false /\ returned = original /\ current = before).
    split; [intros [Heq Hstate]; inversion Heq; auto|].
    intros [-> [-> [-> ->]]]; split; reflexivity.
  - split.
    + intros [[active saved] [acquired [Hsave [result [released [Hcritical
        [resumed [restored [Hrestore [Hresult Hcurrent]]]]]]]]]].
      inversion Hresult; subst result resumed restored.
      exists active, saved, acquired, released; auto.
    + intros [active [saved [acquired [released [Hsave [Hcritical Hrestore]]]]]].
      exists (active, saved), acquired; split; [exact Hsave|].
      exists (error, schedule), released; split; [exact Hcritical|].
      exists returned, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma time_dly_resume_prefix_safe_continuation :
  forall environment critical sg original mask priority
    (continuation : ((Z * bool) * TaskResumeCaller) -> program UCOS2_Verify_State Z)
    before error schedule returned current X,
  time_dly_resume_prefix_program environment critical sg original mask priority
    before ((error, schedule), returned) current ->
  safeExec (fun state => state = before)
    (StateRelMonad.bind
      (time_dly_resume_prefix_program environment critical sg original mask priority) continuation) X ->
  safeExec (fun state => state = current) (continuation ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original mask priority continuation before error schedule
    returned current X Hprefix Hsafe.
  eapply (highstepbind_derive
    (time_dly_resume_prefix_program environment critical sg original mask priority)
    continuation (fun state => state = before) ((error, schedule), returned)
    (fun state => state = current)).
  - intros state ->; exists current; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

(** Source tail: schedule exactly when the protected operation made the
    delayed task ready. The public instance below uses the real Scheduler
    operation; its source precondition is produced from the acquired protocol. *)
Definition time_dly_resume_tail
  (schedule : TaskResumeCaller -> program UCOS2_Verify_State unit)
  (result : (Z * bool) * TaskResumeCaller) : program UCOS2_Verify_State Z :=
  if snd (fst result) then
    StateRelMonad.bind (schedule (snd result)) (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition time_dly_resume_composed_program environment critical sg original mask priority
  (schedule : TaskResumeCaller -> program UCOS2_Verify_State unit)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind
    (time_dly_resume_prefix_program environment critical sg original mask priority)
    (time_dly_resume_tail schedule).

Lemma time_dly_resume_nonschedule_safe_return :
  forall environment critical sg original mask priority schedule before error returned current X,
  time_dly_resume_prefix_program environment critical sg original mask priority
    before ((error, false), returned) current ->
  safeExec (fun state => state = before)
    (time_dly_resume_composed_program environment critical sg original mask priority schedule) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret error) X.
Proof.
  intros environment critical sg original mask priority schedule before error returned current X Hprefix Hsafe.
  exact (time_dly_resume_prefix_safe_continuation environment critical sg original mask priority
    (time_dly_resume_tail schedule) before error false returned current X Hprefix Hsafe).
Qed.

Lemma time_dly_resume_schedule_safe_continuation :
  forall environment critical sg original mask priority schedule before error returned current X,
  time_dly_resume_prefix_program environment critical sg original mask priority
    before ((error, true), returned) current ->
  safeExec (fun state => state = before)
    (time_dly_resume_composed_program environment critical sg original mask priority schedule) X ->
  safeExec (fun state => state = current)
    (StateRelMonad.bind (schedule returned) (fun _ => StateRelMonad.ret error)) X.
Proof.
  intros environment critical sg original mask priority schedule before error returned current X Hprefix Hsafe.
  exact (time_dly_resume_prefix_safe_continuation environment critical sg original mask priority
    (time_dly_resume_tail schedule) before error true returned current X Hprefix Hsafe).
Qed.

Lemma time_dly_resume_early_safe_return :
  forall environment critical sg original mask priority schedule before X,
  63 <= priority ->
  safeExec (fun state => state = before)
    (time_dly_resume_composed_program environment critical sg original mask priority schedule) X ->
  safeExec (fun state => state = before) (StateRelMonad.ret 42) X.
Proof.
  intros environment critical sg original mask priority schedule before X Hrange Hsafe.
  eapply time_dly_resume_nonschedule_safe_return; [|exact Hsafe].
  apply time_dly_resume_prefix_program_iff.
  rewrite (proj2 (Z.leb_le _ _) Hrange); auto.
Qed.

Lemma time_dly_resume_schedule_endpoint_safe_return :
  forall (schedule : program UCOS2_Verify_State unit) before current (error : Z) X,
  schedule before tt current ->
  safeExec (fun state => state = before)
    (StateRelMonad.bind schedule (fun _ => StateRelMonad.ret error)) X ->
  safeExec (fun state => state = current) (StateRelMonad.ret error) X.
Proof. intros; eapply task_resume_schedule_endpoint_safe_return; eassumption. Qed.

(** Only the six accessed TCB fields are exposed. In particular StatPend
    is NOT left in the TaskResume five-field residual. Event/Flag links,
    messages, stack, names and every non-target slot remain owned there. *)
Definition time_dly_resume_node_fields : list TCBLayoutField :=
  map TCBCommonField [TCBStat; TCBStatPend; TCBDly; TCBY; TCBBitX; TCBBitY].

Definition time_dly_resume_node_frame sg state tid node : Assertion :=
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid))
    (filter (fun field =>
      if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields then false else true)
      (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile))) (task_layout_image sg node) **
  task_public_storage_without_task sg state.(TskState) tid **
  UCharArray.missing_i sg.(g_OSRdyTbl) (node.(curPrio) / 8) 0 8
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
  sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Definition time_dly_resume_node_cells sg state tid node : Assertion :=
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStat) (Some (encode_task_status node.(stat))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStatPend) (Some (encode_pend_status node.(statPend))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBDly) (Some node.(dly)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBY) (Some (task_resume_y node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitX) (Some (task_resume_bit_x node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitY) (Some (task_resume_bit_y node)) **
  sg.(g_OSRdyGrp) # UChar |-> task_resume_group sg state **
  (sg.(g_OSRdyTbl) + task_resume_y node * sizeof(UCHAR)) # UChar |-> task_resume_row state node.

Lemma tcb_configured_storage_split_time_dly_resume_fields :
  forall multi profile base image,
  tcb_configured_storage_rep multi profile base image --||--
  (tcb_layout_cell multi base (TCBCommonField TCBStat) (image (TCBCommonField TCBStat)) **
   tcb_layout_cell multi base (TCBCommonField TCBStatPend) (image (TCBCommonField TCBStatPend)) **
   tcb_layout_cell multi base (TCBCommonField TCBDly) (image (TCBCommonField TCBDly)) **
   tcb_layout_cell multi base (TCBCommonField TCBY) (image (TCBCommonField TCBY)) **
   tcb_layout_cell multi base (TCBCommonField TCBBitX) (image (TCBCommonField TCBBitX)) **
   tcb_layout_cell multi base (TCBCommonField TCBBitY) (image (TCBCommonField TCBBitY)) **
   TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
     (filter (fun field => if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields
       then false else true) (tcb_configured_fields multi profile)) image).
Proof.
  intros multi profile base image.
  assert (Hreorder :
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
      (tcb_configured_fields multi profile) image =
    TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
      (time_dly_resume_node_fields ++ filter
        (fun field => if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields
          then false else true) (tcb_configured_fields multi profile)) image).
  { unfold TaskFieldStorage.store_fields; f_equal.
    apply functional_extensionality; intros [common| | | | | | |]; try destruct common;
      destruct multi, profile; reflexivity. }
  assert (Hnodup : NoDup (time_dly_resume_node_fields ++ filter
    (fun field => if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields
      then false else true) (tcb_configured_fields multi profile))).
  { apply NoDup_app.
    - unfold time_dly_resume_node_fields; repeat constructor; simpl; intuition discriminate.
    - apply NoDup_filter; apply tcb_configured_fields_nodup.
    - intros field Hselected Hin; apply filter_In in Hin; destruct Hin as [_ Hin].
      destruct (in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields);
        [discriminate|contradiction]. }
  unfold tcb_configured_storage_rep; rewrite Hreorder.
  unfold time_dly_resume_node_fields at 1; cbn [map app].
  cbn [time_dly_resume_node_fields map app] in Hnodup.
  do 6 (rewrite (TaskFieldStorage.store_fields_cons _ _ _ _ _ _ _ Hnodup);
    apply NoDup_cons_iff in Hnodup; destruct Hnodup as [_ Hnodup]).
  split; entailer!.
Qed.

Lemma time_dly_resume_node_split : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_inv sg state |--
  time_dly_resume_node_cells sg state tid node ** time_dly_resume_node_frame sg state tid node.
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched sg state); Intros.
  sep_apply_l_atomic (task_public_storage_split_task sg state.(TskState) tid node Hnode).
  unfold used_task_rep, task_slot_storage_rep.
  rewrite tcb_configured_storage_split_time_dly_resume_fields.
  unfold sched_raw_rep.
  sep_apply_l_atomic (sched_rows_split_cell sg state.(TskState) state.(SchedState).(readyList)
    (task_resume_y node) Hy).
  unfold time_dly_resume_node_cells, time_dly_resume_node_frame,
    task_resume_group, task_resume_row, task_resume_y, task_resume_bit_x, task_resume_bit_y.
  entailer!.
Qed.

Lemma time_dly_resume_node_merge : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  time_dly_resume_node_cells sg state tid node ** time_dly_resume_node_frame sg state tid node |--
  UCOS2_inv sg state.
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  sep_apply_r_atomic (UCOS2_inv_merge_updated_task_storage_sched sg state state Hvalid eq_refl).
  sepcon_assoc_change.
  sep_apply_r_atomic (task_public_storage_merge_task sg state.(TskState) tid node Hnode).
  unfold used_task_rep, task_slot_storage_rep.
  rewrite tcb_configured_storage_split_time_dly_resume_fields.
  unfold time_dly_resume_node_cells, time_dly_resume_node_frame, sched_raw_rep,
    task_resume_row, task_resume_y, task_resume_group, task_resume_bit_x, task_resume_bit_y.
  sepcon_assoc_change.
  sep_apply_r_atomic (sched_rows_merge_cell sg state.(TskState) state.(SchedState).(readyList)
    (node.(curPrio) / 8) Hy).
  entailer!.
Qed.

Lemma time_dly_resume_field_residual_eq : forall multi profile base node sg,
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (filter (fun field => if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields
      then false else true) (tcb_configured_fields multi profile))
    (task_layout_image sg (task_expire_delay node)) =
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec (tcb_layout_cell multi base)
    (filter (fun field => if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields
      then false else true) (tcb_configured_fields multi profile)) (task_layout_image sg node).
Proof.
  intros; unfold TaskFieldStorage.store_fields; f_equal.
  apply functional_extensionality; intros [common| | | | | | |]; try destruct common;
    destruct multi, profile; reflexivity.
Qed.

Lemma time_dly_resume_updated_fields_merge : forall sg tasks tid node,
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStat) (Some (encode_task_status (task_expire_delay node).(stat))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBStatPend) (Some (encode_pend_status (task_expire_delay node).(statPend))) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBDly) (Some 0) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBY) (Some (task_resume_y node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitX) (Some (task_resume_bit_x node)) **
  tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid)
    (TCBCommonField TCBBitY) (Some (task_resume_bit_y node)) **
  TaskFieldStorage.store_fields TCBLayoutField_eq_dec
    (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg tid))
    (filter (fun field => if in_dec TCBLayoutField_eq_dec field time_dly_resume_node_fields
      then false else true) (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile))) (task_layout_image sg node) **
  task_public_storage_without_task sg tasks tid |--
  task_public_storage sg (glob_task_set_usedtask tasks tid (task_expire_delay node)).
Proof.
  intros; sep_apply_r_atomic (task_public_storage_merge_updated_task sg tasks tid (task_expire_delay node)).
  unfold used_task_rep, task_slot_storage_rep.
  rewrite tcb_configured_storage_split_time_dly_resume_fields.
  rewrite time_dly_resume_field_residual_eq.
  unfold task_resume_y, task_resume_bit_x, task_resume_bit_y; entailer!.
Qed.

Lemma time_dly_resume_mask_frame_update :
  forall environment critical saved_local sg caller saved acquired state tid node,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_resume_mask_frame environment critical saved_local sg caller saved acquired state |--
  task_resume_mask_frame environment critical saved_local sg caller saved acquired
    (time_dly_resume_state sg state tid node).
Proof.
  intros environment critical saved_local sg caller saved acquired state tid node Hnode.
  assert (Hobservation : forall slot updated,
    (glob_task_set_usedtask state.(TskState) tid (task_expire_delay node)).(inUsedTaskStates) slot = Some updated ->
    exists old, state.(TskState).(inUsedTaskStates) slot = Some old /\
      updated.(taskGeneration) = old.(taskGeneration) /\ updated.(tcbStkPtr) = old.(tcbStkPtr)).
  { intros slot updated Hupdated; cbn [glob_task_set_usedtask inUsedTaskStates] in Hupdated.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot.
      injection Hupdated as Hupdated; subst updated; exists node; auto.
    - exists updated; auto. }
  destruct caller as [call|view]; [|reflexivity].
  unfold task_resume_mask_frame; Intros.
  assert (Hcoverage : task_stack_live_coverage state.(TskState) (task_stack_call_active_key call))
    by assumption.
  assert (Hafter : task_stack_live_coverage
    (time_dly_resume_state sg state tid node).(TskState) (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)).
    - intros slot updated Hupdated.
      destruct (Hobservation slot updated Hupdated) as [old [Hold [Hgeneration Hstack]]].
      exists old; split; assumption.
    - reflexivity.
    - exact Hcoverage. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local (time_dly_resume_state sg state tid node)).
  { unfold task_tcb_init_continuation_capsules.
    apply kernel_saved_continuation_publication_spec.kernel_saved_continuation_map_reindex.
    intros key payload updated Hstack Hupdated Hg.
    destruct (Hobservation (fst key) updated Hupdated) as [old [Hold [Hgen Hsp]]].
    exists old; repeat split; auto. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.

(** A source-domain diagnostic, not a newly imposed public precondition.
    The existing generic caller permits the left side; its actual Scheduler
    entry needs the right side, which is false in this domain. *)
Lemma time_dly_resume_stopped_unlocked_generic_entry : forall view state,
  state.(SchedState).(isRunning) = false -> state.(IntrState).(lockNesting) = 0 ->
  task_resume_generic_source view state /\ ~ sched_disabled_entry_source view state.
Proof.
  intros view state Hstopped Hlock; split; [left; exact Hstopped|].
  unfold sched_disabled_entry_source, sched_disabled_isr_source.
  intros [[handler [interrupted [Hcontext [Hrunning Hagrees]]]]|Hpositive];
    [congruence|lia].
Qed.

Lemma time_dly_resume_stopped_unlocked_selects : forall state,
  state.(IntrState).(intNesting) = 0 -> state.(IntrState).(lockNesting) = 0 ->
  os_sched_selection_enabled state = true.
Proof. intros; apply os_sched_selection_enabled_iff; auto. Qed.

Lemma time_dly_resume_boot_has_no_current_storage : forall sg call state,
  call.(os_sched_call_origin) = BootInvocation ->
  ~ os_sched_current_storage_binding sg call state.
Proof.
  intros sg call state Hboot Hbinding.
  unfold os_sched_current_storage_binding in Hbinding; cbv zeta in Hbinding.
  destruct Hbinding as [Hrunning _]; rewrite Hboot in Hrunning; discriminate.
Qed.

Lemma time_dly_resume_boot_priority_free : forall sg task_name flag_name memory_name names priority,
  (UCOS2_boot_state sg task_name flag_name memory_name names).(TskState).(prioTbl) priority = PTFree.
Proof. reflexivity. Qed.

Lemma time_dly_resume_pending_fields : forall node,
  encode_task_status (task_expire_delay node).(stat) =
    (if task_status_has_pending (encode_task_status node.(stat))
     then Z.land (encode_task_status node.(stat)) 200 else encode_task_status node.(stat)) /\
  encode_pend_status (task_expire_delay node).(statPend) =
    (if task_status_has_pending (encode_task_status node.(stat)) then 1 else 0) /\
  (task_expire_delay node).(dly) = 0.
Proof.
  intros node; cbn [task_expire_delay stat statPend dly].
  rewrite task_status_after_timeout_encoding.
  unfold task_status_timeout; destruct task_status_has_pending;
    cbn [fst snd task_status_clear_wait task_pend_any_mask encode_pend_status]; auto.
Qed.

Lemma time_dly_resume_wait_resources_unchanged : forall node,
  (task_expire_delay node).(eventPtr) = node.(eventPtr) /\
  (task_expire_delay node).(eventMultiWaitEvents) = node.(eventMultiWaitEvents) /\
  (task_expire_delay node).(eventMultiRdy) = node.(eventMultiRdy) /\
  (task_expire_delay node).(tcbFlagNode) = node.(tcbFlagNode) /\
  (task_expire_delay node).(tcbFlagsRdy) = node.(tcbFlagsRdy) /\
  (task_expire_delay node).(msg) = node.(msg) /\
  (task_expire_delay node).(nextTCB) = node.(nextTCB) /\
  (task_expire_delay node).(prevTCB) = node.(prevTCB).
Proof. intros; repeat split; reflexivity. Qed.

Lemma time_dly_resume_caller_source_update : forall sg state tid node caller,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_resume_caller_source sg caller state ->
  task_resume_caller_source sg caller (time_dly_resume_state sg state tid node).
Proof.
  intros sg state tid node caller Hnode Hsource.
  assert (Hcurrent : (time_dly_resume_state sg state tid node).(SchedState).(curTaskID) =
    state.(SchedState).(curTaskID)).
  { change ((sched_wake_by_status sg state.(TskState) state.(SchedState) tid
      (encode_task_status (task_expire_delay node).(stat))).(curTaskID) =
      state.(SchedState).(curTaskID)).
    unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. }
  assert (Hrunning : (time_dly_resume_state sg state tid node).(SchedState).(isRunning) =
    state.(SchedState).(isRunning)) by apply sched_wake_by_status_running_eq.
  destruct caller as [call|view].
  - destruct Hsource as [[Horigin [Hactive Hsource]] [Havailable Haddress]].
    unfold task_resume_caller_source, kernel_call_task_source.
    split; [|split; [exact Havailable|exact Haddress]].
    split; [exact Horigin|]; split.
    + eapply glob_task_set_usedtask_preserves_invocation_active;
        [exact Hnode|reflexivity|exact Hactive].
    + unfold task_execution_current in *.
      destruct call.(os_sched_call_origin); [exact I|rewrite Hcurrent; exact Hsource].
  - unfold task_resume_caller_source, task_resume_generic_source,
      sched_disabled_entry_source, sched_disabled_isr_source in *.
    rewrite Hrunning; exact Hsource.
Qed.

Lemma time_dly_resume_critical_preserves_caller_source :
  forall sg priority before result after caller,
  time_dly_resume_critical_code sg priority before result after ->
  task_resume_caller_source sg caller before -> task_resume_caller_source sg caller after.
Proof.
  intros sg priority before result after caller [_ Hstep] Hsource.
  destruct (before.(TskState).(prioTbl) priority) as [| |tid];
    try (destruct Hstep as [_ ->]; exact Hsource).
  destruct Hstep as [old [Hnode Hstep]].
  destruct (Z.eqb old.(dly) 0); destruct Hstep as [_ ->]; [exact Hsource|].
  eapply time_dly_resume_caller_source_update; eassumption.
Qed.

Lemma time_dly_resume_restore_ready_nonempty :
  forall critical sg invocation priority before result released restored,
  kernel_sched_ready_clients critical -> UCOS2_state_inv sg before ->
  time_dly_resume_critical_code sg priority before result released -> snd result = true ->
  critical_region_interval critical sg invocation released restored ->
  restored.(SchedState).(readyList) <> [].
Proof.
  intros critical sg invocation priority before result released restored Hclients Hvalid Heffect Hready Hinterval.
  eapply critical_region_interval_preserves_sched_ready.
  - exact Hclients.
  - exact Hinterval.
  - eapply time_dly_resume_critical_preserves_validity; eassumption.
  - eapply time_dly_resume_critical_success_ready_nonempty; eassumption.
Qed.

(** This is a source-history property, not a consequence added to global
    validity. The explicit boot constructor establishes it. To use it at
    an API call, the actual entry producer and each actual registered
    client must provide it; the generic stopped caller alone does not. *)
Definition time_dly_resume_stopped_tasks_undelayed (state : UCOS2_Verify_State) : Prop :=
  state.(SchedState).(isRunning) = false ->
  forall tid node, state.(TskState).(inUsedTaskStates) tid = Some node -> node.(dly) = 0.

Lemma time_dly_resume_boot_tasks_undelayed : forall sg task_name flag_name memory_name names,
  time_dly_resume_stopped_tasks_undelayed
    (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof. intros; intros Hstopped tid node Hnode; discriminate. Qed.

Lemma time_dly_resume_creation_preserves_undelayed : forall action sg before after,
  time_dly_resume_stopped_tasks_undelayed before ->
  kernel_client_step (task_creation_client action) sg before after ->
  time_dly_resume_stopped_tasks_undelayed after.
Proof.
  intros action sg before after Hbefore [Hguard [_ ->]].
  destruct action as [priority entry slot rest image|priority entry allocation image|
    priority invocation node|invocation].
  - exact Hbefore.
  - exact Hbefore.
  - intros Hstopped tid current Hcurrent.
    change (before.(SchedState).(isRunning) = false) in Hstopped.
    change ((task_commit before.(TskState) priority invocation node).(inUsedTaskStates) tid =
      Some current) in Hcurrent.
    destruct Hguard as [_ [Hready _]].
    assert (Hzero : node.(dly) = 0).
    { unfold is_effectively_ready in Hready.
      destruct (Z.eqb (task_non_suspension_bits node.(stat)) 0); [|discriminate].
      apply Bool.andb_true_iff in Hready; apply Z.eqb_eq; exact (proj2 Hready). }
    pose proof (task_commit_observation Z dly before.(TskState) priority invocation node tid
      (fun _ _ _ => eq_refl)) as Hobservation.
    rewrite Hcurrent in Hobservation; cbn [option_map] in Hobservation.
    destruct (Z.eq_dec tid node.(taskID)).
    + injection Hobservation as Heq; rewrite Heq; exact Hzero.
    + destruct (before.(TskState).(inUsedTaskStates) tid) as [old|] eqn:Hold; [|discriminate].
      cbn [option_map] in Hobservation; injection Hobservation as Heq; rewrite Heq.
      exact (Hbefore Hstopped tid old Hold).
  - exact Hbefore.
Qed.

Lemma time_dly_resume_creation_client_resources : forall action,
  kernel_client_preserves_resources
    (fun sg state => UCOS2_state_inv sg state /\ time_dly_resume_stopped_tasks_undelayed state)
    (task_creation_client action).
Proof.
  intros action sg before after [Hvalid Hundelayed] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources (task_creation_client action)
    (task_creation_client_certificate action) sg before after Hvalid Hstep) as [Hafter Hframes].
  split; [split; [exact Hafter|]|exact Hframes].
  eapply time_dly_resume_creation_preserves_undelayed; eassumption.
Qed.

(** The stack-publication client is the source action that actually hands the
    initialized TCB image and stack buffer to the kernel.  Its certificate
    supplies validity, frames, event frames and continuation preservation;
    the case-local history property is transported through the same concrete
    endpoint.  This is deliberately separate from [task_creation_client]:
    the latter is only the TCB/lifecycle projection and does not publish the
    stack map. *)
Lemma time_dly_resume_stack_publication_preserves_undelayed :
  forall publication sg before after,
  time_dly_resume_stopped_tasks_undelayed before ->
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  time_dly_resume_stopped_tasks_undelayed after.
Proof.
  intros publication sg before after Hbefore Hstep.
  destruct (task_create_stack_publication_raw_projection sg publication before after Hstep)
    as [Hraw Hafter].
  assert (Hraw_history :
    time_dly_resume_stopped_tasks_undelayed
      (task_create_stack_publication_raw_state sg publication before)).
  { eapply time_dly_resume_creation_preserves_undelayed; eassumption. }
  unfold time_dly_resume_stopped_tasks_undelayed in *.
  rewrite Hafter.
  cbn [replace_TskS TskState glob_task_set_parked_stacks] in *.
  exact Hraw_history.
Qed.

Lemma time_dly_resume_stack_publication_client_resources : forall publication,
  kernel_client_preserves_resources
    (fun sg state => UCOS2_state_inv sg state /\ time_dly_resume_stopped_tasks_undelayed state)
    (task_create_stack_publication_client publication).
Proof.
  intros publication sg before after [Hvalid Hbefore] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources
    (task_create_stack_publication_client publication)
    (task_create_stack_publication_certificate publication)
    sg before after Hvalid Hstep)
    as [Hafter [Htask [Hevent Hcontinuation]]].
  split; [split; [exact Hafter|]|].
  - eapply time_dly_resume_stack_publication_preserves_undelayed; eassumption.
  - split; [exact Htask|]. split; [exact Hevent|exact Hcontinuation].
Qed.

(** Registered clients are classified at the source boundary.  A real stack
    publication is consumed through its concrete certificate above; every
    other registered action must provide its own preservation instance.  No
    creation-only client is silently substituted for publication. *)
Definition time_dly_resume_registered_clients (critical : CriticalRegionResources) : Prop :=
  forall action, critical.(critical_region_clients) action ->
    (exists publication, action = task_create_stack_publication_client publication) \/
    kernel_client_preserves_resources
      (fun sg state => UCOS2_state_inv sg state /\ time_dly_resume_stopped_tasks_undelayed state)
      action.

Lemma time_dly_resume_registered_clients_resources : forall critical,
  time_dly_resume_registered_clients critical ->
  forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources
      (fun sg state => UCOS2_state_inv sg state /\ time_dly_resume_stopped_tasks_undelayed state)
      action.
Proof.
  intros critical Hregistered action Hmember.
  destruct (Hregistered action Hmember) as [[publication Haction]|Hother].
  - rewrite Haction; apply time_dly_resume_stack_publication_client_resources.
  - exact Hother.
Qed.

(** A source history records existing initialization, invocation registration,
    and actual registered source actions. No constructor tests the desired
    undelayed property. Its heap endpoint is supplied separately and indexed
    by the identical state in the public contract. *)
Inductive time_dly_resume_initialization_source_history
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (task_name flag_name memory_name : addr) (names : NameResourceState)
  : UCOS2_Verify_State -> Prop :=
| time_dly_resume_history_initialized :
    time_dly_resume_initialization_source_history critical sg
      task_name flag_name memory_name names
      (UCOS2_boot_state sg task_name flag_name memory_name names)
| time_dly_resume_history_begin : forall before origin,
    time_dly_resume_initialization_source_history critical sg
      task_name flag_name memory_name names before ->
    task_invocation_origin_live before.(TskState) origin ->
    time_dly_resume_initialization_source_history critical sg
      task_name flag_name memory_name names
      (replace_TskS (task_begin_invocation origin before.(TskState)) before)
| time_dly_resume_history_client : forall action before after,
    time_dly_resume_initialization_source_history critical sg
      task_name flag_name memory_name names before ->
    critical.(critical_region_clients) action ->
    kernel_client_step action sg before after ->
    time_dly_resume_initialization_source_history critical sg
      task_name flag_name memory_name names after.

Lemma time_dly_resume_initialization_history_invariant :
  forall critical sg task_name flag_name memory_name names initial,
  UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) ->
  time_dly_resume_registered_clients critical ->
  time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names initial ->
  UCOS2_state_inv sg initial /\ time_dly_resume_stopped_tasks_undelayed initial.
Proof.
  intros critical sg task_name flag_name memory_name names initial Hboot Hclients Hhistory.
  induction Hhistory as [|before origin Hhistory IH Hlive|action before after Hhistory IH Hmember Hstep].
  - split; [exact Hboot|apply time_dly_resume_boot_tasks_undelayed].
  - destruct IH as [Hvalid Hdelays]; split.
    + apply UCOS2_begin_task_invocation_preserves_validity; assumption.
    + exact Hdelays.
  - exact (proj1 (time_dly_resume_registered_clients_resources critical Hclients
      action Hmember sg before after IH Hstep)).
Qed.

(** The initialized ownership is an explicit composition input, not a claim
    that this file proves OSInit. It is consumed at the actual boot constructor,
    never manufactured from its pure validity. *)
Lemma time_dly_resume_initialized_output_history :
  forall critical sg task_name flag_name memory_name names,
  UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) |--
  coq_prop (time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names
    (UCOS2_boot_state sg task_name flag_name memory_name names)) &&
  UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros; apply _derivable1_andp_intros; [|reflexivity].
  apply derivable1s_coq_prop_r; constructor.
Qed.

Lemma time_dly_resume_begin_invocation_source_post :
  forall critical sg task_name flag_name memory_name names before origin,
  time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names before ->
  task_invocation_origin_live before.(TskState) origin ->
  let after := replace_TskS (task_begin_invocation origin before.(TskState)) before in
  UCOS2_inv sg before |--
  coq_prop (time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names after) && UCOS2_inv sg after.
Proof.
  intros critical sg task_name flag_name memory_name names before origin Hhistory Hlive after.
  sep_apply_l_atomic (UCOS2_inv_begin_task_invocation sg before origin Hlive).
  apply _derivable1_andp_intros; [|reflexivity].
  apply derivable1s_coq_prop_r; apply time_dly_resume_history_begin; assumption.
Qed.

Lemma time_dly_resume_stack_publication_source_post :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    critical sg task_name flag_name memory_name names publication before,
  time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names before ->
  critical.(critical_region_clients) (task_create_stack_publication_client publication) ->
  UCOS2_state_inv sg before -> task_create_stack_publication_input sg publication before ->
  let after := task_create_stack_publication_state sg publication before in
  task_create_stack_publication_resources external platform port abi sg publication before |--
  coq_prop (time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names after) &&
  (UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi critical sg task_name flag_name memory_name names
    publication before Hhistory Hmember Hvalid Hinput after.
  pose proof (task_create_stack_publication_source_post external platform port abi
    sg publication before Hvalid Hinput) as Hpost.
  cbv zeta in Hpost; fold after in Hpost.
  sep_apply_l_atomic Hpost; Intros.
  assert (Hafter : time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names after).
  { eapply time_dly_resume_history_client; [exact Hhistory|exact Hmember|exact H]. }
  entailer!.
Qed.

(** The existing invariant transport is sufficient. Hclients and Hbefore
    are the missing source obligations, not newly accepted caller facts.
    This conditional lemma is not a completed startup protocol. *)
Lemma time_dly_resume_interval_tasks_undelayed : forall critical sg invocation before after,
  (forall action, critical_region_clients critical action ->
    kernel_client_preserves_resources
      (fun sg state => UCOS2_state_inv sg state /\ time_dly_resume_stopped_tasks_undelayed state) action) ->
  UCOS2_state_inv sg before -> time_dly_resume_stopped_tasks_undelayed before ->
  critical_region_interval critical sg invocation before after ->
  time_dly_resume_stopped_tasks_undelayed after.
Proof.
  intros critical sg invocation before after Hclients Hvalid Hbefore Hinterval.
  pose proof (critical_region_interval_transports_invariant
    (fun sg state => UCOS2_state_inv sg state /\ time_dly_resume_stopped_tasks_undelayed state)
    critical sg invocation before after Hclients Hinterval (conj Hvalid Hbefore)) as Hafter.
  exact (proj2 (proj1 Hafter)).
Qed.

(** Consume the history/client protocol over the exact Generic Save interval.
    The interval here is the one emitted by [task_resume_save_program], not a
    separate abstract transition. *)
Lemma time_dly_resume_generic_save_consumes_history :
  forall environment critical sg view mask initial saved acquired,
  time_dly_resume_registered_clients critical ->
  UCOS2_state_inv sg initial ->
  time_dly_resume_stopped_tasks_undelayed initial ->
  task_resume_save_program environment critical sg (ResumeGenericCaller view) mask
    initial (ResumeGenericCaller view, saved) acquired ->
  time_dly_resume_stopped_tasks_undelayed acquired.
Proof.
  intros environment critical sg view mask initial saved acquired Hregistered
    Hvalid Hbefore Hsave.
  cbn [task_resume_save_program] in Hsave.
  destruct Hsave as [_ [Hinterval _]].
  eapply time_dly_resume_interval_tasks_undelayed;
    [apply time_dly_resume_registered_clients_resources; exact Hregistered
    |exact Hvalid|exact Hbefore|exact Hinterval].
Qed.

(** Compose the source-backed boot history with the SAME Generic Save interval.
    This is the caller-facing bridge: OSInit/application/all-kernel instances
    remain composition premises, while the resulting acquired state is the
    endpoint consumed by the protected Time operation. *)
Lemma time_dly_resume_initialization_then_generic_save :
  forall critical sg task_name flag_name memory_name names
    environment view mask initial saved acquired,
  UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) ->
  time_dly_resume_registered_clients critical ->
  time_dly_resume_initialization_source_history critical sg
    task_name flag_name memory_name names initial ->
  task_resume_save_program environment critical sg (ResumeGenericCaller view) mask
    initial (ResumeGenericCaller view, saved) acquired ->
  time_dly_resume_stopped_tasks_undelayed acquired.
Proof.
  intros critical sg task_name flag_name memory_name names
    environment view mask initial saved acquired Hboot Hregistered Hhistory Hsave.
  destruct (time_dly_resume_initialization_history_invariant critical sg
    task_name flag_name memory_name names initial Hboot Hregistered Hhistory)
    as [Hvalid Hbefore].
  eapply time_dly_resume_generic_save_consumes_history; eassumption.
Qed.

Lemma time_dly_resume_critical_success_running : forall sg priority before result released,
  time_dly_resume_stopped_tasks_undelayed before ->
  time_dly_resume_critical_code sg priority before result released -> snd result = true ->
  before.(SchedState).(isRunning) = true.
Proof.
  intros sg priority before result released Hhistory [_ Hstep] Hready.
  destruct before.(SchedState).(isRunning) eqn:Hrunning; [reflexivity|].
  destruct (before.(TskState).(prioTbl) priority) as [| |tid];
    try (destruct Hstep as [-> _]; discriminate).
  destruct Hstep as [node [Hnode Hstep]].
  rewrite (Hhistory Hrunning tid node Hnode) in Hstep.
  cbn [Z.eqb] in Hstep; destruct Hstep as [-> _]; discriminate.
Qed.

Lemma time_dly_resume_generic_success_disabled : forall sg priority acquired result released view,
  time_dly_resume_stopped_tasks_undelayed acquired ->
  task_resume_generic_source view acquired ->
  time_dly_resume_critical_code sg priority acquired result released -> snd result = true ->
  sched_disabled_entry_source view released.
Proof.
  intros sg priority acquired result released view Hhistory Hsource Hcode Hready.
  pose proof (time_dly_resume_critical_success_running _ _ _ _ _ Hhistory Hcode Hready) as Hrunning.
  pose proof (task_resume_generic_running_entry view acquired Hsource Hrunning) as Hentry.
  destruct (time_dly_resume_critical_preserves_control _ _ _ _ _ Hcode) as [Hintr Hrun].
  unfold sched_disabled_entry_source, sched_disabled_isr_source in *.
  rewrite Hintr, Hrun; exact Hentry.
Qed.

Lemma time_dly_resume_generic_restore_disabled :
  forall critical sg invocation priority acquired result released restored view,
  sched_disabled_completed_clients critical view -> UCOS2_state_inv sg acquired ->
  time_dly_resume_stopped_tasks_undelayed acquired -> task_resume_generic_source view acquired ->
  time_dly_resume_critical_code sg priority acquired result released -> snd result = true ->
  critical_region_interval critical sg invocation released restored ->
  sched_disabled_entry_source view restored.
Proof.
  intros critical sg invocation priority acquired result released restored view
    Hclients Hvalid Hhistory Hsource Hcode Hready Hinterval.
  assert (Hreleased : UCOS2_state_inv sg released)
    by (eapply time_dly_resume_critical_preserves_validity; eassumption).
  destruct (sched_disabled_interval_preserves_context critical sg view invocation released restored
    Hclients Hreleased Hinterval) as [_ Hcontext].
  eapply sched_disabled_context_rely_preserves_entry_source; [exact Hcontext|].
  eapply time_dly_resume_generic_success_disabled; eassumption.
Qed.

(** Only the startup Generic alternative needs the initialization history.
    Already-disabled callers and genuine Task callers retain their existing
    entry protocols. The caller supplies the actual family, never a replacement. *)
Definition time_dly_resume_startup_protocol critical sg initial : Prop :=
  time_dly_resume_registered_clients critical /\
  exists task_name flag_name memory_name names,
    UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) /\
    time_dly_resume_initialization_source_history critical sg
      task_name flag_name memory_name names initial.

Definition time_dly_resume_entry_protocol critical sg caller initial : Prop :=
  match caller with
  | ResumeTaskCaller _ => True
  | ResumeGenericCaller view => sched_disabled_entry_source view initial \/
      time_dly_resume_startup_protocol critical sg initial
  end.

Definition time_dly_resume_acquired_protocol caller acquired : Prop :=
  match caller with
  | ResumeTaskCaller _ => True
  | ResumeGenericCaller view => sched_disabled_entry_source view acquired \/
      time_dly_resume_stopped_tasks_undelayed acquired
  end.

Definition time_dly_resume_acquire_facts environment critical sg original active mask initial acquired saved :=
  task_resume_acquire_facts environment critical sg original active mask initial acquired saved /\
  time_dly_resume_acquired_protocol active acquired.

Lemma time_dly_resume_save_acquired_protocol :
  forall environment critical sg original active mask initial acquired saved,
  UCOS2_state_inv sg initial -> time_dly_resume_entry_protocol critical sg original initial ->
  task_resume_acquire_facts environment critical sg original active mask initial acquired saved ->
  time_dly_resume_acquired_protocol active acquired.
Proof.
  intros environment critical sg original active mask initial acquired saved Hvalid Hentry Hfacts.
  destruct Hfacts as [Hsame [Hacquired [Hinterval [Hsaved [Hclients [Hsource Hsave]]]]]].
  destruct original as [original|view], active as [active|active];
    cbn [task_resume_same_caller] in Hsame; try contradiction.
  - exact I.
  - subst active; cbn [time_dly_resume_entry_protocol time_dly_resume_acquired_protocol] in *.
    destruct Hentry as [Hdisabled|[Hregistered [task_name [flag_name [memory_name [names [Hboot Hhistory]]]]]]].
    + left. cbn [task_resume_save_program fst snd] in Hsave.
      destruct Hsave as [_ [Hsame_interval _]].
      destruct Hclients as [Hcompleted _].
      destruct (sched_disabled_interval_preserves_context critical sg view
        view.(os_execution_invocation) initial acquired Hcompleted Hvalid Hsame_interval)
        as [_ Hcontext].
      eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
    + right; eapply time_dly_resume_initialization_then_generic_save; eassumption.
Qed.

Lemma time_dly_resume_save_output_acquire :
  forall environment critical saved_local sg original mask saved initial,
  UCOS2_state_inv sg initial -> task_resume_clients environment critical original ->
  task_resume_caller_source sg original initial ->
  time_dly_resume_entry_protocol critical sg original initial ->
  task_resume_save_output environment critical saved_local sg original mask saved initial |--
  EX active acquired,
    coq_prop (time_dly_resume_acquire_facts environment critical sg original active mask initial acquired saved) &&
    task_resume_masked environment critical saved_local sg active saved acquired acquired.
Proof.
  intros environment critical saved_local sg original mask saved initial Hvalid Hclients Hsource Hentry.
  sep_apply_l_atomic (task_resume_save_output_acquire__resume_calls_returns environment critical
    saved_local sg original mask saved initial Hvalid Hclients Hsource); Intros active acquired.
  assert (Hprotocol : time_dly_resume_acquired_protocol active acquired).
  { eapply time_dly_resume_save_acquired_protocol; eassumption. }
  Exists active acquired; unfold time_dly_resume_acquire_facts; entailer!.
Qed.

Lemma time_dly_resume_acquired_protocol_restore_disabled :
  forall critical sg view priority acquired result released restored,
  sched_disabled_completed_clients critical view -> UCOS2_state_inv sg acquired ->
  time_dly_resume_acquired_protocol (ResumeGenericCaller view) acquired ->
  task_resume_generic_source view acquired ->
  time_dly_resume_critical_code sg priority acquired result released -> snd result = true ->
  critical_region_interval critical sg view.(os_execution_invocation) released restored ->
  sched_disabled_entry_source view restored.
Proof.
  intros critical sg view priority acquired result released restored Hclients Hvalid
    [Hdisabled|Hhistory] Hsource Hcode Hready Hinterval.
  - assert (Hreleased : UCOS2_state_inv sg released)
      by (eapply time_dly_resume_critical_preserves_validity; eassumption).
    destruct (time_dly_resume_critical_preserves_control _ _ _ _ _ Hcode) as [Hintr Hrun].
    assert (Hentry : sched_disabled_entry_source view released).
    { unfold sched_disabled_entry_source, sched_disabled_isr_source in *.
      rewrite Hintr, Hrun; exact Hdisabled. }
    destruct (sched_disabled_interval_preserves_context critical sg view
      view.(os_execution_invocation) released restored Hclients Hreleased Hinterval)
      as [_ Hcontext].
    eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
  - eapply time_dly_resume_generic_restore_disabled; eassumption.
Qed.

Definition time_dly_resume_return_facts environment critical sg original returned mask initial
  priority result ready_path restored : Prop :=
  task_resume_same_caller returned original /\ UCOS2_state_inv sg restored /\
  task_resume_clients environment critical returned /\ task_resume_caller_source sg returned restored /\
  (match returned with
  | ResumeTaskCaller _ => ready_path = true -> restored.(SchedState).(readyList) <> []
  | ResumeGenericCaller view => ready_path = true -> sched_disabled_entry_source view restored
  end) /\
  time_dly_resume_source_history environment critical sg original mask priority
    initial (result, ready_path) returned restored.

Lemma time_dly_resume_restore_output_return :
  forall environment critical saved_local sg original active mask initial acquired saved
    priority result ready_path released,
  time_dly_resume_acquire_facts environment critical sg original active mask initial acquired saved ->
  time_dly_resume_critical_code sg priority acquired (result, ready_path) released ->
  task_resume_restore_output environment critical saved_local sg active saved released |--
  EX returned restored,
    coq_prop (time_dly_resume_return_facts environment critical sg original returned mask initial
      priority result ready_path restored) &&
    task_resume_closed environment critical saved_local sg returned mask restored.
Proof.
  intros environment critical saved_local sg original active mask initial acquired saved
    priority result ready_path released [Hacquire Hprotocol] Hcode.
  destruct Hacquire as [Hsame [Hvalid [Hinitial [Hsaved [Hclients [Hacquired_source Hsave]]]]]].
  assert (Hreleased : UCOS2_state_inv sg released)
    by (eapply time_dly_resume_critical_preserves_validity; eassumption).
  assert (Hcaller : task_resume_caller_source sg active released)
    by (eapply time_dly_resume_critical_preserves_caller_source; eassumption).
  destruct Hsaved as [Hsaved Hmask]; destruct active as [active|view].
  - cbn [task_resume_restore_output].
    unfold task_tcb_init_continuation_restore_post; Intros returned restored.
    destruct H as [Htrace [Hi [Ho [Hs [Hrestored Hcoverage]]]]].
    assert (Hsame_return : task_tcb_init_stack_same_call returned active)
      by (unfold task_tcb_init_stack_same_call; tauto).
    pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
    destruct Hclients as [Hready Hreturns].
    destruct Hcaller as [Hsource [Havailable Haddress]].
    assert (Hreturned_source : kernel_call_task_source returned restored).
    { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned active restored Hsame_return)).
      exact (task_tcb_init_stack_registered_source_preserved environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical sg active returned released restored
        Hreleased Hsame_return Htrace Hsource). }
    pose proof (Hreturns sg active returned released restored Hreleased Hsource Havailable
      Hsame_return Htrace) as Hreturned_available.
    assert (Hreturned_address :
      tcb_field_address (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
        task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot)) by (rewrite Hs; exact Haddress).
    assert (Hsame_final : task_resume_same_caller (ResumeTaskCaller returned) original).
    { exact (task_resume_same_caller_trans__resume_calls_returns (ResumeTaskCaller returned)
        (ResumeTaskCaller active) original Hsame_return Hsame). }
    assert (Hnonempty : ready_path = true -> restored.(SchedState).(readyList) <> []).
    { intros Hpath; eapply time_dly_resume_restore_ready_nonempty;
        [exact Hready|exact Hvalid|exact Hcode|exact Hpath|exact Hinterval]. }
    assert (Hhistory : time_dly_resume_source_history environment critical sg original mask
      priority initial (result, ready_path) (ResumeTaskCaller returned) restored).
    { exists (ResumeTaskCaller active), saved, acquired, released; split; [exact Hsave|].
      split; [exact Hcode|]; cbn [task_resume_restore_program]; split; assumption. }
    assert (Hfacts : time_dly_resume_return_facts environment critical sg original
      (ResumeTaskCaller returned) mask initial priority result ready_path restored).
    { unfold time_dly_resume_return_facts; cbn [task_resume_clients task_resume_caller_source]; tauto. }
    Exists (ResumeTaskCaller returned) restored; rewrite Hmask.
    cbn [task_resume_closed]; unfold task_tcb_init_continuation_save_input,
      task_create_continuation_input, task_tcb_init_continuation_capsules; entailer!.
  - cbn [task_resume_restore_output]; Intros restored; rename H into Hinterval.
    destruct Hclients as [Hclients Hreturns].
    destruct (task_resume_generic_interval_preserves_source critical sg view released restored
      Hclients Hreturns Hreleased Hcaller Hinterval) as [Hrestored Hsource].
    assert (Hdisabled : ready_path = true -> sched_disabled_entry_source view restored).
    { intro Hpath; eapply time_dly_resume_acquired_protocol_restore_disabled;
        [exact Hclients|exact Hvalid|exact Hprotocol|exact Hacquired_source|
         exact Hcode|exact Hpath|exact Hinterval]. }
    assert (Hhistory : time_dly_resume_source_history environment critical sg original mask
      priority initial (result, ready_path) (ResumeGenericCaller view) restored).
    { exists (ResumeGenericCaller view), saved, acquired, released; split; [exact Hsave|].
      split; [exact Hcode|]; cbn [task_resume_restore_program]; split; [reflexivity|exact Hinterval]. }
    assert (Hfacts : time_dly_resume_return_facts environment critical sg original
      (ResumeGenericCaller view) mask initial priority result ready_path restored).
    { unfold time_dly_resume_return_facts; cbn [task_resume_clients task_resume_caller_source]; tauto. }
    Exists (ResumeGenericCaller view) restored; rewrite Hmask; entailer!.
Qed.

Lemma time_dly_resume_return_facts_safe_return :
  forall environment critical sg original returned mask initial priority result restored schedule X,
  priority < 63 ->
  time_dly_resume_return_facts environment critical sg original returned mask initial
    priority result false restored ->
  safeExec (fun state => state = initial)
    (time_dly_resume_composed_program environment critical sg original mask priority schedule) X ->
  safeExec (fun state => state = restored) (StateRelMonad.ret result) X.
Proof.
  intros environment critical sg original returned mask initial priority result restored schedule X
    Hrange [_ [_ [_ [_ [_ Hhistory]]]]] Hsafe.
  eapply time_dly_resume_nonschedule_safe_return; [|exact Hsafe].
  apply time_dly_resume_prefix_program_iff; rewrite (proj2 (Z.leb_gt _ _) Hrange); exact Hhistory.
Qed.

Lemma time_dly_resume_sched_storage_merge : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  sg.(g_OSRdyGrp) # UChar |->
    (if task_is_suspended node.(stat) then task_resume_group sg state
     else Z.lor (task_resume_group sg state) (task_resume_bit_y node)) **
  (sg.(g_OSRdyTbl) + task_resume_y node * sizeof(UCHAR)) # UChar |->
    (if task_is_suspended node.(stat) then task_resume_row state node
     else Z.lor (task_resume_row state node) (task_resume_bit_x node)) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (task_resume_y node) 0 8
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
  sched_physical_rep sg state.(SchedState) |--
  sched_raw_rep sg (time_dly_resume_state sg state tid node).(TskState)
    (time_dly_resume_state sg state tid node).(SchedState).
Proof.
  intros sg state tid node Hvalid Hnode.
  pose proof (task_resume_reserved_bits_clear__resume_storage sg state tid node Hvalid Hnode) as Hbits.
  pose proof (proj2 (task_resume_live_priority_range__resume_storage sg state tid node Hvalid Hnode)) as Hy.
  assert (Htest : task_status_is_suspended (encode_task_status (task_expire_delay node).(stat)) =
    task_is_suspended node.(stat)) by apply task_expire_delay_preserves_suspension.
  change (time_dly_resume_state sg state tid node).(TskState) with
    (glob_task_set_usedtask state.(TskState) tid (task_expire_delay node)).
  change (time_dly_resume_state sg state tid node).(SchedState) with
    (sched_wake_by_status sg state.(TskState) state.(SchedState) tid
      (encode_task_status (task_expire_delay node).(stat))).
  unfold task_resume_group, task_resume_row, task_resume_y, task_resume_bit_x, task_resume_bit_y in *.
  destruct (task_is_suspended node.(stat)) eqn:Hsuspended.
  - unfold sched_wake_by_status; rewrite Htest.
    assert (Hrep : sched_raw_rep sg (glob_task_set_usedtask state.(TskState) tid (task_expire_delay node))
      state.(SchedState) = sched_raw_rep sg state.(TskState) state.(SchedState)).
    { apply sched_raw_rep_priority_ext; intros slot Hin.
      eapply glob_task_set_usedtask_observation; [exact Hnode|reflexivity]. }
    rewrite Hrep; unfold sched_raw_rep.
    sep_apply_l_atomic (sched_rows_merge_cell sg state.(TskState) state.(SchedState).(readyList)
      (node.(curPrio) / 8) Hy); entailer!.
  - assert (Hr : is_effectively_ready (task_expire_delay node).(stat) (task_expire_delay node).(dly) = true).
    { exact (eq_trans (task_expire_delay_ready_test node Hbits) (f_equal negb Htest)). }
    unfold sched_raw_rep; rewrite sched_wake_by_status_physical_rep_eq.
    rewrite (sched_wake_by_status_eq_wake_task sg state.(TskState) state.(SchedState) tid
      (encode_task_status (task_expire_delay node).(stat)) (task_expire_delay node)
      (task_expire_delay_ready_test node Hbits)).
    destruct (sched_wake_ready_encoding sg state.(TskState) state.(SchedState) tid node
      (task_expire_delay node) Hnode eq_refl Hr) as [Hgroup Hrows].
    rewrite Hgroup.
    sep_apply_l_atomic (sched_rows_merge_wake sg state.(TskState) state.(SchedState) tid node
      (task_expire_delay node) Hnode eq_refl Hr Hy).
    entailer!.
Qed.

Lemma time_dly_resume_resource_residual_eq : forall sg state tid node,
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_raw_rep_missing_task_storage_sched sg state =
    UCOS2_raw_rep_missing_task_storage_sched sg (time_dly_resume_state sg state tid node).
Proof.
  intros sg state tid node Hnode.
  unfold UCOS2_raw_rep_missing_task_storage_sched, time_dly_resume_state;
    cbn [replace_SchedS replace_TskS TskState IntrState EventState TickState FlagState
      MemoryState TimerState StatsState ControlState NameState parkedTaskStacks glob_task_set_usedtask].
  rewrite (event_raw_rep_change_task_index sg state.(TskState)
    (glob_task_set_usedtask state.(TskState) tid (task_expire_delay node)) state.(EventState));
    [reflexivity|].
  apply event_wait_priority_agreement_encodes.
  eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hnode|reflexivity].
Qed.

Lemma time_dly_resume_task_sched_resources_merge : forall sg state tid node,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some node -> node.(dly) <> 0 ->
  task_public_storage sg (time_dly_resume_state sg state tid node).(TskState) **
  sched_raw_rep sg (time_dly_resume_state sg state tid node).(TskState)
    (time_dly_resume_state sg state tid node).(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state |--
  UCOS2_inv sg (time_dly_resume_state sg state tid node).
Proof.
  intros sg state tid node Hvalid Hnode Hd.
  apply UCOS2_inv_merge_updated_task_storage_sched.
  - eapply time_dly_resume_preserves_validity; eassumption.
  - apply time_dly_resume_resource_residual_eq; exact Hnode.
Qed.


(** Concrete public operation: both source-specific Scheduler alternatives
    are the existing call programs. There is no OSRunning test in this tail. *)
Definition time_dly_resume_program environment critical sg caller mask priority
  : program UCOS2_Verify_State Z :=
  time_dly_resume_composed_program environment critical sg caller mask priority
    (fun returned => task_resume_schedule_call_program environment critical sg returned mask).

Definition time_dly_resume_safe environment critical sg caller mask priority initial
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = initial)
    (time_dly_resume_program environment critical sg caller mask priority) X.

Definition time_dly_resume_post environment critical saved_local sg original mask initial priority result
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  (coq_prop (63 <= priority /\ result = 42 /\
      safeExec (fun state => state = initial) (StateRelMonad.ret result) X) &&
    task_resume_closed environment critical saved_local sg original mask initial) ||
  (EX returned restored ready_path,
    coq_prop (0 <= priority < 63 /\ task_resume_same_caller returned original /\
      time_dly_resume_source_history environment critical sg original mask priority initial
        (result, ready_path) returned restored) &&
    (if ready_path then
       task_resume_sched_refined_post environment critical saved_local sg returned mask restored result X
     else coq_prop (safeExec (fun state => state = restored) (StateRelMonad.ret result) X) &&
       task_resume_closed environment critical saved_local sg returned mask restored)).

Lemma time_dly_resume_return_facts_prefix_program :
  forall environment critical sg original returned mask initial priority result ready_path restored,
  priority < 63 ->
  time_dly_resume_return_facts environment critical sg original returned mask initial
    priority result ready_path restored ->
  time_dly_resume_prefix_program environment critical sg original mask priority
    initial ((result, ready_path), returned) restored.
Proof.
  intros environment critical sg original returned mask initial priority result ready_path restored
    Hrange [_ [_ [_ [_ [_ Hhistory]]]]].
  apply time_dly_resume_prefix_program_iff.
  rewrite (proj2 (Z.leb_gt _ _) Hrange); exact Hhistory.
Qed.

Lemma time_dly_resume_return_facts_sched_safe :
  forall environment critical sg original returned mask initial priority result restored X,
  priority < 63 ->
  time_dly_resume_return_facts environment critical sg original returned mask initial
    priority result true restored ->
  time_dly_resume_safe environment critical sg original mask priority initial X ->
  task_resume_sched_safe environment critical sg returned mask restored result X.
Proof.
  intros environment critical sg original returned mask initial priority result restored X
    Hrange Hfacts Hsafe.
  unfold task_resume_sched_safe.
  eapply (time_dly_resume_schedule_safe_continuation environment critical sg original mask priority
    (fun caller => task_resume_schedule_call_program environment critical sg caller mask)
    initial result returned restored X).
  - eapply time_dly_resume_return_facts_prefix_program; eassumption.
  - exact Hsafe.
Qed.

Lemma time_dly_resume_closed_sched_pre :
  forall environment critical saved_local sg original returned mask initial priority restored,
  time_dly_resume_return_facts environment critical sg original returned mask initial
    priority 0 true restored ->
  task_resume_closed environment critical saved_local sg returned mask restored |--
  task_resume_sched_pre environment critical saved_local sg returned mask restored.
Proof.
  intros environment critical saved_local sg original [returned|view] mask initial priority restored Hfacts.
  - destruct Hfacts as [_ [Hvalid [[Hready Hreturns] [Hsource [Hnonempty Hhistory]]]]].
    destruct Hsource as [Hsource [Havailable Haddress]].
    assert (Hcut : os_sched_call_cut sg returned restored).
    { eapply os_sched_call_cut_from_source; eauto. }
    cbn [task_resume_closed task_resume_sched_pre].
    unfold os_sched_continuation_call_pre, os_sched_continuation_pre.
    rewrite <- task_tcb_init_continuation_save_input_closed_world; entailer!.
  - destruct Hfacts as [_ [Hvalid [[Hclients Hreturns] [Hsource [Hdisabled Hhistory]]]]].
    specialize (Hdisabled eq_refl).
    cbn [task_resume_closed task_resume_sched_pre]; entailer!.
Qed.

Lemma time_dly_resume_early_return_post :
  forall environment critical saved_local sg original mask initial priority X,
  63 <= priority ->
  time_dly_resume_safe environment critical sg original mask priority initial X ->
  task_resume_closed environment critical saved_local sg original mask initial |--
  time_dly_resume_post environment critical saved_local sg original mask initial priority 42 X.
Proof.
  intros environment critical saved_local sg original mask initial priority X Hrange Hsafe.
  assert (Hreturn : safeExec (fun state => state = initial) (StateRelMonad.ret 42) X).
  { eapply time_dly_resume_early_safe_return; eassumption. }
  unfold time_dly_resume_post; Left; entailer!.
Qed.

Lemma time_dly_resume_closed_return_post :
  forall environment critical saved_local sg original returned mask initial priority result restored X,
  0 <= priority < 63 ->
  time_dly_resume_return_facts environment critical sg original returned mask initial
    priority result false restored ->
  time_dly_resume_safe environment critical sg original mask priority initial X ->
  task_resume_closed environment critical saved_local sg returned mask restored |--
  time_dly_resume_post environment critical saved_local sg original mask initial priority result X.
Proof.
  intros environment critical saved_local sg original returned mask initial priority result restored X
    Hrange Hfacts Hsafe.
  assert (Hreturn : safeExec (fun state => state = restored) (StateRelMonad.ret result) X).
  { eapply time_dly_resume_return_facts_safe_return; [exact (proj2 Hrange)|exact Hfacts|exact Hsafe]. }
  destruct Hfacts as [Hsame [_ [_ [_ [_ Hhistory]]]]].
  unfold time_dly_resume_post; Right; Exists returned restored false; entailer!.
Qed.

Lemma time_dly_resume_sched_return_post :
  forall environment critical saved_local sg original returned mask initial priority result restored X,
  0 <= priority < 63 ->
  time_dly_resume_return_facts environment critical sg original returned mask initial
    priority result true restored ->
  task_resume_sched_safe environment critical sg returned mask restored result X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored |--
  time_dly_resume_post environment critical saved_local sg original mask initial priority result X.
Proof.
  intros environment critical saved_local sg original returned mask initial priority result restored X
    Hrange Hfacts Hsafe.
  unfold task_resume_sched_safe in Hsafe.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored result X Hsafe).
  destruct Hfacts as [Hsame [_ [_ [_ [_ Hhistory]]]]].
  unfold time_dly_resume_post; Right; Exists returned restored true; entailer!.
Qed.
