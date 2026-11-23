Require Export Ucos2Verify.VC.code.queue.spec.q_post_proof_helpers.
Require Export Ucos2Verify.VC.code.task.spec.task_resume_api_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.ucos2_verify_inv.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Resume's Task world already includes the shared immutable lookup table;
    generic ISR/locked/boot worlds do not. EventTaskRdy needs exactly one. *)
Definition q_post_extra_tables sg caller : Assertion :=
  match caller with ResumeTaskCaller _ => emp | ResumeGenericCaller _ => unmap_table_rep sg end.

Definition q_post_closed environment critical saved_local sg caller mask state : Assertion :=
  task_resume_closed environment critical saved_local sg caller mask state ** q_post_extra_tables sg caller.

Definition q_post_masked environment critical saved_local sg caller saved acquired released : Assertion :=
  task_resume_masked environment critical saved_local sg caller saved acquired released ** q_post_extra_tables sg caller.

Definition q_post_save_output environment critical saved_local sg caller mask saved before : Assertion :=
  task_resume_save_output environment critical saved_local sg caller mask saved before ** q_post_extra_tables sg caller.

Definition q_post_restore_output environment critical saved_local sg caller saved released : Assertion :=
  task_resume_restore_output environment critical saved_local sg caller saved released ** q_post_extra_tables sg caller.

(** The acquired snapshot is distinct from both the earlier type read and
    the actual Restore endpoint. A returned Task caller keeps its real
    context; same-call is not equality of whole contexts. *)
Definition q_post_prefix_program environment critical sg caller mask pe eid message
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((4, false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
      exists active saved acquired error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        q_post_critical sg QueuePostBack eid message acquired (error, schedule) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((encode_os_err_code error, schedule), returned)
    else result = ((1, false), caller) /\ restored = before.

(** OSQPost calls OS_Sched unconditionally after a wake. In particular,
    the Resume API's additional OSRunning load/guard is not copied here. *)
Definition q_post_tail environment critical sg mask
  (result : (Z * bool) * TaskResumeCaller) : program UCOS2_Verify_State Z :=
  if snd (fst result) then
    bind (task_resume_schedule_call_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition q_post_program environment critical sg caller mask pe eid message
  : program UCOS2_Verify_State Z :=
  bind (q_post_prefix_program environment critical sg caller mask pe eid message)
    (q_post_tail environment critical sg mask).

Definition q_post_safe environment critical sg caller mask pe eid message before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (q_post_program environment critical sg caller mask pe eid message) X.

Definition q_post_caller_result environment critical sg original mask pe eid message before
  error returned current : Prop :=
  exists prefix_caller restored schedule,
    q_post_prefix_program environment critical sg original mask pe eid message before
      ((error, schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition q_post_return_safe current error (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret error) X.

Definition q_post_post environment critical saved_local sg original mask pe eid message before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (q_post_caller_result environment critical sg original mask pe eid message before error returned current /\
      q_post_return_safe current error X) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_post_program_null : forall environment critical sg caller mask eid message before,
  q_post_program environment critical sg caller mask 0 eid message before 4 before.
Proof.
  intros; exists ((4, false), caller), before; split.
  - unfold q_post_prefix_program; cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_program_wrong_type : forall environment critical sg caller mask pe eid message before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_post_program environment critical sg caller mask pe eid message before 1 before.
Proof.
  intros; exists ((1, false), caller), before; split.
  - change (q_post_prefix_program environment critical sg caller mask pe eid message
      before ((1, false), caller) before).
    unfold q_post_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H),
      (proj2 (Z.eqb_neq _ _) H0); split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_prefix_protected : forall environment critical sg original active returned mask
  pe eid message before acquired released restored saved error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  q_post_critical sg QueuePostBack eid message acquired (error, schedule) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  q_post_prefix_program environment critical sg original mask pe eid message before
    ((encode_os_err_code error, schedule), returned) restored.
Proof.
  intros; unfold q_post_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0; cbn.
  exists active, saved, acquired, error, schedule, released, returned; auto.
Qed.

Lemma q_post_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid message before restored error schedule X,
  q_post_prefix_program environment critical sg original mask pe eid message before
    ((error, schedule), returned) restored ->
  q_post_safe environment critical sg original mask pe eid message before X ->
  safeExec (fun state => state = restored)
    (q_post_tail environment critical sg mask ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid message before restored error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (q_post_prefix_program environment critical sg original mask pe eid message)
    (q_post_tail environment critical sg mask) (fun state => state = before)
    ((error, schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_post_program_nonschedule : forall environment critical sg original returned mask
  pe eid message before restored error,
  q_post_prefix_program environment critical sg original mask pe eid message before
    ((error, false), returned) restored ->
  q_post_program environment critical sg original mask pe eid message before error restored.
Proof.
  intros; exists ((error, false), returned), restored; split; [assumption|].
  cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_program_schedule : forall environment critical sg original returned final mask
  pe eid message before restored current error,
  q_post_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  task_resume_schedule_program environment critical sg returned mask restored final current ->
  q_post_program environment critical sg original mask pe eid message before error current.
Proof.
  intros; exists ((error, true), returned), restored; split; [assumption|].
  cbn [q_post_tail]; exists tt, current; split; [|split; reflexivity].
  exists final, current; split; [assumption|split; reflexivity].
Qed.

Lemma q_post_safe_return : forall environment critical sg caller mask pe eid message before current error X,
  q_post_program environment critical sg caller mask pe eid message before error current ->
  q_post_safe environment critical sg caller mask pe eid message before X ->
  q_post_return_safe current error X.
Proof.
  intros environment critical sg caller mask pe eid message before current error X Hprogram Hsafe.
  eapply (highstependret_derive
    (q_post_program environment critical sg caller mask pe eid message)
    (fun state => state = before) error (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_post_closed_return : forall environment critical saved_local sg original returned mask
  pe eid message before current error X,
  q_post_caller_result environment critical sg original mask pe eid message before error returned current ->
  q_post_safe environment critical sg original mask pe eid message before X ->
  q_post_closed environment critical saved_local sg returned mask current |--
  q_post_post environment critical saved_local sg original mask pe eid message before error X.
Proof.
  intros.
  assert (Hprogram : q_post_program environment critical sg original mask pe eid message before error current).
  { pose proof H as Hresult; destruct Hresult as [prefix_caller [restored [schedule [Hprefix Htail]]]].
    destruct schedule.
    - eapply q_post_program_schedule with (final := returned); eassumption.
    - destruct Htail as [-> ->]; eapply q_post_program_nonschedule; exact Hprefix. }
  pose proof (q_post_safe_return _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0).
  unfold q_post_post; Exists returned current; entailer!.
Qed.

Lemma q_post_schedule_extra_tables : forall environment critical sg caller mask before returned current,
  task_resume_schedule_program environment critical sg caller mask before returned current ->
  q_post_extra_tables sg returned = q_post_extra_tables sg caller.
Proof.
  intros environment critical sg [call|view] mask before returned current Hprogram.
  - destruct Hprogram as [next [middle [Hstep [Heq Hstate]]]]; subst returned; reflexivity.
  - destruct Hprogram as [[active saved] [acquired [Hsave [[] [released [Hstep Hrestore]]]]]].
    destruct active; [contradiction|]. destruct Hsave as [-> Hrest].
    destruct returned; [contradiction|]. destruct Hrestore as [-> Hinterval]; reflexivity.
Qed.

Lemma q_post_sched_return : forall environment critical saved_local sg original returned mask
  pe eid message before restored error X,
  q_post_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  q_post_safe environment critical sg original mask pe eid message before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  q_post_post environment critical saved_local sg original mask pe eid message before error X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid message before restored error X
    Hprefix Hsafe.
  pose proof (q_post_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_post_tail] in Htail.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Htail).
  unfold task_resume_sched_refined_post; Intros final current.
  assert (Hresult : q_post_caller_result environment critical sg original mask pe eid message
    before error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  unfold q_post_post, q_post_closed; Exists final current; rewrite Htables; entailer!.
  apply derivable1_andp_elim1.
Qed.

Definition q_post_call_input critical sg caller pe before eid observed : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 2 ->
      mutex_query_handle_protocol critical sg
        (task_resume_view caller).(os_execution_invocation) eid)).

(** Explicit C caller scheduling protocol, conditional only on the real
    wake prefix. This is not a CPU postcondition or an extra source guard.
    Boot enqueue/full and both pre-Save errors impose no scheduling cut;
    ISR/locked callers use the already checked generic disabled contract. *)
Definition q_post_schedule_cut (environment : TaskStackCallEnvironment) critical sg caller state : Prop :=
  match caller with
  | ResumeTaskCaller call => kernel_sched_ready_clients critical /\ os_sched_call_cut sg call state
  | ResumeGenericCaller view => sched_disabled_completed_clients critical view /\
      UCOS2_state_inv sg state /\ sched_disabled_entry_source view state
  end.

Definition q_post_schedule_protocol environment critical sg caller mask pe eid message before : Prop :=
  forall returned restored error,
    q_post_prefix_program environment critical sg caller mask pe eid message before
      ((error, true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Lemma q_post_closed_sched_pre : forall environment critical saved_local sg caller mask state,
  q_post_schedule_cut environment critical sg caller state ->
  q_post_closed environment critical saved_local sg caller mask state |--
  task_resume_sched_pre environment critical saved_local sg caller mask state **
    q_post_extra_tables sg caller.
Proof.
  intros environment critical saved_local sg [call|view] mask state Hcut;
    unfold q_post_closed;
    cbn [q_post_schedule_cut task_resume_closed task_resume_sched_pre q_post_extra_tables] in *.
  - unfold os_sched_continuation_call_pre, os_sched_continuation_pre.
    rewrite <- (task_tcb_init_continuation_save_input_closed_world
      environment critical saved_local sg call mask state); entailer!.
  - entailer!.
Qed.

Definition q_post_outside_frame environment saved_local sg caller mask state : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
      (kernel_call_execution_owned environment.(task_stack_call_external)
         environment.(task_stack_call_platform) call mask **
       task_tcb_init_continuation_capsules environment saved_local state ** unmap_table_rep sg)
  | ResumeGenericCaller view =>
      interrupt_platform_running environment.(task_stack_call_platform)
        view.(os_execution_invocation) view.(os_execution_origin) mask **
      os_execution_view_resources environment.(task_stack_call_external) view ** unmap_table_rep sg
  end.

Lemma q_post_closed_equiv : forall environment critical saved_local sg caller mask state,
  UCOS2_state_inv sg state ->
  q_post_closed environment critical saved_local sg caller mask state --||--
  UCOS2_inv sg state ** q_post_outside_frame environment saved_local sg caller mask state.
Proof.
  intros environment critical saved_local sg [call|view] mask state Hvalid;
    unfold q_post_closed, q_post_extra_tables, task_resume_closed, q_post_outside_frame;
    unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
      task_tcb_init_continuation_capsules, sched_disabled_closed, critical_region_outside;
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running;
    unfold UCOS2_inv; split; timeout 60 entailer!.
Qed.

(** Uniform residual: the lookup table is separated explicitly because
    EventTaskRdy borrows it; generic callers never acquire a Task lease. *)
Definition q_post_mask_frame environment critical saved_local sg caller saved acquired released : Assertion :=
  match caller with
  | ResumeTaskCaller call =>
      coq_prop (task_stack_live_coverage released.(TskState) (task_stack_call_active_key call)) &&
      (critical_region_masked environment.(task_stack_call_platform) critical sg
         call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
       os_sched_context_resources environment.(task_stack_call_external) call **
       task_tcb_init_continuation_capsules environment saved_local released)
  | ResumeGenericCaller view =>
      critical_region_masked environment.(task_stack_call_platform) critical sg
        view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
      os_execution_view_resources environment.(task_stack_call_external) view
  end.

Lemma q_post_masked_equiv : forall environment critical saved_local sg caller saved acquired released,
  q_post_masked environment critical saved_local sg caller saved acquired released --||--
  UCOS2_inv sg released ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg caller saved acquired released.
Proof.
  intros environment critical saved_local sg [call|view] saved acquired released;
    unfold q_post_masked, q_post_extra_tables, task_resume_masked, q_post_mask_frame;
    unfold task_tcb_init_continuation_restore_input, sched_disabled_masked;
    split; timeout 60 entailer!.
Qed.

Definition q_post_save_facts environment critical sg original active mask saved before acquired : Prop :=
  UCOS2_state_inv sg acquired /\
  critical_region_interval critical sg (task_resume_view original).(os_execution_invocation) before acquired /\
  interrupt_saved_value mask saved /\
  task_resume_save_program environment critical sg original mask before (active, saved) acquired.

Lemma q_post_save_output_acquire : forall environment critical saved_local sg original mask saved before,
  UCOS2_state_inv sg before ->
  q_post_save_output environment critical saved_local sg original mask saved before |--
  EX active acquired,
    coq_prop (q_post_save_facts environment critical sg original active mask saved before acquired) &&
    q_post_masked environment critical saved_local sg active saved acquired acquired.
Proof.
  intros environment critical saved_local sg [original|view] mask saved before Hvalid;
    unfold q_post_save_output; cbn [task_resume_save_output q_post_extra_tables].
  - unfold task_tcb_init_continuation_save_post; Intros active acquired.
    destruct H as [Hsave Hcoverage].
    pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
    pose proof (proj1 (critical_region_interval_transports_resources critical sg
      original.(os_sched_call_invocation) before acquired Hinterval Hvalid)) as Hafter.
    pose proof Hsave as [_ [_ [_ [_ Hsaved]]]].
    Exists (ResumeTaskCaller active) acquired.
    unfold q_post_save_facts, q_post_masked; cbn [task_resume_view os_sched_execution_view
      task_resume_save_program fst snd task_resume_masked q_post_extra_tables].
    unfold task_tcb_init_continuation_restore_input; entailer!.
  - Intros acquired; destruct H as [Hinterval Hsaved].
    pose proof (proj1 (critical_region_interval_transports_resources critical sg
      view.(os_execution_invocation) before acquired Hinterval Hvalid)) as Hafter.
    Exists (ResumeGenericCaller view) acquired.
    unfold q_post_save_facts, q_post_masked; cbn [task_resume_view task_resume_save_program
      fst snd task_resume_masked q_post_extra_tables].
    unfold sched_disabled_masked, UCOS2_inv; entailer!.
Qed.

Definition q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed current : Prop :=
  q_post_save_facts environment critical sg original active mask saved before acquired /\
  q_post_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q /\
  q_post_lookup acquired eid current /\ current.(eventType) = OS_EVENT_TYPE_Q /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma q_post_public_slot_is_queue : forall state eid observed,
  sem_query_public_slot state eid observed ->
  event_slot_type_value state.(EventState) eid = 2 ->
  q_post_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_Q.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype;
    unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype.
    split; [exact Hused|]. destruct observed.(eventType); cbn in Htype;
      try discriminate; reflexivity.
  - rewrite Hnone in Htype; discriminate.
Qed.

Lemma q_post_acquire_identity : forall environment critical sg original active mask saved
  pe before acquired eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  q_post_call_input critical sg original pe before eid observed ->
  event_slot_type_value before.(EventState) eid = 2 ->
  q_post_save_facts environment critical sg original active mask saved before acquired ->
  exists current,
    q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed current.
Proof.
  intros environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hsave.
  destruct Hinput as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  destruct (q_post_public_slot_is_queue before eid observed Hslot Htype) as [Hlookup Hqueue].
  destruct (mutex_query_handle_interval_preserves_identity critical sg
    (task_resume_view original).(os_execution_invocation) eid before acquired observed
    (Hprotocol Htype) (proj1 (proj2 Hsave)) Hvalid Hlookup)
    as [current [Hcurrent [Hg Hkind]]].
  exists current; unfold q_post_acquire_facts.
  split; [exact Hsave|]. split; [exact Hlookup|]. split; [exact Hqueue|].
  split; [exact Hcurrent|]. split; congruence.
Qed.

Lemma q_post_restore_output_return : forall environment critical saved_local sg active mask saved released,
  UCOS2_state_inv sg released -> interrupt_saved_value mask saved ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  EX returned current,
    coq_prop (task_resume_restore_program environment critical sg active released returned current /\
      UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.
Proof.
  intros environment critical saved_local sg [active|view] mask saved released Hvalid [_ Hmask];
    unfold q_post_restore_output; cbn [task_resume_restore_output q_post_extra_tables].
  - unfold task_tcb_init_continuation_restore_post; Intros returned current.
    destruct H as [Htrace [Hi [Ho [Hs [Hcurrent Hcoverage]]]]].
    assert (Hsame : task_tcb_init_stack_same_call returned active)
      by (unfold task_tcb_init_stack_same_call; tauto).
    Exists (ResumeTaskCaller returned) current.
    unfold q_post_closed; cbn [task_resume_restore_program task_resume_closed q_post_extra_tables].
    unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
      task_tcb_init_continuation_capsules; rewrite Hmask; entailer!.
  - Intros current.
    pose proof (proj1 (critical_region_interval_transports_resources critical sg
      view.(os_execution_invocation) released current H Hvalid)) as Hcurrent.
    Exists (ResumeGenericCaller view) current.
    unfold q_post_closed; cbn [task_resume_restore_program task_resume_closed q_post_extra_tables].
    rewrite Hmask; entailer!.
Qed.

Lemma q_post_mask_frame_event_update : forall environment critical saved_local sg caller saved acquired before after,
  before.(TskState) = after.(TskState) ->
  q_post_mask_frame environment critical saved_local sg caller saved acquired before |--
  q_post_mask_frame environment critical saved_local sg caller saved acquired after.
Proof.
  intros environment critical saved_local sg [call|view] saved acquired before after Heq;
    cbn [q_post_mask_frame]; [unfold task_tcb_init_continuation_capsules; rewrite Heq|]; reflexivity.
Qed.

Lemma q_post_mask_frame_wake_update : forall environment critical saved_local sg caller saved acquired state
  eid node tid old message,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  q_post_mask_frame environment critical saved_local sg caller saved acquired state |--
  q_post_mask_frame environment critical saved_local sg caller saved acquired
    (event_wake_state sg state eid node tid old PendQ message PendOK).
Proof.
  intros environment critical saved_local sg [call|view] saved acquired state eid node tid old message Hold;
    [|reflexivity].
  assert (Hobserve : forall slot updated,
    (event_wake_state sg state eid node tid old PendQ message PendOK).(TskState).(inUsedTaskStates) slot = Some updated ->
    exists previous, state.(TskState).(inUsedTaskStates) slot = Some previous /\
      previous.(taskGeneration) = updated.(taskGeneration) /\ previous.(tcbStkPtr) = updated.(tcbStkPtr)).
  { intros slot updated Hupdated.
    cbn [event_wake_state replace_SchedS replace_EventS replace_TskS TskState
      glob_task_set_usedtask inUsedTaskStates] in Hupdated.
    destruct (Z.eqb slot tid) eqn:Hslot.
    - apply Z.eqb_eq in Hslot; subst slot; injection Hupdated as Hupdated; subst updated;
        exists old; repeat split; assumption || reflexivity.
    - exists updated; auto. }
  unfold q_post_mask_frame; Intros.
  assert (Hcoverage : task_stack_live_coverage
    (event_wake_state sg state eid node tid old PendQ message PendOK).(TskState)
      (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)).
    - intros slot updated Hupdated.
      destruct (Hobserve slot updated Hupdated) as [previous [Hprevious [Hg Hsp]]].
      exists previous; split; [exact Hprevious|symmetry; exact Hg].
    - reflexivity.
    - exact H. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local
      (event_wake_state sg state eid node tid old PendQ message PendOK)).
  { unfold task_tcb_init_continuation_capsules.
    apply kernel_saved_continuation_map_reindex.
    intros key payload updated Hstack Hupdated Hg.
    destruct (Hobserve (fst key) updated Hupdated) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; repeat split; auto. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.
(** Source-facing consequences. These are C call adapters of the unchanged
    Save/Restore interfaces, not additional CPU laws or scheduling promises. *)
Definition q_post_type_context environment saved_local sg caller mask before eid : Assertion :=
  sem_query_type_frame sg before eid **
  q_post_outside_frame environment saved_local sg caller mask before.

Definition q_post_save_pre environment critical saved_local sg caller mask before pe eid observed : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\ pe <> 0 /\
    q_post_call_input critical sg caller pe before eid observed /\
    event_slot_type_value before.(EventState) eid = 2) &&
  q_post_closed environment critical saved_local sg caller mask before.

Definition q_post_save_result environment critical saved_local sg caller mask saved before eid observed : Assertion :=
  EX active acquired current,
    coq_prop (q_post_acquire_facts environment critical sg caller active mask saved
      before acquired eid observed current) &&
    q_post_masked environment critical saved_local sg active saved acquired acquired.

Lemma q_post_save_pre_raw : forall environment critical saved_local sg caller mask before pe eid observed,
  q_post_save_pre environment critical saved_local sg caller mask before pe eid observed |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof. intros; unfold q_post_save_pre; apply derivable1_andp_elim2. Qed.

Lemma q_post_save_result_consequence : forall environment critical saved_local sg caller mask saved before pe eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  q_post_call_input critical sg caller pe before eid observed ->
  event_slot_type_value before.(EventState) eid = 2 ->
  q_post_save_output environment critical saved_local sg caller mask saved before |--
  q_post_save_result environment critical saved_local sg caller mask saved before eid observed.
Proof.
  intros environment critical saved_local sg caller mask saved before pe eid observed Hvalid Hpe Hinput Htype.
  sep_apply_l_atomic (q_post_save_output_acquire environment critical saved_local sg caller mask saved before Hvalid).
  Intros active acquired.
  destruct (q_post_acquire_identity environment critical sg caller active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype H) as [current Hcurrent].
  unfold q_post_save_result; Exists active acquired current; entailer!.
Qed.

Definition q_post_effect sg eid message acquired (error schedule : Z) released : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    q_post_critical sg QueuePostBack eid message acquired (code, request) released.

Definition q_post_prefix_result environment critical sg caller mask pe eid message before
  (error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    q_post_prefix_program environment critical sg caller mask pe eid message before
      ((error, request), returned) current.

Definition q_post_restore_pre environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 2 /\
    UCOS2_state_inv sg released /\ q_post_effect sg eid message acquired error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition q_post_restore_post environment critical saved_local sg caller mask pe eid message before error schedule : Assertion :=
  EX returned current,
    coq_prop (q_post_prefix_result environment critical sg caller mask pe eid message before
      error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_post_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule,
  q_post_restore_pre environment critical saved_local sg caller active mask saved pe eid message
    before acquired released error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold q_post_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma q_post_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  UCOS2_state_inv sg released -> q_post_effect sg eid message acquired error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  q_post_restore_post environment critical saved_local sg caller mask pe eid message before error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid message before acquired released error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : q_post_prefix_result environment critical sg caller mask pe eid message before
    (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply q_post_prefix_protected;
      [exact Hpe|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold q_post_restore_post; Exists returned current; entailer!.
Qed.

Lemma q_post_nonschedule_return : forall environment critical saved_local sg caller mask pe eid message before error X,
  q_post_safe environment critical sg caller mask pe eid message before X ->
  q_post_restore_post environment critical saved_local sg caller mask pe eid message before error 0 |--
  q_post_post environment critical saved_local sg caller mask pe eid message before error X.
Proof.
  intros; unfold q_post_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; [discriminate|].
  assert (Hresult : q_post_caller_result environment critical sg caller mask pe eid message before error returned current).
  { exists returned, current, false; auto. }
  sep_apply_r_atomic (q_post_closed_return environment critical saved_local sg caller returned mask pe eid message before current error X Hresult H).
  entailer!.
Qed.

Lemma q_post_restored_schedule_pre : forall environment critical saved_local sg caller mask pe eid message before error,
  q_post_schedule_protocol environment critical sg caller mask pe eid message before ->
  q_post_restore_post environment critical saved_local sg caller mask pe eid message before error 1 |--
  EX returned current,
    coq_prop (q_post_prefix_result environment critical sg caller mask pe eid message before error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid message before error Hprotocol.
  unfold q_post_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]. pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current error Hprefix)).
  Exists returned current; entailer!.
Qed.

Definition q_post_group_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current : Assertion :=
  coq_prop (q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    q_post_profile sg /\ valid_event_id sg eid) &&
  (q_post_group_frame sg acquired eid current ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition q_post_sched_group state := encode_ready_grp state.(SchedState).(readyList) state.(TskState).
Definition q_post_sched_rows state := sched_row_values state.(TskState) state.(SchedState).(readyList).

Definition q_post_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current tid old : Assertion :=
  coq_prop (q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    q_post_profile sg /\ valid_event_id sg eid /\ q_post_group acquired current <> 0 /\
    event_task_rdy_entry sg acquired.(TskState) eid current tid old) &&
  (q_post_wake_frame sg acquired eid tid **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition q_post_pointer_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current q : Assertion :=
  coq_prop (q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    q_post_profile sg /\ valid_event_id sg eid /\ q_post_group acquired current = 0 /\
    current.(queueFields) = Some q /\ current.(waitList) = [] /\ queue_fields_consistency sg [] q) &&
  (q_post_field_frame sg acquired eid current EventPtrField ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition q_post_store_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current q free slots base : Assertion :=
  coq_prop (q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    q_post_profile sg /\ q_post_group acquired current = 0 /\ base = qcb_addr sg q.(qID) /\
    q_post_queue_facts sg acquired eid current q free slots) &&
  (q_post_queue_frame sg acquired eid free ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition q_post_slot_frame q slots : Assertion :=
  coq_prop (queue_entries q < q.(qSize)) &&
    PtrArray.mixed_missing_i q.(qStart) q.(qInIndex) 0 q.(qSize) slots.
Lemma q_post_group_cell_split : forall sg state eid node,
  q_post_lookup state eid node ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group state node **
      q_post_group_frame sg state eid node).
Proof.
  intros sg state eid node Hnode.
  pose proof (q_post_field_split_full sg state eid node EventGrpField Hnode ltac:(simpl; tauto)) as Hsplit.
  exact Hsplit.
Qed.

Lemma q_post_group_cell_merge : forall sg state eid node,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group state node **
    q_post_group_frame sg state eid node |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node Hvalid Hnode.
  exact (q_post_field_merge_full sg state eid node EventGrpField Hvalid Hnode ltac:(simpl; tauto)).
Qed.

Lemma q_post_acquire_original_type : forall environment critical sg original active mask saved
  before acquired eid observed current,
  q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed current ->
  event_slot_type_value before.(EventState) eid = 2.
Proof.
  intros environment critical sg original active mask saved before acquired eid observed current
    [_ [Hlookup [Hqueue Hrest]]].
  unfold event_slot_type_value; rewrite Hlookup, Hqueue; reflexivity.
Qed.
(** Scheduling admission is established from the actual C caller and the
    same completed Save/Restore traces. No CPU contract obtains readiness. *)
Lemma q_post_back_wake_state : forall sg state eid node message error after,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q ->
  q_post_critical sg QueuePostBack eid message state (error, true) after ->
  exists tid old,
    state.(TskState).(inUsedTaskStates) tid = Some old /\
    after = event_wake_state sg state eid node tid old PendQ message PendOK /\
    UCOS2_state_inv sg after.
Proof.
  intros sg state eid node message error after Hvalid Hnode Htype Hstep.
  pose proof (proj1 (q_post_critical_requests_schedule_iff sg QueuePostBack state eid node message
    (error, true) after Hnode Hstep) eq_refl) as [Hgroup Hrequest].
  destruct Hstep as [current [Hcurrent Hstep]].
  assert (current = node) by congruence; subst current.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hstep.
  destruct Hstep as [Hresult [priority Hcall]].
  destruct (q_post_wake_decompose sg state eid node message priority after Hvalid Hnode Htype Hgroup Hcall)
    as [tid [tail [old [Hlist [Hold [Hpriority [Hafter [Hafter_valid Hlast]]]]]]]].
  exists tid, old; auto.
Qed.

Lemma q_post_wake_preserves_ready_members : forall sg state eid node tid old message slot,
  In slot state.(SchedState).(readyList) ->
  In slot (event_wake_state sg state eid node tid old PendQ message PendOK).(SchedState).(readyList).
Proof.
  intros; apply (proj2 (sched_wake_by_status_membership _ _ _ _ _ _)); left; exact H.
Qed.

Lemma q_post_wake_preserves_ready_nonempty : forall sg state eid node tid old message,
  state.(SchedState).(readyList) <> [] ->
  (event_wake_state sg state eid node tid old PendQ message PendOK).(SchedState).(readyList) <> [].
Proof.
  intros sg state eid node tid old message Hready.
  destruct state.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
  pose proof (q_post_wake_preserves_ready_members sg state eid node tid old message slot
    ltac:(rewrite Hlist; left; reflexivity)) as Hmember.
  intro Hempty; rewrite Hempty in Hmember; contradiction.
Qed.

Lemma q_post_wake_preserves_disabled_source : forall sg state eid node tid old message view,
  sched_disabled_entry_source view state ->
  sched_disabled_entry_source view (event_wake_state sg state eid node tid old PendQ message PendOK).
Proof.
  intros sg state eid node tid old message view Hsource.
  unfold sched_disabled_entry_source, sched_disabled_isr_source in *.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS IntrState SchedState].
  rewrite sched_wake_by_status_running_eq; exact Hsource.
Qed.

Lemma q_post_wake_preserves_task_source : forall sg state eid node tid old message call,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_resume_caller_source sg (ResumeTaskCaller call) state ->
  task_resume_caller_source sg (ResumeTaskCaller call)
    (event_wake_state sg state eid node tid old PendQ message PendOK).
Proof.
  intros sg state eid node tid old message call Hold [[Horigin [Hactive Hcurrent]] [Havailable Haddress]].
  assert (Hcur : (event_wake_state sg state eid node tid old PendQ message PendOK).(SchedState).(curTaskID) =
    state.(SchedState).(curTaskID)).
  { cbn [event_wake_state replace_SchedS SchedState].
    unfold sched_wake_by_status; destruct task_status_is_suspended; reflexivity. }
  unfold task_resume_caller_source, kernel_call_task_source.
  split; [|split; [exact Havailable|exact Haddress]].
  split; [exact Horigin|]; split.
  - eapply glob_task_set_usedtask_preserves_invocation_active;
      [exact Hold|reflexivity|exact Hactive].
  - unfold task_execution_current in *.
    destruct call.(os_sched_call_origin); [exact I|rewrite Hcur; exact Hcurrent].
Qed.

Lemma q_post_save_program_facts : forall environment critical sg original active mask saved before acquired,
  UCOS2_state_inv sg before ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  q_post_save_facts environment critical sg original active mask saved before acquired.
Proof.
  intros environment critical sg [original|view] [active|next] mask saved before acquired Hvalid Hsave;
    try contradiction.
  - pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
    pose proof (proj1 (critical_region_interval_transports_resources critical sg
      original.(os_sched_call_invocation) before acquired Hinterval Hvalid)) as Hafter.
    pose proof Hsave as [_ [_ [_ [_ Hsaved]]]].
    unfold q_post_save_facts; cbn [task_resume_view os_sched_execution_view]; tauto.
  - destruct Hsave as [-> [Hinterval Hsaved]].
    pose proof (proj1 (critical_region_interval_transports_resources critical sg
      view.(os_execution_invocation) before acquired Hinterval Hvalid)) as Hafter.
    unfold q_post_save_facts; cbn [task_resume_view task_resume_save_program fst snd]; tauto.
Qed.

Lemma q_post_prefix_wake_decompose : forall environment critical sg original mask pe eid message before
  observed returned restored error,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg original pe before eid observed ->
  q_post_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  exists active saved acquired node tid old,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    acquired.(TskState).(inUsedTaskStates) tid = Some old /\
    UCOS2_state_inv sg (event_wake_state sg acquired eid node tid old PendQ message PendOK) /\
    task_resume_restore_program environment critical sg active
      (event_wake_state sg acquired eid node tid old PendQ message PendOK) returned restored.
Proof.
  intros environment critical sg original mask pe eid message before observed returned restored error
    Hvalid Hinput Hprefix.
  unfold q_post_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype.
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  destruct (q_post_acquire_identity environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  destruct (q_post_back_wake_state sg acquired eid node message code released (proj1 Hfacts) Hnode Hqueue Hstep)
    as [tid [old [Hold [-> Hreleased]]]].
  exists active, saved, acquired, node, tid, old.
  split; [exact Hfacts|]. split; [exact Hacquire|]. auto.
Qed.

Lemma q_post_task_save_source : forall environment critical sg original active mask saved before acquired,
  UCOS2_state_inv sg before ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller original) before ->
  task_resume_save_program environment critical sg (ResumeTaskCaller original) mask before
    (ResumeTaskCaller active, saved) acquired ->
  task_resume_caller_source sg (ResumeTaskCaller active) acquired.
Proof.
  intros environment critical sg original active mask saved before acquired Hvalid Hreturns
    [Hsource [Havailable Haddress]] Hsave.
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call active original)
    by (unfold task_tcb_init_stack_same_call; tauto).
  split.
  - exact (kernel_call_save_source_preserves_task_source environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg original active mask saved before acquired
      Hvalid Hsource Hsave).
  - split.
    + exact (Hreturns sg original active before acquired Hvalid Hsource Havailable Hsame Htrace).
    + rewrite Hs; exact Haddress.
Qed.

Lemma q_post_task_restore_source : forall environment critical sg active returned released restored,
  UCOS2_state_inv sg released ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller active) released ->
  task_resume_restore_program environment critical sg (ResumeTaskCaller active) released
    (ResumeTaskCaller returned) restored ->
  UCOS2_state_inv sg restored /\
  task_resume_caller_source sg (ResumeTaskCaller returned) restored /\
  critical_region_interval critical sg active.(os_sched_call_invocation) released restored.
Proof.
  intros environment critical sg active returned released restored Hvalid Hreturns
    [Hsource [Havailable Haddress]] [Htrace Hsame].
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    active.(os_sched_call_invocation) released restored Hinterval Hvalid)) as Hrestored.
  split; [exact Hrestored|]. split; [|exact Hinterval]. split.
  - apply (proj2 (task_tcb_init_stack_same_call_source_iff returned active restored Hsame)).
    exact (task_tcb_init_stack_registered_source_preserved environment.(task_stack_call_external)
      environment.(task_stack_call_port) critical sg active returned released restored
      Hvalid Hsame Htrace Hsource).
  - split.
    + exact (Hreturns sg active returned released restored Hvalid Hsource Havailable Hsame Htrace).
    + destruct Hsame as [_ [_ Hstack]]; rewrite Hstack; exact Haddress.
Qed.

Lemma q_post_schedule_protocol_task : forall environment critical sg call mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  q_post_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid message before.
Proof.
  intros environment critical sg call mask pe eid message before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored error Hprefix.
  destruct (q_post_prefix_wake_decompose environment critical sg (ResumeTaskCaller call) mask pe eid message
    before observed returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [tid [old [Hsave [Hacquire [Hold [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  pose proof (q_post_wake_preserves_task_source sg acquired eid node tid old message active Hold Hactive)
    as Hreleased_source.
  destruct (q_post_task_restore_source environment critical sg active returned
    (event_wake_state sg acquired eid node tid old PendQ message PendOK) restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; [exact Hclients|exact Hreturn_interval|exact Hreleased|].
    apply q_post_wake_preserves_ready_nonempty; exact Hacquired_ready. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma q_post_schedule_protocol_disabled : forall environment critical sg view mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  q_post_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid message before.
Proof.
  intros environment critical sg view mask pe eid message before observed Hvalid Hinput Hclients Hsource
    returned restored error Hprefix.
  destruct (q_post_prefix_wake_decompose environment critical sg (ResumeGenericCaller view) mask pe eid message
    before observed returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [tid [old [Hsave [Hacquire [Hold [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  pose proof (q_post_wake_preserves_disabled_source sg acquired eid node tid old message view Hacquired_source)
    as Hreleased_source.
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    (event_wake_state sg acquired eid node tid old PendQ message PendOK) restored
    Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma q_post_schedule_protocol_task_idle : forall environment critical sg call mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  q_post_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid message before.
Proof.
  intros environment critical sg call mask pe eid message before observed Hvalid Hinput Hclients Hreturns Hsource Hidle.
  eapply q_post_schedule_protocol_task; [exact Hvalid|exact Hinput|exact Hclients|exact Hreturns|exact Hsource|].
  eapply sched_idle_ready_nonempty; [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.
