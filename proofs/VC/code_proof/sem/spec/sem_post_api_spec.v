Require Export Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Public OSSemPost composition. The protected Sem effect remains owned
    by sem_post_spec; caller-neutral resource transport is reused unchanged.
    Every normal endpoint below is the actual Save/Restore/Scheduler endpoint,
    not a frozen whole-call context or a protected-state identity. *)
Definition sem_post_api_prefix_program environment critical sg caller mask pe eid
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((4, false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 3 then
      exists active saved acquired error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        sem_post_critical sg eid acquired (error, schedule) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((encode_os_err_code error, schedule), returned)
    else result = ((1, false), caller) /\ restored = before.

(** OSSemPost calls OS_Sched unconditionally after a wake. In particular,
    the Resume API's additional OSRunning load/guard is not copied here. *)

Definition sem_post_api_program environment critical sg caller mask pe eid
  : program UCOS2_Verify_State Z :=
  bind (sem_post_api_prefix_program environment critical sg caller mask pe eid)
    (q_post_tail environment critical sg mask).

Definition sem_post_api_safe environment critical sg caller mask pe eid before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (sem_post_api_program environment critical sg caller mask pe eid) X.

Definition sem_post_api_caller_result environment critical sg original mask pe eid before
  error returned current : Prop :=
  exists prefix_caller restored schedule,
    sem_post_api_prefix_program environment critical sg original mask pe eid before
      ((error, schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition sem_post_api_post environment critical saved_local sg original mask pe eid before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (sem_post_api_caller_result environment critical sg original mask pe eid before error returned current /\
      q_post_return_safe current error X) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma sem_post_api_program_null : forall environment critical sg caller mask eid before,
  sem_post_api_program environment critical sg caller mask 0 eid before 4 before.
Proof.
  intros; exists ((4, false), caller), before; split.
  - unfold sem_post_api_prefix_program; cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma sem_post_api_program_wrong_type : forall environment critical sg caller mask pe eid before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_post_api_program environment critical sg caller mask pe eid before 1 before.
Proof.
  intros; exists ((1, false), caller), before; split.
  - change (sem_post_api_prefix_program environment critical sg caller mask pe eid
      before ((1, false), caller) before).
    unfold sem_post_api_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H),
      (proj2 (Z.eqb_neq _ _) H0); split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma sem_post_api_prefix_protected : forall environment critical sg original active returned mask
  pe eid before acquired released restored saved error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  sem_post_critical sg eid acquired (error, schedule) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  sem_post_api_prefix_program environment critical sg original mask pe eid before
    ((encode_os_err_code error, schedule), returned) restored.
Proof.
  intros; unfold sem_post_api_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0; cbn.
  exists active, saved, acquired, error, schedule, released, returned; auto.
Qed.

Lemma sem_post_api_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid before restored error schedule X,
  sem_post_api_prefix_program environment critical sg original mask pe eid before
    ((error, schedule), returned) restored ->
  sem_post_api_safe environment critical sg original mask pe eid before X ->
  safeExec (fun state => state = restored)
    (q_post_tail environment critical sg mask ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid before restored error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (sem_post_api_prefix_program environment critical sg original mask pe eid)
    (q_post_tail environment critical sg mask) (fun state => state = before)
    ((error, schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma sem_post_api_program_nonschedule : forall environment critical sg original returned mask
  pe eid before restored error,
  sem_post_api_prefix_program environment critical sg original mask pe eid before
    ((error, false), returned) restored ->
  sem_post_api_program environment critical sg original mask pe eid before error restored.
Proof.
  intros; exists ((error, false), returned), restored; split; [assumption|].
  cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma sem_post_api_program_schedule : forall environment critical sg original returned final mask
  pe eid before restored current error,
  sem_post_api_prefix_program environment critical sg original mask pe eid before
    ((error, true), returned) restored ->
  task_resume_schedule_program environment critical sg returned mask restored final current ->
  sem_post_api_program environment critical sg original mask pe eid before error current.
Proof.
  intros; exists ((error, true), returned), restored; split; [assumption|].
  cbn [q_post_tail]; exists tt, current; split; [|split; reflexivity].
  exists final, current; split; [assumption|split; reflexivity].
Qed.

Lemma sem_post_api_safe_return : forall environment critical sg caller mask pe eid before current error X,
  sem_post_api_program environment critical sg caller mask pe eid before error current ->
  sem_post_api_safe environment critical sg caller mask pe eid before X ->
  q_post_return_safe current error X.
Proof.
  intros environment critical sg caller mask pe eid before current error X Hprogram Hsafe.
  eapply (highstependret_derive
    (sem_post_api_program environment critical sg caller mask pe eid)
    (fun state => state = before) error (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma sem_post_api_closed_return : forall environment critical saved_local sg original returned mask
  pe eid before current error X,
  sem_post_api_caller_result environment critical sg original mask pe eid before error returned current ->
  sem_post_api_safe environment critical sg original mask pe eid before X ->
  q_post_closed environment critical saved_local sg returned mask current |--
  sem_post_api_post environment critical saved_local sg original mask pe eid before error X.
Proof.
  intros.
  assert (Hprogram : sem_post_api_program environment critical sg original mask pe eid before error current).
  { pose proof H as Hresult; destruct Hresult as [prefix_caller [restored [schedule [Hprefix Htail]]]].
    destruct schedule.
    - eapply sem_post_api_program_schedule with (final := returned); eassumption.
    - destruct Htail as [-> ->]; eapply sem_post_api_program_nonschedule; exact Hprefix. }
  pose proof (sem_post_api_safe_return _ _ _ _ _ _ _ _ _ _ _ Hprogram H0).
  unfold sem_post_api_post; Exists returned current; entailer!.
Qed.

Lemma sem_post_api_sched_return : forall environment critical saved_local sg original returned mask
  pe eid before restored error X,
  sem_post_api_prefix_program environment critical sg original mask pe eid before
    ((error, true), returned) restored ->
  sem_post_api_safe environment critical sg original mask pe eid before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  sem_post_api_post environment critical saved_local sg original mask pe eid before error X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid before restored error X
    Hprefix Hsafe.
  pose proof (sem_post_api_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_post_tail] in Htail.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Htail).
  unfold task_resume_sched_refined_post; Intros final current.
  assert (Hresult : sem_post_api_caller_result environment critical sg original mask pe eid
    before error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  unfold sem_post_api_post, q_post_closed; Exists final current; rewrite Htables; entailer!.
  apply derivable1_andp_elim1.
Qed.

Definition sem_post_api_call_input critical sg caller pe before eid observed : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 3 ->
      sem_post_handle_protocol critical sg
        (task_resume_view caller).(os_execution_invocation) eid)).

(** Explicit C caller scheduling protocol, conditional only on the real
    wake prefix. This is not a CPU postcondition or an extra source guard.
    Acquired count/overflow and both pre-Save errors impose no scheduling cut;
    ISR/locked callers use the already checked generic disabled contract. *)

Definition sem_post_api_schedule_protocol environment critical sg caller mask pe eid before : Prop :=
  forall returned restored error,
    sem_post_api_prefix_program environment critical sg caller mask pe eid before
      ((error, true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Definition sem_post_api_acquire_facts environment critical sg original active mask saved before acquired eid observed current : Prop :=
  q_post_save_facts environment critical sg original active mask saved before acquired /\
  sem_post_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\
  sem_post_lookup acquired eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration).

Lemma sem_post_api_public_slot_is_semaphore : forall state eid observed,
  sem_query_public_slot state eid observed ->
  event_slot_type_value state.(EventState) eid = 3 ->
  sem_post_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype;
    unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype.
    split; [exact Hused|]. destruct observed.(eventType); cbn in Htype;
      try discriminate; reflexivity.
  - rewrite Hnone in Htype; discriminate.
Qed.

Lemma sem_post_api_acquire_identity : forall environment critical sg original active mask saved
  pe before acquired eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  sem_post_api_call_input critical sg original pe before eid observed ->
  event_slot_type_value before.(EventState) eid = 3 ->
  q_post_save_facts environment critical sg original active mask saved before acquired ->
  exists current,
    sem_post_api_acquire_facts environment critical sg original active mask saved before acquired eid observed current.
Proof.
  intros environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hsave.
  destruct Hinput as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  destruct (sem_post_api_public_slot_is_semaphore before eid observed Hslot Htype) as [Hlookup Hsem].
  destruct (sem_post_handle_interval_preserves_identity critical sg
    (task_resume_view original).(os_execution_invocation) eid before acquired observed
    (Hprotocol Htype) (proj1 (proj2 Hsave)) Hvalid Hlookup)
    as [current [Hcurrent [Hg Hkind]]].
  exists current; unfold sem_post_api_acquire_facts.
  split; [exact Hsave|]. split; [exact Hlookup|]. split; [exact Hsem|].
  split; [exact Hcurrent|]. split; congruence.
Qed.

Lemma sem_post_api_mask_frame_wake_update : forall environment critical saved_local sg caller saved acquired state
  eid node tid old,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  q_post_mask_frame environment critical saved_local sg caller saved acquired state |--
  q_post_mask_frame environment critical saved_local sg caller saved acquired
    (event_wake_state sg state eid node tid old PendSem 0 PendOK).
Proof.
  intros environment critical saved_local sg [call|view] saved acquired state eid node tid old Hold;
    [|reflexivity].
  assert (Hobserve : forall slot updated,
    (event_wake_state sg state eid node tid old PendSem 0 PendOK).(TskState).(inUsedTaskStates) slot = Some updated ->
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
    (event_wake_state sg state eid node tid old PendSem 0 PendOK).(TskState)
      (task_stack_call_active_key call)).
  { eapply task_stack_live_coverage_used_map_frame with (before := state.(TskState)).
    - intros slot updated Hupdated.
      destruct (Hobserve slot updated Hupdated) as [previous [Hprevious [Hg Hsp]]].
      exists previous; split; [exact Hprevious|symmetry; exact Hg].
    - reflexivity.
    - exact H. }
  assert (Hcapsules : task_tcb_init_continuation_capsules environment saved_local state |--
    task_tcb_init_continuation_capsules environment saved_local
      (event_wake_state sg state eid node tid old PendSem 0 PendOK)).
  { unfold task_tcb_init_continuation_capsules.
    apply kernel_saved_continuation_map_reindex.
    intros key payload updated Hstack Hupdated Hg.
    destruct (Hobserve (fst key) updated Hupdated) as [previous [Hprevious [Hgen Hsp]]].
    exists previous; repeat split; auto. }
  sep_apply_l_atomic Hcapsules; entailer!.
Qed.
(** Source-facing consequences. These are C call adapters of the unchanged
    Save/Restore interfaces, not additional CPU laws or scheduling promises. *)

Definition sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\ pe <> 0 /\
    sem_post_api_call_input critical sg caller pe before eid observed /\
    event_slot_type_value before.(EventState) eid = 3) &&
  q_post_closed environment critical saved_local sg caller mask before.

Definition sem_post_api_save_result environment critical saved_local sg caller mask saved before eid observed : Assertion :=
  EX active acquired current,
    coq_prop (sem_post_api_acquire_facts environment critical sg caller active mask saved
      before acquired eid observed current) &&
    q_post_masked environment critical saved_local sg active saved acquired acquired.

Lemma sem_post_api_save_pre_raw : forall environment critical saved_local sg caller mask before pe eid observed,
  sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof. intros; unfold sem_post_api_save_pre; apply derivable1_andp_elim2. Qed.

Lemma sem_post_api_save_result_consequence : forall environment critical saved_local sg caller mask saved before pe eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  sem_post_api_call_input critical sg caller pe before eid observed ->
  event_slot_type_value before.(EventState) eid = 3 ->
  q_post_save_output environment critical saved_local sg caller mask saved before |--
  sem_post_api_save_result environment critical saved_local sg caller mask saved before eid observed.
Proof.
  intros environment critical saved_local sg caller mask saved before pe eid observed Hvalid Hpe Hinput Htype.
  sep_apply_l_atomic (q_post_save_output_acquire environment critical saved_local sg caller mask saved before Hvalid).
  Intros active acquired.
  destruct (sem_post_api_acquire_identity environment critical sg caller active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype H) as [current Hcurrent].
  unfold sem_post_api_save_result; Exists active acquired current; entailer!.
Qed.

Definition sem_post_api_prefix_result environment critical sg caller mask pe eid before
  (error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    sem_post_api_prefix_program environment critical sg caller mask pe eid before
      ((error, request), returned) current.

Definition sem_post_api_restore_pre environment critical saved_local sg caller active mask saved pe eid
  before acquired released error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 3 /\
    UCOS2_state_inv sg released /\ sem_post_critical_result sg eid acquired error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before error schedule : Assertion :=
  EX returned current,
    coq_prop (sem_post_api_prefix_result environment critical sg caller mask pe eid before
      error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma sem_post_api_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid
  before acquired released error schedule,
  sem_post_api_restore_pre environment critical saved_local sg caller active mask saved pe eid
    before acquired released error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold sem_post_api_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma sem_post_api_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid
  before acquired released error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 ->
  UCOS2_state_inv sg released -> sem_post_critical_result sg eid acquired error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid before acquired released error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : sem_post_api_prefix_result environment critical sg caller mask pe eid before
    (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply sem_post_api_prefix_protected;
      [exact Hpe|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold sem_post_api_restore_post; Exists returned current; entailer!.
Qed.

Lemma sem_post_api_nonschedule_return : forall environment critical saved_local sg caller mask pe eid before error X,
  sem_post_api_safe environment critical sg caller mask pe eid before X ->
  sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before error 0 |--
  sem_post_api_post environment critical saved_local sg caller mask pe eid before error X.
Proof.
  intros; unfold sem_post_api_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; [discriminate|].
  assert (Hresult : sem_post_api_caller_result environment critical sg caller mask pe eid before error returned current).
  { exists returned, current, false; auto. }
  sep_apply_r_atomic (sem_post_api_closed_return environment critical saved_local sg caller returned mask pe eid before current error X Hresult H).
  entailer!.
Qed.

Lemma sem_post_api_restored_schedule_pre : forall environment critical saved_local sg caller mask pe eid before error,
  sem_post_api_schedule_protocol environment critical sg caller mask pe eid before ->
  sem_post_api_restore_post environment critical saved_local sg caller mask pe eid before error 1 |--
  EX returned current,
    coq_prop (sem_post_api_prefix_result environment critical sg caller mask pe eid before error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid before error Hprotocol.
  unfold sem_post_api_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]. pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current error Hprefix)).
  Exists returned current; entailer!.
Qed.

Definition sem_post_api_group_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current : Assertion :=
  coq_prop (sem_post_api_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    sem_post_profile sg /\ valid_event_id sg eid /\ event_object_layout_prop sg eid) &&
  (sem_post_group_frame sg acquired eid current ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Definition sem_post_api_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current tid old : Assertion :=
  coq_prop (sem_post_api_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    sem_post_profile sg /\ valid_event_id sg eid /\ event_object_layout_prop sg eid /\ sem_post_group acquired current <> 0 /\
    event_task_rdy_entry sg acquired.(TskState) eid current tid old) &&
  (sem_post_wake_frame sg acquired eid tid **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Lemma sem_post_api_group_cell_split : forall sg state eid node,
  sem_post_lookup state eid node ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    ((event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group state node **
      sem_post_group_frame sg state eid node).
Proof.
  intros sg state eid node Hnode.
  pose proof (sem_post_field_split_full sg state eid node EventGrpField Hnode ltac:(simpl; tauto)) as Hsplit.
  exact Hsplit.
Qed.

Lemma sem_post_api_group_cell_merge : forall sg state eid node,
  UCOS2_state_inv sg state -> sem_post_lookup state eid node ->
  (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group state node **
    sem_post_group_frame sg state eid node |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node Hvalid Hnode.
  exact (sem_post_field_merge_full sg state eid node EventGrpField Hvalid Hnode ltac:(simpl; tauto)).
Qed.

Lemma sem_post_api_acquire_original_type : forall environment critical sg original active mask saved
  before acquired eid observed current,
  sem_post_api_acquire_facts environment critical sg original active mask saved before acquired eid observed current ->
  event_slot_type_value before.(EventState) eid = 3.
Proof.
  intros environment critical sg original active mask saved before acquired eid observed current
    [_ [Hlookup [Hsem Hrest]]].
  unfold event_slot_type_value; rewrite Hlookup, Hsem; reflexivity.
Qed.
(** Scheduling admission is established from the actual C caller and the
    same completed Save/Restore traces. No CPU contract obtains readiness. *)

Lemma sem_post_api_wake_state : forall sg state eid node error after,
  UCOS2_state_inv sg state -> sem_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_post_critical sg eid state (error, true) after ->
  exists tid old,
    state.(TskState).(inUsedTaskStates) tid = Some old /\
    after = event_wake_state sg state eid node tid old PendSem 0 PendOK /\
    UCOS2_state_inv sg after.
Proof.
  intros sg state eid node error after Hvalid Hnode Htype Hstep.
  pose proof (sem_post_critical_preserves_validity sg state eid node
    (error, true) after Hvalid Hnode Htype Hstep) as Hafter.
  destruct (sem_post_critical_wake_observation sg state eid node error after
    Hvalid Hnode Htype Hstep) as [tid [tail [old [Hlist [Hold [Herror [Hstate Hlookup]]]]]]].
  exists tid, old; auto.
Qed.

Lemma sem_post_api_wake_preserves_ready_members : forall sg state eid node tid old slot,
  In slot state.(SchedState).(readyList) ->
  In slot (event_wake_state sg state eid node tid old PendSem 0 PendOK).(SchedState).(readyList).
Proof.
  intros; apply (proj2 (sched_wake_by_status_membership _ _ _ _ _ _)); left; exact H.
Qed.

Lemma sem_post_api_wake_preserves_ready_nonempty : forall sg state eid node tid old,
  state.(SchedState).(readyList) <> [] ->
  (event_wake_state sg state eid node tid old PendSem 0 PendOK).(SchedState).(readyList) <> [].
Proof.
  intros sg state eid node tid old Hready.
  destruct state.(SchedState).(readyList) as [|slot tail] eqn:Hlist; [contradiction|].
  pose proof (sem_post_api_wake_preserves_ready_members sg state eid node tid old slot
    ltac:(rewrite Hlist; left; reflexivity)) as Hmember.
  intro Hempty; rewrite Hempty in Hmember; contradiction.
Qed.

Lemma sem_post_api_wake_preserves_disabled_source : forall sg state eid node tid old view,
  sched_disabled_entry_source view state ->
  sched_disabled_entry_source view (event_wake_state sg state eid node tid old PendSem 0 PendOK).
Proof.
  intros sg state eid node tid old view Hsource.
  unfold sched_disabled_entry_source, sched_disabled_isr_source in *.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS IntrState SchedState].
  rewrite sched_wake_by_status_running_eq; exact Hsource.
Qed.

Lemma sem_post_api_wake_preserves_task_source : forall sg state eid node tid old call,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_resume_caller_source sg (ResumeTaskCaller call) state ->
  task_resume_caller_source sg (ResumeTaskCaller call)
    (event_wake_state sg state eid node tid old PendSem 0 PendOK).
Proof.
  intros sg state eid node tid old call Hold [[Horigin [Hactive Hcurrent]] [Havailable Haddress]].
  assert (Hcur : (event_wake_state sg state eid node tid old PendSem 0 PendOK).(SchedState).(curTaskID) =
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

Lemma sem_post_api_prefix_wake_decompose : forall environment critical sg original mask pe eid before
  observed returned restored error,
  UCOS2_state_inv sg before ->
  sem_post_api_call_input critical sg original pe before eid observed ->
  sem_post_api_prefix_program environment critical sg original mask pe eid before
    ((error, true), returned) restored ->
  exists active saved acquired node tid old,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    sem_post_api_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    acquired.(TskState).(inUsedTaskStates) tid = Some old /\
    UCOS2_state_inv sg (event_wake_state sg acquired eid node tid old PendSem 0 PendOK) /\
    task_resume_restore_program environment critical sg active
      (event_wake_state sg acquired eid node tid old PendSem 0 PendOK) returned restored.
Proof.
  intros environment critical sg original mask pe eid before observed returned restored error
    Hvalid Hinput Hprefix.
  unfold sem_post_api_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype.
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  destruct (sem_post_api_acquire_identity environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hsem Hg]]]]].
  destruct (sem_post_api_wake_state sg acquired eid node code released (proj1 Hfacts) Hnode Hsem Hstep)
    as [tid [old [Hold [-> Hreleased]]]].
  exists active, saved, acquired, node, tid, old.
  split; [exact Hfacts|]. split; [exact Hacquire|]. auto.
Qed.

Lemma sem_post_api_schedule_protocol_task : forall environment critical sg call mask pe eid before observed,
  UCOS2_state_inv sg before ->
  sem_post_api_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  sem_post_api_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid before.
Proof.
  intros environment critical sg call mask pe eid before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored error Hprefix.
  destruct (sem_post_api_prefix_wake_decompose environment critical sg (ResumeTaskCaller call) mask pe eid
    before observed returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [tid [old [Hsave [Hacquire [Hold [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  pose proof (sem_post_api_wake_preserves_task_source sg acquired eid node tid old active Hold Hactive)
    as Hreleased_source.
  destruct (q_post_task_restore_source environment critical sg active returned
    (event_wake_state sg acquired eid node tid old PendSem 0 PendOK) restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; [exact Hclients|exact Hreturn_interval|exact Hreleased|].
    apply sem_post_api_wake_preserves_ready_nonempty; exact Hacquired_ready. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma sem_post_api_schedule_protocol_disabled : forall environment critical sg view mask pe eid before observed,
  UCOS2_state_inv sg before ->
  sem_post_api_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  sem_post_api_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid before.
Proof.
  intros environment critical sg view mask pe eid before observed Hvalid Hinput Hclients Hsource
    returned restored error Hprefix.
  destruct (sem_post_api_prefix_wake_decompose environment critical sg (ResumeGenericCaller view) mask pe eid
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
  pose proof (sem_post_api_wake_preserves_disabled_source sg acquired eid node tid old view Hacquired_source)
    as Hreleased_source.
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    (event_wake_state sg acquired eid node tid old PendSem 0 PendOK) restored
    Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma sem_post_api_schedule_protocol_task_idle : forall environment critical sg call mask pe eid before observed,
  UCOS2_state_inv sg before ->
  sem_post_api_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  sem_post_api_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid before.
Proof.
  intros environment critical sg call mask pe eid before observed Hvalid Hinput Hclients Hreturns Hsource Hidle.
  eapply sem_post_api_schedule_protocol_task; [exact Hvalid|exact Hinput|exact Hclients|exact Hreturns|exact Hsource|].
  eapply sched_idle_ready_nonempty; [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.

Definition sem_post_api_count_context environment critical saved_local sg caller active mask saved before acquired
  eid observed current : Assertion :=
  coq_prop (sem_post_api_acquire_facts environment critical sg caller active mask saved before acquired eid observed current /\
    sem_post_profile sg /\ valid_event_id sg eid /\ event_object_layout_prop sg eid /\ sem_post_group acquired current = 0 /\
    0 <= encode_event_cnt_value current <= 65535) &&
  (sem_post_count_frame sg acquired eid current ** unmap_table_rep sg **
   q_post_mask_frame environment critical saved_local sg active saved acquired acquired).

Lemma sem_post_api_mask_frame_count_update : forall environment critical saved_local sg caller saved acquired
  entry eid current,
  q_post_mask_frame environment critical saved_local sg caller saved acquired entry |--
  q_post_mask_frame environment critical saved_local sg caller saved acquired
    (sem_post_count_checkpoint entry eid current).
Proof.
  intros; apply q_post_mask_frame_event_update.
  unfold sem_post_count_checkpoint; destruct Z.ltb; reflexivity.
Qed.

Lemma sem_post_api_schedule_protocol_null : forall environment critical sg caller mask eid before,
  sem_post_api_schedule_protocol environment critical sg caller mask 0 eid before.
Proof.
  intros environment critical sg caller mask eid before returned restored error Hprefix.
  unfold sem_post_api_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Hresult _]; discriminate.
Qed.

Lemma sem_post_api_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid before,
  event_slot_type_value before.(EventState) eid <> 3 ->
  sem_post_api_schedule_protocol environment critical sg caller mask pe eid before.
Proof.
  intros environment critical sg caller mask pe eid before Htype returned restored error Hprefix.
  unfold sem_post_api_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); [destruct Hprefix as [Heq _]; discriminate|].
  rewrite (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

(** Caller-owned no-wake R for initialization/boot clients. The property
    must survive every registered foreign action in the very Save interval;
    a BootInvocation tag or the entry bitmap alone does not establish it. *)
Definition sem_post_api_no_waiters (sg : StableGlobVars) (eid : EventID)
  (state : UCOS2_Verify_State) : Prop :=
  forall node, sem_post_lookup state eid node -> sem_post_group state node = 0.

Definition sem_post_api_no_waiter_clients critical sg invocation eid : Prop :=
  forall action before after,
    critical_region_clients critical action -> kernel_client_actor action <> Some invocation ->
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    sem_post_api_no_waiters sg eid before -> sem_post_api_no_waiters sg eid after.

Lemma sem_post_api_interval_preserves_no_waiters : forall critical sg invocation eid before after,
  sem_post_api_no_waiter_clients critical sg invocation eid ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> sem_post_api_no_waiters sg eid before ->
  sem_post_api_no_waiters sg eid after.
Proof.
  intros critical sg invocation eid before after Hclients Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  induction Hinterval as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid Hnone; [exact Hnone|].
  apply IH.
  - eapply kernel_client_preserves_validity;
      [exact (critical_region_client_certificates critical action Hin)|exact Hvalid|exact Hstep].
  - eapply Hclients; eassumption.
Qed.

Lemma sem_post_api_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid before,
  UCOS2_state_inv sg before ->
  sem_post_api_no_waiter_clients critical sg (task_resume_view caller).(os_execution_invocation) eid ->
  sem_post_api_no_waiters sg eid before ->
  sem_post_api_schedule_protocol environment critical sg caller mask pe eid before.
Proof.
  intros environment critical sg caller mask pe eid before Hvalid Hclients Hnone
    returned restored error Hprefix.
  unfold sem_post_api_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3);
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  pose proof (sem_post_api_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) eid before acquired
    Hclients (proj1 (proj2 Hfacts)) Hvalid Hnone) as Hacquired.
  destruct Hstep as [node [Hlookup Hstep]].
  unfold sem_post_api_no_waiters, sem_post_group in Hacquired.
  rewrite (Hacquired node Hlookup), Z.eqb_refl in Hstep.
  destruct Hstep as [fields [_ Hstep]]; destruct Z.ltb;
    destruct Hstep as [Hresult _]; discriminate.
Qed.
