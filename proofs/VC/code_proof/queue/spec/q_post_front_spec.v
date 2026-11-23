Require Export Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
Require Export Ucos2Verify.VC.code.queue.q_post_source_protocol.
Require Import Coq.Strings.String Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.task_idle_ready.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Source-faithful OSQPostFront API composition. Only the protected effect
    differs from Post; the actual Save/Restore and unconditional wake-tail
    Scheduler keep their checked C-modular contracts and explicit relies.
    The same arbitrary X observes the actual returned state, not the
    pre-Restore snapshot. No eventual-return property is asserted. *)

Definition q_post_front_prefix_program environment critical sg caller mask pe eid message
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((4, false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
      exists active saved acquired error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        q_post_critical sg QueuePostFront eid message acquired (error, schedule) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((encode_os_err_code error, schedule), returned)
    else result = ((1, false), caller) /\ restored = before.

Definition q_post_front_program environment critical sg caller mask pe eid message
  : program UCOS2_Verify_State Z :=
  bind (q_post_front_prefix_program environment critical sg caller mask pe eid message)
    (q_post_tail environment critical sg mask).

Definition q_post_front_safe environment critical sg caller mask pe eid message before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (q_post_front_program environment critical sg caller mask pe eid message) X.

Definition q_post_front_caller_result environment critical sg original mask pe eid message before
  error returned current : Prop :=
  exists prefix_caller restored schedule,
    q_post_front_prefix_program environment critical sg original mask pe eid message before
      ((error, schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition q_post_front_post environment critical saved_local sg original mask pe eid message before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (q_post_front_caller_result environment critical sg original mask pe eid message before error returned current /\
      q_post_return_safe current error X) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_post_front_program_null : forall environment critical sg caller mask eid message before,
  q_post_front_program environment critical sg caller mask 0 eid message before 4 before.
Proof.
  intros; exists ((4, false), caller), before; split.
  - unfold q_post_front_prefix_program; cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_front_program_wrong_type : forall environment critical sg caller mask pe eid message before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_post_front_program environment critical sg caller mask pe eid message before 1 before.
Proof.
  intros; exists ((1, false), caller), before; split.
  - change (q_post_front_prefix_program environment critical sg caller mask pe eid message
      before ((1, false), caller) before).
    unfold q_post_front_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H),
      (proj2 (Z.eqb_neq _ _) H0); split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_front_prefix_protected : forall environment critical sg original active returned mask
  pe eid message before acquired released restored saved error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  q_post_critical sg QueuePostFront eid message acquired (error, schedule) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  q_post_front_prefix_program environment critical sg original mask pe eid message before
    ((encode_os_err_code error, schedule), returned) restored.
Proof.
  intros; unfold q_post_front_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0; cbn.
  exists active, saved, acquired, error, schedule, released, returned; auto.
Qed.

Lemma q_post_front_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid message before restored error schedule X,
  q_post_front_prefix_program environment critical sg original mask pe eid message before
    ((error, schedule), returned) restored ->
  q_post_front_safe environment critical sg original mask pe eid message before X ->
  safeExec (fun state => state = restored)
    (q_post_tail environment critical sg mask ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid message before restored error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (q_post_front_prefix_program environment critical sg original mask pe eid message)
    (q_post_tail environment critical sg mask) (fun state => state = before)
    ((error, schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_post_front_program_nonschedule : forall environment critical sg original returned mask
  pe eid message before restored error,
  q_post_front_prefix_program environment critical sg original mask pe eid message before
    ((error, false), returned) restored ->
  q_post_front_program environment critical sg original mask pe eid message before error restored.
Proof.
  intros; exists ((error, false), returned), restored; split; [assumption|].
  cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_front_program_schedule : forall environment critical sg original returned final mask
  pe eid message before restored current error,
  q_post_front_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  task_resume_schedule_program environment critical sg returned mask restored final current ->
  q_post_front_program environment critical sg original mask pe eid message before error current.
Proof.
  intros; exists ((error, true), returned), restored; split; [assumption|].
  cbn [q_post_tail]; exists tt, current; split; [|split; reflexivity].
  exists final, current; split; [assumption|split; reflexivity].
Qed.

Lemma q_post_front_safe_return : forall environment critical sg caller mask pe eid message before current error X,
  q_post_front_program environment critical sg caller mask pe eid message before error current ->
  q_post_front_safe environment critical sg caller mask pe eid message before X ->
  q_post_return_safe current error X.
Proof.
  intros environment critical sg caller mask pe eid message before current error X Hprogram Hsafe.
  eapply (highstependret_derive
    (q_post_front_program environment critical sg caller mask pe eid message)
    (fun state => state = before) error (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_post_front_closed_return : forall environment critical saved_local sg original returned mask
  pe eid message before current error X,
  q_post_front_caller_result environment critical sg original mask pe eid message before error returned current ->
  q_post_front_safe environment critical sg original mask pe eid message before X ->
  q_post_closed environment critical saved_local sg returned mask current |--
  q_post_front_post environment critical saved_local sg original mask pe eid message before error X.
Proof.
  intros.
  assert (Hprogram : q_post_front_program environment critical sg original mask pe eid message before error current).
  { pose proof H as Hresult; destruct Hresult as [prefix_caller [restored [schedule [Hprefix Htail]]]].
    destruct schedule.
    - eapply q_post_front_program_schedule with (final := returned); eassumption.
    - destruct Htail as [-> ->]; eapply q_post_front_program_nonschedule; exact Hprefix. }
  pose proof (q_post_front_safe_return _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0).
  unfold q_post_front_post; Exists returned current; entailer!.
Qed.

Lemma q_post_front_sched_return : forall environment critical saved_local sg original returned mask
  pe eid message before restored error X,
  q_post_front_prefix_program environment critical sg original mask pe eid message before
    ((error, true), returned) restored ->
  q_post_front_safe environment critical sg original mask pe eid message before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  q_post_front_post environment critical saved_local sg original mask pe eid message before error X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid message before restored error X
    Hprefix Hsafe.
  pose proof (q_post_front_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_post_tail] in Htail.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Htail).
  unfold task_resume_sched_refined_post; Intros final current.
  assert (Hresult : q_post_front_caller_result environment critical sg original mask pe eid message
    before error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  unfold q_post_front_post, q_post_closed; Exists final current; rewrite Htables; entailer!.
  apply derivable1_andp_elim1.
Qed.

Definition q_post_front_schedule_protocol environment critical sg caller mask pe eid message before : Prop :=
  forall returned restored error,
    q_post_front_prefix_program environment critical sg caller mask pe eid message before
      ((error, true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Definition q_post_front_effect sg eid message acquired (error schedule : Z) released : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    q_post_critical sg QueuePostFront eid message acquired (code, request) released.

Definition q_post_front_prefix_result environment critical sg caller mask pe eid message before
  (error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    q_post_front_prefix_program environment critical sg caller mask pe eid message before
      ((error, request), returned) current.

Definition q_post_front_restore_pre environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 2 /\
    UCOS2_state_inv sg released /\ q_post_front_effect sg eid message acquired error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition q_post_front_restore_post environment critical saved_local sg caller mask pe eid message before error schedule : Assertion :=
  EX returned current,
    coq_prop (q_post_front_prefix_result environment critical sg caller mask pe eid message before
      error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_post_front_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule,
  q_post_front_restore_pre environment critical saved_local sg caller active mask saved pe eid message
    before acquired released error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold q_post_front_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma q_post_front_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid message
  before acquired released error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  UCOS2_state_inv sg released -> q_post_front_effect sg eid message acquired error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  q_post_front_restore_post environment critical saved_local sg caller mask pe eid message before error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid message before acquired released error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : q_post_front_prefix_result environment critical sg caller mask pe eid message before
    (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply q_post_front_prefix_protected;
      [exact Hpe|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold q_post_front_restore_post; Exists returned current; entailer!.
Qed.

Lemma q_post_front_nonschedule_return : forall environment critical saved_local sg caller mask pe eid message before error X,
  q_post_front_safe environment critical sg caller mask pe eid message before X ->
  q_post_front_restore_post environment critical saved_local sg caller mask pe eid message before error 0 |--
  q_post_front_post environment critical saved_local sg caller mask pe eid message before error X.
Proof.
  intros; unfold q_post_front_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; [discriminate|].
  assert (Hresult : q_post_front_caller_result environment critical sg caller mask pe eid message before error returned current).
  { exists returned, current, false; auto. }
  sep_apply_r_atomic (q_post_front_closed_return environment critical saved_local sg caller returned mask pe eid message before current error X Hresult H).
  entailer!.
Qed.

Lemma q_post_front_restored_schedule_pre : forall environment critical saved_local sg caller mask pe eid message before error,
  q_post_front_schedule_protocol environment critical sg caller mask pe eid message before ->
  q_post_front_restore_post environment critical saved_local sg caller mask pe eid message before error 1 |--
  EX returned current,
    coq_prop (q_post_front_prefix_result environment critical sg caller mask pe eid message before error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid message before error Hprotocol.
  unfold q_post_front_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]. pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current error Hprefix)).
  Exists returned current; entailer!.
Qed.

(** Front and Back share exactly the wake prefix. The no-wait enqueue
    branches are deliberately not identified by this equivalence. *)
Lemma q_post_front_wake_critical_iff : forall sg eid message before error after,
  q_post_critical sg QueuePostFront eid message before (error, true) after <->
  q_post_critical sg QueuePostBack eid message before (error, true) after.
Proof.
  intros; unfold q_post_critical; split; intros [node [Hnode Hstep]];
    exists node; split; [exact Hnode| |exact Hnode|];
    destruct (Z.eqb (encode_event_wait_grp (waitList node) (TskState before)) 0).
  - destruct Hstep as [q [Hq Hstep]]; destruct (Z.leb (qSize q) (queue_entries q)).
    + destruct Hstep as [Heq _]; discriminate.
    + destruct Hstep as [slots [next [_ [_ [Heq _]]]]]; discriminate.
  - exact Hstep.
  - destruct Hstep as [q [Hq Hstep]]; destruct (Z.leb (qSize q) (queue_entries q)).
    + destruct Hstep as [Heq _]; discriminate.
    + destruct Hstep as [slots [next [_ [_ [Heq _]]]]]; discriminate.
  - exact Hstep.
Qed.

Lemma q_post_front_wake_prefix_iff : forall environment critical sg caller mask pe eid message
  before error returned restored,
  q_post_front_prefix_program environment critical sg caller mask pe eid message before
    ((error, true), returned) restored <->
  q_post_prefix_program environment critical sg caller mask pe eid message before
    ((error, true), returned) restored.
Proof.
  intros; unfold q_post_front_prefix_program, q_post_prefix_program.
  destruct (Z.eqb pe 0); [reflexivity|].
  destruct (Z.eqb (event_slot_type_value (EventState before) eid) 2); [|reflexivity].
  split; intros [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]];
    inversion Hresult; subst schedule next error;
    exists active, saved, acquired, code, true, released, returned;
    split; [exact Hsave| |exact Hsave|]; split.
  - apply (proj1 (q_post_front_wake_critical_iff _ _ _ _ _ _)); exact Hstep.
  - split; [exact Hrestore|reflexivity].
  - apply (proj2 (q_post_front_wake_critical_iff _ _ _ _ _ _)); exact Hstep.
  - split; [exact Hrestore|reflexivity].
Qed.

Lemma q_post_front_schedule_protocol_iff : forall environment critical sg caller mask pe eid message before,
  q_post_front_schedule_protocol environment critical sg caller mask pe eid message before <->
  q_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros; unfold q_post_front_schedule_protocol, q_post_schedule_protocol.
  split; intros Hprotocol returned restored error Hprefix; apply Hprotocol with (error := error).
  - apply (proj2 (q_post_front_wake_prefix_iff _ _ _ _ _ _ _ _ _ _ _ _)); exact Hprefix.
  - apply (proj1 (q_post_front_wake_prefix_iff _ _ _ _ _ _ _ _ _ _ _ _)); exact Hprefix.
Qed.

Lemma q_post_front_schedule_protocol_task : forall environment critical sg call mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  q_post_front_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid message before.
Proof.
  intros; apply (proj2 (q_post_front_schedule_protocol_iff _ _ _ _ _ _ _ _ _)).
  eapply q_post_schedule_protocol_task_idle; eassumption.
Qed.

Lemma q_post_front_schedule_protocol_disabled : forall environment critical sg view mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  q_post_front_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid message before.
Proof.
  intros; apply (proj2 (q_post_front_schedule_protocol_iff _ _ _ _ _ _ _ _ _)).
  eapply q_post_schedule_protocol_disabled; eassumption.
Qed.

Lemma q_post_front_schedule_protocol_no_waiters_sources : forall environment critical sg caller mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  q_post_front_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros; apply (proj2 (q_post_front_schedule_protocol_iff _ _ _ _ _ _ _ _ _)).
  eapply q_post_schedule_protocol_no_waiters_sources; eassumption.
Qed.

(** Out, not In, is writable. Start/End/Size and the unused link cell
    remain owned at every intermediate raw Out value. *)
Definition q_post_front_qcb_readonly (base : addr) (q : QueueFields) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQPtr")) # Ptr |->_ **
  (&(base # "os_q" ->ₛ "OSQIn")) # Ptr |-> queue_in_addr q.

Definition q_post_front_qcb_cells (base : addr) (q : QueueFields) (qout count : Z) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQOut")) # Ptr |-> qout **
  (&(base # "os_q" ->ₛ "OSQEntries")) # UShort |-> count **
  (&(base # "os_q" ->ₛ "OSQSize")) # UShort |-> q.(qSize) **
  (&(base # "os_q" ->ₛ "OSQEnd")) # Ptr |-> queue_end_addr q **
  (&(base # "os_q" ->ₛ "OSQStart")) # Ptr |-> q.(qStart) **
  q_post_front_qcb_readonly base q.

Lemma q_post_front_qcb_cells_equiv : forall sg q,
  q_post_profile sg -> valid_queue_id sg q.(qID) ->
  used_queue_control_block sg q --||--
    q_post_front_qcb_cells (qcb_addr sg q.(qID)) q (queue_out_addr q) (queue_entries q).
Proof.
  intros sg q [_ [_ [Hlayout [[Hmax Hsize] Harg]]]] Hqid.
  specialize (Hlayout q.(qID) Hqid).
  change (sizeof ("os_q") = sizeof_OS_Q) in Hsize.
  rewrite Hsize in Hlayout; fold (qcb_addr sg q.(qID)) in Hlayout.
  destruct Hlayout as [Hptr [Hstart [Hend [Hin [Hout [Hsz Hentries]]]]]].
  unfold q_post_front_qcb_cells, q_post_front_qcb_readonly.
  rewrite Hptr, Hstart, Hend, Hin, Hout, Hsz, Hentries.
  unfold used_queue_control_block; split; entailer!.
Qed.

Definition q_post_front_enqueued_fields q message : QueueFields :=
  queue_with_contents q q.(qInIndex)
    (queue_retreat_index q.(qSize) q.(qOutIndex)) (message :: q.(qMessages)).

Definition q_post_front_enqueue_state state eid node q message slots : UCOS2_Verify_State :=
  replace_EventS (queue_update state.(EventState) eid node
    (q_post_front_enqueued_fields q message) (q_post_enqueue_slots true q message slots)) state.

Definition q_post_front_wrapped_out (q : QueueFields) : addr :=
  if Z.eqb (queue_out_addr q) q.(qStart) then queue_end_addr q else queue_out_addr q.

Definition q_post_front_next_out (q : QueueFields) : addr :=
  q_post_front_wrapped_out q - Ucos2Verify.lib.event.sizeof_ptr.

Lemma q_post_front_next_out_eq : forall q,
  q_post_front_next_out q =
    q.(qStart) + queue_retreat_index q.(qSize) q.(qOutIndex) * ptr_size_Z.
Proof.
  intro q; unfold q_post_front_next_out, q_post_front_wrapped_out.
  rewrite queue_out_start_eqb; unfold queue_retreat_index.
  destruct (Z.eqb q.(qOutIndex) 0).
  - change (q.(qStart) + q.(qSize) * 4 - 4 =
      q.(qStart) + (q.(qSize) - 1) * 4); lia.
  - change (q.(qStart) + q.(qOutIndex) * 4 - 4 =
      q.(qStart) + (q.(qOutIndex) - 1) * 4); lia.
Qed.

Lemma q_post_front_enqueue_some : forall q message,
  queue_entries q < q.(qSize) ->
  queue_enqueue_front q message = Some (q_post_front_enqueued_fields q message).
Proof.
  intros; unfold queue_enqueue_front, q_post_front_enqueued_fields.
  rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity.
Qed.

Lemma q_post_front_nonfull_bounds : forall sg q,
  queue_fields_consistency sg [] q -> queue_entries q < q.(qSize) ->
  0 < q.(qSize) /\ 0 <= q.(qOutIndex) < q.(qSize) /\
  0 <= queue_entries q < 65535 /\
  q.(qStart) <= q_post_front_next_out q < queue_end_addr q.
Proof.
  intros sg q Hvalid Hroom.
  pose proof (Zlength_nonneg q.(qMessages)) as Hcount.
  fold (queue_entries q) in Hcount.
  assert (Hsize : 0 < q.(qSize)) by lia.
  pose proof (queue_fields_consistency_positive sg [] q Hvalid Hsize) as [_ [Hout _]].
  pose proof (queue_retreat_index_in_range _ _ Hsize Hout) as Hnext.
  pose proof Hvalid as [_ [_ [Hsize_bound _]]].
  rewrite q_post_front_next_out_eq.
  change (0 < q.(qSize) /\ 0 <= q.(qOutIndex) < q.(qSize) /\
    0 <= queue_entries q < 65535 /\
    q.(qStart) <= q.(qStart) + queue_retreat_index q.(qSize) q.(qOutIndex) * 4 <
      q.(qStart) + q.(qSize) * 4).
  repeat split; lia.
Qed.

Definition q_post_front_slot_frame q slots : Assertion :=
  coq_prop (queue_entries q < q.(qSize)) &&
    PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex)) 0 q.(qSize) slots.

Lemma q_post_front_slot_split : forall sg q slots,
  queue_fields_consistency sg [] q -> queue_entries q < q.(qSize) ->
  queue_buffer_rep q slots |--
  coq_prop (queue_slots_model q slots) &&
    (q_post_front_next_out q # Ptr |->_ **
     PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex)) 0 q.(qSize) slots).
Proof.
  intros sg q slots Hvalid Hroom.
  pose proof (q_post_front_nonfull_bounds sg q Hvalid Hroom) as [Hsize [Hout _]].
  pose proof (queue_retreat_index_in_range _ _ Hsize Hout) as Hnext.
  rewrite q_post_front_next_out_eq.
  sep_apply_l_atomic (queue_buffer_split_slot q slots
    (queue_retreat_index q.(qSize) q.(qOutIndex)) Hnext).
  Intros; unfold PtrArray.mixedstoreA.
  destruct (Znth (queue_retreat_index q.(qSize) q.(qOutIndex)) slots None) as [value|];
    cbn [StorePtrAsElement.storeA StorePtrAsElement.undefstoreA].
  - sep_apply_l_atomic (store_ptr_undef_store_ptr
      (q.(qStart) + queue_retreat_index q.(qSize) q.(qOutIndex) * ptr_size_Z) value); entailer!.
  - entailer!.
Qed.

Lemma q_post_front_qcb_enqueued_equiv : forall sg q message,
  q_post_profile sg -> valid_queue_id sg q.(qID) -> queue_entries q < q.(qSize) ->
  q_post_front_qcb_cells (qcb_addr sg q.(qID)) q (q_post_front_next_out q) (queue_entries q + 1) --||--
  used_queue_control_block sg (q_post_front_enqueued_fields q message).
Proof.
  intros sg q message Hprofile Hqid Hroom.
  assert (Hnext : queue_out_addr (q_post_front_enqueued_fields q message) = q_post_front_next_out q).
  { rewrite q_post_front_next_out_eq.
    unfold queue_out_addr, q_post_front_enqueued_fields, queue_with_contents;
      cbn; reflexivity. }
  assert (Hcount : queue_entries (q_post_front_enqueued_fields q message) = queue_entries q + 1).
  { change (Zlength (message :: q.(qMessages)) = Zlength q.(qMessages) + 1).
    rewrite Zlength_cons; lia. }
  rewrite (q_post_front_qcb_cells_equiv sg (q_post_front_enqueued_fields q message) Hprofile Hqid).
  rewrite Hnext, Hcount.
  unfold q_post_front_qcb_cells, q_post_front_qcb_readonly, queue_end_addr, queue_in_addr,
    q_post_front_enqueued_fields, queue_with_contents; reflexivity.
Qed.

Lemma q_post_front_enqueue_merge : forall sg state eid node q free slots message,
  q_post_queue_facts sg state eid node q free slots ->
  queue_entries q < q.(qSize) ->
  used_queue_control_block sg (q_post_front_enqueued_fields q message) **
    q_post_front_next_out q # Ptr |-> message **
    PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex)) 0 q.(qSize) slots **
    q_post_queue_frame sg state eid free |--
  UCOS2_inv sg (q_post_front_enqueue_state state eid node q message slots).
Proof.
  intros sg state eid node q free slots message
    [Hvalid [Hnode [Htype [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]] Hroom.
  pose proof (q_post_front_enqueue_some q message Hroom) as Hstep.
  assert (Haddr : q_post_front_next_out q = queue_out_addr (q_post_front_enqueued_fields q message)).
  { rewrite q_post_front_next_out_eq; reflexivity. }
  rewrite Haddr.
  sep_apply_l_atomic (queue_enqueue_front_merge_buffer sg q slots message
    (q_post_front_enqueued_fields q message) Hqvalid Hmodel Hstep).
  unfold q_post_front_enqueue_state, q_post_queue_frame, queue_buffer_rep; Intros.
  pose proof (q_post_enqueue_merge_global sg QueuePostFront state eid node q message
    (q_post_front_enqueued_fields q message) slots free Hvalid Hbinding Hpart Hnode Htype Hq
    Hempty Hmodel Hstep) as Hmerge.
  cbn zeta in Hmerge; sep_apply_r_atomic Hmerge.
  unfold q_post_enqueue_slots; entailer!.
Qed.

Lemma q_post_front_wake_critical : forall sg entry eid current message priority after,
  q_post_lookup entry eid current -> q_post_group entry current <> 0 ->
  q_post_wake_result sg eid message entry after priority ->
  q_post_critical sg QueuePostFront eid message entry (OS_ERR_NONE, true) after.
Proof.
  intros; apply (proj2 (q_post_front_wake_critical_iff _ _ _ _ _ _)).
  eapply q_post_wake_critical; eassumption.
Qed.

Lemma q_post_front_full_critical : forall sg entry eid current q message,
  q_post_lookup entry eid current -> current.(queueFields) = Some q ->
  q_post_group entry current = 0 -> q.(qSize) <= queue_entries q ->
  q_post_critical sg QueuePostFront eid message entry (OS_ERR_Q_FULL, false) entry.
Proof.
  intros sg entry eid current q message Hlookup Hq Hgroup Hfull.
  exists current; split; [exact Hlookup|].
  change (encode_event_wait_grp (waitList current) (TskState entry) = 0) in Hgroup.
  rewrite Hgroup; exists q; split; [exact Hq|].
  rewrite (proj2 (Z.leb_le _ _) Hfull); split; reflexivity.
Qed.

Lemma q_post_front_enqueue_critical : forall sg entry eid current q message slots,
  q_post_lookup entry eid current -> current.(queueFields) = Some q ->
  q_post_group entry current = 0 ->
  entry.(EventState).(publishedQueueBytes) q.(qID) = Some slots ->
  queue_entries q < q.(qSize) ->
  q_post_critical sg QueuePostFront eid message entry (OS_ERR_NONE, false)
    (q_post_front_enqueue_state entry eid current q message slots).
Proof.
  intros sg entry eid current q message slots Hlookup Hq Hgroup Hslots Hroom.
  exists current; split; [exact Hlookup|].
  change (encode_event_wait_grp (waitList current) (TskState entry) = 0) in Hgroup.
  rewrite Hgroup; exists q; split; [exact Hq|].
  rewrite (proj2 (Z.leb_gt _ _) Hroom).
  exists slots, (q_post_front_enqueued_fields q message).
  split; [exact Hslots|]; split; [apply q_post_front_enqueue_some; exact Hroom|].
  split; reflexivity.
Qed.
