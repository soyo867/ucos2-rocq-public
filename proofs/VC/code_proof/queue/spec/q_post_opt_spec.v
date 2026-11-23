Require Export Ucos2Verify.VC.code.queue.spec.q_post_api_spec.
Require Export Ucos2Verify.VC.code.queue.q_post_source_protocol.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From AUXLib Require Import ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic ArrayLib MapLib.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** Options is the entire INT8U observation, not a three-bit enumeration.
    The protected relation already ignores bits other than 1, 2 and 4. *)
Definition q_post_opt_prefix_program environment critical sg caller mask pe eid message options
  : program UCOS2_Verify_State ((Z * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((4, false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
      exists active saved acquired error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        q_post_critical sg (QueuePostOptions options) eid message acquired (error, schedule) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((encode_os_err_code error, schedule), returned)
    else result = ((1, false), caller) /\ restored = before.

Definition q_post_opt_program environment critical sg caller mask pe eid message options
  : program UCOS2_Verify_State Z :=
  bind (q_post_opt_prefix_program environment critical sg caller mask pe eid message options)
    (q_post_tail environment critical sg mask).

Definition q_post_opt_safe environment critical sg caller mask pe eid message options before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (q_post_opt_program environment critical sg caller mask pe eid message options) X.

Definition q_post_opt_caller_result environment critical sg original mask pe eid message options before
  error returned current : Prop :=
  exists prefix_caller restored schedule,
    q_post_opt_prefix_program environment critical sg original mask pe eid message options before
      ((error, schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition q_post_opt_post environment critical saved_local sg original mask pe eid message options before error
  (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX returned current,
    coq_prop (q_post_opt_caller_result environment critical sg original mask pe eid message options before
      error returned current /\ q_post_return_safe current error X) &&
    q_post_closed environment critical saved_local sg returned mask current.

Definition q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before : Prop :=
  forall returned restored error,
    q_post_opt_prefix_program environment critical sg caller mask pe eid message options before
      ((error, true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Lemma q_post_opt_program_null : forall environment critical sg caller mask eid message options before,
  q_post_opt_program environment critical sg caller mask 0 eid message options before 4 before.
Proof.
  intros; exists ((4, false), caller), before; split.
  - unfold q_post_opt_prefix_program; cbn; split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_opt_program_wrong_type : forall environment critical sg caller mask pe eid message options before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_post_opt_program environment critical sg caller mask pe eid message options before 1 before.
Proof.
  intros; exists ((1, false), caller), before; split.
  - change (q_post_opt_prefix_program environment critical sg caller mask pe eid message options
      before ((1, false), caller) before).
    unfold q_post_opt_prefix_program; rewrite (proj2 (Z.eqb_neq _ _) H),
      (proj2 (Z.eqb_neq _ _) H0); split; reflexivity.
  - cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_opt_prefix_protected : forall environment critical sg original active returned mask
  pe eid message options before acquired released restored saved error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  q_post_critical sg (QueuePostOptions options) eid message acquired (error, schedule) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  q_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((encode_os_err_code error, schedule), returned) restored.
Proof.
  intros; unfold q_post_opt_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0; cbn.
  exists active, saved, acquired, error, schedule, released, returned; auto.
Qed.

Lemma q_post_opt_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid message options before restored error schedule X,
  q_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, schedule), returned) restored ->
  q_post_opt_safe environment critical sg original mask pe eid message options before X ->
  safeExec (fun state => state = restored)
    (q_post_tail environment critical sg mask ((error, schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid message options before restored error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (q_post_opt_prefix_program environment critical sg original mask pe eid message options)
    (q_post_tail environment critical sg mask) (fun state => state = before)
    ((error, schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_post_opt_program_nonschedule : forall environment critical sg original returned mask
  pe eid message options before restored error,
  q_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, false), returned) restored ->
  q_post_opt_program environment critical sg original mask pe eid message options before error restored.
Proof.
  intros; exists ((error, false), returned), restored; split; [assumption|].
  cbn [q_post_tail]; split; reflexivity.
Qed.

Lemma q_post_opt_program_schedule : forall environment critical sg original returned final mask
  pe eid message options before restored current error,
  q_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, true), returned) restored ->
  task_resume_schedule_program environment critical sg returned mask restored final current ->
  q_post_opt_program environment critical sg original mask pe eid message options before error current.
Proof.
  intros; exists ((error, true), returned), restored; split; [assumption|].
  cbn [q_post_tail]; exists tt, current; split; [|split; reflexivity].
  exists final, current; split; [assumption|split; reflexivity].
Qed.

Lemma q_post_opt_safe_return : forall environment critical sg caller mask pe eid message options before current error X,
  q_post_opt_program environment critical sg caller mask pe eid message options before error current ->
  q_post_opt_safe environment critical sg caller mask pe eid message options before X ->
  q_post_return_safe current error X.
Proof.
  intros environment critical sg caller mask pe eid message options before current error X Hprogram Hsafe.
  eapply (highstependret_derive
    (q_post_opt_program environment critical sg caller mask pe eid message options)
    (fun state => state = before) error (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_post_opt_closed_return : forall environment critical saved_local sg original returned mask
  pe eid message options before current error X,
  q_post_opt_caller_result environment critical sg original mask pe eid message options before error returned current ->
  q_post_opt_safe environment critical sg original mask pe eid message options before X ->
  q_post_closed environment critical saved_local sg returned mask current |--
  q_post_opt_post environment critical saved_local sg original mask pe eid message options before error X.
Proof.
  intros.
  assert (Hprogram : q_post_opt_program environment critical sg original mask pe eid message options before error current).
  { pose proof H as Hresult; destruct Hresult as [prefix_caller [restored [schedule [Hprefix Htail]]]].
    destruct schedule.
    - eapply q_post_opt_program_schedule with (final := returned); eassumption.
    - destruct Htail as [-> ->]; eapply q_post_opt_program_nonschedule; exact Hprefix. }
  pose proof (q_post_opt_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0).
  unfold q_post_opt_post; Exists returned current; entailer!.
Qed.

Lemma q_post_opt_sched_return : forall environment critical saved_local sg original returned mask
  pe eid message options before restored error X,
  q_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, true), returned) restored ->
  q_post_opt_safe environment critical sg original mask pe eid message options before X ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  q_post_opt_post environment critical saved_local sg original mask pe eid message options before error X.
Proof.
  intros environment critical saved_local sg original returned mask pe eid message options before restored error X Hprefix Hsafe.
  pose proof (q_post_opt_prefix_safe_continuation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hprefix Hsafe) as Htail.
  cbn [q_post_tail] in Htail.
  sep_apply_l_atomic (task_resume_sched_post_safe_return environment critical saved_local sg
    returned mask restored error X Htail).
  unfold task_resume_sched_refined_post; Intros final current.
  assert (Hresult : q_post_opt_caller_result environment critical sg original mask pe eid message options
    before error final current).
  { exists returned, restored, true; split; [exact Hprefix|exact (proj1 H)]. }
  pose proof (q_post_schedule_extra_tables _ _ _ _ _ _ _ _ (proj1 H)) as Htables.
  unfold q_post_opt_post, q_post_closed; Exists final current; rewrite Htables; entailer!.
  apply derivable1_andp_elim1.
Qed.

Definition q_post_opt_schedule_flag (options : Z) : Z :=
  if Z.eqb (Z.land options 4) 0 then 1 else 0.

Definition q_post_opt_effect sg eid message options acquired (error schedule : Z) released : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    q_post_critical sg (QueuePostOptions options) eid message acquired (code, request) released.

Definition q_post_opt_prefix_result environment critical sg caller mask pe eid message options before
  (error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    q_post_opt_prefix_program environment critical sg caller mask pe eid message options before
      ((error, request), returned) current.

Definition q_post_opt_restore_pre environment critical saved_local sg caller active mask saved pe eid message options
  before acquired released error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 2 /\
    UCOS2_state_inv sg released /\ q_post_opt_effect sg eid message options acquired error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error schedule : Assertion :=
  EX returned current,
    coq_prop (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before
      error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_post_opt_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid message options
  before acquired released error schedule,
  q_post_opt_restore_pre environment critical saved_local sg caller active mask saved pe eid message options
    before acquired released error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold q_post_opt_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma q_post_opt_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid message options
  before acquired released error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 ->
  UCOS2_state_inv sg released -> q_post_opt_effect sg eid message options acquired error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid message options before acquired released error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : q_post_opt_prefix_result environment critical sg caller mask pe eid message options before
    (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply q_post_opt_prefix_protected;
      [exact Hpe|exact Htype|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold q_post_opt_restore_post; Exists returned current; entailer!.
Qed.

Lemma q_post_opt_nonschedule_return : forall environment critical saved_local sg caller mask pe eid message options before error X,
  q_post_opt_safe environment critical sg caller mask pe eid message options before X ->
  q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error 0 |--
  q_post_opt_post environment critical saved_local sg caller mask pe eid message options before error X.
Proof.
  intros; unfold q_post_opt_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid].
  destruct request; [discriminate|].
  assert (Hresult : q_post_opt_caller_result environment critical sg caller mask pe eid message options before error returned current).
  { exists returned, current, false; auto. }
  sep_apply_r_atomic (q_post_opt_closed_return environment critical saved_local sg caller returned mask pe eid message options before current error X Hresult H).
  entailer!.
Qed.

Lemma q_post_opt_restored_schedule_pre : forall environment critical saved_local sg caller mask pe eid message options before error,
  q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before ->
  q_post_opt_restore_post environment critical saved_local sg caller mask pe eid message options before error 1 |--
  EX returned current,
    coq_prop (q_post_opt_prefix_result environment critical sg caller mask pe eid message options before error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid message options before error Hprotocol.
  unfold q_post_opt_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]. pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current error Hprefix)).
  Exists returned current; entailer!.
Qed.

(** A loop prefix is represented by continuation composition, never by a
    complete event_broadcast at an intermediate nonempty bitmap. The pure
    relation does not own or manufacture any of the current heap. *)
Definition q_post_opt_broadcast_cont sg eid message acquired current : Prop :=
  forall suffix final, q_post_broadcast sg eid message current suffix final ->
    exists priorities, q_post_broadcast sg eid message acquired priorities final.

Lemma q_post_opt_broadcast_cont_start : forall sg eid message state,
  q_post_opt_broadcast_cont sg eid message state state.
Proof. intros sg eid message state suffix final Hsuffix; eauto. Qed.

Lemma q_post_opt_broadcast_cont_step : forall sg eid message acquired current node priority after,
  q_post_opt_broadcast_cont sg eid message acquired current ->
  q_post_lookup current eid node -> q_post_group current node <> 0 ->
  q_post_wake_result sg eid message current after priority ->
  q_post_opt_broadcast_cont sg eid message acquired after.
Proof.
  intros sg eid message acquired current node priority after Hcont Hnode Hgroup Hstep suffix final Hsuffix.
  apply (Hcont (priority :: suffix) final).
  eapply event_broadcast_next; eassumption.
Qed.

Lemma q_post_opt_broadcast_cont_done : forall sg eid message acquired current node,
  q_post_opt_broadcast_cont sg eid message acquired current ->
  q_post_lookup current eid node -> q_post_group current node = 0 ->
  exists priorities, q_post_broadcast sg eid message acquired priorities current.
Proof.
  intros sg eid message acquired current node Hcont Hnode Hzero.
  apply (Hcont [] current); eapply event_broadcast_done; eassumption.
Qed.

Definition q_post_opt_loop_facts environment critical sg caller active mask saved before acquired
  eid observed initial message current node : Prop :=
  q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed initial /\
  q_post_profile sg /\ valid_event_id sg eid /\ q_post_group acquired initial <> 0 /\
  UCOS2_state_inv sg current /\ q_post_lookup current eid node /\
  node.(eventType) = OS_EVENT_TYPE_Q /\
  q_post_opt_broadcast_cont sg eid message acquired current.

Definition q_post_opt_loop_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial message current node : Assertion :=
  coq_prop (q_post_opt_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial message current node) &&
  (q_post_group_frame sg current eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired current).

Definition q_post_opt_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial message current node tid old : Assertion :=
  coq_prop (q_post_opt_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial message current node /\ q_post_group current node <> 0 /\
    event_task_rdy_entry sg current.(TskState) eid node tid old) &&
  (q_post_wake_frame sg current eid tid **
    q_post_mask_frame environment critical saved_local sg active saved acquired current).

Lemma q_post_opt_loop_wake_split : forall environment critical saved_local sg caller active mask saved before acquired
  eid observed initial message current node,
  q_post_group current node <> 0 ->
  q_post_opt_loop_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial message current node **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group current node |--
  EX tid old,
    q_post_opt_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
      eid observed initial message current node tid old **
    event_task_rdy_pre sg current.(TskState) eid node tid old 4 0
      (q_post_sched_group current) (q_post_sched_rows current).
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed initial message current node Hgroup.
  unfold q_post_opt_loop_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hinitial [Hvalid [Hnode [Htype Hcont]]]]]]].
  sep_apply_l_atomic (q_post_group_cell_merge sg current eid node Hvalid Hnode).
  assert (Hlayout : event_object_layout_prop sg eid).
  { exact (proj1 (proj2 Hprofile) eid Heid). }
  sep_apply_l_atomic (q_post_wake_split sg current eid node Hvalid Hnode Htype Hgroup Hlayout).
  Intros tid old; Exists tid old; unfold q_post_opt_loop_wake_context; entailer!.
Qed.

Lemma q_post_opt_loop_wake_merge : forall environment critical saved_local sg caller active mask saved before acquired
  eid observed initial message current node tid old priority,
  q_post_opt_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial message current node tid old **
    event_task_rdy_post sg current.(TskState) eid node tid old message 4 0
      (q_post_sched_group current) (q_post_sched_rows current) priority |--
  EX after next,
    q_post_opt_loop_context environment critical saved_local sg caller active mask saved before acquired
      eid observed initial message after next **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group after next.
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed initial message current node tid old priority.
  unfold q_post_opt_loop_wake_context; Intros.
  destruct H as [Hfacts [Hgroup Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hinitial [Hvalid [Hnode [Htype Hcont]]]]]]].
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (q_post_wake_merge sg current eid node tid old message priority Hvalid Hnode Htype Hentry).
  Intros after.
  pose proof (q_post_opt_broadcast_cont_step sg eid message acquired current node priority after
    Hcont Hnode Hgroup H) as Hnext_cont.
  destruct (q_post_wake_decompose sg current eid node message priority after Hvalid Hnode Htype Hgroup H)
    as [selected [tail [previous [Hlist [Hold [Hpriority [Hafter [Hafter_valid Hafter_node]]]]]]]].
  subst after.
  sep_apply_l_atomic (q_post_mask_frame_wake_update environment critical saved_local sg active saved acquired current
    eid node selected previous message Hold).
  sep_apply_l_atomic (q_post_group_cell_split sg
    (event_wake_state sg current eid node selected previous PendQ message PendOK)
    eid (event_set_wait_list node tail) Hafter_node).
  Intros.
  Exists (event_wake_state sg current eid node selected previous PendQ message PendOK)
    (event_set_wait_list node tail).
  unfold q_post_opt_loop_context, q_post_opt_loop_facts; entailer!.
Qed.

Lemma q_post_opt_single_wake_critical : forall sg entry eid current message options priority after,
  q_post_lookup entry eid current -> q_post_group entry current <> 0 ->
  Z.land options 1 = 0 -> q_post_wake_result sg eid message entry after priority ->
  q_post_critical sg (QueuePostOptions options) eid message entry
    (OS_ERR_NONE, Z.eqb (Z.land options 4) 0) after.
Proof.
  intros sg entry eid current message options priority after Hlookup Hgroup Hsingle Hstep.
  unfold q_post_group in Hgroup.
  exists current; split; [exact Hlookup|].
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup); split; [reflexivity|].
  cbn [q_post_broadcast_requested]; rewrite Hsingle; cbn; exists priority; exact Hstep.
Qed.

Lemma q_post_opt_broadcast_critical : forall sg entry eid current message options priorities after,
  q_post_lookup entry eid current -> q_post_group entry current <> 0 ->
  Z.land options 1 <> 0 -> q_post_broadcast sg eid message entry priorities after ->
  q_post_critical sg (QueuePostOptions options) eid message entry
    (OS_ERR_NONE, Z.eqb (Z.land options 4) 0) after.
Proof.
  intros sg entry eid current message options priorities after Hlookup Hgroup Hbroadcast Hloop.
  unfold q_post_group in Hgroup.
  exists current; split; [exact Hlookup|].
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup); split; [reflexivity|].
  cbn [q_post_broadcast_requested]; rewrite (proj2 (Z.eqb_neq _ _) Hbroadcast); cbn.
  exists priorities; exact Hloop.
Qed.

Lemma q_post_opt_full_critical : forall sg entry eid current q message options,
  q_post_lookup entry eid current -> current.(queueFields) = Some q ->
  q_post_group entry current = 0 -> q.(qSize) <= queue_entries q ->
  q_post_critical sg (QueuePostOptions options) eid message entry (OS_ERR_Q_FULL, false) entry.
Proof.
  intros sg entry eid current q message options Hlookup Hq Hgroup Hfull.
  unfold q_post_group in Hgroup.
  exists current; split; [exact Hlookup|].
  rewrite Hgroup; exists q; split; [exact Hq|].
  rewrite (proj2 (Z.leb_le _ _) Hfull); split; reflexivity.
Qed.

Lemma q_post_opt_loop_restore : forall environment critical saved_local sg caller active mask saved before acquired
  pe eid observed initial message options current node,
  pe <> 0 -> Z.land options 1 <> 0 -> q_post_group current node = 0 ->
  q_post_opt_loop_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial message current node **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> q_post_group current node |--
  q_post_opt_restore_pre environment critical saved_local sg caller active mask saved pe eid message options
    before acquired current 0 (q_post_opt_schedule_flag options).
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired pe eid observed initial message options current node
    Hpe Hbroadcast Hzero.
  unfold q_post_opt_loop_context; Intros.
  destruct H as [Hacquire [Hprofile [Heid [Hinitial [Hvalid [Hnode [Htype Hcont]]]]]]].
  destruct (q_post_opt_broadcast_cont_done sg eid message acquired current node Hcont Hnode Hzero)
    as [priorities Hloop].
  pose proof Hacquire as [Hsave [_ [_ [Hinitial_node Hrest]]]].
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbefore_type.
  pose proof (q_post_opt_broadcast_critical sg acquired eid initial message options priorities current
    Hinitial_node Hinitial Hbroadcast Hloop) as Hstep.
  assert (Heffect : q_post_opt_effect sg eid message options acquired 0 (q_post_opt_schedule_flag options) current).
  { exists OS_ERR_NONE, (Z.eqb (Z.land options 4) 0); repeat split; assumption || reflexivity. }
  sep_apply_l_atomic (q_post_group_cell_merge sg current eid node Hvalid Hnode).
  unfold q_post_opt_restore_pre; rewrite q_post_masked_equiv; entailer!.
Qed.

Definition q_post_opt_next_out (q : QueueFields) : addr :=
  (if Z.eqb (queue_out_addr q) q.(qStart) then queue_end_addr q else queue_out_addr q) - 4.

Definition q_post_opt_front_fields q message : QueueFields :=
  queue_with_contents q q.(qInIndex) (queue_retreat_index q.(qSize) q.(qOutIndex))
    (message :: q.(qMessages)).

Definition q_post_opt_enqueued_fields options q message : QueueFields :=
  if q_post_front_requested (QueuePostOptions options)
  then q_post_opt_front_fields q message else q_post_enqueued_fields q message.

Definition q_post_opt_enqueue_state options state eid node q message slots : UCOS2_Verify_State :=
  replace_EventS (queue_update state.(EventState) eid node
    (q_post_opt_enqueued_fields options q message)
    (q_post_enqueue_slots (q_post_front_requested (QueuePostOptions options)) q message slots)) state.

Definition q_post_opt_qcb_cells (base : addr) (q : QueueFields) (qin qout count : Z) : Assertion :=
  (&(base # "os_q" ->ₛ "OSQIn")) # Ptr |-> qin **
  (&(base # "os_q" ->ₛ "OSQOut")) # Ptr |-> qout **
  (&(base # "os_q" ->ₛ "OSQEntries")) # UShort |-> count **
  (&(base # "os_q" ->ₛ "OSQSize")) # UShort |-> q.(qSize) **
  (&(base # "os_q" ->ₛ "OSQEnd")) # Ptr |-> queue_end_addr q **
  (&(base # "os_q" ->ₛ "OSQStart")) # Ptr |-> q.(qStart) **
  (&(base # "os_q" ->ₛ "OSQPtr")) # Ptr |->_ .

Definition q_post_opt_front_slot_frame q slots : Assertion :=
  coq_prop (queue_entries q < q.(qSize)) &&
    PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex))
      0 q.(qSize) slots.

Definition q_post_opt_written_buffer options q message slots : Assertion :=
  if q_post_front_requested (QueuePostOptions options) then
    q_post_opt_next_out q # Ptr |-> message ** q_post_opt_front_slot_frame q slots
  else queue_in_addr q # Ptr |-> message ** q_post_slot_frame q slots.

Definition q_post_opt_written_in options q : addr :=
  if q_post_front_requested (QueuePostOptions options) then queue_in_addr q else q_post_next_in q.
Definition q_post_opt_written_out options q : addr :=
  if q_post_front_requested (QueuePostOptions options) then q_post_opt_next_out q else queue_out_addr q.

Lemma q_post_opt_qcb_cells_equiv : forall sg q,
  q_post_profile sg -> valid_queue_id sg q.(qID) ->
  used_queue_control_block sg q --||--
    q_post_opt_qcb_cells (qcb_addr sg q.(qID)) q (queue_in_addr q) (queue_out_addr q) (queue_entries q).
Proof.
  intros sg q Hprofile Hqid.
  rewrite (q_post_qcb_cells_equiv sg q Hprofile Hqid).
  unfold q_post_qcb_cells, q_post_qcb_readonly, q_post_opt_qcb_cells; split; entailer!.
Qed.

Lemma q_post_opt_next_out_eq : forall q,
  q_post_opt_next_out q = q.(qStart) + queue_retreat_index q.(qSize) q.(qOutIndex) * 4.
Proof.
  intros q; unfold q_post_opt_next_out; rewrite queue_out_start_eqb.
  unfold queue_retreat_index, queue_out_addr, queue_end_addr, Ucos2Verify.lib.event.sizeof_ptr.
  destruct (Z.eqb q.(qOutIndex) 0); lia.
Qed.

Lemma q_post_opt_front_nonfull_bounds : forall sg q,
  queue_fields_consistency sg [] q -> queue_entries q < q.(qSize) ->
  0 < q.(qSize) /\ 0 <= q.(qOutIndex) < q.(qSize) /\
  0 <= queue_retreat_index q.(qSize) q.(qOutIndex) < q.(qSize) /\
  q.(qStart) <= q_post_opt_next_out q < queue_end_addr q.
Proof.
  intros sg q Hvalid Hroom.
  pose proof (q_post_nonfull_bounds sg q Hvalid Hroom) as [Hsize _].
  pose proof (queue_fields_consistency_positive sg [] q Hvalid Hsize) as [_ [Hout _]].
  pose proof (queue_retreat_index_in_range _ _ Hsize Hout) as Hnext.
  rewrite q_post_opt_next_out_eq; unfold queue_end_addr, Ucos2Verify.lib.event.sizeof_ptr; repeat split; lia.
Qed.

Lemma q_post_opt_front_slot_split : forall sg q slots,
  queue_fields_consistency sg [] q -> queue_entries q < q.(qSize) ->
  queue_buffer_rep q slots |--
  coq_prop (queue_slots_model q slots) &&
    (q_post_opt_next_out q # Ptr |->_ **
     PtrArray.mixed_missing_i q.(qStart) (queue_retreat_index q.(qSize) q.(qOutIndex)) 0 q.(qSize) slots).
Proof.
  intros sg q slots Hvalid Hroom.
  pose proof (q_post_opt_front_nonfull_bounds sg q Hvalid Hroom) as [_ [_ [Hindex _]]].
  sep_apply_l_atomic (queue_buffer_split_slot q slots (queue_retreat_index q.(qSize) q.(qOutIndex)) Hindex).
  Intros; rewrite q_post_opt_next_out_eq; unfold PtrArray.mixedstoreA.
  destruct (Znth (queue_retreat_index q.(qSize) q.(qOutIndex)) slots None) as [value|];
    cbn [StorePtrAsElement.storeA StorePtrAsElement.undefstoreA].
  - sep_apply_l_atomic (store_ptr_undef_store_ptr
      (q.(qStart) + queue_retreat_index q.(qSize) q.(qOutIndex) * ptr_size_Z) value); entailer!.
  - entailer!.
Qed.

Lemma q_post_opt_enqueue_some : forall options q message,
  queue_entries q < q.(qSize) ->
  q_post_enqueue (q_post_front_requested (QueuePostOptions options)) q message =
    Some (q_post_opt_enqueued_fields options q message).
Proof.
  intros options q message Hroom; unfold q_post_enqueue, q_post_opt_enqueued_fields.
  destruct (q_post_front_requested (QueuePostOptions options)).
  - unfold queue_enqueue_front, q_post_opt_front_fields; rewrite (proj2 (Z.ltb_lt _ _) Hroom); reflexivity.
  - apply q_post_enqueue_back_some; exact Hroom.
Qed.

Lemma q_post_opt_enqueue_critical : forall sg entry eid current q message options slots,
  q_post_lookup entry eid current -> current.(queueFields) = Some q ->
  q_post_group entry current = 0 ->
  entry.(EventState).(publishedQueueBytes) q.(qID) = Some slots ->
  queue_entries q < q.(qSize) ->
  q_post_critical sg (QueuePostOptions options) eid message entry (OS_ERR_NONE, false)
    (q_post_opt_enqueue_state options entry eid current q message slots).
Proof.
  intros sg entry eid current q message options slots Hlookup Hq Hgroup Hslots Hroom.
  unfold q_post_group in Hgroup.
  exists current; split; [exact Hlookup|]. rewrite Hgroup.
  exists q; split; [exact Hq|]. rewrite (proj2 (Z.leb_gt _ _) Hroom).
  exists slots, (q_post_opt_enqueued_fields options q message); repeat split.
  - exact Hslots.
  - apply q_post_opt_enqueue_some; exact Hroom.
Qed.

Lemma q_post_opt_qcb_enqueued_equiv : forall sg options q message,
  q_post_profile sg -> valid_queue_id sg q.(qID) ->
  q_post_opt_qcb_cells (qcb_addr sg q.(qID)) q
    (q_post_opt_written_in options q) (q_post_opt_written_out options q) (queue_entries q + 1) --||--
  used_queue_control_block sg (q_post_opt_enqueued_fields options q message).
Proof.
  intros sg options q message Hprofile Hqid.
  assert (Hid : valid_queue_id sg (q_post_opt_enqueued_fields options q message).(qID)).
  { unfold q_post_opt_enqueued_fields; destruct (q_post_front_requested (QueuePostOptions options)); exact Hqid. }
  rewrite (q_post_opt_qcb_cells_equiv sg (q_post_opt_enqueued_fields options q message) Hprofile Hid).
  unfold q_post_opt_enqueued_fields, q_post_opt_written_in, q_post_opt_written_out.
  destruct (q_post_front_requested (QueuePostOptions options)).
  - assert (Hout : queue_out_addr (q_post_opt_front_fields q message) = q_post_opt_next_out q).
    { rewrite q_post_opt_next_out_eq; reflexivity. }
    assert (Hcount : queue_entries (q_post_opt_front_fields q message) = queue_entries q + 1).
    { change (Zlength (message :: q.(qMessages)) = Zlength q.(qMessages) + 1).
      rewrite Zlength_cons; lia. }
    rewrite Hout, Hcount.
    unfold q_post_opt_qcb_cells, queue_in_addr, queue_end_addr, q_post_opt_front_fields, queue_with_contents; reflexivity.
  - assert (Hin : queue_in_addr (q_post_enqueued_fields q message) = q_post_next_in q).
    { unfold q_post_next_in; rewrite queue_in_advance_end_eqb.
      unfold queue_in_addr, q_post_enqueued_fields, queue_with_contents; cbn.
      unfold queue_advance_index; destruct (Z.eqb (q.(qInIndex) + 1) q.(qSize));
        unfold Ucos2Verify.lib.event.sizeof_ptr; lia. }
    assert (Hcount : queue_entries (q_post_enqueued_fields q message) = queue_entries q + 1).
    { unfold queue_entries, q_post_enqueued_fields, queue_with_contents; cbn.
      rewrite Zlength_app, Zlength_cons, Zlength_nil; lia. }
    rewrite Hin, Hcount.
    unfold q_post_opt_qcb_cells, queue_out_addr, queue_end_addr, q_post_enqueued_fields, queue_with_contents; reflexivity.
Qed.

Lemma q_post_opt_enqueue_merge : forall sg options state eid node q free slots message,
  q_post_queue_facts sg state eid node q free slots ->
  queue_entries q < q.(qSize) ->
  used_queue_control_block sg (q_post_opt_enqueued_fields options q message) **
    q_post_opt_written_buffer options q message slots ** q_post_queue_frame sg state eid free |--
  UCOS2_inv sg (q_post_opt_enqueue_state options state eid node q message slots).
Proof.
  intros sg options state eid node q free slots message
    [Hvalid [Hnode [Htype [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]] Hroom.
  pose proof (q_post_opt_enqueue_some options q message Hroom) as Hstep.
  assert (Hbuffer : q_post_opt_written_buffer options q message slots |--
    queue_buffer_rep (q_post_opt_enqueued_fields options q message)
      (q_post_enqueue_slots (q_post_front_requested (QueuePostOptions options)) q message slots)).
  { unfold q_post_opt_written_buffer, q_post_opt_enqueued_fields, q_post_enqueue_slots.
    destruct (q_post_front_requested (QueuePostOptions options)) eqn:E.
    - unfold q_post_opt_front_slot_frame; Intros.
      assert (Hout : queue_out_addr (q_post_opt_front_fields q message) = q_post_opt_next_out q).
      { rewrite q_post_opt_next_out_eq; reflexivity. }
      rewrite <- Hout.
      sep_apply_l_atomic (queue_enqueue_front_merge_buffer sg q slots message (q_post_opt_front_fields q message)
        Hqvalid Hmodel ltac:(unfold queue_enqueue_front, q_post_opt_front_fields;
          rewrite (proj2 (Z.ltb_lt _ _) Hroom); reflexivity)).
      entailer!.
    - unfold q_post_slot_frame; Intros.
      sep_apply_l_atomic (queue_enqueue_back_merge_buffer sg q slots message (q_post_enqueued_fields q message)
        Hqvalid Hmodel (q_post_enqueue_back_some q message Hroom)); entailer!. }
  sep_apply_l_atomic Hbuffer.
  unfold q_post_opt_enqueue_state, q_post_queue_frame, queue_buffer_rep; Intros.
  pose proof (q_post_enqueue_merge_global sg (QueuePostOptions options) state eid node q message
    (q_post_opt_enqueued_fields options q message) slots free Hvalid Hbinding Hpart Hnode Htype Hq
    Hempty Hmodel Hstep) as Hmerge.
  cbn zeta in Hmerge; sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma q_post_opt_broadcast_preserves : forall sg eid message (P : UCOS2_Verify_State -> Prop),
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendQ message PendOK)) ->
  forall state priorities after,
  q_post_broadcast sg eid message state priorities after ->
  forall node, UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_Q -> P state -> P after.
Proof.
  intros sg eid message P Hpreserve state priorities after Hloop.
  induction Hloop as [state actual Hactual Hzero |
    state actual priority mid priorities after Hactual Hgroup Hstep Hloop IH];
    intros node Hvalid Hnode Htype HP.
  - exact HP.
  - assert (actual = node) by congruence; subst actual.
    destruct (q_post_wake_decompose sg state eid node message priority mid Hvalid Hnode Htype Hgroup Hstep)
      as [tid [tail [old [Hlist [Hold [Hpriority [Hmid [Hmid_valid Hmid_node]]]]]]]].
    subst mid; eapply IH with (node := event_set_wait_list node tail).
    + exact Hmid_valid.
    + exact Hmid_node.
    + exact Htype.
    + eapply Hpreserve; eassumption.
Qed.

Lemma q_post_opt_scheduled_effect_preserves : forall sg eid message options (P : UCOS2_Verify_State -> Prop),
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendQ message PendOK)) ->
  forall state node error after,
  UCOS2_state_inv sg state -> q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  q_post_critical sg (QueuePostOptions options) eid message state (error, true) after ->
  P state -> P after.
Proof.
  intros sg eid message options P Hpreserve state node error after Hvalid Hnode Htype Hstep HP.
  pose proof (proj1 (q_post_critical_requests_schedule_iff sg (QueuePostOptions options) state eid node message
    (error, true) after Hnode Hstep) eq_refl) as [Hgroup Hrequest].
  destruct Hstep as [actual [Hactual Hstep]]; assert (actual = node) by congruence; subst actual.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup) in Hstep.
  destruct Hstep as [_ Hstep]. destruct (q_post_broadcast_requested (QueuePostOptions options)).
  - destruct Hstep as [priorities Hloop].
    eapply q_post_opt_broadcast_preserves; eassumption.
  - destruct Hstep as [priority Hcall].
    destruct (q_post_wake_decompose sg state eid node message priority after Hvalid Hnode Htype Hgroup Hcall)
      as [tid [tail [old [Hlist [Hold [Hpriority [-> Hrest]]]]]]].
    eapply Hpreserve; eassumption.
Qed.

Lemma q_post_opt_prefix_wake_decompose : forall environment critical sg original mask pe eid message options before
  observed returned restored error,
  UCOS2_state_inv sg before -> q_post_call_input critical sg original pe before eid observed ->
  q_post_opt_prefix_program environment critical sg original mask pe eid message options before
    ((error, true), returned) restored ->
  exists active saved acquired node code released,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    q_post_critical sg (QueuePostOptions options) eid message acquired (code, true) released /\
    UCOS2_state_inv sg released /\
    task_resume_restore_program environment critical sg active released returned restored.
Proof.
  intros environment critical sg original mask pe eid message options before observed returned restored error
    Hvalid Hinput Hprefix.
  unfold q_post_opt_prefix_program in Hprefix.
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
  pose proof (q_post_critical_preserves_validity sg (QueuePostOptions options) acquired eid node message
    (code, true) released (proj1 Hfacts) Hnode Hqueue Hstep) as Hreleased.
  exists active, saved, acquired, node, code, released; auto.
Qed.

Lemma q_post_opt_schedule_protocol_null : forall environment critical sg caller mask eid message options before,
  q_post_opt_schedule_protocol environment critical sg caller mask 0 eid message options before.
Proof.
  intros environment critical sg caller mask eid message options before returned restored error Hprefix.
  unfold q_post_opt_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma q_post_opt_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid message options before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before Hpe Htype returned restored error Hprefix.
  unfold q_post_opt_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma q_post_opt_schedule_protocol_no_sched : forall environment critical sg caller mask pe eid message options before,
  Z.land options 4 <> 0 ->
  q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before Hnosched returned restored error Hprefix.
  unfold q_post_opt_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2);
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule next.
  destruct Hstep as [node [Hnode Hbody]].
  pose proof (proj1 (q_post_critical_requests_schedule_iff sg (QueuePostOptions options) acquired eid node message
    (code, true) released Hnode ltac:(exists node; auto)) eq_refl) as [_ Hrequest].
  cbn [q_post_wake_requests_schedule] in Hrequest.
  apply Z.eqb_eq in Hrequest; contradiction.
Qed.

Lemma q_post_opt_schedule_protocol_task : forall environment critical sg call mask pe eid message options before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical -> task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before -> before.(SchedState).(readyList) <> [] ->
  q_post_opt_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid message options before.
Proof.
  intros environment critical sg call mask pe eid message options before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored error Hprefix.
  destruct (q_post_opt_prefix_wake_decompose environment critical sg (ResumeTaskCaller call) mask pe eid message options
    before observed returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [code [released [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  assert (Hreleased_source : task_resume_caller_source sg (ResumeTaskCaller active) released).
  { eapply q_post_opt_scheduled_effect_preserves with
      (sg := sg) (eid := eid) (message := message) (options := options)
      (state := acquired) (node := node) (error := code)
      (P := task_resume_caller_source sg (ResumeTaskCaller active)); try eassumption.
    intros; eapply q_post_wake_preserves_task_source; eassumption. }
  destruct (q_post_task_restore_source environment critical sg active returned released restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { eapply q_post_opt_scheduled_effect_preserves with
      (sg := sg) (eid := eid) (message := message) (options := options)
      (state := acquired) (node := node) (error := code)
      (P := fun s => s.(SchedState).(readyList) <> []); try eassumption.
    intros; apply q_post_wake_preserves_ready_nonempty; assumption. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma q_post_opt_schedule_protocol_disabled : forall environment critical sg view mask pe eid message options before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  q_post_opt_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid message options before.
Proof.
  intros environment critical sg view mask pe eid message options before observed Hvalid Hinput Hclients Hsource
    returned restored error Hprefix.
  destruct (q_post_opt_prefix_wake_decompose environment critical sg (ResumeGenericCaller view) mask pe eid message options
    before observed returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [code [released [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  assert (Hreleased_source : sched_disabled_entry_source view released).
  { eapply q_post_opt_scheduled_effect_preserves with
      (sg := sg) (eid := eid) (message := message) (options := options)
      (state := acquired) (node := node) (error := code)
      (P := sched_disabled_entry_source view); try eassumption.
    intros; apply q_post_wake_preserves_disabled_source; assumption. }
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    released restored Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma q_post_opt_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid message options before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  (forall active saved acquired node,
    q_post_save_facts environment critical sg caller active mask saved before acquired ->
    q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed node ->
    node.(waitList) = []) ->
  q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before observed Hvalid Hinput Hempty
    returned restored error Hprefix.
  destruct (q_post_opt_prefix_wake_decompose environment critical sg caller mask pe eid message options
    before observed returned restored error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [code [released [Hsave [Hacquire [Hstep Hrest]]]]]]]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  pose proof (proj1 (q_post_critical_requests_schedule_iff sg (QueuePostOptions options) acquired eid node message
    (code, true) released Hnode Hstep) eq_refl) as [Hgroup Hrequest].
  rewrite (Hempty active saved acquired node Hsave Hacquire) in Hgroup.
  exfalso; exact (Hgroup eq_refl).
Qed.

Lemma q_post_opt_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid message options before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before -> q_post_no_waiters_clients critical ->
  q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before observed Hvalid Hinput Hempty Hclients.
  eapply q_post_opt_schedule_protocol_acquired_no_waiters; [exact Hvalid|exact Hinput|].
  intros active saved acquired node Hfacts Hacquire.
  destruct Hfacts as [Hacquired [Hinterval Hrest]].
  destruct Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  destruct (q_post_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) before acquired Hclients Hvalid Hempty Hinterval)
    as [_ Hempty_acquired].
  exact (Hempty_acquired eid node Hnode Hqueue).
Qed.

Lemma q_post_opt_schedule_protocol_no_waiters_sources : forall environment critical sg caller mask pe eid message options before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  q_post_opt_schedule_protocol environment critical sg caller mask pe eid message options before.
Proof.
  intros environment critical sg caller mask pe eid message options before observed Hvalid Hinput Hempty Hfamily.
  eapply q_post_opt_schedule_protocol_no_waiters; [exact Hvalid|exact Hinput|exact Hempty|].
  apply q_post_no_waiters_clients_from_source_family; exact Hfamily.
Qed.

Lemma q_post_opt_loop_context_facts__broadcast : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial message current node,
  q_post_opt_loop_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial message current node |--
  coq_prop (q_post_opt_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial message current node).
Proof.
  intros; unfold q_post_opt_loop_context; entailer!.
Qed.
