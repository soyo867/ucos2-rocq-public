(** Public SemDel source composition: actual Save, protected deletion,
    actual Restore, and the source-requested Task/Disabled Scheduler tail. *)

Require Export Ucos2Verify.VC.code.sem.spec.sem_del_call_helpers.
Require Export Ucos2Verify.VC.code.sem.spec.sem_post_api_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_del_spec.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.field_storage.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(** Reuse the selected historical profile and existing Sem representations.
    In particular, do not strengthen this profile to all-slot field layout. *)
Definition sem_del_source_api_profile := sem_del_profile.
Definition sem_del_source_api_output_address (error_addr perr : Z) : Prop :=
  error_addr = perr.

(** A legitimate FREE slot is readable and reaches the real TYPE error.
    The handle protocol is needed only on the path which actually saves. *)
Definition sem_del_source_api_call_input critical sg caller pe before eid observed : Prop :=
  pe = 0 \/
  (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
   sem_query_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 3 ->
      q_del_int_nesting before <= 0 ->
      sem_post_handle_protocol critical sg
        (task_resume_view caller).(os_execution_invocation) eid)).

Lemma sem_del_source_api_call_input_acquire : forall critical sg caller pe before eid observed,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 ->
  q_del_int_nesting before <= 0 ->
  sem_del_source_api_call_input critical sg caller pe before eid observed ->
  sem_post_api_call_input critical sg caller pe before eid observed.
Proof.
  intros critical sg caller pe before eid observed Hpe Htype Hint [Hzero|Hinput];
    [contradiction|].
  destruct Hinput as [Hnonzero [Haddr [Hid [Hpublic Hgo]]]].
  right; split; [exact Hnonzero|].
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hpublic|].
  intros; exact (Hgo Htype Hint).
Qed.

Lemma sem_del_source_api_type_split : forall environment critical saved_local sg caller mask before pe eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  sem_del_source_api_call_input critical sg caller pe before eid observed ->
  q_post_closed environment critical saved_local sg caller mask before |--
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value before.(EventState) eid **
  q_post_type_context environment saved_local sg caller mask before eid.
Proof.
  intros environment critical saved_local sg caller mask before pe eid observed Hvalid Hpe Hinput.
  destruct Hinput as [Hzero|[_ [Haddr [Hid [Hpublic Hprotocol]]]]]; [contradiction|].
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hpublic).
  unfold q_post_type_context; entailer!.
Qed.

Lemma sem_del_source_api_type_merge : forall environment critical saved_local sg caller mask before eid,
  UCOS2_state_inv sg before ->
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value before.(EventState) eid **
    q_post_type_context environment saved_local sg caller mask before eid |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof.
  intros; rewrite (q_post_closed_equiv _ _ _ _ _ _ _ H).
  unfold q_post_type_context.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid H); entailer!.
Qed.

Lemma sem_del_source_api_type_to_interrupt : forall environment (critical : CriticalRegionResources) saved_local sg caller mask before eid,
  UCOS2_state_inv sg before ->
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value before.(EventState) eid **
    q_post_type_context environment saved_local sg caller mask before eid |--
  sg.(g_OSIntNesting) # UChar |-> q_del_int_nesting before **
    q_del_interrupt_context environment saved_local sg caller mask before.
Proof.
  intros.
  sep_apply_l_atomic (sem_del_source_api_type_merge environment critical saved_local sg caller mask before eid H).
  apply q_del_interrupt_split; exact H.
Qed.

Lemma sem_del_source_api_interrupt_to_save : forall environment critical saved_local sg caller mask before pe eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  event_slot_type_value before.(EventState) eid = 3 -> q_del_int_nesting before <= 0 ->
  sem_del_source_api_call_input critical sg caller pe before eid observed ->
  sg.(g_OSIntNesting) # UChar |-> q_del_int_nesting before **
    q_del_interrupt_context environment saved_local sg caller mask before |--
  sem_post_api_save_pre environment critical saved_local sg caller mask before pe eid observed.
Proof.
  intros environment critical saved_local sg caller mask before pe eid observed Hvalid Hpe Htype Hint Hinput.
  pose proof (sem_del_source_api_call_input_acquire _ _ _ _ _ _ _ Hpe Htype Hint Hinput) as Hgo.
  sep_apply_l_atomic (q_del_interrupt_merge environment critical saved_local sg caller mask before Hvalid).
  unfold sem_post_api_save_pre; entailer!.
Qed.

Definition sem_del_source_api_prefix_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (((Z * Z) * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = (((pe, 4), false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 3 then
      if Z.ltb 0 (q_del_int_nesting before) then
        result = (((pe, 15), false), caller) /\ restored = before
      else exists active saved acquired pointer error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        sem_delete_critical sg eid (unsigned_last_nbits opt 8) acquired
          (pointer, (error, schedule)) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = (((pointer, encode_os_err_code error), schedule), returned)
    else result = (((pe, 1), false), caller) /\ restored = before.

Definition sem_del_source_api_tail environment critical sg mask
  (result : ((Z * Z) * bool) * TaskResumeCaller)
  : program UCOS2_Verify_State (Z * Z) :=
  if snd (fst result) then
    bind (task_resume_schedule_call_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition sem_del_source_api_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (Z * Z) :=
  bind (sem_del_source_api_prefix_program environment critical sg caller mask pe eid opt)
    (sem_del_source_api_tail environment critical sg mask).

Definition sem_del_source_api_safe environment critical sg caller mask pe eid opt before
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (sem_del_source_api_program environment critical sg caller mask pe eid opt) X.

Definition sem_del_source_api_return_safe current pointer error
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret (pointer, error)) X.

Definition sem_del_source_api_caller_result environment critical sg original mask pe eid opt before
  pointer error returned current : Prop :=
  exists prefix_caller restored schedule,
    sem_del_source_api_prefix_program environment critical sg original mask pe eid opt before
      (((pointer, error), schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition sem_del_source_api_post environment critical saved_local sg original mask pe eid opt before
  error_addr pointer (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error returned current,
    coq_prop (sem_del_source_api_caller_result environment critical sg original mask pe eid opt before
      pointer error returned current /\ sem_del_source_api_return_safe current pointer error X) &&
    (q_post_closed environment critical saved_local sg returned mask current **
      error_addr # UChar |-> error).

Definition sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before : Prop :=
  forall returned restored pointer error,
    sem_del_source_api_prefix_program environment critical sg caller mask pe eid opt before
      (((pointer, error), true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Lemma sem_del_source_api_null_result : forall environment critical sg caller mask eid opt before,
  sem_del_source_api_caller_result environment critical sg caller mask 0 eid opt before 0 4 caller before.
Proof.
  intros; exists caller, before, false; split.
  - unfold sem_del_source_api_prefix_program; cbn; split; reflexivity.
  - split; reflexivity.
Qed.

Lemma sem_del_source_api_schedule_protocol_null : forall environment critical sg caller mask eid opt before,
  sem_del_source_api_schedule_protocol environment critical sg caller mask 0 eid opt before.
Proof. intros environment critical sg caller mask eid opt before returned restored pointer error [Hresult _]; discriminate. Qed.

Lemma sem_del_source_api_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype returned restored pointer error Hprefix.
  unfold sem_del_source_api_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Hresult _]; discriminate.
Qed.

Lemma sem_del_source_api_schedule_protocol_isr : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 -> 0 < q_del_int_nesting before ->
  sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype Hint returned restored pointer error Hprefix.
  unfold sem_del_source_api_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), Htype, (proj2 (Z.ltb_lt _ _) Hint) in Hprefix.
  destruct Hprefix as [Hresult _]; discriminate.
Qed.

Lemma sem_del_source_api_schedule_protocol_no_request_option : forall environment critical sg caller mask pe eid opt before,
  0 <= opt <= 255 -> opt <> 1 ->
  sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hrange Hopt returned restored pointer error Hprefix.
  unfold sem_del_source_api_prefix_program in Hprefix.
  destruct (Z.eqb pe 0); [destruct Hprefix as [Hresult _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3);
    [|destruct Hprefix as [Hresult _]; discriminate].
  destruct (Z.ltb 0 (q_del_int_nesting before));
    [destruct Hprefix as [Hresult _]; discriminate|].
  destruct Hprefix as [active [saved [acquired [number [code [request [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]]].
  injection Hresult as Hnumber Hcode Hrequest Hcaller; subst number request next.
  unfold sem_delete_critical, event_delete_critical in Hstep.
  rewrite (unsigned_last_nbits_eq opt 8 ltac:(cbn; lia)) in Hstep.
  destruct Hstep as [node [Hnode Hstep]].
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp node.(waitList) acquired.(TskState)) 0));
      destruct Hstep as [Hresult _]; discriminate.
  - rewrite (proj2 (Z.eqb_neq _ _) Hopt) in Hstep; destruct Hstep as [Hresult _]; discriminate.
Qed.

Lemma sem_del_source_api_wrong_type_result : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_del_source_api_caller_result environment critical sg caller mask pe eid opt before pe 1 caller before.
Proof.
  intros; exists caller, before, false; split.
  - unfold sem_del_source_api_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) H), (proj2 (Z.eqb_neq _ _) H0); split; reflexivity.
  - split; reflexivity.
Qed.

Lemma sem_del_source_api_isr_result : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 -> 0 < q_del_int_nesting before ->
  sem_del_source_api_caller_result environment critical sg caller mask pe eid opt before pe 15 caller before.
Proof.
  intros; exists caller, before, false; split.
  - unfold sem_del_source_api_prefix_program.
    rewrite (proj2 (Z.eqb_neq _ _) H), H0, (proj2 (Z.ltb_lt _ _) H1); cbn; split; reflexivity.
  - split; reflexivity.
Qed.

Lemma sem_del_source_api_call_input_free : forall critical sg caller pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  before.(EventState).(inUsedEventStates) eid = None ->
  In eid before.(EventState).(unUsedEventStates) ->
  sem_del_source_api_call_input critical sg caller pe before eid observed.
Proof.
  intros critical sg caller pe before eid observed Hpe Haddr Hid Hnone Hfree.
  right; split; [exact Hpe|]; split; [exact Haddr|]; split; [exact Hid|].
  split; [right; auto|]. unfold event_slot_type_value; rewrite Hnone; discriminate.
Qed.

Lemma sem_del_source_api_call_input_isr : forall critical sg caller pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed -> 0 < q_del_int_nesting before ->
  sem_del_source_api_call_input critical sg caller pe before eid observed.
Proof.
  intros critical sg caller pe before eid observed Hpe Haddr Hid Hpublic Hint.
  right; split; [exact Hpe|]; split; [exact Haddr|]; split; [exact Hid|].
  split; [exact Hpublic|]; intros; lia.
Qed.

Lemma sem_del_source_api_prefix_protected : forall environment critical sg original active returned mask
  pe eid opt before acquired released restored saved pointer error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 ->
  q_del_int_nesting before <= 0 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  sem_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (error, schedule)) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  sem_del_source_api_prefix_program environment critical sg original mask pe eid opt before
    (((pointer, encode_os_err_code error), schedule), returned) restored.
Proof.
  intros; unfold sem_del_source_api_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0, (proj2 (Z.ltb_ge _ _) H1); cbn.
  exists active, saved, acquired, pointer, error, schedule, released, returned; auto.
Qed.

Lemma sem_del_source_api_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid opt before restored pointer error schedule X,
  sem_del_source_api_prefix_program environment critical sg original mask pe eid opt before
    (((pointer, error), schedule), returned) restored ->
  sem_del_source_api_safe environment critical sg original mask pe eid opt before X ->
  safeExec (fun state => state = restored)
    (sem_del_source_api_tail environment critical sg mask (((pointer, error), schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid opt before restored pointer error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (sem_del_source_api_prefix_program environment critical sg original mask pe eid opt)
    (sem_del_source_api_tail environment critical sg mask) (fun state => state = before)
    (((pointer, error), schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma sem_del_source_api_result_program : forall environment critical sg original mask pe eid opt before
  pointer error returned current,
  sem_del_source_api_caller_result environment critical sg original mask pe eid opt before
    pointer error returned current ->
  sem_del_source_api_program environment critical sg original mask pe eid opt before (pointer, error) current.
Proof.
  intros environment critical sg original mask pe eid opt before pointer error returned current
    [prefix_caller [restored [schedule [Hprefix Htail]]]].
  exists (((pointer, error), schedule), prefix_caller), restored; split; [exact Hprefix|].
  destruct schedule; cbn [sem_del_source_api_tail].
  - exists tt, current; split; [|split; reflexivity].
    exists returned, current; split; [exact Htail|split; reflexivity].
  - destruct Htail as [-> ->]; split; reflexivity.
Qed.

Lemma sem_del_source_api_safe_return : forall environment critical sg caller mask pe eid opt before current pointer error X,
  sem_del_source_api_program environment critical sg caller mask pe eid opt before (pointer, error) current ->
  sem_del_source_api_safe environment critical sg caller mask pe eid opt before X ->
  sem_del_source_api_return_safe current pointer error X.
Proof.
  intros environment critical sg caller mask pe eid opt before current pointer error X Hprogram Hsafe.
  eapply (highstependret_derive
    (sem_del_source_api_program environment critical sg caller mask pe eid opt)
    (fun state => state = before) (pointer, error) (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma sem_del_source_api_closed_return : forall environment critical saved_local sg original returned mask
  pe eid opt before current error_addr pointer error X,
  sem_del_source_api_caller_result environment critical sg original mask pe eid opt before
    pointer error returned current ->
  sem_del_source_api_safe environment critical sg original mask pe eid opt before X ->
  q_post_closed environment critical saved_local sg returned mask current **
    error_addr # UChar |-> error |--
  sem_del_source_api_post environment critical saved_local sg original mask pe eid opt before error_addr pointer X.
Proof.
  intros.
  pose proof (sem_del_source_api_result_program _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hprogram.
  pose proof (sem_del_source_api_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0) as Hsafe.
  unfold sem_del_source_api_post; Exists error returned current; entailer!.
Qed.

(** A prefix relates the actual current heap to the initial acquired heap.
    It does not assume that the C loop or any future call returns. *)
Definition sem_del_source_api_effect sg eid opt acquired (pointer error schedule : Z) released : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    sem_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (code, request)) released.

Definition sem_del_source_api_prefix_result environment critical sg caller mask pe eid opt before
  (pointer error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    sem_del_source_api_prefix_program environment critical sg caller mask pe eid opt before
      (((pointer, error), request), returned) current.

Definition sem_del_source_api_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 3 /\ q_del_int_nesting before <= 0 /\
    UCOS2_state_inv sg released /\ sem_del_source_api_effect sg eid opt acquired pointer error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition sem_del_source_api_restore_post environment critical saved_local sg caller mask pe eid opt before
  pointer error schedule : Assertion :=
  EX returned current,
    coq_prop (sem_del_source_api_prefix_result environment critical sg caller mask pe eid opt before
      pointer error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma sem_del_source_api_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule,
  sem_del_source_api_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
    before acquired released pointer error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold sem_del_source_api_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma sem_del_source_api_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 3 -> q_del_int_nesting before <= 0 ->
  UCOS2_state_inv sg released -> sem_del_source_api_effect sg eid opt acquired pointer error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  sem_del_source_api_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid opt before acquired released pointer error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hint Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : sem_del_source_api_prefix_result environment critical sg caller mask pe eid opt before
    pointer (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply sem_del_source_api_prefix_protected;
      [exact Hpe|exact Htype|exact Hint|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold sem_del_source_api_restore_post; Exists returned current; entailer!.
Qed.

Lemma sem_del_source_api_restore_schedule : forall environment critical saved_local sg caller mask pe eid opt before pointer error,
  sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before ->
  sem_del_source_api_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error 1 |--
  EX returned current,
    coq_prop (sem_del_source_api_prefix_result environment critical sg caller mask pe eid opt before
      pointer error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid opt before pointer error Hprotocol.
  unfold sem_del_source_api_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]; pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current pointer error Hprefix)).
  Exists returned current; entailer!.
Qed.

Definition sem_del_source_api_finish_context environment critical saved_local sg original mask pe eid opt before
  pointer error : Assertion :=
  EX returned current,
    coq_prop (sem_del_source_api_caller_result environment critical sg original mask pe eid opt before
      pointer error returned current) &&
    (q_post_closed environment critical saved_local sg returned mask current).

Definition sem_del_source_api_after_schedule_context environment critical saved_local sg original mask pe eid opt before
  waiting : Assertion :=
  sem_del_source_api_finish_context environment critical saved_local sg original mask pe eid opt before 0 0 ||
  (coq_prop (waiting <> 1) &&
    (sem_del_source_api_restore_post environment critical saved_local sg original mask pe eid opt before 0 0 waiting)).

Lemma sem_del_source_api_finish_return : forall environment critical saved_local sg original mask pe eid opt before
  pointer error error_addr X,
  sem_del_source_api_safe environment critical sg original mask pe eid opt before X ->
  sem_del_source_api_finish_context environment critical saved_local sg original mask pe eid opt before pointer error **
    error_addr # UChar |-> error |--
  sem_del_source_api_post environment critical saved_local sg original mask pe eid opt before error_addr pointer X.
Proof.
  intros; unfold sem_del_source_api_finish_context; Intros returned current.
  sep_apply_r_atomic (sem_del_source_api_closed_return environment critical saved_local sg original returned mask
    pe eid opt before current error_addr pointer error X H0 H); entailer!.
Qed.

Lemma sem_del_source_api_nonschedule_finish : forall environment critical saved_local sg caller mask pe eid opt before
  pointer error schedule,
  schedule <> 1 ->
  sem_del_source_api_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error schedule |--
  sem_del_source_api_finish_context environment critical saved_local sg caller mask pe eid opt before pointer error.
Proof.
  intros; unfold sem_del_source_api_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid]; destruct request; [contradiction|].
  unfold sem_del_source_api_finish_context; Exists returned current.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists returned, current, false; split; [exact Hprefix|split; reflexivity].
Qed.

Lemma sem_del_source_api_sched_finish : forall environment critical saved_local sg original returned mask
  pe eid opt before restored pointer error,
  sem_del_source_api_prefix_result environment critical sg original mask pe eid opt before pointer error 1 returned restored ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  sem_del_source_api_finish_context environment critical saved_local sg original mask pe eid opt before pointer error.
Proof.
  intros environment critical saved_local sg original returned mask pe eid opt before restored pointer error
    [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_del_sched_post_endpoint environment critical saved_local sg returned mask restored).
  Intros final current; unfold sem_del_source_api_finish_context; Exists final current.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists returned, restored, true; split; assumption.
Qed.


(** Keep the initial waiting observation throughout the broadcast. Del needs
    no processed-count log: the established sem_del_abort_prefix already
    relates every intermediate state to the same acquired state. *)
Definition sem_del_source_api_acquired_group_context environment critical saved_local sg caller active mask saved
  before acquired eid observed initial : Assertion :=
  coq_prop (sem_del_profile sg) &&
  sem_post_api_group_context environment critical saved_local sg caller active mask saved
    before acquired eid observed initial.

Lemma sem_del_source_api_save_group_split : forall environment critical saved_local sg caller mask saved
  before eid observed,
  sem_del_profile sg -> valid_event_id sg eid -> event_object_layout_prop sg eid ->
  sem_post_api_save_result environment critical saved_local sg caller mask saved before eid observed |--
  EX active acquired initial,
    sem_del_source_api_acquired_group_context environment critical saved_local sg caller active mask saved
      before acquired eid observed initial **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_del_group acquired initial.
Proof.
  intros environment critical saved_local sg caller mask saved before eid observed Hprofile Hid Hlayout.
  unfold sem_post_api_save_result; Intros active acquired initial.
  pose proof H as [Hsave [Hobserved [Hobservedtype [Hinitial [Hinitialtype Hg]]]]].
  rewrite q_post_masked_equiv.
  sep_apply_l_atomic (sem_post_api_group_cell_split sg acquired eid initial Hinitial).
  assert (Hpostprofile : sem_post_profile sg) by (exact (proj1 Hprofile)).
  Exists active acquired initial.
  unfold sem_del_source_api_acquired_group_context, sem_post_api_group_context; entailer!.
Qed.

Definition sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
  eid observed initial state node waiting : Prop :=
  sem_post_api_acquire_facts environment critical sg caller active mask saved before acquired eid observed initial /\
  sem_del_profile sg /\ valid_event_id sg eid /\ event_object_layout_prop sg eid /\
  q_del_int_nesting before <= 0 /\ sem_del_waiting acquired initial waiting /\
  sem_del_loop_facts sg eid acquired state node.

Definition sem_del_source_api_loop_group_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node waiting : Assertion :=
  coq_prop (sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node waiting) &&
  (sem_post_group_frame sg state eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition sem_del_source_api_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node waiting tid old : Assertion :=
  coq_prop (sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node waiting /\ sem_del_group state node <> 0 /\
    event_task_rdy_entry sg state.(TskState) eid node tid old) &&
  (sem_post_wake_frame sg state eid tid **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition sem_del_source_api_recycle_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node waiting option : Assertion :=
  coq_prop (sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node waiting /\ sem_del_group state node = 0 /\
    ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1)) &&
  (sem_del_recycle_frame sg state eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Lemma sem_del_source_api_waiting_observation : forall acquired initial waiting,
  waiting = q_del_waiting acquired initial -> sem_del_waiting acquired initial waiting.
Proof.
  intros acquired initial waiting ->; unfold q_del_waiting.
  destruct (Z.eqb (q_post_group acquired initial) 0) eqn:Hgroup.
  - left; split; [apply Z.eqb_eq; exact Hgroup|reflexivity].
  - right; split; [apply Z.eqb_neq; exact Hgroup|reflexivity].
Qed.

Lemma sem_del_source_api_acquired_loop_start : forall environment critical saved_local sg caller active mask saved
  before acquired eid observed initial waiting,
  q_del_int_nesting before <= 0 -> waiting = q_del_waiting acquired initial ->
  sem_del_source_api_acquired_group_context environment critical saved_local sg caller active mask saved
    before acquired eid observed initial |--
  sem_del_source_api_loop_group_context environment critical saved_local sg caller active mask saved
    before acquired eid observed initial acquired initial waiting.
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed initial waiting Hint Hwaiting.
  unfold sem_del_source_api_acquired_group_context, sem_post_api_group_context; Intros.
  match goal with H : sem_post_api_acquire_facts _ _ _ _ _ _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct H as [Hacquire [Hprofile [Hid Hlayout]]] end.
  pose proof Hacquire as [Hsave [Hobserved [Hobservedtype [Hinitial [Hinitialtype Hg]]]]].
  pose proof (sem_del_source_api_waiting_observation acquired initial waiting Hwaiting) as Hwait.
  assert (Hloop : sem_del_loop_facts sg eid acquired acquired initial).
  { split; [constructor|]; split; [exact Hinitial|]; split; [exact Hinitialtype|exact (proj1 Hsave)]. }
  unfold sem_del_source_api_loop_group_context, sem_del_source_api_loop_facts; entailer!.
Qed.

Lemma sem_del_source_api_event_layout : forall sg eid,
  event_object_layout_prop sg eid ->
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) = event_addr sg eid + OSEventType_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) = event_addr sg eid + OSEventPtr_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) = event_addr sg eid + OSEventCnt_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) = event_addr sg eid + OSEventGrp_off.
Proof. intros sg eid [[Htype [Hptr Hcnt]] [Hgrp Htbl]]; auto. Qed.

(** Both the NO_PEND-with-waiters and invalid-option paths restore a
    locally unchanged acquired state, but their actual return state is
    subsequently supplied by Restore, never fixed to that state. *)
Lemma sem_del_source_api_unchanged_restore : forall environment critical saved_local
  sg caller active mask saved pe before acquired eid observed initial waiting option pointer error,
  pe = event_addr sg eid -> pe <> 0 -> 0 <= option <= 255 ->
  sem_del_critical_result sg eid option acquired pointer error 0 acquired ->
  sem_del_source_api_loop_group_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial acquired initial waiting **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_del_group acquired initial |--
  sem_del_source_api_restore_pre environment critical saved_local sg caller active mask saved pe eid option before acquired
    acquired pointer error 0.
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed initial waiting
    option pointer error Hpe Hnonzero Hrange Hcritical.
  unfold sem_del_source_api_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hid [Hlayout [Hint [Hwaiting [Hprefix [Hnode [Htype Hvalid]]]]]]]]].
  assert (Heffect : sem_del_source_api_effect sg eid option acquired pointer error 0 acquired).
  { unfold sem_del_source_api_effect.
    rewrite (unsigned_last_nbits_eq option 8 ltac:(cbn; lia)); exact Hcritical. }
  pose proof (sem_post_api_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  unfold sem_del_group.
  sep_apply_l_atomic (sem_post_api_group_cell_merge sg acquired eid initial Hvalid Hnode).
  unfold sem_del_source_api_restore_pre; rewrite q_post_masked_equiv.
  pose proof (proj1 Hacquire) as Hsave; entailer!.
Qed.

(** Field split/merge below call the old protected SemDel proofs. There is
    no new residual model, queue-storage ownership, or application payload. *)
Lemma sem_del_source_api_group_split_recycle : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial state node waiting option,
  sem_del_group state node = 0 ->
  ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1) ->
  sem_del_source_api_loop_group_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node waiting **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_del_group state node |--
  sem_del_source_api_recycle_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node waiting option **
    (event_addr sg eid + OSEventType_off) # UChar |-> 3 **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg node **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value node **
    sg.(g_OSEventFreeList) # Ptr |-> sem_del_free_head sg state.
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed initial state node
    waiting option Hzero Hoption.
  unfold sem_del_source_api_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hid [Hlayout [Hint [Hwaiting [Hprefix [Hnode [Htype Hvalid]]]]]]]]].
  unfold sem_del_group.
  sep_apply_l_atomic (sem_post_api_group_cell_merge sg state eid node Hvalid Hnode).
  sep_apply_l_atomic (sem_del_recycle_split sg state eid node Hnode).
  cbn [event_cell event_field_offset]. rewrite Htype; cbn [encode_event_type].
  unfold sem_del_source_api_recycle_context, OSEventType_off, OSEventPtr_off, OSEventCnt_off; entailer!.
Qed.

Lemma sem_del_source_api_recycle_effect : forall environment critical sg caller active mask saved before acquired
  eid observed initial state node waiting option,
  sem_del_source_api_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node waiting ->
  sem_del_group state node = 0 ->
  ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1) ->
  sem_del_source_api_effect sg eid option acquired 0 0 waiting (event_delete_recycle_state sg state eid node).
Proof.
  intros environment critical sg caller active mask saved before acquired eid observed initial state node waiting option
    [Hacquire [Hprofile [Hid [Hlayout [Hint [Hwaiting Hloop]]]]]] Hzero Hoption.
  pose proof Hacquire as [Hsave [Hobserved [Hobservedtype [Hinitial [Hinitialtype Hg]]]]].
  destruct Hoption as [[-> [-> ->]]| ->].
  - change (sem_del_critical_result sg eid 0 acquired 0 0 0
      (event_delete_recycle_state sg acquired eid node)).
    apply sem_del_critical_no_pend_empty; [exact (proj1 (proj2 Hloop))|exact Hzero].
  - change (sem_del_critical_result sg eid 1 acquired 0 0 waiting
      (event_delete_recycle_state sg state eid node)).
    eapply sem_del_critical_always_recycled; eassumption.
Qed.

Lemma sem_del_source_api_recycle_restore : forall environment critical saved_local
  sg caller active mask saved pe before acquired eid observed initial state node waiting option,
  pe = event_addr sg eid -> pe <> 0 ->
  sem_del_source_api_recycle_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node waiting option **
    (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> sem_del_free_head sg state **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> pe |--
  sem_del_source_api_restore_pre environment critical saved_local sg caller active mask saved pe eid option before acquired
    (event_delete_recycle_state sg state eid node) 0 0 waiting.
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed initial state node
    waiting option Hpe Hnonzero.
  unfold sem_del_source_api_recycle_context; Intros.
  destruct H as [Hfacts [Hzero Hoption]].
  pose proof Hfacts as [Hacquire [Hprofile [Hid [Hlayout [Hint [Hwaiting [Hprefix [Hnode [Htype Hvalid]]]]]]]]].
  pose proof (sem_del_source_api_recycle_effect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hfacts Hzero Hoption) as Heffect.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [Hfields [_ [_ Hentries]]]]]] _]]]].
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) node.(waitList)
    (proj1 (Hentries eid node Hnode))) Hzero) as Hempty.
  assert (Hreleased : UCOS2_state_inv sg (event_delete_recycle_state sg state eid node)).
  { unfold event_delete_recycle_state; eapply UCOS2_event_recycle_preserves_validity;
      [exact Hvalid|exact Hnode|rewrite Htype; discriminate|exact Hempty]. }
  pose proof (sem_post_api_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  assert (Hmerge : (event_addr sg eid + OSEventType_off) # UChar |-> 0 **
    (event_addr sg eid + OSEventPtr_off) # Ptr |-> sem_del_free_head sg state **
    (event_addr sg eid + OSEventCnt_off) # UShort |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid ** sem_del_recycle_frame sg state eid node |--
    UCOS2_inv sg (event_delete_recycle_state sg state eid node)).
  { exact (sem_del_recycle_merge sg state eid node Hvalid Hnode Htype Hzero). }
  rewrite Hpe; sep_apply_l_atomic Hmerge.
  sep_apply_l_atomic (q_post_mask_frame_event_update environment critical saved_local sg active saved acquired
    state (event_delete_recycle_state sg state eid node) eq_refl).
  unfold sem_del_source_api_restore_pre; rewrite q_post_masked_equiv.
  pose proof (proj1 Hacquire) as Hsave; entailer!.
Qed.


(** Del composes the PendAbort-owned mask-frame transport without
    reproducing or changing its proof. *)
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_abort_source_api_spec.

Lemma sem_del_source_api_loop_split_wake : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial state node waiting,
  sem_del_group state node <> 0 ->
  sem_del_source_api_loop_group_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node waiting **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_del_group state node |--
  EX tid old,
    sem_del_source_api_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
      eid observed initial state node waiting tid old **
    event_task_rdy_pre sg state.(TskState) eid node tid old 1 2
      (q_post_sched_group state) (q_post_sched_rows state).
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed initial state node
    waiting Hgroup.
  unfold sem_del_source_api_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Hid [Hlayout [Hint [Hwaiting [Hprefix [Hnode [Htype Hvalid]]]]]]]]].
  unfold sem_del_group.
  sep_apply_l_atomic (sem_post_api_group_cell_merge sg state eid node Hvalid Hnode).
  sep_apply_l_atomic (sem_del_wake_split_full sg state eid node Hvalid Hnode Htype Hgroup Hlayout).
  Intros tid old; Exists tid old; unfold sem_del_source_api_loop_wake_context; entailer!.
Qed.

Lemma sem_del_source_api_loop_merge_wake : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial state node waiting tid old priority,
  sem_del_source_api_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node waiting tid old **
    event_task_rdy_post sg state.(TskState) eid node tid old 0 1 2
      (q_post_sched_group state) (q_post_sched_rows state) priority |--
  EX next next_node,
    sem_del_source_api_loop_group_context environment critical saved_local sg caller active mask saved before acquired
      eid observed initial next next_node waiting **
    (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_del_group next next_node.
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed initial state node
    waiting tid old priority.
  unfold sem_del_source_api_loop_wake_context; Intros.
  destruct H as [Hfacts [Hgroup Hentry]].
  pose proof Hfacts as [Hacquire [Hprofile [Hid [Hlayout [Hint [Hwaiting Hloop]]]]]].
  pose proof Hloop as [Hprefix [Hnode [Htype Hvalid]]].
  pose proof Hentry as [Hsg [Hentrylayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  destruct node.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg state eid node tid tail PendSem 0 PendAbort
    Hvalid Hnode ltac:(rewrite Htype; reflexivity) Hlist)
    as [found [Hfound [Hcall [Hvalid_after Hnode_after]]]].
  assert (found = old) by congruence; subst found.
  unfold q_post_sched_group, q_post_sched_rows.
  sep_apply_l_atomic (sem_del_wake_merge_full sg state eid node tid old priority Hvalid Hnode Htype Hentry).
  Intros next.
  match goal with H : sem_del_wake_result sg eid state next priority |- _ => rename H into Hwake end.
  pose proof Hwake as Hnext; unfold sem_del_wake_result in Hnext.
  rewrite Hcall in Hnext; injection Hnext as Hpriority Hnext; subst next.
  sep_apply_l_atomic (sem_pend_abort_source_mask_frame_wake_update
    environment critical saved_local sg active saved acquired state eid node tid old Hold).
  destruct (sem_del_wake_loop_facts sg eid acquired state node priority
    (event_wake_state sg state eid node tid old PendSem 0 PendAbort) Hloop Hgroup Hwake)
    as [next_node Hnext_loop].
  pose proof Hnext_loop as [Hnext_prefix [Hnext_node [Hnext_type Hnext_valid]]].
  sep_apply_l_atomic (sem_post_api_group_cell_split sg
    (event_wake_state sg state eid node tid old PendSem 0 PendAbort) eid next_node Hnext_node).
  Exists (event_wake_state sg state eid node tid old PendSem 0 PendAbort) next_node.
  unfold sem_del_source_api_loop_group_context, sem_del_source_api_loop_facts; entailer!.
Qed.

(** Source-preserved Scheduler admission reuses the five PendAbort
    mask-frame/broadcast/source-preservation interfaces. *)
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_abort_source_api_spec.

Lemma sem_del_source_api_critical_preserves : forall (P : UCOS2_Verify_State -> Prop) sg eid,
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node ->
    node.(eventType) = OS_EVENT_TYPE_SEM ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendSem 0 PendAbort)) ->
  (forall state node, P state -> P (event_delete_recycle_state sg state eid node)) ->
  forall before node opt result after,
    UCOS2_state_inv sg before -> q_post_lookup before eid node -> node.(eventType) = OS_EVENT_TYPE_SEM ->
    sem_delete_critical sg eid opt before result after -> P before -> P after.
Proof.
  intros P sg eid Hwake Hrecycle before node opt result after Hvalid Hnode Htype Hcritical HP.
  unfold sem_delete_critical, event_delete_critical in Hcritical.
  destruct Hcritical as [other [Hother Hstep]].
  assert (other = node) by congruence; subst other.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp node.(waitList) before.(TskState)) 0)).
    + destruct Hstep as [_ ->]; exact HP.
    + destruct Hstep as [_ ->]; apply Hrecycle; exact HP.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [ready [last [Hloop [_ [_ ->]]]]]].
      apply Hrecycle; eapply sem_pend_abort_source_broadcast_preserves; eassumption.
    + destruct Hstep as [_ ->]; exact HP.
Qed.


Lemma sem_del_source_api_prefix_wake_decompose : forall environment critical sg original mask pe eid opt before
  observed returned restored pointer error,
  UCOS2_state_inv sg before -> sem_del_source_api_call_input critical sg original pe before eid observed ->
  sem_del_source_api_prefix_program environment critical sg original mask pe eid opt before
    (((pointer, error), true), returned) restored ->
  exists active saved acquired node released code,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    sem_post_api_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    sem_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (code, true)) released /\
    UCOS2_state_inv sg released /\
    task_resume_restore_program environment critical sg active released returned restored.
Proof.
  intros environment critical sg original mask pe eid opt before observed returned restored pointer error
    Hvalid Hinput Hprefix.
  unfold sem_del_source_api_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct (Z.ltb 0 (q_del_int_nesting before)) eqn:Hint;
    [destruct Hprefix as [Heq _]; discriminate|].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype; apply Z.ltb_ge in Hint.
  destruct Hprefix as [active [saved [acquired [number [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]]].
  injection Hresult as Hnumber Hcode Hschedule Hcaller; subst number schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  pose proof (sem_del_source_api_call_input_acquire _ _ _ _ _ _ _ Hpe Htype Hint Hinput) as Hacquire_input.
  destruct (sem_post_api_acquire_identity environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hacquire_input Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hsem Hg]]]]].
  pose proof (event_delete_critical_preserves_validity sg acquired eid node PendSem
    (unsigned_last_nbits opt 8) (pointer, (code, true)) released
    (proj1 Hfacts) Hnode ltac:(rewrite Hsem; reflexivity)
    ltac:(rewrite Hsem; discriminate) Hstep) as Hreleased.
  exists active, saved, acquired, node, released, code.
  split; [exact Hfacts|]; split; [exact Hacquire|]; auto.
Qed.

Lemma sem_del_source_api_schedule_protocol_task : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  sem_del_source_api_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  sem_del_source_api_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored pointer error Hprefix.
  destruct (sem_del_source_api_prefix_wake_decompose environment critical sg (ResumeTaskCaller call)
    mask pe eid opt before observed returned restored pointer error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hsem Hgeneration]]]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  assert (Hreleased_source : task_resume_caller_source sg (ResumeTaskCaller active) released).
  { eapply (sem_del_source_api_critical_preserves
      (task_resume_caller_source sg (ResumeTaskCaller active)) sg eid).
    - intros; eapply sem_pend_abort_source_wake_preserves_task_source; eassumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hsem.
    - exact Hstep.
    - exact Hactive. }
  destruct (q_post_task_restore_source environment critical sg active returned released restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { eapply (sem_del_source_api_critical_preserves
      (fun state => state.(SchedState).(readyList) <> []) sg eid).
    - intros; apply sem_pend_abort_source_wake_preserves_ready_nonempty; assumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hsem.
    - exact Hstep.
    - exact Hacquired_ready. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma sem_del_source_api_schedule_protocol_task_idle : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  sem_del_source_api_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  sem_del_source_api_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients Hreturns Hsource Hidle.
  eapply sem_del_source_api_schedule_protocol_task;
    [exact Hvalid|exact Hinput|exact Hclients|exact Hreturns|exact Hsource|].
  eapply sched_idle_ready_nonempty;
    [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.

Lemma sem_del_source_api_schedule_protocol_disabled : forall environment critical sg view mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  sem_del_source_api_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  sem_del_source_api_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid opt before.
Proof.
  intros environment critical sg view mask pe eid opt before observed Hvalid Hinput Hclients Hsource
    returned restored pointer error Hprefix.
  destruct (sem_del_source_api_prefix_wake_decompose environment critical sg (ResumeGenericCaller view)
    mask pe eid opt before observed returned restored pointer error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hsem Hgeneration]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  assert (Hreleased_source : sched_disabled_entry_source view released).
  { eapply (sem_del_source_api_critical_preserves (sched_disabled_entry_source view) sg eid).
    - intros; apply sem_pend_abort_source_wake_preserves_disabled_source; assumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hsem.
    - exact Hstep.
    - exact Hacquired_source. }
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    released restored Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma sem_del_source_api_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> sem_del_source_api_call_input critical sg caller pe before eid observed ->
  (forall active saved acquired node,
    q_post_save_facts environment critical sg caller active mask saved before acquired ->
    sem_post_api_acquire_facts environment critical sg caller active mask saved before acquired eid observed node ->
    node.(waitList) = []) ->
  sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty
    returned restored pointer error Hprefix.
  destruct (sem_del_source_api_prefix_wake_decompose environment critical sg caller mask pe eid opt before
    observed returned restored pointer error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hsem Hgeneration]]]]].
  pose proof (Hempty active saved acquired node Hsave Hacquire) as Hnil.
  pose proof (proj1 (event_delete_critical_requests_schedule_iff sg acquired eid node PendSem
    (unsigned_last_nbits opt 8) (pointer, (code, true)) released Hnode Hstep) eq_refl) as [_ Hnonempty].
  rewrite Hnil in Hnonempty; exfalso; apply Hnonempty; reflexivity.
Qed.

(** Existing SemPost source-preserved no-waiters fact also covers real
    no-wake/Boot callers; a Boot tag alone is deliberately insufficient. *)
Lemma sem_del_source_api_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> sem_del_source_api_call_input critical sg caller pe before eid observed ->
  sem_post_api_no_waiter_clients critical sg (task_resume_view caller).(os_execution_invocation) eid ->
  sem_post_api_no_waiters sg eid before ->
  sem_del_source_api_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hclients Hnone.
  eapply sem_del_source_api_schedule_protocol_acquired_no_waiters; [exact Hvalid|exact Hinput|].
  intros active saved acquired node Hsave Hacquire.
  pose proof (sem_post_api_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) eid before acquired
    Hclients (proj1 (proj2 Hsave)) Hvalid Hnone) as Hempty.
  pose proof Hacquire as [_ [_ [_ [Hnode [Htype Hg]]]]].
  pose proof (proj1 Hsave) as [_ [_ [_ [[_ [_ [_ [Hfields [_ [_ Hentries]]]]]] _]]]].
  apply (proj1 (encode_event_wait_grp_zero_iff_empty sg acquired.(TskState) node.(waitList)
    (proj1 (Hentries eid node Hnode)))); exact (Hempty node Hnode).
Qed.

