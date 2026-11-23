Require Export Ucos2Verify.VC.code.mbox.spec.mbox_delete_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_pend_abort_spec.
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

(** The shared mailbox profile already binds all ECB field addresses.
    No Queue payload or pointed-to application-message ownership is required. *)
Definition mbox_del_profile := mbox_post_profile.

(** Type is checked before ISR. Lifetime and the observed live node are
    required only when this invocation actually proceeds to Save. *)
Definition mbox_del_call_input critical sg caller pe before eid observed : Prop :=
  pe = 0 \/
  (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
   mbox_accept_public_slot before eid /\
   (event_slot_type_value before.(EventState) eid = 1 ->
      q_del_int_nesting before <= 0 ->
      mutex_query_handle_protocol critical sg
        (task_resume_view caller).(os_execution_invocation) eid /\
      q_post_lookup before eid observed)).

Lemma mbox_del_call_input_acquire : forall critical sg caller pe before eid observed,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  q_del_int_nesting before <= 0 ->
  mbox_del_call_input critical sg caller pe before eid observed ->
  mbox_pend_abort_call_input critical sg caller pe before eid observed.
Proof.
  intros critical sg caller pe before eid observed Hpe Htype Hint [Hzero|Hinput];
    [contradiction|].
  destruct Hinput as [Hnonzero [Haddr [Hid [Hpublic Hgo]]]].
  destruct (Hgo Htype Hint) as [Hprotocol Hnode].
  split.
  - right; split; [exact Hnonzero|].
    split; [exact Haddr|].
    split; [exact Hid|].
    split; [exact Hpublic|intros; exact Hprotocol].
  - intros; exact Hnode.
Qed.

Lemma mbox_del_type_split : forall environment critical saved_local sg caller mask before pe eid observed,
  UCOS2_state_inv sg before -> pe <> 0 ->
  mbox_del_call_input critical sg caller pe before eid observed ->
  q_post_closed environment critical saved_local sg caller mask before |--
  (event_addr sg eid + OSEventType_off) # UChar |-> event_slot_type_value before.(EventState) eid **
  mbox_post_type_context environment saved_local sg caller mask before eid.
Proof.
  intros environment critical saved_local sg caller mask before pe eid observed Hvalid Hpe Hinput.
  destruct Hinput as [Hzero|[_ [Haddr [Hid [Hpublic Hprotocol]]]]]; [contradiction|].
  rewrite (q_post_closed_equiv environment critical saved_local sg caller mask before Hvalid).
  sep_apply_l_atomic (mbox_accept_type_split_full sg before eid Hpublic).
  unfold mbox_post_type_context; entailer!.
Qed.

Definition mbox_del_prefix_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (((Z * Z) * bool) * TaskResumeCaller) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = (((pe, 4), false), caller) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 1 then
      if Z.ltb 0 (q_del_int_nesting before) then
        result = (((pe, 15), false), caller) /\ restored = before
      else exists active saved acquired pointer error schedule released returned,
        task_resume_save_program environment critical sg caller mask before
          (active, saved) acquired /\
        mbox_delete_critical sg eid (unsigned_last_nbits opt 8) acquired
          (pointer, (error, schedule)) released /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = (((pointer, encode_os_err_code error), schedule), returned)
    else result = (((pe, 1), false), caller) /\ restored = before.

Definition mbox_del_tail environment critical sg mask
  (result : ((Z * Z) * bool) * TaskResumeCaller)
  : program UCOS2_Verify_State (Z * Z) :=
  if snd (fst result) then
    bind (task_resume_schedule_call_program environment critical sg (snd result) mask)
      (fun _ => StateRelMonad.ret (fst (fst result)))
  else StateRelMonad.ret (fst (fst result)).

Definition mbox_del_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (Z * Z) :=
  bind (mbox_del_prefix_program environment critical sg caller mask pe eid opt)
    (mbox_del_tail environment critical sg mask).

Definition mbox_del_safe environment critical sg caller mask pe eid opt before
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (mbox_del_program environment critical sg caller mask pe eid opt) X.

Definition mbox_del_return_safe current pointer error
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret (pointer, error)) X.

Definition mbox_del_caller_result environment critical sg original mask pe eid opt before
  pointer error returned current : Prop :=
  exists prefix_caller restored schedule,
    mbox_del_prefix_program environment critical sg original mask pe eid opt before
      (((pointer, error), schedule), prefix_caller) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition mbox_del_post environment critical saved_local sg original mask pe eid opt before
  error_addr pointer (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error returned current,
    coq_prop (mbox_del_caller_result environment critical sg original mask pe eid opt before
      pointer error returned current /\ mbox_del_return_safe current pointer error X) &&
    (q_post_closed environment critical saved_local sg returned mask current **
      error_addr # UChar |-> error).

Definition mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before : Prop :=
  forall returned restored pointer error,
    mbox_del_prefix_program environment critical sg caller mask pe eid opt before
      (((pointer, error), true), returned) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Lemma mbox_del_prefix_protected : forall environment critical sg original active returned mask
  pe eid opt before acquired released restored saved pointer error schedule,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 1 ->
  q_del_int_nesting before <= 0 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  mbox_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (error, schedule)) released ->
  task_resume_restore_program environment critical sg active released returned restored ->
  mbox_del_prefix_program environment critical sg original mask pe eid opt before
    (((pointer, encode_os_err_code error), schedule), returned) restored.
Proof.
  intros; unfold mbox_del_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0, (proj2 (Z.ltb_ge _ _) H1); cbn.
  exists active, saved, acquired, pointer, error, schedule, released, returned; auto.
Qed.

Lemma mbox_del_prefix_safe_continuation : forall environment critical sg original returned mask
  pe eid opt before restored pointer error schedule X,
  mbox_del_prefix_program environment critical sg original mask pe eid opt before
    (((pointer, error), schedule), returned) restored ->
  mbox_del_safe environment critical sg original mask pe eid opt before X ->
  safeExec (fun state => state = restored)
    (mbox_del_tail environment critical sg mask (((pointer, error), schedule), returned)) X.
Proof.
  intros environment critical sg original returned mask pe eid opt before restored pointer error schedule X
    Hprefix Hsafe.
  eapply (highstepbind_derive
    (mbox_del_prefix_program environment critical sg original mask pe eid opt)
    (mbox_del_tail environment critical sg mask) (fun state => state = before)
    (((pointer, error), schedule), returned) (fun state => state = restored)).
  - intros state ->; exists restored; split; [exact Hprefix|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_del_result_program : forall environment critical sg original mask pe eid opt before
  pointer error returned current,
  mbox_del_caller_result environment critical sg original mask pe eid opt before
    pointer error returned current ->
  mbox_del_program environment critical sg original mask pe eid opt before (pointer, error) current.
Proof.
  intros environment critical sg original mask pe eid opt before pointer error returned current
    [prefix_caller [restored [schedule [Hprefix Htail]]]].
  exists (((pointer, error), schedule), prefix_caller), restored; split; [exact Hprefix|].
  destruct schedule; cbn [mbox_del_tail].
  - exists tt, current; split; [|split; reflexivity].
    exists returned, current; split; [exact Htail|split; reflexivity].
  - destruct Htail as [-> ->]; split; reflexivity.
Qed.

Lemma mbox_del_safe_return : forall environment critical sg caller mask pe eid opt before current pointer error X,
  mbox_del_program environment critical sg caller mask pe eid opt before (pointer, error) current ->
  mbox_del_safe environment critical sg caller mask pe eid opt before X ->
  mbox_del_return_safe current pointer error X.
Proof.
  intros environment critical sg caller mask pe eid opt before current pointer error X Hprogram Hsafe.
  eapply (highstependret_derive
    (mbox_del_program environment critical sg caller mask pe eid opt)
    (fun state => state = before) (pointer, error) (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma mbox_del_closed_return : forall environment critical saved_local sg original returned mask
  pe eid opt before current error_addr pointer error X,
  mbox_del_caller_result environment critical sg original mask pe eid opt before
    pointer error returned current ->
  mbox_del_safe environment critical sg original mask pe eid opt before X ->
  q_post_closed environment critical saved_local sg returned mask current **
    error_addr # UChar |-> error |--
  mbox_del_post environment critical saved_local sg original mask pe eid opt before error_addr pointer X.
Proof.
  intros.
  pose proof (mbox_del_result_program _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hprogram.
  pose proof (mbox_del_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0) as Hsafe.
  unfold mbox_del_post; Exists error returned current; entailer!.
Qed.

(** A prefix relates the actual current heap to the initial acquired heap.
    It does not assume that the C loop or any future call returns. *)
Definition mbox_del_effect sg eid opt acquired (pointer error schedule : Z) released : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    mbox_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (code, request)) released.

Definition mbox_del_prefix_result environment critical sg caller mask pe eid opt before
  (pointer error schedule : Z) returned current : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    mbox_del_prefix_program environment critical sg caller mask pe eid opt before
      (((pointer, error), request), returned) current.

Definition mbox_del_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 1 /\ q_del_int_nesting before <= 0 /\
    UCOS2_state_inv sg released /\ mbox_del_effect sg eid opt acquired pointer error schedule released) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition mbox_del_restore_post environment critical saved_local sg caller mask pe eid opt before
  pointer error schedule : Assertion :=
  EX returned current,
    coq_prop (mbox_del_prefix_result environment critical sg caller mask pe eid opt before
      pointer error schedule returned current /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma mbox_del_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule,
  mbox_del_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
    before acquired released pointer error schedule |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold mbox_del_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma mbox_del_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 1 -> q_del_int_nesting before <= 0 ->
  UCOS2_state_inv sg released -> mbox_del_effect sg eid opt acquired pointer error schedule released ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  mbox_del_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error schedule.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid opt before acquired released pointer error schedule
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hint Hvalid [code [request [-> [-> Hstep]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : mbox_del_prefix_result environment critical sg caller mask pe eid opt before
    pointer (encode_os_err_code code) (if request then 1 else 0) returned current).
  { exists request; split; [reflexivity|]. eapply mbox_del_prefix_protected;
      [exact Hpe|exact Htype|exact Hint|exact Hsave|exact Hstep|exact (proj1 H)]. }
  unfold mbox_del_restore_post; Exists returned current; entailer!.
Qed.

Lemma mbox_del_restore_schedule : forall environment critical saved_local sg caller mask pe eid opt before pointer error,
  mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before ->
  mbox_del_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error 1 |--
  EX returned current,
    coq_prop (mbox_del_prefix_result environment critical sg caller mask pe eid opt before
      pointer error 1 returned current) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid opt before pointer error Hprotocol.
  unfold mbox_del_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]; pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current pointer error Hprefix)).
  Exists returned current; entailer!.
Qed.

Definition mbox_del_finish_context environment critical saved_local sg original mask pe eid opt before
  pointer error : Assertion :=
  EX returned current,
    coq_prop (mbox_del_caller_result environment critical sg original mask pe eid opt before
      pointer error returned current) &&
    (q_post_closed environment critical saved_local sg returned mask current).

Definition mbox_del_after_schedule_context environment critical saved_local sg original mask pe eid opt before
  waiting : Assertion :=
  mbox_del_finish_context environment critical saved_local sg original mask pe eid opt before 0 0 ||
  (coq_prop (waiting <> 1) &&
    (mbox_del_restore_post environment critical saved_local sg original mask pe eid opt before 0 0 waiting)).

Lemma mbox_del_finish_return : forall environment critical saved_local sg original mask pe eid opt before
  pointer error error_addr X,
  mbox_del_safe environment critical sg original mask pe eid opt before X ->
  mbox_del_finish_context environment critical saved_local sg original mask pe eid opt before pointer error **
    error_addr # UChar |-> error |--
  mbox_del_post environment critical saved_local sg original mask pe eid opt before error_addr pointer X.
Proof.
  intros; unfold mbox_del_finish_context; Intros returned current.
  sep_apply_r_atomic (mbox_del_closed_return environment critical saved_local sg original returned mask
    pe eid opt before current error_addr pointer error X H0 H); entailer!.
Qed.

Lemma mbox_del_nonschedule_finish : forall environment critical saved_local sg caller mask pe eid opt before
  pointer error schedule,
  schedule <> 1 ->
  mbox_del_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error schedule |--
  mbox_del_finish_context environment critical saved_local sg caller mask pe eid opt before pointer error.
Proof.
  intros; unfold mbox_del_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid]; destruct request; [contradiction|].
  unfold mbox_del_finish_context; Exists returned current.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists returned, current, false; split; [exact Hprefix|split; reflexivity].
Qed.

Lemma mbox_del_sched_finish : forall environment critical saved_local sg original returned mask
  pe eid opt before restored pointer error,
  mbox_del_prefix_result environment critical sg original mask pe eid opt before pointer error 1 returned restored ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned |--
  mbox_del_finish_context environment critical saved_local sg original mask pe eid opt before pointer error.
Proof.
  intros environment critical saved_local sg original returned mask pe eid opt before restored pointer error
    [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_del_sched_post_endpoint environment critical saved_local sg returned mask restored).
  Intros final current; unfold mbox_del_finish_context; Exists final current.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists returned, restored, true; split; assumption.
Qed.

Definition mbox_del_loop_facts environment critical sg caller active mask saved before acquired
  eid observed initial state node processed waiting : Prop :=
  mbox_pend_abort_acquire_facts environment critical sg caller active mask saved before acquired eid observed initial /\
  mbox_del_profile sg /\ valid_event_id sg eid /\ q_del_int_nesting before <= 0 /\
  waiting = q_del_waiting acquired initial /\
  UCOS2_state_inv sg state /\ q_post_lookup state eid node /\ node.(eventType) = OS_EVENT_TYPE_MBOX /\
  mbox_pend_abort_progress sg eid acquired state processed.

Definition mbox_del_loop_group_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting : Assertion :=
  coq_prop (mbox_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting) &&
  (q_post_group_frame sg state eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition mbox_del_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting tid old : Assertion :=
  coq_prop (mbox_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting /\ q_post_group state node <> 0 /\
    event_task_rdy_entry sg state.(TskState) eid node tid old) &&
  (q_post_wake_frame sg state eid tid **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).


(** The residual retains all nonwritten ECB bytes at the current post-wake
    image. Queue storage is merely framed; Mailbox has no Queue payload. *)
Definition mbox_del_recycle_frame sg state eid node : Assertion :=
  store_map_missing_i (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) eid **
  q_del_event_residual sg state eid node ** event_free_storage_rep sg state.(EventState) **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Definition mbox_del_recycle_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting option : Assertion :=
  coq_prop (mbox_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting /\
    node.(queueFields) = None /\ node.(waitList) = [] /\
    ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1)) &&
  (mbox_del_recycle_frame sg state eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Lemma mbox_del_empty_mailbox_fields : forall sg state eid node,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> q_post_group state node = 0 ->
  node.(queueFields) = None /\ node.(waitList) = [].
Proof.
  intros sg state eid node Hvalid Hnode Htype Hzero.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [Hfields [_ [_ Hentries]]]]]] _]]]].
  split.
  - apply non_queue_event_has_no_queue_fields;
      [exact (Hfields eid node Hnode)|rewrite Htype; discriminate].
  - apply (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) node.(waitList)
      (proj1 (Hentries eid node Hnode)))); exact Hzero.
Qed.

Lemma mbox_del_event_layout : forall sg eid,
  mbox_del_profile sg -> valid_event_id sg eid ->
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) = event_addr sg eid + OSEventType_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) = event_addr sg eid + OSEventPtr_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) = event_addr sg eid + OSEventCnt_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) = event_addr sg eid + OSEventGrp_off.
Proof.
  intros sg eid [_ Hlayout] Heid.
  destruct (Hlayout eid Heid) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]]; auto.
Qed.

Lemma mbox_del_recycle_split : forall sg state eid node,
  q_post_lookup state eid node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
  UCOS2_inv sg state |--
  mbox_del_recycle_frame sg state eid node **
  (event_pool_addr sg eid + OSEventType_off) # UChar |-> 1 **
  (event_pool_addr sg eid + OSEventPtr_off) # Ptr |->_ **
  (event_pool_addr sg eid + OSEventCnt_off) # UShort |-> q_del_event_count node **
  sg.(g_OSEventFreeList) # Ptr |-> q_del_event_free_head sg state.
Proof.
  intros sg state eid node Hnode Htype.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid node Hnode).
  sep_apply_l_atomic (q_del_event_split_recycle_fields sg state eid node).
  unfold mbox_del_recycle_frame, event_raw_rep_no_eid, event_free_root_rep,
    q_del_event_count, q_del_event_free_head.
  cbn [event_cell event_image event_field_offset].
  rewrite Htype; cbn [encode_event_type].
  unfold OSEventType_off, OSEventPtr_off, OSEventCnt_off; entailer!.
  apply store_ptr_undef_store_ptr.
Qed.

Lemma mbox_del_recycle_merge_world : forall sg state eid node,
  UCOS2_state_inv sg state -> q_post_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_MBOX -> node.(queueFields) = None -> node.(waitList) = [] ->
  mbox_del_recycle_frame sg state eid node **
    (event_pool_addr sg eid + 0) # UChar |-> 0 **
    (event_pool_addr sg eid + 4) # Ptr |-> q_del_event_free_head sg state **
    (event_pool_addr sg eid + 8) # UShort |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid |--
  UCOS2_inv sg (event_delete_recycle_state sg state eid node).
Proof.
  intros sg state eid node Hvalid Hnode Htype Hnone Hempty.
  unfold mbox_del_recycle_frame, event_delete_recycle_state.
  sep_apply_r_atomic (UCOS2_inv_merge_event_recycle sg state eid node
    (event_image sg state.(TskState) node) Hvalid Hnode
    ltac:(rewrite Htype; discriminate) Hnone Hempty).
  sepcon_assoc_change.
  sep_apply_r_atomic (q_del_event_merge_recycled_fields sg state eid node).
  entailer!.
Qed.

Lemma mbox_del_group_split_recycle : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial state node processed waiting option,
  q_post_group state node = 0 ->
  ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1) ->
  mbox_del_loop_group_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) # UChar |-> q_post_group state node |--
  mbox_del_recycle_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting option **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) # UChar |-> 1 **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |->_ **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) # UShort |-> q_del_event_count node **
    sg.(g_OSEventFreeList) # Ptr |-> q_del_event_free_head sg state.
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed
    initial state node processed waiting option Hzero Hoption.
  unfold mbox_del_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  destruct (mbox_del_event_layout sg eid Hprofile Heid) as [Htypeaddr [Hptraddr [Hcntaddr Hgrpaddr]]].
  rewrite Htypeaddr, Hptraddr, Hcntaddr, Hgrpaddr.
  sep_apply_l_atomic (q_post_group_cell_merge sg state eid node Hvalid Hnode).
  destruct (mbox_del_empty_mailbox_fields sg state eid node Hvalid Hnode Htype Hzero) as [Hnone Hempty].
  sep_apply_l_atomic (mbox_del_recycle_split sg state eid node Hnode Htype).
  unfold mbox_del_recycle_context; entailer!.
Qed.

Lemma mbox_del_recycle_effect : forall environment critical sg caller active mask saved before acquired
  eid observed initial state node processed waiting option,
  mbox_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting ->
  node.(waitList) = [] ->
  ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1) ->
  mbox_del_effect sg eid option acquired 0 0 waiting (event_delete_recycle_state sg state eid node).
Proof.
  intros environment critical sg caller active mask saved before acquired eid observed initial
    state node processed waiting option Hfacts Hempty Hoption.
  destruct Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobservedtype [Hinitial [Hinitialtype Hgeneration]]]]].
  assert (Hzero : q_post_group state node = 0).
  { unfold q_post_group; rewrite Hempty; reflexivity. }
  destruct Hoption as [[-> [-> ->]]| ->].
  - unfold mbox_del_effect; exists OS_ERR_NONE, false; cbn [encode_os_err_code unsigned_last_nbits].
    split; [reflexivity|]; split; [reflexivity|].
    unfold mbox_delete_critical, event_delete_critical; exists node; split; [exact Hnode|].
    cbn [unsigned_last_nbits]. fold (q_post_group acquired node).
    rewrite Hzero; cbn; split; reflexivity.
  - assert (Hbroadcast : event_broadcast sg eid PendMbox 0 PendAbort acquired processed state).
    { eapply mbox_pend_abort_progress_done; eassumption. }
    unfold mbox_del_effect; exists OS_ERR_NONE, (negb (Z.eqb (q_post_group acquired initial) 0)).
    split; [reflexivity|]; split.
    + rewrite Hwaiting; unfold q_del_waiting.
      destruct (Z.eqb (q_post_group acquired initial) 0); reflexivity.
    + unfold mbox_delete_critical, event_delete_critical; exists initial; split; [exact Hinitial|].
      change (exists priorities ready node',
        event_broadcast sg eid PendMbox 0 PendAbort acquired priorities ready /\
        q_post_lookup ready eid node' /\
        (0, (OS_ERR_NONE, negb (Z.eqb (q_post_group acquired initial) 0))) =
          (0, (OS_ERR_NONE, negb (Z.eqb (q_post_group acquired initial) 0))) /\
        event_delete_recycle_state sg state eid node = event_delete_recycle_state sg ready eid node').
      exists processed, state, node; auto.
Qed.

Lemma mbox_del_recycle_restore : forall environment critical saved_local
  sg caller active mask saved pe before acquired eid observed initial state node processed waiting option,
  pe = event_addr sg eid -> pe <> 0 ->
  mbox_del_recycle_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting option **
    (&((pe) # "os_event" ->ₛ "OSEventType")) # UChar |-> 0 **
    (&((pe) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> q_del_event_free_head sg state **
    (&((pe) # "os_event" ->ₛ "OSEventCnt")) # UShort |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> pe |--
  mbox_del_restore_pre environment critical saved_local sg caller active mask saved pe eid option before acquired
    (event_delete_recycle_state sg state eid node) 0 0 waiting.
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed
    initial state node processed waiting option Hpe Hnonzero.
  unfold mbox_del_recycle_context; Intros.
  destruct H as [Hfacts [Hnone [Hempty Hoption]]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof (mbox_del_recycle_effect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hfacts Hempty Hoption) as Heffect.
  assert (Hreleased : UCOS2_state_inv sg (event_delete_recycle_state sg state eid node)).
  { unfold event_delete_recycle_state; eapply UCOS2_event_recycle_preserves_validity;
      [exact Hvalid|exact Hnode|rewrite Htype; discriminate|exact Hempty]. }
  pose proof (mbox_pend_abort_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  destruct (mbox_del_event_layout sg eid Hprofile Heid) as [Htypeaddr [Hptraddr [Hcntaddr Hgrpaddr]]].
  rewrite Hpe, Htypeaddr, Hptraddr, Hcntaddr.
  unfold event_addr, OSEventType_off, OSEventPtr_off, OSEventCnt_off.
  sep_apply (mbox_del_recycle_merge_world sg state eid node Hvalid Hnode Htype Hnone Hempty).
  sep_apply_l_atomic (q_post_mask_frame_event_update environment critical saved_local sg active saved acquired
    state (event_delete_recycle_state sg state eid node) eq_refl).
  unfold mbox_del_restore_pre; rewrite q_post_masked_equiv.
  pose proof (proj1 Hacquire) as Hsave.
  assert (Hnonzero' : event_addr sg eid <> 0) by (rewrite <- Hpe; exact Hnonzero).
  entailer!.
Qed.

Lemma mbox_del_critical_preserves : forall (P : UCOS2_Verify_State -> Prop) sg eid,
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node ->
    node.(eventType) = OS_EVENT_TYPE_MBOX ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendMbox 0 PendAbort)) ->
  (forall state node, P state -> P (event_delete_recycle_state sg state eid node)) ->
  forall before node opt result after,
    UCOS2_state_inv sg before -> q_post_lookup before eid node -> node.(eventType) = OS_EVENT_TYPE_MBOX ->
    mbox_delete_critical sg eid opt before result after -> P before -> P after.
Proof.
  intros P sg eid Hwake Hrecycle before node opt result after Hvalid Hnode Htype Hcritical HP.
  unfold mbox_delete_critical, event_delete_critical in Hcritical.
  destruct Hcritical as [other [Hother Hstep]].
  assert (other = node) by congruence; subst other.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp node.(waitList) before.(TskState)) 0)).
    + destruct Hstep as [_ ->]; exact HP.
    + destruct Hstep as [_ ->]; apply Hrecycle; exact HP.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [ready [last [Hloop [_ [_ ->]]]]]].
      apply Hrecycle; eapply mbox_pend_abort_broadcast_preserves; eassumption.
    + destruct Hstep as [_ ->]; exact HP.
Qed.


Lemma mbox_del_prefix_wake_decompose : forall environment critical sg original mask pe eid opt before
  observed returned restored pointer error,
  UCOS2_state_inv sg before -> mbox_del_call_input critical sg original pe before eid observed ->
  mbox_del_prefix_program environment critical sg original mask pe eid opt before
    (((pointer, error), true), returned) restored ->
  exists active saved acquired node released code,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    mbox_pend_abort_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    mbox_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (code, true)) released /\
    UCOS2_state_inv sg released /\
    task_resume_restore_program environment critical sg active released returned restored.
Proof.
  intros environment critical sg original mask pe eid opt before observed returned restored pointer error
    Hvalid Hinput Hprefix.
  unfold mbox_del_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 1) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct (Z.ltb 0 (q_del_int_nesting before)) eqn:Hint;
    [destruct Hprefix as [Heq _]; discriminate|].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype; apply Z.ltb_ge in Hint.
  destruct Hprefix as [active [saved [acquired [number [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]]].
  injection Hresult as Hnumber Hcode Hschedule Hcaller; subst number schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  pose proof (mbox_del_call_input_acquire _ _ _ _ _ _ _ Hpe Htype Hint Hinput) as Hacquire_input.
  destruct (mbox_pend_abort_acquire_identity environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hacquire_input Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hmbox Hg]]]]].
  pose proof (event_delete_critical_preserves_validity sg acquired eid node PendMbox
    (unsigned_last_nbits opt 8) (pointer, (code, true)) released
    (proj1 Hfacts) Hnode ltac:(rewrite Hmbox; reflexivity)
    ltac:(rewrite Hmbox; discriminate) Hstep) as Hreleased.
  exists active, saved, acquired, node, released, code.
  split; [exact Hfacts|]; split; [exact Hacquire|]; auto.
Qed.

Lemma mbox_del_schedule_protocol_task : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  mbox_del_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  mbox_del_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored pointer error Hprefix.
  destruct (mbox_del_prefix_wake_decompose environment critical sg (ResumeTaskCaller call)
    mask pe eid opt before observed returned restored pointer error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hmbox Hgeneration]]]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  assert (Hreleased_source : task_resume_caller_source sg (ResumeTaskCaller active) released).
  { eapply (mbox_del_critical_preserves
      (task_resume_caller_source sg (ResumeTaskCaller active)) sg eid).
    - intros; eapply mbox_pend_abort_wake_preserves_task_source; eassumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hmbox.
    - exact Hstep.
    - exact Hactive. }
  destruct (q_post_task_restore_source environment critical sg active returned released restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { eapply (mbox_del_critical_preserves
      (fun state => state.(SchedState).(readyList) <> []) sg eid).
    - intros; apply mbox_pend_abort_wake_preserves_ready_nonempty; assumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hmbox.
    - exact Hstep.
    - exact Hacquired_ready. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma mbox_del_schedule_protocol_task_idle : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  mbox_del_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  mbox_del_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients Hreturns Hsource Hidle.
  eapply mbox_del_schedule_protocol_task;
    [exact Hvalid|exact Hinput|exact Hclients|exact Hreturns|exact Hsource|].
  eapply sched_idle_ready_nonempty;
    [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.

Lemma mbox_del_schedule_protocol_disabled : forall environment critical sg view mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  mbox_del_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  mbox_del_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid opt before.
Proof.
  intros environment critical sg view mask pe eid opt before observed Hvalid Hinput Hclients Hsource
    returned restored pointer error Hprefix.
  destruct (mbox_del_prefix_wake_decompose environment critical sg (ResumeGenericCaller view)
    mask pe eid opt before observed returned restored pointer error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hmbox Hgeneration]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  assert (Hreleased_source : sched_disabled_entry_source view released).
  { eapply (mbox_del_critical_preserves (sched_disabled_entry_source view) sg eid).
    - intros; apply mbox_pend_abort_wake_preserves_disabled_source; assumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hmbox.
    - exact Hstep.
    - exact Hacquired_source. }
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    released restored Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma mbox_del_schedule_protocol_null : forall environment critical sg caller mask eid opt before,
  mbox_del_schedule_protocol environment critical sg caller mask 0 eid opt before.
Proof.
  intros environment critical sg caller mask eid opt before returned restored pointer error Hprefix.
  unfold mbox_del_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_del_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 1 ->
  mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype returned restored pointer error Hprefix.
  unfold mbox_del_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma mbox_del_schedule_protocol_isr : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 1 -> 0 < q_del_int_nesting before ->
  mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype Hint returned restored pointer error Hprefix.
  unfold mbox_del_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), Htype, (proj2 (Z.ltb_lt _ _) Hint) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

(** Empty-wait Boot paths are justified by actual initializer/history sources.
    No task is required to become ready merely because its wait is aborted. *)
Lemma mbox_del_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> mbox_del_call_input critical sg caller pe before eid observed ->
  (forall active saved acquired node,
    q_post_save_facts environment critical sg caller active mask saved before acquired ->
    mbox_pend_abort_acquire_facts environment critical sg caller active mask saved before acquired eid observed node ->
    node.(waitList) = []) ->
  mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty
    returned restored pointer error Hprefix.
  destruct (mbox_del_prefix_wake_decompose environment critical sg caller mask pe eid opt before
    observed returned restored pointer error Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hmbox Hgeneration]]]]].
  pose proof (Hempty active saved acquired node Hsave Hacquire) as Hnil.
  pose proof (proj1 (event_delete_critical_requests_schedule_iff sg acquired eid node PendMbox
    (unsigned_last_nbits opt 8) (pointer, (code, true)) released Hnode Hstep) eq_refl) as [_ Hnonempty].
  rewrite Hnil in Hnonempty; exfalso; apply Hnonempty; reflexivity.
Qed.

Lemma mbox_del_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> mbox_del_call_input critical sg caller pe before eid observed ->
  mbox_pend_abort_mailboxes_no_waiters before -> mbox_pend_abort_no_waiters_clients critical ->
  mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty Hclients.
  eapply mbox_del_schedule_protocol_acquired_no_waiters; [exact Hvalid|exact Hinput|].
  intros active saved acquired node Hfacts Hacquire.
  destruct Hfacts as [Hacquired [Hinterval Hrest]].
  destruct Hacquire as [_ [_ [_ [Hnode [Hmbox Hgeneration]]]]].
  destruct (mbox_pend_abort_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) before acquired
    Hclients Hvalid Hempty Hinterval) as [_ Hempty_acquired].
  exact (Hempty_acquired eid node Hnode Hmbox).
Qed.

Lemma mbox_del_schedule_protocol_boot_sources : forall environment critical sg caller mask pe eid opt before observed
  task_name flag_name memory_name names invocation,
  UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) ->
  critical_region_interval critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  mbox_del_call_input critical sg caller pe before eid observed ->
  (forall action, critical_region_clients critical action -> mbox_pend_abort_no_waiters_source_client action) ->
  mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed task_name flag_name memory_name names
    invocation Hboot Hhistory Hinput Hfamily.
  pose proof (mbox_pend_abort_no_waiters_clients_from_source_family critical Hfamily) as Hclients.
  destruct (mbox_pend_abort_interval_preserves_no_waiters critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before Hclients Hboot
    (mbox_pend_abort_boot_mailboxes_no_waiters sg task_name flag_name memory_name names) Hhistory) as [Hvalid Hempty].
  eapply mbox_del_schedule_protocol_no_waiters; eassumption.
Qed.

Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.

Lemma mbox_del_boot_initializer_schedule_protocol : forall environment critical sg caller mask pe eid opt before observed
  task_name flag_name memory_name names invocation,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true -> sg.(osKernelConfig).(cfgMemoryNames) = true ->
    exists chars, readable_name names memory_name chars) ->
  critical_region_interval critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  mbox_del_call_input critical sg caller pe before eid observed ->
  (forall action, critical_region_clients critical action -> mbox_pend_abort_no_waiters_source_client action) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names |--
  coq_prop (mbox_del_schedule_protocol environment critical sg caller mask pe eid opt before) &&
    UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros environment critical sg caller mask pe eid opt before observed task_name flag_name memory_name names
    invocation Hprofile Htcb Hnames Hmemory Hhistory Hinput Hfamily.
  sep_apply_l_atomic (mbox_pend_abort_boot_initializer_establishes_no_waiters
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  Intros.
  pose proof (mbox_del_schedule_protocol_boot_sources environment critical sg caller mask pe eid opt before observed
    task_name flag_name memory_name names invocation (proj1 H) Hhistory Hinput Hfamily) as Hprotocol.
  entailer!.
Qed.
