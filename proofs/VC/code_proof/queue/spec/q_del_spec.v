Require Export Ucos2Verify.VC.code.queue.spec.q_delete_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_pend_abort_spec.
Require Import Ucos2Verify.lib.error_codes Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia Coq.Strings.String.
From AUXLib Require Import ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic MapLib ArrayLib.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.
Local Open Scope string_scope.

(** A successful deletion returns the actual removed buffer.  In particular
    [QDelBufferSnapshot q []] for a zero-capacity queue remains distinguishable from
    failure, even though both spatial interpretations can be emp. *)
Inductive QDelBuffer : Type :=
| QDelNoBuffer
| QDelBufferSnapshot (queue : QueueFields) (slots : list (option Z)).

Definition q_del_buffer_rep (buffer : QDelBuffer) : Assertion :=
  match buffer with
  | QDelNoBuffer => emp
  | QDelBufferSnapshot q slots => PtrArray.mixed_full q.(qStart) q.(qSize) slots
  end.

Definition q_del_int_nesting state := state.(IntrState).(intNesting).
Definition q_del_waiting state node : Z := if Z.eqb (q_post_group state node) 0 then 0 else 1.

(** The receipt is bound to the protected recycle checkpoint, not to a
    possibly reused ECB/QCB slot after Restore.  The high-level observation
    remains (returned_pointer,error); this receipt also retains the linear
    caller resource which that observation does not describe. *)
Definition q_del_buffer_release sg eid opt acquired released error buffer : Prop :=
  match buffer with
  | QDelNoBuffer => error <> OS_ERR_NONE /\ released = acquired
  | QDelBufferSnapshot q slots => error = OS_ERR_NONE /\
      exists ready node,
        q_post_lookup ready eid node /\ node.(queueFields) = Some q /\
        ready.(EventState).(publishedQueueBytes) q.(qID) = Some slots /\
        released = q_delete_recycle_state sg ready eid node q /\
        ((opt = 0 /\ ready = acquired) \/
         (opt = 1 /\ exists priorities,
           event_broadcast sg eid PendQ 0 PendAbort acquired priorities ready))
  end.

Definition q_del_effect sg eid opt acquired (pointer error schedule : Z) released buffer : Prop :=
  exists code (request : bool),
    error = encode_os_err_code code /\ schedule = (if request then 1 else 0) /\
    q_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (code, request)) released /\
    q_del_buffer_release sg eid (unsigned_last_nbits opt 8) acquired released code buffer.

Definition q_del_prefix_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State ((((Z * Z) * bool) * TaskResumeCaller) * QDelBuffer) :=
  fun before result restored =>
    if Z.eqb pe 0 then result = ((((pe, 4), false), caller), QDelNoBuffer) /\ restored = before
    else if Z.eqb (event_slot_type_value before.(EventState) eid) 2 then
      if Z.ltb 0 (q_del_int_nesting before) then
        result = ((((pe, 15), false), caller), QDelNoBuffer) /\ restored = before
      else exists active saved acquired pointer error schedule released returned buffer,
        task_resume_save_program environment critical sg caller mask before (active, saved) acquired /\
        q_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (error, schedule)) released /\
        q_del_buffer_release sg eid (unsigned_last_nbits opt 8) acquired released error buffer /\
        task_resume_restore_program environment critical sg active released returned restored /\
        result = ((((pointer, encode_os_err_code error), schedule), returned), buffer)
    else result = ((((pe, 1), false), caller), QDelNoBuffer) /\ restored = before.

Definition q_del_tail environment critical sg mask
  (result : (((Z * Z) * bool) * TaskResumeCaller) * QDelBuffer)
  : program UCOS2_Verify_State (Z * Z) :=
  if snd (fst (fst result)) then
    bind (task_resume_schedule_call_program environment critical sg (snd (fst result)) mask)
      (fun _ => StateRelMonad.ret (fst (fst (fst result))))
  else StateRelMonad.ret (fst (fst (fst result))).

Definition q_del_program environment critical sg caller mask pe eid opt
  : program UCOS2_Verify_State (Z * Z) :=
  bind (q_del_prefix_program environment critical sg caller mask pe eid opt)
    (q_del_tail environment critical sg mask).

Definition q_del_safe environment critical sg caller mask pe eid opt before
  (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (q_del_program environment critical sg caller mask pe eid opt) X.

Definition q_del_return_safe current pointer error (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current) (StateRelMonad.ret (pointer, error)) X.

Definition q_del_caller_result environment critical sg original mask pe eid opt before
  pointer error returned current buffer : Prop :=
  exists prefix_caller restored schedule,
    q_del_prefix_program environment critical sg original mask pe eid opt before
      ((((pointer, error), schedule), prefix_caller), buffer) restored /\
    if schedule then
      task_resume_schedule_program environment critical sg prefix_caller mask restored returned current
    else returned = prefix_caller /\ current = restored.

Definition q_del_post environment critical saved_local sg original mask pe eid opt before
  error_addr pointer (X : (Z * Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX error returned current buffer,
    coq_prop (q_del_caller_result environment critical sg original mask pe eid opt before
      pointer error returned current buffer /\ q_del_return_safe current pointer error X) &&
    (q_post_closed environment critical saved_local sg returned mask current **
      q_del_buffer_rep buffer ** error_addr # UChar |-> error).

Definition q_del_schedule_protocol environment critical sg caller mask pe eid opt before : Prop :=
  forall returned restored pointer error buffer,
    q_del_prefix_program environment critical sg caller mask pe eid opt before
      ((((pointer, error), true), returned), buffer) restored ->
    q_post_schedule_cut environment critical sg returned restored.

Lemma q_del_prefix_protected : forall environment critical sg original active returned mask
  pe eid opt before acquired released restored saved pointer error schedule buffer,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 -> q_del_int_nesting before <= 0 ->
  task_resume_save_program environment critical sg original mask before (active, saved) acquired ->
  q_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (error, schedule)) released ->
  q_del_buffer_release sg eid (unsigned_last_nbits opt 8) acquired released error buffer ->
  task_resume_restore_program environment critical sg active released returned restored ->
  q_del_prefix_program environment critical sg original mask pe eid opt before
    ((((pointer, encode_os_err_code error), schedule), returned), buffer) restored.
Proof.
  intros; unfold q_del_prefix_program.
  rewrite (proj2 (Z.eqb_neq _ _) H), H0, (proj2 (Z.ltb_ge _ _) H1); cbn.
  exists active, saved, acquired, pointer, error, schedule, released, returned, buffer; auto.
Qed.

Lemma q_del_result_program : forall environment critical sg original mask pe eid opt before
  pointer error returned current buffer,
  q_del_caller_result environment critical sg original mask pe eid opt before
    pointer error returned current buffer ->
  q_del_program environment critical sg original mask pe eid opt before (pointer, error) current.
Proof.
  intros environment critical sg original mask pe eid opt before pointer error returned current buffer
    [prefix_caller [restored [schedule [Hprefix Htail]]]].
  exists ((((pointer, error), schedule), prefix_caller), buffer), restored; split; [exact Hprefix|].
  destruct schedule; cbn [q_del_tail].
  - exists tt, current; split; [|split; reflexivity].
    exists returned, current; split; [exact Htail|split; reflexivity].
  - destruct Htail as [-> ->]; split; reflexivity.
Qed.

Lemma q_del_safe_return : forall environment critical sg caller mask pe eid opt before current pointer error X,
  q_del_program environment critical sg caller mask pe eid opt before (pointer, error) current ->
  q_del_safe environment critical sg caller mask pe eid opt before X ->
  q_del_return_safe current pointer error X.
Proof.
  intros environment critical sg caller mask pe eid opt before current pointer error X Hprogram Hsafe.
  eapply (highstependret_derive
    (q_del_program environment critical sg caller mask pe eid opt)
    (fun state => state = before) (pointer, error) (fun _ state => state = current)).
  - intros state ->; exists current; split; [exact Hprogram|reflexivity].
  - exact Hsafe.
Qed.

Lemma q_del_closed_return : forall environment critical saved_local sg original returned mask
  pe eid opt before current error_addr pointer error buffer X,
  q_del_caller_result environment critical sg original mask pe eid opt before
    pointer error returned current buffer ->
  q_del_safe environment critical sg original mask pe eid opt before X ->
  q_post_closed environment critical saved_local sg returned mask current **
    q_del_buffer_rep buffer ** error_addr # UChar |-> error |--
  q_del_post environment critical saved_local sg original mask pe eid opt before error_addr pointer X.
Proof.
  intros.
  pose proof (q_del_result_program _ _ _ _ _ _ _ _ _ _ _ _ _ _ H) as Hprogram.
  pose proof (q_del_safe_return _ _ _ _ _ _ _ _ _ _ _ _ _ Hprogram H0) as Hsafe.
  unfold q_del_post; Exists error returned current buffer; entailer!.
Qed.

Definition q_del_interrupt_context environment saved_local sg caller mask before : Assertion :=
  coq_prop (UCOS2_state_inv sg before) &&
  (interrupt_inv_no_int_nesting sg before.(IntrState) ** UCOS2_raw_rep_missing_interrupt sg before **
    q_post_outside_frame environment saved_local sg caller mask before).

Lemma q_del_interrupt_split : forall environment critical saved_local sg caller mask before,
  UCOS2_state_inv sg before ->
  q_post_closed environment critical saved_local sg caller mask before |--
  sg.(g_OSIntNesting) # UChar |-> q_del_int_nesting before **
    q_del_interrupt_context environment saved_local sg caller mask before.
Proof.
  intros; rewrite (q_post_closed_equiv _ _ _ _ _ _ _ H), UCOS2_inv_split_interrupt.
  unfold q_del_interrupt_context, interrupt_inv, interrupt_inv_no_int_nesting,
    store_int_state, q_del_int_nesting; entailer!.
Qed.

Lemma q_del_interrupt_merge : forall environment critical saved_local sg caller mask before,
  UCOS2_state_inv sg before ->
  sg.(g_OSIntNesting) # UChar |-> q_del_int_nesting before **
    q_del_interrupt_context environment saved_local sg caller mask before |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof.
  intros; rewrite (q_post_closed_equiv _ _ _ _ _ _ _ H), UCOS2_inv_split_interrupt.
  unfold q_del_interrupt_context, interrupt_inv, interrupt_inv_no_int_nesting,
    store_int_state, q_del_int_nesting; entailer!.
Qed.

Definition q_del_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule buffer : Assertion :=
  coq_prop (q_post_save_facts environment critical sg caller active mask saved before acquired /\
    pe <> 0 /\ event_slot_type_value before.(EventState) eid = 2 /\ q_del_int_nesting before <= 0 /\
    UCOS2_state_inv sg released /\ q_del_effect sg eid opt acquired pointer error schedule released buffer) &&
  q_post_masked environment critical saved_local sg active saved acquired released.

Definition q_del_prefix_result environment critical sg caller mask pe eid opt before
  (pointer error schedule : Z) returned current buffer : Prop :=
  exists request : bool, schedule = (if request then 1 else 0) /\
    q_del_prefix_program environment critical sg caller mask pe eid opt before
      ((((pointer, error), request), returned), buffer) current.

Definition q_del_restore_post environment critical saved_local sg caller mask pe eid opt before
  pointer error schedule buffer : Assertion :=
  EX returned current,
    coq_prop (q_del_prefix_result environment critical sg caller mask pe eid opt before
      pointer error schedule returned current buffer /\ UCOS2_state_inv sg current) &&
    q_post_closed environment critical saved_local sg returned mask current.

Lemma q_del_restore_pre_raw : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule buffer,
  q_del_restore_pre environment critical saved_local sg caller active mask saved pe eid opt
    before acquired released pointer error schedule buffer |--
  q_post_masked environment critical saved_local sg active saved acquired released.
Proof. intros; unfold q_del_restore_pre; apply derivable1_andp_elim2. Qed.

Lemma q_del_restore_post_consequence : forall environment critical saved_local sg caller active mask saved pe eid opt
  before acquired released pointer error schedule buffer,
  q_post_save_facts environment critical sg caller active mask saved before acquired ->
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 -> q_del_int_nesting before <= 0 ->
  UCOS2_state_inv sg released -> q_del_effect sg eid opt acquired pointer error schedule released buffer ->
  q_post_restore_output environment critical saved_local sg active saved released |--
  q_del_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error schedule buffer.
Proof.
  intros environment critical saved_local sg caller active mask saved pe eid opt before acquired released pointer error schedule buffer
    [_ [_ [Hsaved Hsave]]] Hpe Htype Hint Hvalid [code [request [-> [-> [Hstep Hbuffer]]]]].
  sep_apply_l_atomic (q_post_restore_output_return environment critical saved_local sg active mask saved released Hvalid Hsaved).
  Intros returned current.
  assert (Hprefix : q_del_prefix_result environment critical sg caller mask pe eid opt before
    pointer (encode_os_err_code code) (if request then 1 else 0) returned current buffer).
  { exists request; split; [reflexivity|]. eapply q_del_prefix_protected;
      [exact Hpe|exact Htype|exact Hint|exact Hsave|exact Hstep|exact Hbuffer|exact (proj1 H)]. }
  unfold q_del_restore_post; Exists returned current; entailer!.
Qed.

Definition q_del_loop_facts environment critical sg caller active mask saved before acquired
  eid observed initial state node processed waiting : Prop :=
  q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed initial /\
  q_post_profile sg /\ valid_event_id sg eid /\ q_del_int_nesting before <= 0 /\
  waiting = q_del_waiting acquired initial /\
  UCOS2_state_inv sg state /\ q_post_lookup state eid node /\ node.(eventType) = OS_EVENT_TYPE_Q /\
  q_pend_abort_progress sg eid acquired state processed.

Definition q_del_loop_group_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting : Assertion :=
  coq_prop (q_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting) &&
  (q_post_group_frame sg state eid node ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition q_del_loop_wake_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting tid old : Assertion :=
  coq_prop (q_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting /\ q_post_group state node <> 0 /\
    event_task_rdy_entry sg state.(TskState) eid node tid old) &&
  (q_post_wake_frame sg state eid tid **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

(** These residuals remove precisely the three ECB fields written by the
    tail and the QCB link.  Every other byte has the post-wake image. *)
Definition q_del_event_residual sg state eid node : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_pool_addr sg eid))
    (remove EventField_eq_dec EventTypeField
      (remove EventField_eq_dec EventPtrField
        (remove EventField_eq_dec EventCntField (event_fields sg.(osKernelConfig).(cfgEventNames)))))
    (event_image sg state.(TskState) node).

Definition q_del_recycle_frame sg state eid node q free slots : Assertion :=
  store_map_missing_i (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) eid **
  q_del_event_residual sg state eid node ** event_free_storage_rep sg state.(EventState) **
  store_map_missing_i (published_queue_node_rep sg state.(EventState)) state.(EventState).(inUsedEventStates) eid **
  store_free_queue_nodes sg free ** qcb_storage_without_field sg q.(qID) (qcb_fields_image q) QCBPtr **
  queue_buffer_rep q slots ** UCOS2_raw_rep_missing_event_queue sg state.

Definition q_del_recycle_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting option q free slots : Assertion :=
  coq_prop (q_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting /\
    q_post_queue_facts sg state eid node q free slots /\
    ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1)) &&
  (q_del_recycle_frame sg state eid node q free slots ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition q_del_event_count node := encode_event_cnt_value node.
Definition q_del_event_free_head sg state :=
  event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)).

Definition q_del_pointer_context environment critical saved_local sg caller active mask saved before acquired
  eid observed initial state node processed waiting option q : Assertion :=
  coq_prop (q_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting /\ q_post_group state node = 0 /\
    node.(queueFields) = Some q /\ node.(waitList) = [] /\ queue_fields_consistency sg [] q /\
    ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1)) &&
  (q_post_field_frame sg state eid node EventPtrField ** unmap_table_rep sg **
    q_post_mask_frame environment critical saved_local sg active saved acquired state).

Definition q_del_finish_context environment critical saved_local sg original mask pe eid opt before
  pointer error : Assertion :=
  EX returned current buffer,
    coq_prop (q_del_caller_result environment critical sg original mask pe eid opt before
      pointer error returned current buffer) &&
    (q_post_closed environment critical saved_local sg returned mask current ** q_del_buffer_rep buffer).

Definition q_del_after_schedule_context environment critical saved_local sg original mask pe eid opt before
  waiting : Assertion :=
  q_del_finish_context environment critical saved_local sg original mask pe eid opt before 0 0 ||
  (EX buffer, coq_prop (waiting <> 1) &&
    (q_del_restore_post environment critical saved_local sg original mask pe eid opt before 0 0 waiting buffer **
      q_del_buffer_rep buffer)).

Lemma q_del_finish_return : forall environment critical saved_local sg original mask pe eid opt before
  pointer error error_addr X,
  q_del_safe environment critical sg original mask pe eid opt before X ->
  q_del_finish_context environment critical saved_local sg original mask pe eid opt before pointer error **
    error_addr # UChar |-> error |--
  q_del_post environment critical saved_local sg original mask pe eid opt before error_addr pointer X.
Proof.
  intros; unfold q_del_finish_context; Intros returned current buffer.
  sep_apply_r_atomic (q_del_closed_return environment critical saved_local sg original returned mask
    pe eid opt before current error_addr pointer error buffer X H0 H); entailer!.
Qed.

Lemma q_del_nonschedule_finish : forall environment critical saved_local sg caller mask pe eid opt before
  pointer error schedule buffer,
  schedule <> 1 ->
  q_del_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error schedule buffer **
    q_del_buffer_rep buffer |--
  q_del_finish_context environment critical saved_local sg caller mask pe eid opt before pointer error.
Proof.
  intros; unfold q_del_restore_post; Intros returned current.
  destruct H0 as [[request [Hrequest Hprefix]] Hvalid]; destruct request; [contradiction|].
  unfold q_del_finish_context; Exists returned current buffer.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists returned, current, false; split; [exact Hprefix|split; reflexivity].
Qed.

Lemma q_del_restore_schedule : forall environment critical saved_local sg caller mask pe eid opt before pointer error buffer,
  q_del_schedule_protocol environment critical sg caller mask pe eid opt before ->
  q_del_restore_post environment critical saved_local sg caller mask pe eid opt before pointer error 1 buffer |--
  EX returned current,
    coq_prop (q_del_prefix_result environment critical sg caller mask pe eid opt before
      pointer error 1 returned current buffer) &&
    (task_resume_sched_pre environment critical saved_local sg returned mask current ** q_post_extra_tables sg returned).
Proof.
  intros environment critical saved_local sg caller mask pe eid opt before pointer error buffer Hprotocol.
  unfold q_del_restore_post; Intros returned current.
  destruct H as [Hresult Hvalid]; pose proof Hresult as [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_post_closed_sched_pre environment critical saved_local sg returned mask current
    (Hprotocol returned current pointer error buffer Hprefix)).
  Exists returned current; entailer!.
Qed.

(** The endpoint comes from the actual scheduler return heap.  Buffer ownership
    stays outside its footprint; no equality with the protected state is used. *)
Lemma q_del_sched_post_endpoint : forall environment critical saved_local sg caller mask before,
  task_resume_sched_post environment critical saved_local sg caller mask before ** q_post_extra_tables sg caller |--
  EX returned current,
    coq_prop (task_resume_schedule_program environment critical sg caller mask before returned current) &&
    q_post_closed environment critical saved_local sg returned mask current.
Proof.
  intros environment critical saved_local sg [call|view] mask before;
    cbn [task_resume_sched_post q_post_extra_tables].
  - unfold os_sched_continuation_history_return_post at 1; Intros returned current.
    Exists (ResumeTaskCaller returned) current.
    apply _derivable1_andp_intros.
    + entailer!; cbn [task_resume_schedule_program].
      exists returned, current; split; [apply os_sched_continuation_program_iff; tauto|split; reflexivity].
    + unfold q_post_closed; cbn [q_post_extra_tables task_resume_closed].
      rewrite task_tcb_init_continuation_save_input_closed_world; entailer!.
  - unfold sched_disabled_contextual_post at 1; Intros saved acquired current.
    Exists (ResumeGenericCaller view) current.
    apply _derivable1_andp_intros.
    + entailer!; cbn [task_resume_schedule_program].
      exists (ResumeGenericCaller view, saved), acquired; split.
      * cbn [task_resume_save_program fst snd]; split; [reflexivity|tauto].
      * exists tt, acquired; split.
        -- split; [tauto|reflexivity].
        -- cbn [task_resume_restore_program fst]; split; [reflexivity|tauto].
    + unfold q_post_closed; cbn [q_post_extra_tables task_resume_closed]; entailer!.
Qed.

Lemma q_del_sched_finish : forall environment critical saved_local sg original returned mask
  pe eid opt before restored pointer error buffer,
  q_del_prefix_result environment critical sg original mask pe eid opt before pointer error 1 returned restored buffer ->
  task_resume_sched_post environment critical saved_local sg returned mask restored **
    q_post_extra_tables sg returned ** q_del_buffer_rep buffer |--
  q_del_finish_context environment critical saved_local sg original mask pe eid opt before pointer error.
Proof.
  intros environment critical saved_local sg original returned mask pe eid opt before restored pointer error buffer
    [request [Hrequest Hprefix]].
  destruct request; [|discriminate].
  sep_apply_l_atomic (q_del_sched_post_endpoint environment critical saved_local sg returned mask restored).
  Intros final current; unfold q_del_finish_context; Exists final current buffer.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists returned, restored, true; split; assumption.
Qed.

Lemma q_del_critical_preserves : forall (P : UCOS2_Verify_State -> Prop) sg eid,
  (forall state node tid old,
    UCOS2_state_inv sg state -> q_post_lookup state eid node ->
    node.(eventType) = OS_EVENT_TYPE_Q ->
    state.(TskState).(inUsedTaskStates) tid = Some old -> P state ->
    P (event_wake_state sg state eid node tid old PendQ 0 PendAbort)) ->
  (forall state node q, P state -> P (q_delete_recycle_state sg state eid node q)) ->
  forall before node opt result after,
    UCOS2_state_inv sg before -> q_post_lookup before eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
    q_delete_critical sg eid opt before result after -> P before -> P after.
Proof.
  intros P sg eid Hwake Hrecycle before node opt result after Hvalid Hnode Htype [other [Hother Hstep]] HP.
  assert (other = node) by congruence; subst other.
  destruct (Z.eqb opt 0).
  - destruct (negb (Z.eqb (encode_event_wait_grp node.(waitList) before.(TskState)) 0)).
    + destruct Hstep as [_ ->]; exact HP.
    + destruct Hstep as [q [_ [_ ->]]]; apply Hrecycle; exact HP.
  - destruct (Z.eqb opt 1).
    + destruct Hstep as [priorities [ready [last [q [Hloop [_ [_ [_ ->]]]]]]]].
      apply Hrecycle; eapply q_pend_abort_broadcast_preserves; eassumption.
    + destruct Hstep as [_ ->]; exact HP.
Qed.

Lemma q_del_prefix_wake_decompose : forall environment critical sg original mask pe eid opt before
  observed returned restored pointer error buffer,
  UCOS2_state_inv sg before -> q_post_call_input critical sg original pe before eid observed ->
  q_del_prefix_program environment critical sg original mask pe eid opt before
    ((((pointer, error), true), returned), buffer) restored ->
  exists active saved acquired node released code,
    q_post_save_facts environment critical sg original active mask saved before acquired /\
    q_post_acquire_facts environment critical sg original active mask saved before acquired eid observed node /\
    q_delete_critical sg eid (unsigned_last_nbits opt 8) acquired (pointer, (code, true)) released /\
    UCOS2_state_inv sg released /\
    task_resume_restore_program environment critical sg active released returned restored.
Proof.
  intros environment critical sg original mask pe eid opt before observed returned restored pointer error buffer
    Hvalid Hinput Hprefix.
  unfold q_del_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  destruct (Z.ltb 0 (q_del_int_nesting before)); [destruct Hprefix as [Heq _]; discriminate|].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype.
  destruct Hprefix as [active [saved [acquired [number [code [schedule [released [next [receipt
    [Hsave [Hstep [Hreceipt [Hrestore Hresult]]]]]]]]]]]]].
  injection Hresult as Hnumber Hcode Hschedule Hcaller Hbuffer; subst number schedule next receipt.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  destruct (q_post_acquire_identity environment critical sg original active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hg]]]]].
  pose proof (q_delete_critical_preserves_validity sg acquired eid node (unsigned_last_nbits opt 8)
    (pointer, (code, true)) released (proj1 Hfacts) Hnode Hqueue Hstep) as Hreleased.
  exists active, saved, acquired, node, released, code.
  split; [exact Hfacts|]; split; [exact Hacquire|]; auto.
Qed.

Lemma q_del_schedule_protocol_task : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  before.(SchedState).(readyList) <> [] ->
  q_del_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients
    Hreturns Hsource Hready returned restored pointer error buffer Hprefix.
  destruct (q_del_prefix_wake_decompose environment critical sg (ResumeTaskCaller call)
    mask pe eid opt before observed returned restored pointer error buffer Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct active as [active|view]; [|contradiction].
  destruct returned as [returned|view]; [|contradiction].
  pose proof (q_post_task_save_source environment critical sg call active mask saved before acquired
    Hvalid Hreturns Hsource Hactualsave) as Hactive.
  assert (Hreleased_source : task_resume_caller_source sg (ResumeTaskCaller active) released).
  { eapply (q_del_critical_preserves
      (task_resume_caller_source sg (ResumeTaskCaller active)) sg eid).
    - intros; eapply q_pend_abort_wake_preserves_task_source; eassumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hqueue.
    - exact Hstep.
    - exact Hactive. }
  destruct (q_post_task_restore_source environment critical sg active returned released restored
    Hreleased Hreturns Hreleased_source Hrestore) as [Hrestored [Hreturned Hreturn_interval]].
  assert (Hacquired_ready : acquired.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  assert (Hreleased_ready : released.(SchedState).(readyList) <> []).
  { eapply (q_del_critical_preserves
      (fun state => state.(SchedState).(readyList) <> []) sg eid).
    - intros; apply q_pend_abort_wake_preserves_ready_nonempty; assumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hqueue.
    - exact Hstep.
    - exact Hacquired_ready. }
  assert (Hrestored_ready : restored.(SchedState).(readyList) <> []).
  { eapply critical_region_interval_preserves_sched_ready; eassumption. }
  split; [exact Hclients|].
  destruct Hreturned as [Hsource_returned [Havailable Haddress]].
  eapply os_sched_call_cut_from_source; eassumption.
Qed.

Lemma q_del_schedule_protocol_task_idle : forall environment critical sg call mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeTaskCaller call) pe before eid observed ->
  kernel_sched_ready_clients critical ->
  task_resume_completed_task_returns environment critical ->
  task_resume_caller_source sg (ResumeTaskCaller call) before ->
  task_idle_ready sg before.(TskState) ->
  q_del_schedule_protocol environment critical sg (ResumeTaskCaller call) mask pe eid opt before.
Proof.
  intros environment critical sg call mask pe eid opt before observed Hvalid Hinput Hclients Hreturns Hsource Hidle.
  eapply q_del_schedule_protocol_task;
    [exact Hvalid|exact Hinput|exact Hclients|exact Hreturns|exact Hsource|].
  eapply sched_idle_ready_nonempty;
    [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.

Lemma q_del_schedule_protocol_disabled : forall environment critical sg view mask pe eid opt before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg (ResumeGenericCaller view) pe before eid observed ->
  sched_disabled_completed_clients critical view -> sched_disabled_entry_source view before ->
  q_del_schedule_protocol environment critical sg (ResumeGenericCaller view) mask pe eid opt before.
Proof.
  intros environment critical sg view mask pe eid opt before observed Hvalid Hinput Hclients Hsource
    returned restored pointer error buffer Hprefix.
  destruct (q_del_prefix_wake_decompose environment critical sg (ResumeGenericCaller view)
    mask pe eid opt before observed returned restored pointer error buffer Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hsave as [Hacquired [Hinterval [Hsaved Hactualsave]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct active as [call|active]; [contradiction|].
  destruct Hactualsave as [-> Hsave_rest].
  destruct returned as [call|returned]; [contradiction|].
  destruct Hrestore as [-> Hreturn_interval].
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    before acquired Hclients Hvalid Hinterval) as [Hafter Hcontext].
  pose proof (sched_disabled_context_rely_preserves_entry_source _ _ _ _ Hcontext Hsource) as Hacquired_source.
  assert (Hreleased_source : sched_disabled_entry_source view released).
  { eapply (q_del_critical_preserves (sched_disabled_entry_source view) sg eid).
    - intros; apply q_pend_abort_wake_preserves_disabled_source; assumption.
    - intros; exact H.
    - exact Hacquired.
    - exact Hnode.
    - exact Hqueue.
    - exact Hstep.
    - exact Hacquired_source. }
  destruct (sched_disabled_interval_preserves_context critical sg view view.(os_execution_invocation)
    released restored Hclients Hreleased Hreturn_interval) as [Hrestored Hreturn_context].
  split; [exact Hclients|]; split; [exact Hrestored|].
  eapply sched_disabled_context_rely_preserves_entry_source; eassumption.
Qed.

Lemma q_del_schedule_protocol_null : forall environment critical sg caller mask eid opt before,
  q_del_schedule_protocol environment critical sg caller mask 0 eid opt before.
Proof.
  intros environment critical sg caller mask eid opt before returned restored pointer error buffer Hprefix.
  unfold q_del_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma q_del_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype returned restored pointer error buffer Hprefix.
  unfold q_del_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma q_del_schedule_protocol_isr : forall environment critical sg caller mask pe eid opt before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 2 -> 0 < q_del_int_nesting before ->
  q_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before Hpe Htype Hint returned restored pointer error buffer Hprefix.
  unfold q_del_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), Htype, (proj2 (Z.ltb_lt _ _) Hint) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

(** Empty-wait Boot paths are justified by actual initializer/history sources.
    No task is required to become ready merely because its wait is aborted. *)
Lemma q_del_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  (forall active saved acquired node,
    q_post_save_facts environment critical sg caller active mask saved before acquired ->
    q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed node ->
    node.(waitList) = []) ->
  q_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty
    returned restored pointer error buffer Hprefix.
  destruct (q_del_prefix_wake_decompose environment critical sg caller mask pe eid opt before
    observed returned restored pointer error buffer Hvalid Hinput Hprefix)
    as [active [saved [acquired [node [released [code
      [Hsave [Hacquire [Hstep [Hreleased Hrestore]]]]]]]]]].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  pose proof (Hempty active saved acquired node Hsave Hacquire) as Hnil.
  pose proof (proj1 (q_delete_critical_requests_schedule_iff sg acquired eid node
    (unsigned_last_nbits opt 8) (pointer, (code, true)) released Hnode Hstep) eq_refl) as [_ Hnonempty].
  rewrite Hnil in Hnonempty; exfalso; apply Hnonempty; reflexivity.
Qed.

Lemma q_del_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid opt before observed,
  UCOS2_state_inv sg before -> q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before -> q_post_no_waiters_clients critical ->
  q_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed Hvalid Hinput Hempty Hclients.
  eapply q_del_schedule_protocol_acquired_no_waiters; [exact Hvalid|exact Hinput|].
  intros active saved acquired node Hfacts Hacquire.
  destruct Hfacts as [Hacquired [Hinterval Hrest]].
  destruct Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct (q_post_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) before acquired
    Hclients Hvalid Hempty Hinterval) as [_ Hempty_acquired].
  exact (Hempty_acquired eid node Hnode Hqueue).
Qed.

Lemma q_del_schedule_protocol_boot_sources : forall environment critical sg caller mask pe eid opt before observed
  task_name flag_name memory_name names invocation,
  UCOS2_state_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names) ->
  critical_region_interval critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  q_post_call_input critical sg caller pe before eid observed ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  q_del_schedule_protocol environment critical sg caller mask pe eid opt before.
Proof.
  intros environment critical sg caller mask pe eid opt before observed task_name flag_name memory_name names
    invocation Hboot Hhistory Hinput Hfamily.
  pose proof (q_post_no_waiters_clients_from_source_family critical Hfamily) as Hclients.
  destruct (q_post_interval_preserves_no_waiters critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before Hclients Hboot
    (q_post_boot_queues_no_waiters sg task_name flag_name memory_name names) Hhistory) as [Hvalid Hempty].
  eapply q_del_schedule_protocol_no_waiters; eassumption.
Qed.

Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.

Lemma q_del_boot_initializer_schedule_protocol : forall environment critical sg caller mask pe eid opt before observed
  task_name flag_name memory_name names invocation,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true -> sg.(osKernelConfig).(cfgMemoryNames) = true ->
    exists chars, readable_name names memory_name chars) ->
  critical_region_interval critical sg invocation
    (UCOS2_boot_state sg task_name flag_name memory_name names) before ->
  q_post_call_input critical sg caller pe before eid observed ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names |--
  coq_prop (q_del_schedule_protocol environment critical sg caller mask pe eid opt before) &&
    UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros environment critical sg caller mask pe eid opt before observed task_name flag_name memory_name names
    invocation Hprofile Htcb Hnames Hmemory Hhistory Hinput Hfamily.
  sep_apply_l_atomic (q_post_boot_initializer_establishes_no_waiters
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  Intros.
  pose proof (q_del_schedule_protocol_boot_sources environment critical sg caller mask pe eid opt before observed
    task_name flag_name memory_name names invocation (proj1 H) Hhistory Hinput Hfamily) as Hprotocol.
  entailer!.
Qed.

Lemma q_del_event_split_recycle_fields : forall sg state eid node,
  used_event_rep sg state.(TskState) eid node |--
  event_cell (event_pool_addr sg eid) EventTypeField (event_image sg state.(TskState) node EventTypeField) **
  event_cell (event_pool_addr sg eid) EventPtrField (event_image sg state.(TskState) node EventPtrField) **
  event_cell (event_pool_addr sg eid) EventCntField (event_image sg state.(TskState) node EventCntField) **
  q_del_event_residual sg state eid node.
Proof.
  intros sg state eid node.
  pose proof (event_fields_nodup sg.(osKernelConfig).(cfgEventNames)) as Hfields.
  assert (Hcnt : NoDup (remove EventField_eq_dec EventCntField
    (event_fields sg.(osKernelConfig).(cfgEventNames)))).
  { rewrite <- remove_alt; unfold remove'; apply NoDup_filter; exact Hfields. }
  assert (Hptr : NoDup (remove EventField_eq_dec EventPtrField
    (remove EventField_eq_dec EventCntField
      (event_fields sg.(osKernelConfig).(cfgEventNames))))).
  { rewrite <- remove_alt; unfold remove'; apply NoDup_filter; exact Hcnt. }
  unfold used_event_rep, event_storage_rep, q_del_event_residual, event_addr.
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field EventField (option Z)
    EventField_eq_dec (event_cell (event_pool_addr sg eid)) _
    (event_image sg state.(TskState) node) EventCntField Hfields
    ltac:(unfold event_fields; simpl; tauto)).
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field EventField (option Z)
    EventField_eq_dec (event_cell (event_pool_addr sg eid)) _
    (event_image sg state.(TskState) node) EventPtrField Hcnt
    ltac:(apply in_in_remove; [discriminate|unfold event_fields; simpl; tauto])).
  sep_apply_l_atomic (EventFieldStorage.store_fields_split_field EventField (option Z)
    EventField_eq_dec (event_cell (event_pool_addr sg eid)) _
    (event_image sg state.(TskState) node) EventTypeField Hptr
    ltac:(apply in_in_remove; [discriminate|];
      apply in_in_remove; [discriminate|unfold event_fields; simpl; tauto])).
  entailer!.
Qed.

Lemma q_del_event_merge_recycled_fields : forall sg state eid node,
  q_del_event_residual sg state eid node **
    (event_pool_addr sg eid + 0) # UChar |-> 0 **
    (event_pool_addr sg eid + 4) # Ptr |-> q_del_event_free_head sg state **
    (event_pool_addr sg eid + 8) # UShort |-> 0 |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_recycle_image sg state.(EventState).(unUsedEventStates) (event_image sg state.(TskState) node)).
Proof.
  intros sg state eid node.
  pose proof (event_fields_nodup sg.(osKernelConfig).(cfgEventNames)) as Hfields.
  assert (Hcnt : NoDup (remove EventField_eq_dec EventCntField
    (event_fields sg.(osKernelConfig).(cfgEventNames)))).
  { rewrite <- remove_alt; unfold remove'; apply NoDup_filter; exact Hfields. }
  assert (Hptr : NoDup (remove EventField_eq_dec EventPtrField
    (remove EventField_eq_dec EventCntField
      (event_fields sg.(osKernelConfig).(cfgEventNames))))).
  { rewrite <- remove_alt; unfold remove'; apply NoDup_filter; exact Hcnt. }
  unfold event_storage_rep, q_del_event_residual, event_recycle_image, event_write.
  pose proof (EventFieldStorage.store_fields_merge_updated_field EventField (option Z)
    EventField_eq_dec (event_cell (event_pool_addr sg eid)) _
    (event_image sg state.(TskState) node) EventTypeField (Some 0) Hptr
    ltac:(apply in_in_remove; [discriminate|];
      apply in_in_remove; [discriminate|unfold event_fields; simpl; tauto])) as Htype_merge.
  cbn [event_cell event_field_offset] in Htype_merge.
  sep_apply_l_atomic Htype_merge.
  pose proof (EventFieldStorage.store_fields_merge_updated_field EventField (option Z)
    EventField_eq_dec (event_cell (event_pool_addr sg eid)) _
    (field_update EventField_eq_dec (event_image sg state.(TskState) node) EventTypeField (Some 0))
    EventPtrField (Some (q_del_event_free_head sg state)) Hcnt
    ltac:(apply in_in_remove; [discriminate|unfold event_fields; simpl; tauto])) as Hptr_merge.
  cbn [event_cell event_field_offset] in Hptr_merge.
  sep_apply_l_atomic Hptr_merge.
  pose proof (EventFieldStorage.store_fields_merge_updated_field EventField (option Z)
    EventField_eq_dec (event_cell (event_pool_addr sg eid)) _
    (field_update EventField_eq_dec
      (field_update EventField_eq_dec (event_image sg state.(TskState) node) EventTypeField (Some 0))
      EventPtrField (Some (q_del_event_free_head sg state)))
    EventCntField (Some 0) Hfields ltac:(unfold event_fields; simpl; tauto)) as Hcnt_merge.
  cbn [event_cell event_field_offset] in Hcnt_merge.
  sep_apply_l_atomic Hcnt_merge.
  unfold q_del_event_free_head; entailer!.
Qed.

(** This is the resource consequence of the six stores, using both live-map
    residuals and the actual post-wake image.  It produces exactly one buffer. *)
Lemma q_del_recycle_merge_world : forall sg state eid node q free slots,
  q_post_queue_facts sg state eid node q free slots ->
  q_del_recycle_frame sg state eid node q free slots **
    (qcb_addr sg q.(qID) + OSQPtr_off) # Ptr |-> queue_free_head sg free **
    sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg q.(qID) **
    (event_pool_addr sg eid + 0) # UChar |-> 0 **
    (event_pool_addr sg eid + 4) # Ptr |-> q_del_event_free_head sg state **
    (event_pool_addr sg eid + 8) # UShort |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> event_pool_addr sg eid |--
  UCOS2_inv sg (q_delete_recycle_state sg state eid node q) **
    q_del_buffer_rep (QDelBufferSnapshot q slots).
Proof.
  intros sg state eid node q free slots
    [Hvalid [Hnode [Htype [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]].
  unfold q_del_recycle_frame, q_delete_recycle_state, q_del_buffer_rep.
  sep_apply_r_atomic (UCOS2_inv_merge_queue_recycle sg state free eid node q
    (event_image sg state.(TskState) node) slots Hvalid Hbinding Hpart Hnode Htype Hq Hempty).
  sepcon_assoc_change.
  sep_apply_r_atomic (q_del_event_merge_recycled_fields sg state eid node).
  sepcon_assoc_change.
  sep_apply_r_atomic (qcb_recycle_storage_implies_free sg q.(qID) (qcb_fields_image q) (queue_free_head sg free)).
  sepcon_assoc_change.
  sep_apply_r_atomic (qcb_recycle_merge_storage sg q.(qID) (qcb_fields_image q) (queue_free_head sg free)).
  entailer!.
Qed.

Lemma q_del_uchar_range__entry_and_early_returns : forall address value,
  address # UChar |-> value |--
  coq_prop (0 <= value <= 255) && address # UChar |-> value.
Proof. intros; unfold store_uchar; entailer!. Qed.
Lemma q_del_type_merge_closed__entry_and_early_returns :
  forall environment critical saved_local sg caller mask before eid,
  q_post_profile sg -> valid_event_id sg eid -> UCOS2_state_inv sg before ->
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventType")) # UChar |->
    event_slot_type_value before.(EventState) eid **
    q_post_type_context environment saved_local sg caller mask before eid |--
  q_post_closed environment critical saved_local sg caller mask before.
Proof.
  intros environment critical saved_local sg caller mask before eid Hprofile Hid Hvalid.
  destruct Hprofile as [_ [Hlayout _]].
  pose proof (proj1 (proj1 (Hlayout eid Hid))) as Htype.
  rewrite Htype, (q_post_closed_equiv _ _ _ _ _ _ _ Hvalid).
  unfold q_post_type_context.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  entailer!.
Qed.
Lemma q_del_event_layout__recycle_and_protected_errors : forall sg eid,
  q_post_profile sg -> valid_event_id sg eid ->
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) = event_addr sg eid + OSEventType_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) = event_addr sg eid + OSEventPtr_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) = event_addr sg eid + OSEventCnt_off /\
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) = event_addr sg eid + OSEventGrp_off.
Proof.
  intros sg eid [_ [Hlayout _]] Heid.
  destruct (Hlayout eid Heid) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]]; auto.
Qed.
Lemma q_del_qcb_ptr_layout__recycle_and_protected_errors : forall sg q,
  q_post_profile sg -> queue_fields_consistency sg [] q ->
  (&(((qcb_addr (sg) ((qID (q))))) # "os_q" ->ₛ "OSQPtr")) = qcb_addr sg q.(qID) + OSQPtr_off.
Proof.
  intros sg q [_ [_ [Hlayout [[Hmax Hsize] Harg]]]] Hq.
  pose proof Hq as [Hqid _].
  specialize (Hlayout q.(qID) Hqid).
  change (sizeof ("os_q") = sizeof_OS_Q) in Hsize.
  rewrite Hsize in Hlayout; exact (proj1 Hlayout).
Qed.
Lemma q_del_group_split_pointer__recycle_and_protected_errors : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial state node processed waiting option,
  q_post_group state node = 0 ->
  ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1) ->
  q_del_loop_group_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp")) # UChar |-> q_post_group state node |--
  EX q, q_del_pointer_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting option q **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> qcb_addr sg q.(qID).
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed
    initial state node processed waiting option Hzero Hoption.
  unfold q_del_loop_group_context; Intros.
  pose proof H as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  destruct (q_del_event_layout__recycle_and_protected_errors sg eid Hprofile Heid)
    as [_ [Hptr [_ Hgrp]]].
  rewrite Hgrp, Hptr.
  sep_apply_l_atomic (q_post_group_cell_merge sg state eid node Hvalid Hnode).
  destruct (q_post_queue_current sg state eid node Hvalid Hnode Htype Hzero)
    as [q [Hq [Hempty Hqvalid]]].
  sep_apply_l_atomic (q_post_pointer_split sg state eid node q Hnode Htype Hq).
  Intros.
  Exists q; unfold q_del_pointer_context; entailer!.
Qed.
Lemma q_del_pointer_split_recycle__recycle_and_protected_errors : forall environment critical saved_local
  sg caller active mask saved before acquired eid observed initial state node processed waiting option q,
  q_del_pointer_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting option q **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> qcb_addr sg q.(qID) |--
  EX free slots,
    q_del_recycle_context environment critical saved_local sg caller active mask saved before acquired
      eid observed initial state node processed waiting option q free slots **
    (&(((qcb_addr (sg) ((qID (q))))) # "os_q" ->ₛ "OSQPtr")) # Ptr |->_ **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) # UChar |-> 2 **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> qcb_addr sg q.(qID) **
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) # UShort |-> q_del_event_count node **
    sg.(g_OSQFreeList) # Ptr |-> queue_free_head sg free **
    sg.(g_OSEventFreeList) # Ptr |-> q_del_event_free_head sg state.
Proof.
  intros environment critical saved_local sg caller active mask saved before acquired eid observed
    initial state node processed waiting option q.
  unfold q_del_pointer_context; Intros.
  destruct H as [Hfacts [Hzero [Hq [Hempty [Hqvalid Hoption]]]]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  destruct (q_del_event_layout__recycle_and_protected_errors sg eid Hprofile Heid)
    as [Htypeaddr [Hptraddr [Hcntaddr Hgrpaddr]]].
  rewrite Htypeaddr, Hptraddr, Hcntaddr,
    (q_del_qcb_ptr_layout__recycle_and_protected_errors sg q Hprofile Hqvalid).
  sep_apply_l_atomic (q_post_pointer_merge sg state eid node q Hvalid Hnode Htype Hq).
  sep_apply_l_atomic (q_post_queue_split sg state eid node q Hnode Htype Hq Hempty).
  Intros free slots.
  unfold q_post_queue_frame.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid node Hnode).
  sep_apply_l_atomic (q_del_event_split_recycle_fields sg state eid node).
  rewrite used_queue_control_block_fields_equiv.
  sep_apply_l_atomic (qcb_storage_split_field sg q.(qID) (qcb_fields_image q) QCBPtr).
  cbn [event_cell event_image event_field_offset encode_event_type
    qcb_cell qcb_fields_image qcb_field_offset].
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value.
  rewrite Htype, Hq; cbn [encode_event_type].
  Exists free slots.
  unfold q_del_recycle_context, q_del_recycle_frame, event_raw_rep_no_eid,
    event_free_root_rep, store_free_queue_list, q_del_event_count, q_del_event_free_head.
  entailer!.
Qed.
Lemma q_del_recycle_effect__recycle_and_protected_errors : forall environment critical sg caller active
  mask saved before acquired eid observed initial state node processed waiting option q free slots,
  q_del_loop_facts environment critical sg caller active mask saved before acquired
    eid observed initial state node processed waiting ->
  q_post_queue_facts sg state eid node q free slots ->
  ((option = 0 /\ state = acquired /\ waiting = 0) \/ option = 1) ->
  q_del_effect sg eid option acquired 0 0 waiting (q_delete_recycle_state sg state eid node q)
    (QDelBufferSnapshot q slots).
Proof.
  intros environment critical sg caller active mask saved before acquired eid observed initial
    state node processed waiting option q free slots Hfacts Hqueue Hoption.
  destruct Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof Hacquire as [Hsave [Hobserved [Hobservedtype [Hinitial [Hinitialtype Hgeneration]]]]].
  pose proof Hqueue as [_ [_ [_ [Hq [Hempty [Hqvalid [Hbinding [Hpart [Hslots Hmodel]]]]]]]]].
  assert (Hzero : q_post_group state node = 0).
  { unfold q_post_group; rewrite Hempty; reflexivity. }
  destruct Hoption as [[-> [-> ->]]| ->].
  - unfold q_del_effect; exists OS_ERR_NONE, false; cbn [encode_os_err_code unsigned_last_nbits].
    split; [reflexivity|]; split; [reflexivity|]; split.
    + unfold q_delete_critical; exists node; split; [exact Hnode|].
      cbn [unsigned_last_nbits]. fold (q_post_group acquired node).
      rewrite Hzero; cbn; exists q; auto.
    + unfold q_del_buffer_release; split; [reflexivity|].
      exists acquired, node; repeat split; auto.
  - assert (Hbroadcast : event_broadcast sg eid PendQ 0 PendAbort acquired processed state).
    { eapply q_pend_abort_progress_done; eassumption. }
    unfold q_del_effect; exists OS_ERR_NONE, (negb (Z.eqb (q_post_group acquired initial) 0)).
    split; [reflexivity|]; split.
    + rewrite Hwaiting; unfold q_del_waiting.
      destruct (Z.eqb (q_post_group acquired initial) 0); reflexivity.
    + split.
      * unfold q_delete_critical; exists initial; split; [exact Hinitial|].
        change (exists priorities ready node' q',
          event_broadcast sg eid PendQ 0 PendAbort acquired priorities ready /\
          q_post_lookup ready eid node' /\ queueFields node' = Some q' /\
          (0, (OS_ERR_NONE, negb (Z.eqb (q_post_group acquired initial) 0))) =
            (0, (OS_ERR_NONE, negb (Z.eqb (q_post_group acquired initial) 0))) /\
          q_delete_recycle_state sg state eid node q = q_delete_recycle_state sg ready eid node' q').
        exists processed, state, node, q; auto.
      * unfold q_del_buffer_release; split; [reflexivity|].
        exists state, node; repeat split; auto; right; split; [reflexivity|eauto].
Qed.
Lemma q_del_recycle_restore__recycle_and_protected_errors : forall environment critical saved_local
  sg caller active mask saved pe before acquired eid observed initial state node processed waiting option q free slots,
  pe = event_addr sg eid -> pe <> 0 ->
  q_del_recycle_context environment critical saved_local sg caller active mask saved before acquired
    eid observed initial state node processed waiting option q free slots **
    (&(((qcb_addr (sg) ((qID (q))))) # "os_q" ->ₛ "OSQPtr")) # Ptr |-> queue_free_head sg free **
    sg.(g_OSQFreeList) # Ptr |-> qcb_addr sg q.(qID) **
    (&(pe # "os_event" ->ₛ "OSEventType")) # UChar |-> 0 **
    (&(pe # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> q_del_event_free_head sg state **
    (&(pe # "os_event" ->ₛ "OSEventCnt")) # UShort |-> 0 **
    sg.(g_OSEventFreeList) # Ptr |-> pe |--
  q_del_restore_pre environment critical saved_local sg caller active mask saved pe eid option before acquired
    (q_delete_recycle_state sg state eid node q) 0 0 waiting (QDelBufferSnapshot q slots) **
    q_del_buffer_rep (QDelBufferSnapshot q slots).
Proof.
  intros environment critical saved_local sg caller active mask saved pe before acquired eid observed
    initial state node processed waiting option q free slots Hpe Hnonzero.
  unfold q_del_recycle_context; Intros.
  destruct H as [Hfacts [Hqueue Hoption]].
  pose proof Hfacts as [Hacquire [Hprofile [Heid [Hint [Hwaiting [Hvalid [Hnode [Htype Hprogress]]]]]]]].
  pose proof Hqueue as [_ [_ [_ [Hq [Hempty [Hqvalid Hrest]]]]]].
  pose proof (q_del_recycle_effect__recycle_and_protected_errors _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hfacts Hqueue Hoption) as Heffect.
  assert (Hreleased : UCOS2_state_inv sg (q_delete_recycle_state sg state eid node q)).
  { unfold q_delete_recycle_state; eapply UCOS2_queue_recycle_preserves_validity; eassumption. }
  pose proof (q_post_acquire_original_type _ _ _ _ _ _ _ _ _ _ _ _ Hacquire) as Hbeforetype.
  destruct (q_del_event_layout__recycle_and_protected_errors sg eid Hprofile Heid)
    as [Htypeaddr [Hptraddr [Hcntaddr Hgrpaddr]]].
  rewrite Hpe, Htypeaddr, Hptraddr, Hcntaddr,
    (q_del_qcb_ptr_layout__recycle_and_protected_errors sg q Hprofile Hqvalid).
  unfold event_addr, OSEventType_off, OSEventPtr_off, OSEventCnt_off.
  sep_apply (q_del_recycle_merge_world sg state eid node q free slots Hqueue).
  sep_apply_l_atomic (q_post_mask_frame_event_update environment critical saved_local sg active saved acquired
    state (q_delete_recycle_state sg state eid node q) eq_refl).
  unfold q_del_restore_pre; rewrite q_post_masked_equiv.
  pose proof (proj1 Hacquire) as Hsave.
  assert (Hnonzero' : event_addr sg eid <> 0) by (rewrite <- Hpe; exact Hnonzero).
  entailer!.
Qed.
