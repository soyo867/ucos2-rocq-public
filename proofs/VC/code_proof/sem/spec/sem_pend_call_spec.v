Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.
Local Open Scope monad_scope.

(** Source-faithful staged relations for V2.93.01 OSSemPend.  This file
    proves the independent prefix/count resources and makes the remaining
    call-boundary obligations visible.  It is not a complete C proof and
    does not promote ready/current/wait effects to a public precondition.
    All unmasked heap observations retain the common conditional CPU/CSL
    boundary of the adopted semaphore functions. *)
Definition sem_pend_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgSafetyCritical) = false /\
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false.

Definition sem_pend_error_cell (perr : addr) : Assertion := perr # UChar |->_ .

(** The selected profile has no perr NULL test: its uninitialized byte is
    a caller-owned writable cell. NULL pevent returns before any ECB read;
    a nonnull public handle may be either used or recycled FREE. Private
    ECB storage does not follow from a numerical ID.  The handle lifetime
    condition is needed only on the ordered arm which actually reaches
    the first Save. It is not retained across the blocking interval. *)
Definition sem_pend_call_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
   sem_query_public_slot before eid observed /\
   (event_slot_type_value before.(EventState) eid = 3 ->
    before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
    mutex_query_handle_protocol critical sg invocation eid)).

Definition sem_pend_precritical_error
  (pevent type_byte int_nesting lock_nesting : Z) : option OSErrCode :=
  if Z.eqb pevent 0 then Some OS_ERR_PEVENT_NULL
  else sem_pend_context_error type_byte int_nesting lock_nesting.

Lemma sem_pend_precritical_null : forall type_byte int_nesting lock_nesting,
  sem_pend_precritical_error 0 type_byte int_nesting lock_nesting = Some OS_ERR_PEVENT_NULL.
Proof. reflexivity. Qed.

Lemma sem_pend_precritical_type : forall pevent type_byte int_nesting lock_nesting,
  pevent <> 0 -> type_byte <> 3 ->
  sem_pend_precritical_error pevent type_byte int_nesting lock_nesting = Some OS_ERR_EVENT_TYPE.
Proof.
  intros * Hpe Htype; unfold sem_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe); apply sem_pend_context_error_type_first; exact Htype.
Qed.

Lemma sem_pend_precritical_free : forall pevent int_nesting lock_nesting,
  pevent <> 0 ->
  sem_pend_precritical_error pevent 0 int_nesting lock_nesting = Some OS_ERR_EVENT_TYPE.
Proof. intros; apply sem_pend_precritical_type; lia. Qed.

Lemma sem_pend_precritical_isr : forall pevent int_nesting lock_nesting,
  pevent <> 0 -> 0 < int_nesting ->
  sem_pend_precritical_error pevent 3 int_nesting lock_nesting = Some OS_ERR_PEND_ISR.
Proof.
  intros * Hpe Hnest; unfold sem_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe); apply sem_pend_context_error_isr_before_lock; exact Hnest.
Qed.

Lemma sem_pend_precritical_locked : forall pevent lock_nesting,
  pevent <> 0 -> 0 < lock_nesting ->
  sem_pend_precritical_error pevent 3 0 lock_nesting = Some OS_ERR_PEND_LOCKED.
Proof.
  intros * Hpe Hlock; unfold sem_pend_precritical_error.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe); apply sem_pend_context_error_locked; exact Hlock.
Qed.

Lemma sem_pend_precritical_clear : forall pevent,
  pevent <> 0 -> sem_pend_precritical_error pevent 3 0 0 = None.
Proof. intros pevent Hpe; unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hpe); reflexivity. Qed.

Lemma sem_pend_call_input_nonnull : forall critical sg invocation pevent before eid observed,
  sem_pend_call_input critical sg invocation pevent before eid observed -> pevent <> 0 ->
  pevent = event_addr sg eid /\ valid_event_id sg eid /\
  sem_query_public_slot before eid observed /\
  (event_slot_type_value before.(EventState) eid = 3 ->
   before.(IntrState).(intNesting) <= 0 -> before.(IntrState).(lockNesting) <= 0 ->
   mutex_query_handle_protocol critical sg invocation eid).
Proof. intros * [Hzero|[_ Hlive]] Hnonzero; [contradiction|exact Hlive]. Qed.

(** A raw call chain, not a validity/readiness filter. Restore exposes the
    ordinary pre-Sched interval, OS_Sched acquires its own fresh entry and
    may return only according to its actual original-invocation relation;
    the second Save acquires yet another fresh entry.  This definition
    supplies no wait-effect projection or current-task stage theorem. *)
Definition sem_pend_schedule_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context returned : OsSchedCallContext)
  (waiting resumed : UCOS2_Verify_State) : Prop :=
  exists sched_entry scheduled,
    critical_region_interval critical sg context.(os_sched_call_invocation) waiting sched_entry /\
    os_sched_c_return external critical sg sched_entry context returned scheduled /\
    critical_region_interval critical sg context.(os_sched_call_invocation) scheduled resumed.

Definition sem_pend_call_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent timeout : Z) : program UCOS2_Verify_State OSErrCode :=
  fun before code after =>
    (pevent = 0 /\ code = OS_ERR_PEVENT_NULL /\ after = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\
      sem_query_public_slot before eid observed /\
      ((sem_pend_context_error (event_slot_type_value before.(EventState) eid)
          before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code /\
        after = before) \/
       (sem_pend_context_error (event_slot_type_value before.(EventState) eid)
          before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None /\
        exists entry current start checkpoint,
          critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
          mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
          current.(eventGeneration) = observed.(eventGeneration) /\
          sem_pend_first_critical sg eid timeout entry start checkpoint /\
          match start with
          | SemPendAcquired => code = OS_ERR_NONE /\ after = checkpoint
          | SemPendWaiting tid generation =>
              context.(os_sched_call_origin) = RunningInvocation tid generation /\
              exists returned resumed task,
                sem_pend_schedule_return external critical sg context returned checkpoint resumed /\
                resumed.(SchedState).(curTaskID) = Some tid /\
                resumed.(TskState).(inUsedTaskStates) tid = Some task /\
                task.(taskGeneration) = generation /\
                sem_pend_resume_critical sg eid resumed code after
          end))).

Lemma sem_pend_call_null_return : forall external critical sg context timeout before,
  sem_pend_call_program external critical sg context 0 timeout before OS_ERR_PEVENT_NULL before.
Proof. intros; left; auto. Qed.

Lemma sem_pend_call_context_return : forall external critical sg context pevent timeout
  before eid observed code,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_call_program external critical sg context pevent timeout before code before.
Proof.
  intros * Hnonzero Haddr Hid Hslot Herr; right; split; [exact Hnonzero|].
  exists eid, observed; split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|].
  left; auto.
Qed.

Lemma sem_pend_immediate_first_critical : forall sg entry eid current fields timeout,
  mutex_query_lookup entry eid current -> current.(semFields) = Some fields ->
  0 < fields.(semCount) ->
  sem_pend_first_critical sg eid timeout entry SemPendAcquired
    (sem_count_update_state entry eid current (fields.(semCount) - 1)).
Proof.
  intros * Hlookup Hfields Hpositive; exists current, fields.
  split; [exact Hlookup|]; split; [exact Hfields|].
  rewrite (proj2 (Z.ltb_lt _ _) Hpositive); auto.
Qed.

(** The count residual is the adopted full Event/Queue/global frame.
    Its structural split is reused from Post, not Post's increment semantics. *)
Lemma sem_pend_count_merge_decrement : forall sg entry eid current,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> 0 < encode_event_cnt_value current ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> (encode_event_cnt_value current - 1) **
    sem_post_count_frame sg entry eid current |--
  UCOS2_inv sg (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hpositive.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields;
    [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  assert (Hdecrement : sem_fields_consistency current.(waitList)
    {| semCount := encode_event_cnt_value current - 1 |}).
  { rewrite Hcount; apply sem_decrement_preserves_consistency; [exact Hpayload|lia]. }
  unfold sem_post_count_frame.
  sep_apply_l_atomic (UCOS2_inv_merge_sem_count sg entry eid current
    (encode_event_cnt_value current - 1) Hvalid Hlookup Htype Hdecrement); entailer!.
Qed.

Lemma sem_pend_count_merge_unchanged : forall sg entry eid current,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
    sem_post_count_frame sg entry eid current |-- UCOS2_inv sg entry.
Proof.
  intros sg entry eid current Hvalid Hlookup Htype.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields;
    [|contradiction].
  unfold sem_post_count_frame, encode_event_cnt_value; rewrite Htype, Hfields.
  sep_apply_l_atomic (sem_rep_merge_count sg entry.(TskState) eid current fields Htype Hfields).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Lemma sem_pend_resume_success_code : sem_pend_resume_error 0 = OS_ERR_NONE.
Proof. reflexivity. Qed.

Lemma sem_pend_resume_abort_code : sem_pend_resume_error 2 = OS_ERR_PEND_ABORT.
Proof. reflexivity. Qed.

Lemma sem_pend_resume_timeout_code : sem_pend_resume_error 1 = OS_ERR_TIMEOUT.
Proof. reflexivity. Qed.

(** Exact source stores in the returning tail.  These observations are
    independent of which resume code led to that tail, and do not assert
    that a TCB or global frame can be obtained from an absent current. *)
Lemma sem_pend_cleanup_common_fields : forall multi old,
  (task_event_pend_cleanup multi false old).(stat) = Byte.zero /\
  (task_event_pend_cleanup multi false old).(statPend) = PendOK /\
  (task_event_pend_cleanup multi false old).(eventPtr) = None /\
  (task_event_pend_cleanup multi false old).(dly) = old.(dly) /\
  (task_event_pend_cleanup multi false old).(msg) = old.(msg) /\
  (task_event_pend_cleanup multi false old).(taskGeneration) = old.(taskGeneration).
Proof. intros []; repeat split; reflexivity. Qed.

(** Both Pend's prefix and common tail write three cells of one complete
    TCB. The third cell is Dly in the prefix, EventPtr in the tail. The
    other concrete fields (including padding) remain in this exact list
    residual, rather than in an abstract slice or another copy of a TCB. *)
Definition sem_pend_tcb_residual (base : addr) (image : TCBCommonImage)
  (third : TCBField) : Assertion :=
  tcb64_fields_rep base (remove TCBField_eq_dec third
    (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))) image.

Lemma sem_pend_tcb_fields_remove_nodup : forall field fields,
  NoDup fields -> NoDup (remove TCBField_eq_dec field fields).
Proof.
  intros field fields Hnd; induction Hnd as [|head rest Hnot Hnd IH]; [constructor|].
  simpl; destruct (TCBField_eq_dec field head); [exact IH|].
  constructor; [intro Hin; apply Hnot; apply in_remove in Hin; tauto|exact IH].
Qed.

Lemma sem_pend_tcb_three_fields_split : forall base image third,
  third <> TCBStat -> third <> TCBStatPend ->
  tcb64_storage_rep base image |--
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base third (image third) ** sem_pend_tcb_residual base image third.
Proof.
  intros base image third Hstat Hpend.
  assert (Hnd1 : NoDup (remove TCBField_eq_dec TCBStat tcb_fields))
    by (apply sem_pend_tcb_fields_remove_nodup, tcb_fields_nodup).
  assert (Hnd2 : NoDup (remove TCBField_eq_dec TCBStatPend
      (remove TCBField_eq_dec TCBStat tcb_fields)))
    by (apply sem_pend_tcb_fields_remove_nodup; exact Hnd1).
  assert (HinPend : In TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))
    by (apply in_in_remove; [discriminate|apply tcb_fields_complete]).
  assert (HinThird : In third (remove TCBField_eq_dec TCBStatPend
      (remove TCBField_eq_dec TCBStat tcb_fields)))
    by (repeat apply in_in_remove; assumption || apply tcb_fields_complete).
  sep_apply_l_atomic (tcb64_storage_split base image TCBStat).
  unfold tcb64_storage_without.
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBStat tcb_fields) base image TCBStatPend Hnd1 HinPend).
  sep_apply_l_atomic (tcb64_fields_rep_split
    (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))
    base image third Hnd2 HinThird).
  unfold sem_pend_tcb_residual; entailer!.
Qed.

Lemma sem_pend_tcb_three_fields_merge_updated : forall base image third status pend value,
  third <> TCBStat -> third <> TCBStatPend ->
  tcb_cell base TCBStat (Some status) **
  tcb_cell base TCBStatPend (Some pend) **
  tcb_cell base third (Some value) ** sem_pend_tcb_residual base image third |--
  tcb64_storage_rep base (tcb_write
    (tcb_write (tcb_write image TCBStat (Some status)) TCBStatPend (Some pend)) third (Some value)).
Proof.
  intros base image third status pend value Hstat Hpend.
  assert (Hnd1 : NoDup (remove TCBField_eq_dec TCBStat tcb_fields))
    by (apply sem_pend_tcb_fields_remove_nodup, tcb_fields_nodup).
  assert (Hnd2 : NoDup (remove TCBField_eq_dec TCBStatPend
      (remove TCBField_eq_dec TCBStat tcb_fields)))
    by (apply sem_pend_tcb_fields_remove_nodup; exact Hnd1).
  assert (HinPend : In TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))
    by (apply in_in_remove; [discriminate|apply tcb_fields_complete]).
  assert (HinThird : In third (remove TCBField_eq_dec TCBStatPend
      (remove TCBField_eq_dec TCBStat tcb_fields)))
    by (repeat apply in_in_remove; assumption || apply tcb_fields_complete).
  assert (Hcomm : tcb_write (tcb_write (tcb_write image third (Some value))
      TCBStatPend (Some pend)) TCBStat (Some status) =
    tcb_write (tcb_write (tcb_write image TCBStat (Some status))
      TCBStatPend (Some pend)) third (Some value)).
  { apply functional_extensionality; intro field; unfold tcb_write, field_update.
    destruct (TCBField_eq_dec field third), (TCBField_eq_dec field TCBStat),
      (TCBField_eq_dec field TCBStatPend); congruence. }
  rewrite <- Hcomm; unfold sem_pend_tcb_residual.
  sep_apply_l_atomic (tcb64_fields_rep_merge_updated
    (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))
    base image third (Some value) Hnd2 HinThird).
  sep_apply_l_atomic (tcb64_fields_rep_merge_updated
    (remove TCBField_eq_dec TCBStat tcb_fields)
    base (tcb_write image third (Some value)) TCBStatPend (Some pend) Hnd1 HinPend).
  fold (tcb64_storage_without base TCBStat
    (tcb_write (tcb_write image third (Some value)) TCBStatPend (Some pend))).
  sep_apply_l_atomic (tcb64_storage_merge_updated base
    (tcb_write (tcb_write image third (Some value)) TCBStatPend (Some pend)) TCBStat (Some status)).
  entailer!.
Qed.

Lemma sem_pend_tcb_merge_wait_prefix : forall sg tid old timeout,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 1)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBDly |--
  tcb64_storage_rep (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)).
Proof.
  intros; rewrite task_prepare_event_wait_image_eq.
  apply sem_pend_tcb_three_fields_merge_updated; discriminate.
Qed.

Lemma sem_pend_tcb_merge_cleanup : forall sg tid old,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBEventPtr |--
  tcb64_storage_rep (task_slot_addr sg tid)
    (task_tcb64_image sg (task_event_pend_cleanup false false old)).
Proof.
  intros sg tid old.
  assert (Himage : task_tcb64_image sg (task_event_pend_cleanup false false old) =
    tcb_write (tcb_write (tcb_write (task_tcb64_image sg old) TCBStat (Some 0))
      TCBStatPend (Some 0)) TCBEventPtr (Some 0)).
  { apply functional_extensionality; intros []; reflexivity. }
  rewrite Himage; apply sem_pend_tcb_three_fields_merge_updated; discriminate.
Qed.

Definition sem_pend_full_task_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (tid : TaskID) : Assertion :=
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sched_raw_rep sg entry.(TskState) entry.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry.

Lemma sem_pend_full_task_split : forall sg entry tid old,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_inv sg entry |-- tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg old) **
    sem_pend_full_task_frame sg entry tid.
Proof.
  intros sg entry tid old Hvalid Hold; pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  rewrite UCOS2_inv_open_task_storage_sched; Intros.
  sep_apply_l_atomic (sem_post_task_storage_split sg entry.(TskState) tid old Hmulti Hprofiling Hold).
  unfold sem_pend_full_task_frame; entailer!.
Qed.

(** A prefix temporarily disagrees with the ready list and has not yet
    installed EventPtr. Reconstruct the actual public TCB storage only;
    do not claim UCOS2_inv during that source transient. *)
Lemma sem_pend_full_task_merge_storage : forall sg entry tid new,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg new) **
    sem_pend_full_task_frame sg entry tid |--
  task_public_storage sg (glob_task_set_usedtask entry.(TskState) tid new) **
  sched_raw_rep sg entry.(TskState) entry.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg entry.
Proof.
  intros sg entry tid new Hmulti Hprofile; unfold sem_pend_full_task_frame.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid new Hmulti Hprofile).
  entailer!.
Qed.

(** The projected source family is an internal coverage premise, not a
    restriction added to OSSemPend's public precondition. Its actual
    operations prove their wait effects in sem_pend_wait_trace_spec.
    The global client registry and hook source binding must still be
    extended before this can cover every enabled interference action. *)
Lemma sem_pend_schedule_return_projection :
  forall external critical sg context returned waiting resumed tid old,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  sem_pend_schedule_return external critical sg context returned waiting resumed ->
  waiting.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection waiting.(TskState) resumed.(TskState) tid old.
Proof.
  intros * Hclients Hhook [entry [scheduled [Hbefore [Hsched Hafter]]]] Hold.
  destruct (sem_pend_resumption_trace_projection _ sg context.(os_sched_call_invocation) None
    waiting false entry Hclients Hbefore tid old Hold) as [entered [Hentered Hfirst]].
  destruct (sem_pend_sched_return_projection external critical sg entry context returned scheduled
    tid entered Hclients Hhook Hsched Hentered) as [current [Hcurrent Hsecond]].
  destruct (sem_pend_resumption_trace_projection _ sg context.(os_sched_call_invocation) None
    scheduled false resumed Hclients Hafter tid current Hcurrent) as [last [Hlast Hthird]].
  exists last; split; [exact Hlast|].
  eapply rt_trans; [exact Hfirst|eapply rt_trans; eassumption].
Qed.

Lemma sem_pend_schedule_return_preserves_continuation :
  forall external critical sg context returned waiting resumed tid old eid generation,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_projected_source_client external.(os_sched_hook_action) ->
  sem_pend_schedule_return external critical sg context returned waiting resumed ->
  waiting.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  exists current, resumed.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros * Hclients Hhook Hreturn Hold Hcont.
  destruct (sem_pend_schedule_return_projection external critical sg context returned waiting resumed
    tid old Hclients Hhook Hreturn Hold) as [current [Hcurrent Heffects]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** Source-facing views used by the literal C annotation successor.  These
    definitions do not add current/ready to the public call domain.  The
    corresponding source-entry cuts remain actual generated obligations. *)
Definition sem_pend_c_program external critical sg context pevent timeout
  : program UCOS2_Verify_State Z :=
  fun before error after => exists code,
    error = encode_os_err_code code /\
    sem_pend_call_program external critical sg context pevent timeout before code after.

(** The annotation frontend treats [program] as an opaque type constructor.
    This proposition is its explicit application, not a different relation. *)
Definition sem_pend_c_result external critical sg context pevent timeout before error after : Prop :=
  sem_pend_c_program external critical sg context pevent timeout before error after.

Definition sem_pend_save_facts critical sg invocation mask saved before entry : Prop :=
  UCOS2_state_inv sg before /\ critical_region_interval critical sg invocation before entry /\
  interrupt_saved_value mask saved /\ UCOS2_state_inv sg entry.

Definition sem_pend_interrupt_frame sg state : Assertion :=
  UCOS2_raw_rep_missing_module sg state InterruptModule.

Definition sem_pend_sched_without_current sg state : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(SchedState).(readyList) state.(TskState) **
  sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if state.(SchedState).(isRunning) then 1 else 0).

Definition sem_pend_prefix_frame sg entry tid old : Assertion :=
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBDly **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sem_pend_sched_without_current sg entry ** UCOS2_raw_rep_missing_task_storage_sched sg entry.

Definition sem_pend_cleanup_frame sg entry tid old : Assertion :=
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBEventPtr **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sem_pend_sched_without_current sg entry ** UCOS2_raw_rep_missing_task_storage_sched sg entry.

Definition sem_pend_wait_entry sg entry eid current tid old : Prop :=
  UCOS2_state_inv sg entry /\ encode_event_cnt_value current = 0 /\
  entry.(SchedState).(curTaskID) = Some tid /\
  entry.(TskState).(inUsedTaskStates) tid = Some old /\
  mutex_query_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  old.(curPrio) <> sg.(osLowestPrio) /\ old.(eventPtr) = None /\
  old.(eventMultiWaitEvents) = [] /\ old.(tcbFlagNode) = 0 /\
  In tid entry.(SchedState).(readyList) /\ event_object_layout_prop sg eid.

Definition sem_pend_wait_call_frame sg entry eid current tid old timeout : Assertion :=
  event_task_wait_tcb_rest (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  UCharArray.missing_i sg.(g_OSRdyTbl) (old.(curPrio) / 8) 0 8
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte entry.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg entry.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> entry.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0) **
  event_task_wait_event_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (old.(curPrio) / 8) (event_image sg entry.(TskState) current) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg entry.

Definition sem_pend_resume_entry sg resumed eid tid old : Prop :=
  UCOS2_state_inv sg resumed /\ resumed.(SchedState).(curTaskID) = Some tid /\
  resumed.(TskState).(inUsedTaskStates) tid = Some old /\
  sem_pend_resume_registration eid old /\ In tid resumed.(SchedState).(readyList).

Definition sem_pend_wait_call_post sg entry eid current tid old timeout : Assertion :=
  event_task_wait_post sg.(g_OSTCBCur) (task_slot_addr sg tid) (event_addr sg eid)
    sg.(g_OSRdyGrp) sg.(g_OSRdyTbl) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8))
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState)) **
  sem_pend_wait_call_frame sg entry eid current tid old timeout.

Definition sem_pend_remove_call_frame sg entry eid current tid old : Assertion :=
  event_task_remove_tcb_frame (task_slot_addr sg tid) (task_tcb64_image sg old) **
  event_task_remove_ecb_frame sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8) **
  store_prio_tbl sg entry.(TskState).(prioTbl) ** sem_post_task_frame sg entry.(TskState) tid **
  sem_pend_sched_without_current sg entry **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg entry.

Definition sem_pend_call_post external platform critical sg context mask pevent timeout perr before X : Assertion :=
  EX after returned error,
    coq_prop (sem_pend_c_program external critical sg context pevent timeout before error after /\
      safeExec (LastSeen after) (return error) X) **
    (perr # UChar |-> error **
     sem_post_return_resources external platform critical sg context returned mask after).

(** [coq_prop] uses the generated spatial convention, as in SemPost.
    This retains the metadata TT frame; every concrete owner remains in
    [sem_post_return_resources] and the caller's output byte. *)

Lemma sem_pend_interrupt_split : forall sg state,
  UCOS2_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
  (sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
   sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) ** sem_pend_interrupt_frame sg state).
Proof.
  intros; rewrite (UCOS2_inv_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state, sem_pend_interrupt_frame; entailer!.
Qed.

Lemma sem_pend_interrupt_merge : forall sg state,
  UCOS2_state_inv sg state ->
  sg.(g_OSIntNesting) # UChar |-> state.(IntrState).(intNesting) **
  sg.(g_OSLockNesting) # UChar |-> state.(IntrState).(lockNesting) ** sem_pend_interrupt_frame sg state |--
  UCOS2_inv sg state.
Proof.
  intros sg state Hvalid; rewrite (UCOS2_inv_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state, sem_pend_interrupt_frame.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) state.(IntrState).(intNesting)).
  prop_apply_p (store_uchar_range sg.(g_OSLockNesting) state.(IntrState).(lockNesting)).
  entailer!; unfold interrupt_in_range; lia.
Qed.

Lemma sem_pend_save_consequence : forall critical sg invocation mask saved before entry,
  UCOS2_state_inv sg before -> critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved -> sem_pend_save_facts critical sg invocation mask saved before entry.
Proof.
  intros; unfold sem_pend_save_facts.
  split; [exact H|]; split; [exact H0|]; split; [exact H1|].
  exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ H0 H)).
Qed.

Lemma sem_pend_restore_consequence : forall platform critical sg invocation origin mask saved before entry checkpoint,
  sem_pend_save_facts critical sg invocation mask saved before entry ->
  UCOS2_state_inv sg checkpoint ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
  critical_region_outside critical sg invocation checkpoint |--
  mutex_query_closed platform critical sg invocation origin mask checkpoint.
Proof.
  intros * [_ [_ [[Hsaved Hmask] _]]] Hvalid.
  rewrite Hmask; unfold mutex_query_closed; entailer!.
Qed.

Lemma sem_pend_c_null_return : forall external critical sg context timeout before,
  sem_pend_c_program external critical sg context 0 timeout before 4 before.
Proof. intros; exists OS_ERR_PEVENT_NULL; split; [reflexivity|apply sem_pend_call_null_return]. Qed.

Lemma sem_pend_c_context_return : forall external critical sg context pevent timeout before eid observed code,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some code ->
  sem_pend_c_program external critical sg context pevent timeout before (encode_os_err_code code) before.
Proof.
  intros; exists code; split; [reflexivity|eapply sem_pend_call_context_return; eassumption].
Qed.

Lemma sem_pend_c_immediate_return :
  forall external critical sg context pevent timeout before eid observed mask saved entry current,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_query_acquire_facts critical sg context.(os_sched_call_invocation) eid mask saved before entry observed current ->
  0 < encode_event_cnt_value current ->
  sem_pend_c_program external critical sg context pevent timeout before 0
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
Proof.
  intros * Hnonnull Haddr Hid Hslot Hcontext Hacquire Hpositive.
  destruct Hacquire as [Hinterval [Hvalid [Hsaved [Hlookup0 [Hlookup [Htype0 [Htype Hgen]]]]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  exists OS_ERR_NONE; split; [reflexivity|].
  right; split; [exact Hnonnull|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|].
  right; split; [exact Hcontext|].
  exists entry, current, SemPendAcquired,
    (sem_count_update_state entry eid current (encode_event_cnt_value current - 1)).
  split; [exact Hinterval|]; split; [exact Hlookup|]; split; [exact Htype|].
  split; [exact Hgen|]; split.
  - rewrite Hcount; eapply sem_pend_immediate_first_critical; eauto; lia.
  - auto.
Qed.

Lemma sem_pend_call_post_from_result : forall external platform critical sg context returned mask
  pevent timeout perr before after error X,
  sem_pend_c_program external critical sg context pevent timeout before error after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_c_program external critical sg context pevent timeout)) sem_query_observe_error) X ->
  TT ** mutex_query_closed platform critical sg context.(os_sched_call_invocation) context.(os_sched_call_origin) mask after **
  os_sched_context_resources external returned ** unmap_table_rep sg ** perr # UChar |-> error |--
  sem_pend_call_post external platform critical sg context mask pevent timeout perr before X.
Proof.
  intros * Hresult Hexec.
  pose proof (sem_query_safe_return _ _ _ _ _ Hresult Hexec) as Hsafe.
  unfold sem_pend_call_post; Exists after returned error.
  unfold mutex_query_closed, sem_post_return_resources; entailer!.
Qed.

Lemma sem_pend_wait_entry_row_in_range : forall sg entry eid current tid old,
  sem_pend_wait_entry sg entry eid current tid old -> 0 <= old.(curPrio) / 8 < 8.
Proof.
  intros * [Hvalid [_ [_ [Hold _]]]].
  pose proof Hvalid as [Hprofile [Htasks _]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority tid old Hold); unfold task_priority_in_range in Hpriority.
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Lemma sem_pend_task_priority_in_range : forall sg entry tid old,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) tid = Some old ->
  0 <= old.(curPrio) <= 63.
Proof.
  intros * [Hprofile [Htasks _]] Hold.
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority tid old Hold); unfold task_priority_in_range in Hpriority; lia.
Qed.

(** The literal three prefix stores are reassembled only as TCB storage,
    then split for the actual raw OS_EventTaskWait contract.  No global
    validity is claimed for the transient prefix. *)
Lemma sem_pend_wait_prefix_split_call : forall sg entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (Z.lor (encode_task_status old.(stat)) 1)) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBDly (Some timeout) **
  sem_pend_prefix_frame sg entry tid old |--
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
  tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
  tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
  (&(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl") + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8) **
  &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    # UChar |-> encode_event_wait_grp current.(waitList) entry.(TskState) **
  (sg.(g_OSRdyTbl) + old.(curPrio) / 8 * sizeof(UCHAR))
    # UChar |-> encode_ready_tbl_at_or entry.(SchedState).(readyList) entry.(TskState) (old.(curPrio) / 8) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sem_pend_wait_call_frame sg entry eid current tid old timeout.
Proof.
  intros * Hentry.
  pose proof (sem_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [_ [_ [Hold [He [Htype [Hnonidle [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  unfold sem_pend_prefix_frame.
  sep_apply_l_atomic (sem_pend_tcb_merge_wait_prefix sg tid old timeout).
  sep_apply_l_atomic (event_task_wait_tcb_split (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))).
  unfold sem_pend_sched_without_current, UCOS2_raw_rep_missing_task_storage_sched.
  sep_apply_l_atomic (sched_rows_split_cell sg entry.(TskState) entry.(SchedState).(readyList)
    (old.(curPrio) / 8) Hrow).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_wait_event_split_c_fields sg eid
    (event_image sg entry.(TskState) current) (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState)) Hlayout Hrow
    (event_table_image_eq sg entry.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold sem_pend_wait_call_frame, UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [task_tcb64_image task_prepare_event_wait].
  try rewrite Hnone; cbn [encode_event_link].
  entailer!.
  cbn [task_prepare_event_wait eventPtr curPrio tcb_y_of_prio].
  rewrite Hnone; reflexivity.
Qed.

Lemma sem_pend_wait_call_merge : forall sg entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  sem_pend_wait_call_post sg entry eid current tid old timeout |--
  UCOS2_inv sg (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Hentry.
  pose proof (sem_pend_wait_entry_row_in_range _ _ _ _ _ _ Hentry) as Hrow.
  destruct Hentry as [Hvalid [Hcount [Hcur [Hold [He [Htype [Hnonidle [Hnone [Hmulti0 [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [[Hrdy Hmeta] [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  pose proof (Hpriorities tid old Hold) as Hrange.
  assert (Hprio : valid_task_prio sg old.(curPrio))
    by (unfold valid_task_prio, task_priority_in_range in *; lia).
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem) by (rewrite Htype; reflexivity).
  assert (Hunavailable : event_wait_resource_unavailable current).
  { pose proof Hevents as [_ [_ [_ [_ [Hpayload _]]]]].
    specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
    unfold event_wait_resource_unavailable; rewrite Htype in Hpayload |- *.
    destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
    unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount; exact Hcount. }
  assert (Hnotowner : forall m, current.(eventType) = OS_EVENT_TYPE_MUTEX ->
    current.(mutexFields) = Some m -> m.(mfOwner) <> Some tid) by (intros; congruence).
  pose proof (sched_ready_in_range_implies_structure sg entry.(TskState) entry.(SchedState) Hrdy) as Hstructure.
  unfold sem_pend_wait_call_post, sem_pend_wait_call_frame, event_task_wait_post.
  pose proof (event_task_wait_tcb_merge_event_ptr (task_slot_addr sg tid)
    (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) (event_addr sg eid)) as Htcb.
  change (tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (event_addr sg eid)) **
    tcb_cell (task_slot_addr sg tid) TCBY (Some (old.(curPrio) / 8)) **
    tcb_cell (task_slot_addr sg tid) TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
    tcb_cell (task_slot_addr sg tid) TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
    event_task_wait_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout)) |--
    tcb64_storage_rep (task_slot_addr sg tid)
      (tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))
        TCBEventPtr (Some (event_addr sg eid)))) in Htcb.
  cbn [tcb_cell tcb_field_address] in Htcb.
  unfold tcb_y_of_prio in Htcb.
  sepcon_assoc_change.
  sep_apply_l_atomic Htcb.
  assert (Himage : tcb_write (task_tcb64_image sg (task_prepare_event_wait old PendSem timeout))
    TCBEventPtr (Some (event_addr sg eid)) =
    task_tcb64_image sg (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)))
    by (symmetry; apply task_set_event_ptr_image_eq).
  rewrite Himage.
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)) Hmulti Hprofiling).
  sep_apply_l_atomic (event_task_wait_event_merge_c_fields sg eid (event_image sg entry.(TskState) current)
    (old.(curPrio) / 8)
    (encode_event_wait_tbl_at_or current.(waitList) entry.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) entry.(TskState))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) Hlayout Hrow).
  sep_apply_l_atomic (event_task_wait_ready_merge_removed_task sg entry.(TskState) entry.(SchedState)
    tid old Hsg Hunique Hold Hrange Hstructure Hrow).
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_pend_storage sg entry eid current tid old PendSem timeout
    Hvalid He Hold Hprio Hnone Hmulti0 Hflag Hready Hkind Hunavailable Hnotowner heap).
  revert heap Hheap.
  match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
  cbn [event_pend_state event_wait_state replace_SchedS replace_EventS replace_TskS TskState SchedState].
  rewrite <- Hindex; unfold sched_raw_rep, sched_physical_rep.
  cbn [sched_remove_ready_task curSchedPrio highRdyPrio curTaskID highRdyTid ctxSwCtr isRunning].
  try rewrite Hcur; cbn [encode_task_link].
  entailer!.
  unfold sched_remove_ready_task, tcb_bit_x_of_prio, tcb_bit_y_of_prio.
  cbn; rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma sem_pend_tcb_merge_cleanup_unchanged : forall sg tid old,
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  sem_pend_tcb_residual (task_slot_addr sg tid) (task_tcb64_image sg old) TCBEventPtr |--
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg old).
Proof.
  intros.
  assert (Himage : tcb_write (tcb_write (tcb_write (task_tcb64_image sg old)
    TCBStat (Some (encode_task_status old.(stat)))) TCBStatPend (Some (encode_pend_status old.(statPend))))
    TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) = task_tcb64_image sg old).
  { apply functional_extensionality; intros []; reflexivity. }
  rewrite <- Himage at 2.
  apply sem_pend_tcb_three_fields_merge_updated; discriminate.
Qed.

Lemma sem_pend_resume_split_remove_call : forall sg resumed eid tid old current,
  sem_pend_resume_entry sg resumed eid tid old -> mutex_query_lookup resumed eid current ->
  event_object_layout_prop sg eid ->
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  sem_pend_cleanup_frame sg resumed tid old |--
  event_task_remove_pre (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old.
Proof.
  intros * [Hvalid [Hcur [Hold [Hregistration Hready]]]] He Hlayout.
  pose proof Hvalid as [Hprofile [Htasks _]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority tid old Hold); unfold task_priority_in_range in Hpriority.
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8)
    by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  unfold sem_pend_cleanup_frame.
  sep_apply_l_atomic (sem_pend_tcb_merge_cleanup_unchanged sg tid old).
  unfold UCOS2_raw_rep_missing_task_storage_sched.
  sep_apply_l_atomic (event_raw_rep_split_eid sg resumed.(TskState) resumed.(EventState) eid current He).
  unfold used_event_rep.
  sep_apply_l_atomic (event_task_remove_storage_layout_split sg eid (task_slot_addr sg tid)
    (task_tcb64_image sg old) (event_image sg resumed.(TskState) current) (old.(curPrio) / 8)
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) Hlayout Hrow eq_refl eq_refl eq_refl
    (event_table_image_eq sg resumed.(TskState) current (old.(curPrio) / 8) Hrow) eq_refl).
  unfold sem_pend_remove_call_frame, UCOS2_raw_rep_missing_task_storage_sched_event; entailer!.
Qed.

(** Source histories are internal annotation facts.  Each constructor is
    justified by actual call/store observations; none is a public entry
    restriction or an assumption that scheduling eventually returns. *)
Definition sem_pend_wait_origin critical sg context mask saved before observed
  entry eid current tid old : Prop :=
  sem_query_acquire_facts critical sg context.(os_sched_call_invocation) eid mask saved
    before entry observed current /\
  sem_pend_wait_entry sg entry eid current tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  kernel_call_task_source context entry /\
  sched_current_consistency entry.(TskState) entry.(SchedState).

Definition sem_pend_wait_history critical sg context mask before observed eid timeout waiting : Prop :=
  UCOS2_state_inv sg waiting /\ kernel_call_task_source context waiting /\
  sched_current_consistency waiting.(TskState) waiting.(SchedState) /\
  exists saved entry current tid old,
    sem_pend_wait_origin critical sg context mask saved before observed entry eid current tid old /\
    waiting = event_pend_state sg entry eid current tid old PendSem timeout.

Definition sem_pend_scheduled_history external critical sg context mask before observed eid timeout scheduled : Prop :=
  exists waiting selected returned,
    sem_pend_wait_history critical sg context mask before observed eid timeout waiting /\
    os_sched_acquire_safety external critical sg context waiting /\
    critical_region_interval critical sg context.(os_sched_call_invocation) waiting selected /\
    os_sched_c_return external critical sg selected context returned scheduled.

Definition sem_pend_resume_origin external critical sg context mask before observed eid timeout resumed tid old : Prop :=
  sem_pend_resume_entry sg resumed eid tid old /\
  context.(os_sched_call_origin) = RunningInvocation tid old.(taskGeneration) /\
  exists waiting returned,
    sem_pend_wait_history critical sg context mask before observed eid timeout waiting /\
    sem_pend_schedule_return external critical sg context returned waiting resumed.

Definition sem_pend_cleanup_entry sg cleaning tid node : Prop :=
  UCOS2_state_inv sg cleaning /\ cleaning.(SchedState).(curTaskID) = Some tid /\
  cleaning.(TskState).(inUsedTaskStates) tid = Some node /\
  node.(eventPtr) = None /\ node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0 /\
  In tid cleaning.(SchedState).(readyList).

Definition sem_pend_cleanup_origin external critical sg context mask before observed eid timeout error cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  exists resumed old code,
    sem_pend_resume_origin external critical sg context mask before observed eid timeout resumed tid old /\
    error = encode_os_err_code code /\
    sem_pend_resume_critical sg eid resumed code (event_pend_cleanup_state sg false cleaning tid node).

(** ABI facts are needed only when an actual first-Save entry observes an
    empty semaphore. The positive-count and ordered error branches do not
    access these cells. This predicate contains no task/protocol premise. *)
Definition sem_pend_blocking_layout critical sg invocation before eid gcur ggrp gtbl : Prop :=
  forall entry current,
    critical_region_interval critical sg invocation before entry ->
    mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
    encode_event_cnt_value current = 0 ->
    gcur = sg.(g_OSTCBCur) /\ ggrp = sg.(g_OSRdyGrp) /\ gtbl = sg.(g_OSRdyTbl) /\
    event_object_layout_prop sg eid.

Lemma sem_pend_resume_cleanup_without_timeout :
  forall external critical sg context mask before observed eid timeout resumed tid old,
  sem_pend_resume_origin external critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) <> PendTimeout ->
  sem_pend_cleanup_origin external critical sg context mask before observed eid timeout
    (encode_os_err_code (sem_pend_resume_error (encode_pend_status old.(statPend)))) resumed tid old.
Proof.
  intros * Horigin Hnotimeout.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]; split; [exact Hcur|]; split; [exact Hold|].
    split; [destruct old.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]; split; assumption.
  - exists resumed, old, (sem_pend_resume_error (encode_pend_status old.(statPend))).
    split; [exact Horigin|]; split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|]; split; [reflexivity|].
    destruct old.(statPend); reflexivity || contradiction.
Qed.

Lemma sem_pend_resume_cleanup_timeout :
  forall external critical sg context mask before observed eid timeout resumed tid old current,
  sem_pend_resume_origin external critical sg context mask before observed eid timeout resumed tid old ->
  old.(statPend) = PendTimeout -> mutex_query_lookup resumed eid current ->
  sem_pend_cleanup_origin external critical sg context mask before observed eid timeout 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None).
Proof.
  intros * Horigin Htimeout He.
  pose proof Horigin as [[Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hhistory].
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found.
  split.
  - unfold sem_pend_cleanup_entry.
    split; [eapply UCOS2_event_task_remove_preserves_validity; eassumption|].
    split; [exact Hcur|].
    split.
    + cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + split; [reflexivity|]; split; [exact Hmulti|]; split; assumption.
  - exists resumed, old, OS_ERR_TIMEOUT; split; [exact Horigin|]; split; [reflexivity|].
    exists tid, old; split; [exact Hcur|]; split; [exact Hold|].
    rewrite Htimeout; split; [reflexivity|]; exists current; auto.
Qed.

Lemma sem_pend_cleanup_split : forall sg state tid old,
  UCOS2_state_inv sg state -> state.(SchedState).(curTaskID) = Some tid ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_inv sg state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some (encode_event_link sg old.(eventPtr))) **
  sem_pend_cleanup_frame sg state tid old.
Proof.
  intros * Hvalid Hcur Hold.
  sep_apply_l_atomic (sem_pend_full_task_split sg state tid old Hvalid Hold).
  sep_apply_l_atomic (sem_pend_tcb_three_fields_split (task_slot_addr sg tid)
    (task_tcb64_image sg old) TCBEventPtr ltac:(discriminate) ltac:(discriminate)).
  unfold sem_pend_full_task_frame, sem_pend_cleanup_frame, sem_pend_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  cbn [task_tcb64_image]; rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma sem_pend_cleanup_merge : forall sg state tid old,
  sem_pend_cleanup_entry sg state tid old ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
  tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
  sem_pend_cleanup_frame sg state tid old |--
  UCOS2_inv sg (event_pend_cleanup_state sg false state tid old).
Proof.
  intros * [Hvalid [Hcur [Hold [Hnone [Hmulti0 [Hflag Hready]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold sem_pend_cleanup_frame.
  sepcon_assoc_change.
  sep_apply_l_atomic (sem_pend_tcb_merge_cleanup sg tid old).
  sep_apply_l_atomic (sem_post_task_storage_merge sg state.(TskState) tid
    (task_event_pend_cleanup false false old) Hmulti Hprofiling).
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_pend_cleanup sg state tid old false
    Hvalid Hold Hnone Hmulti0 Hflag Hready heap).
  revert heap Hheap.
  match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
  cbn [event_pend_cleanup_state replace_TskS TskState].
  rewrite Hmulti; unfold sem_pend_sched_without_current, sched_raw_rep, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma sem_pend_remove_call_merge : forall sg resumed eid current tid old,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) = PendTimeout ->
  mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old |--
  UCOS2_inv sg (event_task_remove_state resumed eid current tid old).
Proof.
  intros * [Hvalid [Hcur [Hold [[Hmulti0 [Hflag Hregistration]] Hready]]]] Htimeout He Hlayout.
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  pose proof (Hentries eid current He) as [Hcanonical _].
  destruct (proj2 (proj2 Hcanonical) tid Hin) as [found [HpriorityLookup Hprio]].
  assert (found = old) by congruence; subst found.
  unfold sem_pend_remove_call_frame, tcb_bit_x_of_prio, tcb_bit_y_of_prio,
    tcb_x_of_prio, tcb_y_of_prio.
  sepcon_assoc_change.
  sep_apply_l_atomic (event_task_remove_abstract_storage_consequence sg resumed.(TskState)
    eid current tid old (task_slot_addr sg tid) Hlayout Hsg Hunique Hcanonical Hprio Hold).
  sep_apply_l_atomic (sem_post_task_storage_merge sg resumed.(TskState) tid
    (task_set_event_ptr old None) Hmulti Hprofiling).
  fold (used_event_rep sg resumed.(TskState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg resumed.(TskState) resumed.(EventState)
    eid (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  assert (Hindex : sched_raw_rep sg resumed.(TskState) resumed.(SchedState) =
    sched_raw_rep sg (glob_task_set_usedtask resumed.(TskState) tid (task_set_event_ptr old None)) resumed.(SchedState)).
  { apply sched_raw_rep_priority_ext; intros slot HinSlot.
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  intros heap Hheap.
  apply (UCOS2_inv_merge_event_task_remove sg resumed eid current tid old Hvalid He Hin Hold heap).
  revert heap Hheap.
  match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
  cbn [event_task_remove_state replace_TskS replace_EventS TskState SchedState EventState].
  rewrite <- Hindex; unfold sem_pend_sched_without_current, sched_raw_rep, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link]; entailer!.
Qed.

Lemma sem_pend_wait_entry_first_critical : forall sg entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  sem_pend_first_critical sg eid timeout entry (SemPendWaiting tid old.(taskGeneration))
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * [Hvalid [Hcount [Hcur [Hold [He [Htype Hrest]]]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount.
  exists current, fields; split; [exact He|]; split; [exact Hfields|].
  rewrite Hcount; cbn; exists tid, old; repeat split; assumption || reflexivity.
Qed.

Lemma sem_pend_wait_entry_preserves_validity : forall sg entry eid current tid old timeout,
  sem_pend_wait_entry sg entry eid current tid old ->
  UCOS2_state_inv sg (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Hentry.
  destruct Hentry as [Hvalid [Hcount [Hcur [Hold [He [Htype [Hnonidle [Hnone [Hmulti [Hflag [Hready Hlayout]]]]]]]]]]].
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current He); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields; [|contradiction].
  unfold encode_event_cnt_value in Hcount; rewrite Htype, Hfields in Hcount.
  eapply sem_pend_wait_preserves_validity; eauto; lia.
Qed.

Lemma sem_pend_wait_origin_history : forall critical sg context mask saved before observed entry eid current tid old timeout,
  sem_pend_wait_origin critical sg context mask saved before observed entry eid current tid old ->
  sem_pend_wait_history critical sg context mask before observed eid timeout
    (event_pend_state sg entry eid current tid old PendSem timeout).
Proof.
  intros * Horigin; split.
  - eapply sem_pend_wait_entry_preserves_validity; exact (proj1 (proj2 Horigin)).
  - split.
    + destruct Horigin as [Hacquire [Hentry [Horigin [[Hlease [Hactive Hcurrent]] Hcache]]]].
      pose proof Hentry as [_ [_ [_ [Hnode _]]]].
      split; [exact Hlease|]. split.
      * cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState].
        eapply glob_task_set_usedtask_preserves_invocation_active;
          [exact Hnode|reflexivity|exact Hactive].
      * exact Hcurrent.
    + split.
      * destruct Horigin as [Hacquire [Hentry [Horigin [Hsource Hcache]]]].
        pose proof Hentry as [_ [_ [Hcurrent [Hnode _]]]].
        unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
        destruct Hcache as [node [Hlookup Hpriority]].
        assert (node = old) by congruence; subst node.
        unfold sched_current_consistency.
        change (match entry.(SchedState).(curTaskID) with
          | None => entry.(SchedState).(curSchedPrio) = None
          | Some selected => exists node,
              (if Z.eqb selected tid then
                 Some (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid))
               else entry.(TskState).(inUsedTaskStates) selected) = Some node /\
              entry.(SchedState).(curSchedPrio) = Some node.(curPrio)
          end).
        rewrite Hcurrent; exists (task_set_event_ptr (task_prepare_event_wait old PendSem timeout) (Some eid)).
        split; [rewrite Z.eqb_refl; reflexivity|exact Hpriority].
      * exists saved, entry, current, tid, old; auto.
Qed.

Lemma sem_pend_scheduled_history_validity : forall external critical sg context mask before observed eid timeout scheduled,
  sem_pend_scheduled_history external critical sg context mask before observed eid timeout scheduled ->
  UCOS2_state_inv sg scheduled.
Proof.
  intros * [waiting [selected [returned [[Hvalid Hhistory] [Hsafe [Hinterval Hreturn]]]]]].
  eapply sem_post_sched_return_preserves_validity; eassumption.
Qed.

Lemma sem_pend_cleanup_origin_result : forall external critical sg context mask before observed eid
  pevent timeout error cleaning tid node,
  pevent <> 0 -> pevent = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_cleanup_origin external critical sg context mask before observed eid timeout error cleaning tid node ->
  sem_pend_c_program external critical sg context pevent timeout before error
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * Hnonzero Haddr Hid Hslot Hcontext [Hclean [resumed [old [code [Hresume [Herror Hstep]]]]]].
  destruct Hresume as [[Hvalid [Hcur [Hold Hrest]]] [Horigin [waiting [returned [Hhistory Hschedule]]]]].
  destruct Hhistory as [Hwaiting [HwaitingSource [HwaitingCache [saved [entry [current [first_tid [first [HfirstOrigin HwaitingEq]]]]]]]]].
  destruct HfirstOrigin as [Hacquire [Hentry [HfirstOrigin [HfirstSource HfirstCache]]]].
  assert (Hsame : first_tid = tid /\ first.(taskGeneration) = old.(taskGeneration)) by (rewrite Horigin in HfirstOrigin; inversion HfirstOrigin; auto).
  destruct Hsame as [-> Hgeneration].
  pose proof (sem_pend_wait_entry_first_critical sg entry eid current tid first timeout Hentry) as Hfirst.
  destruct Hacquire as [Hinterval [Hentryvalid [Hsaved [Hbefore [Hcurrent [Hbeforetype [Htype Hgen]]]]]]].
  exists code; split; [exact Herror|].
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|].
  right; split; [exact Hcontext|].
  exists entry, current, (SemPendWaiting tid first.(taskGeneration)), waiting.
  split; [exact Hinterval|]; split; [exact Hcurrent|]; split; [exact Htype|].
  split; [exact Hgen|]; split; [rewrite HwaitingEq; exact Hfirst|].
  split; [exact HfirstOrigin|]; exists returned, resumed, old.
  split; [exact Hschedule|]; split; [exact Hcur|]; split; [exact Hold|]; split; [symmetry; exact Hgeneration|exact Hstep].
Qed.

(** Source/os_sem.c:381-382, consuming OS_Sched's existing ordinary Ensure.
    Its acquisition-safety premise is exactly the existing callee Require,
    still open at canonical which12. Both source branches retain their
    original return relation and resources. Only an ACTUAL switched return
    yields the task-source consequence; the no-switch case is not silently
    narrowed. The next interrupted Save and Pend-specific ready/registration
    facts remain separate obligations, so this does not close which14. *)
Lemma sem_pend_sched_post_save_input :
  forall external platform critical sg original mask before,
  UCOS2_state_inv sg before ->
  os_sched_acquire_safety external critical sg original before ->
  os_sched_post external platform critical sg original mask before |--
  EX acquired returned final,
    coq_prop (critical_region_interval critical sg original.(os_sched_call_invocation)
        before acquired /\
      os_sched_c_return external critical sg acquired original returned final /\
      (os_sched_requests_switch acquired = true -> kernel_call_task_source returned final)) &&
    (mutex_query_closed platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) mask final **
     os_sched_context_resources external returned ** unmap_table_rep sg).
Proof.
  intros external platform critical sg original mask before Hvalid Hsafe.
  sep_apply_l_atomic (os_sched_post_returns_owned_execution external platform critical
    sg original mask before); Intros acquired returned final.
  assert (Hinterval : critical_region_interval critical sg original.(os_sched_call_invocation)
    before acquired) by tauto.
  assert (Hreturn : os_sched_c_return external critical sg acquired original returned final) by tauto.
  pose proof (sem_post_sched_return_preserves_validity external critical sg original
    before acquired returned final Hvalid Hsafe Hinterval Hreturn) as Hfinal.
  assert (Hsource : os_sched_requests_switch acquired = true ->
    kernel_call_task_source returned final).
  { intro Hrequest; eapply os_sched_c_return_task_source_on_switch.
    - exact (proj2 (Hsafe acquired Hinterval) Hrequest).
    - exact Hrequest.
    - exact Hreturn. }
  Exists acquired returned final.
  unfold mutex_query_closed, kernel_call_execution_owned; entailer!.
Qed.

(** Source/os_sem.c:382: the next OS_ENTER_CRITICAL after OS_Sched.
    On the normal first-level IRQ branch the real selector writes both
    high-ready caches, then the equal-priority comparison avoids a switch.
    Its exact return producer supplies the EXISTING Save Require on that
    final heap, retaining the resumed compiler/stack context, inactive
    handler frame and unmap table. No new Require or callee Ensure is
    introduced. Invocation registration and the matched saved context are
    premises of this internal handler-return cut, not CPU-token facts.

    The returned source fact is about this cut only: the potentially
    interrupted execution of the next Save still needs its paired
    source/heap trace. This lemma does not close canonical which14. *)
Lemma sem_pend_same_priority_irq_save_input :
  forall external platform port critical sg context state heap restored_pc,
  os_int_exit_interrupted_call_binding context ->
  task_invocation_active state.(TskState)
    context.(os_int_exit_interrupted_call).(os_sched_call_invocation)
    context.(os_int_exit_interrupted_call).(os_sched_call_origin) ->
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  state.(SchedState).(isRunning) = true ->
  interrupt_exit_requests_schedule true state.(IntrState) = true ->
  state.(SchedState).(readyList) <> [] ->
  sched_selected_priority state.(TskState) state.(SchedState) =
    sched_priority_byte state.(SchedState).(curSchedPrio) ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_inv sg state ** unmap_table_rep sg **
    armv7a_irq_handler_frame external platform port context) heap ->
  exists final,
    let returned := os_int_exit_wrapper_restored_state
      (os_int_exit_same_priority_state state)
      context.(os_int_exit_interrupted_stack) in
    os_int_exit_masked_same_priority_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final
      (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
      context.(os_int_exit_interrupted_sp) /\
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc) /\
       kernel_call_task_source (os_int_exit_resumed_call context) returned) &&
      (mutex_query_closed platform critical sg
         (os_int_exit_resumed_call context).(os_sched_call_invocation)
         (os_int_exit_resumed_call context).(os_sched_call_origin)
         context.(os_int_exit_interrupted_mask) returned **
       os_sched_context_resources external (os_int_exit_resumed_call context) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments) ** unmap_table_rep sg)) final.
Proof.
  intros external platform port critical sg context state heap restored_pc
    [Hstack Horigin] Hactive Hcurrent Hsaved Hrunning Hschedule Hnonempty
    Hequal Haddress Hpc Hbefore.
  destruct (armv7a_irq_same_priority_resumes_saved_call external platform port
    sg context state heap restored_pc Hcurrent Hsaved Hrunning Hschedule
    Hnonempty Hequal Haddress Hpc Hbefore) as [final [Hfragment [Hreads Hpost]]].
  set (returned := os_int_exit_wrapper_restored_state
    (os_int_exit_same_priority_state state) context.(os_int_exit_interrupted_stack)).
  assert (Hsource : kernel_call_task_source (os_int_exit_resumed_call context) returned).
  { unfold kernel_call_task_source, os_int_exit_resumed_call.
    cbn [os_sched_call_origin os_sched_call_stack os_sched_call_invocation].
    split; [exact Horigin|]. split; [exact Hactive|].
    unfold task_execution_current; rewrite Horigin; exact (proj1 Hcurrent). }
  assert (Hhandoff :
    coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
         context.(os_int_exit_interrupted_mask) ** UCOS2_inv sg returned **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments) ** unmap_table_rep sg) |--
    coq_prop (restored_pc = context.(os_int_exit_interrupted_pc) /\
      kernel_call_task_source (os_int_exit_resumed_call context) returned) &&
      (mutex_query_closed platform critical sg
         (os_int_exit_resumed_call context).(os_sched_call_invocation)
         (os_int_exit_resumed_call context).(os_sched_call_origin)
         context.(os_int_exit_interrupted_mask) returned **
       os_sched_context_resources external (os_int_exit_resumed_call context) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments) ** unmap_table_rep sg)).
  { Intros.
    sep_apply_l_atomic (kernel_call_owned_heap_save_input external platform critical sg
      (os_int_exit_resumed_call context) context.(os_int_exit_interrupted_mask) returned Hsource).
    unfold kernel_call_save_pre, kernel_call_execution_owned, mutex_query_closed.
    entailer!. }
  exists final; split; [exact Hfragment|]. split; [exact Hreads|].
  exact (Hhandoff final Hpost).
Qed.

(** The actual second-Save consumer's independent current/TCB resource
    part, on the local no-interruption source branch. Wait registration and
    ready membership are not inferred here, and this is not which14 Qed. *)
Lemma sem_pend_switched_uninterrupted_save_current_resources :
  forall arch external platform critical sg context returned selected scheduled
    registers before final_registers resumed after,
  os_sched_switch_input external sg context selected ->
  os_sched_requests_switch selected = true ->
  os_sched_c_return external critical sg selected context returned scheduled ->
  kernel_call_save_uninterrupted_execution arch registers scheduled before
    final_registers resumed after ->
  (critical_region_masked platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) final_registers.(kernel_save_r0) resumed **
    UCOS2_inv sg resumed) after ->
  final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  final_registers.(kernel_save_cpsr) = Z.lor registers.(kernel_save_cpsr) 192 /\
  final_registers.(kernel_save_return_word) = Some registers.(kernel_save_lr) /\
  exists node,
    node.(taskGeneration) = returned.(os_sched_call_stack).(stackLeaseGeneration) /\
    kernel_call_task_source returned resumed /\
    (critical_region_masked platform critical sg context.(os_sched_call_invocation)
       context.(os_sched_call_origin) final_registers.(kernel_save_r0) resumed **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
       TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
     sem_pend_cleanup_frame sg resumed returned.(os_sched_call_stack).(stackLeaseSlot) node) after.
Proof.
  intros arch external platform critical sg context returned selected scheduled
    registers before final_registers resumed after Hinput Hswitch Hreturn Hrun Hpost.
  destruct (kernel_call_save_uninterrupted_return_values _ _ _ _ _ _ _ Hrun)
    as [Hr0 [Hcpsr Hlr]].
  split; [exact Hr0|]. split; [exact Hcpsr|]. split; [exact Hlr|].
  destruct (kernel_call_save_instructions_preserve_kernel _ _ _ _ _ _ _ _ Hrun)
    as [Hstate Hmemory]; subst resumed.
  pose proof (os_sched_c_return_task_source_on_switch external critical sg selected
    context returned scheduled Hinput Hswitch Hreturn) as Hsource.
  destruct (kernel_call_task_source_current_at returned scheduled Hsource)
    as [Hcurrent [node [Hnode Hgeneration]]].
  assert (Hvalid : UCOS2_state_inv sg scheduled).
  { destruct Hpost as [masked [owned [Hjoin [Hmasked [Hvalid Hraw]]]]]; exact Hvalid. }
  exists node; split; [exact Hgeneration|]. split; [exact Hsource|].
  assert (Hsplit :
    critical_region_masked platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) final_registers.(kernel_save_r0) scheduled **
    UCOS2_inv sg scheduled |--
    critical_region_masked platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) final_registers.(kernel_save_r0) scheduled **
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot) **
    tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
      TCBStat (Some (encode_task_status node.(stat))) **
    tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
      TCBStatPend (Some (encode_pend_status node.(statPend))) **
    tcb_cell (task_slot_addr sg returned.(os_sched_call_stack).(stackLeaseSlot))
      TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
    sem_pend_cleanup_frame sg scheduled returned.(os_sched_call_stack).(stackLeaseSlot) node).
  { sep_apply_l_atomic (sem_pend_cleanup_split sg scheduled
      returned.(os_sched_call_stack).(stackLeaseSlot) node Hvalid Hcurrent Hnode); entailer!. }
  exact (Hsplit after Hpost).
Qed.

(** The actual OS_Sched Ensure supplies this entry, rather than a new
    public Require. Only its switched normal-return branch has an absent
    original parked key; that branch starts the focused protocol with no
    dormant capsule. The no-switch branch is retained with an empty frame.
    IRQ's real save transition must subsequently issue any capsule. *)
Lemma sem_pend_sched_post_focus_save_input :
  forall external platform port critical
    (abi : Armv7aContinuationABI external platform port) sg original mask before pc lr,
  UCOS2_state_inv sg before ->
  os_sched_acquire_safety external critical sg original before ->
  os_sched_post external platform critical sg original mask before |--
  EX selected returned final,
    coq_prop (critical_region_interval critical sg original.(os_sched_call_invocation)
        before selected /\
      os_sched_c_return external critical sg selected original returned final /\
      (os_sched_requests_switch selected = true -> kernel_call_task_source returned final)) &&
    (mutex_query_closed platform critical sg returned.(os_sched_call_invocation)
       returned.(os_sched_call_origin) mask final **
     os_sched_context_resources external returned ** unmap_table_rep sg **
     (if os_sched_requests_switch selected then
        armv7a_parked_continuations abi (armv7a_call_focus returned pc lr) final
      else emp)).
Proof.
  intros external platform port critical abi sg original mask before pc lr Hvalid Hsafe.
  sep_apply_l_atomic (sem_pend_sched_post_save_input external platform critical sg
    original mask before Hvalid Hsafe); Intros selected returned final.
  assert (Hinterval : critical_region_interval critical sg original.(os_sched_call_invocation)
    before selected) by tauto.
  assert (Hreturn : os_sched_c_return external critical sg selected original returned final) by tauto.
  pose proof (sem_post_sched_return_preserves_validity external critical sg original
    before selected returned final Hvalid Hsafe Hinterval Hreturn) as Hfinal.
  destruct (os_sched_requests_switch selected) eqn:Hswitch.
  - assert (Hnone : final.(TskState).(parkedTaskStacks)
      (task_stack_key returned.(os_sched_call_stack)) = None).
    { unfold os_sched_c_return in Hreturn; rewrite Hswitch in Hreturn.
      destruct Hreturn as [installed [Hsource [Htrace [Harch [Hi [Ho [Hs
        [Hactive [Hcurrent Hparked]]]]]]]]]. rewrite Hs; exact Hparked. }
    assert (Hopen : mutex_query_closed platform critical sg returned.(os_sched_call_invocation)
        returned.(os_sched_call_origin) mask final |--
      mutex_query_closed platform critical sg returned.(os_sched_call_invocation)
        returned.(os_sched_call_origin) mask final **
      armv7a_parked_continuations abi (armv7a_call_focus returned pc lr) final).
    { rewrite mutex_query_closed_equiv.
      intros owned [cpu [world [Hsplit [Hcpu Hworld]]]].
      pose proof (armv7a_continuation_world_open_absent external platform port
        abi (armv7a_call_focus returned pc lr) sg final Hnone world Hworld) as Hextended.
      assert (Hresources : (interrupt_platform_running platform returned.(os_sched_call_invocation)
        returned.(os_sched_call_origin) mask **
        armv7a_continuation_world abi (armv7a_call_focus returned pc lr)
          (UCOS2_inv sg) final) owned).
      { exists cpu, world; split; [exact Hsplit|]; split; assumption. }
      clear Hsplit Hcpu Hworld Hextended cpu world.
      revert owned Hresources.
      match goal with |- forall m : model, ?P m -> ?Q m => change (P |-- Q) end.
      unfold armv7a_continuation_world; entailer!. }
    sep_apply_l_atomic Hopen.
    Exists selected returned final; rewrite Hswitch; entailer!; tauto.
  - Exists selected returned final; rewrite Hswitch; entailer!; tauto.
Qed.

(** Source/os_sem.c, the Save immediately after OS_Sched. This consumer
    covers the source branch interrupted after MRS and then restored at
    the CPSID cursor. Unlike the previous local consumer, its masked/full
    post heap is NOT an input: the selected dormant continuation is
    consumed by actual restore and the real CPSID/DSB/BX suffix produces
    that post on the same evolving model. [world] is the actual installed
    state; its current fact comes from install, not the CPU token.

    The residual keeps the SAME parked resource map, inactive handler
    stack and borrowed caller frame. No public Require is changed. This
    proves the current/used/resource portion of which14, not its still
    separate Wait registry/ready protocol or an arbitrary IRQ producer. *)
Lemma sem_pend_restored_save_current_resources :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg handler saved original transfer registers heap restored final_registers resumed after
    (frame : Assertion),
  let world := os_int_exit_installed_state transfer in
  saved.(armv7a_continuation_call) = Some original ->
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  os_int_exit_destination_binding external transfer ->
  saved.(armv7a_continuation_stack) = transfer.(os_int_exit_incoming_stack) ->
  saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
  saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 ->
  registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
  registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
  registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
  interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
  armv7a_continuation_restore_reads saved heap ->
  (interrupt_platform_running platform handler.(os_int_exit_invocation)
     handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
   task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
     saved.(armv7a_continuation_fragments) **
   armv7a_dormant_continuation continuations saved **
   (armv7a_continuation_world continuations
      (armv7a_call_focus original (armv7a_save_entry_address suffix + 4)
          saved.(armv7a_continuation_lr)) (UCOS2_inv sg) world ** frame)) heap ->
  armv7a_restore_transition continuations handler saved heap restored ->
  armv7a_save_suffix_transition suffix registers world restored final_registers resumed after ->
  resumed = world /\
  final_registers.(kernel_save_return_word) = Some saved.(armv7a_continuation_lr) /\
  final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
  exists node,
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    (critical_region_masked platform critical sg original.(os_sched_call_invocation)
       original.(os_sched_call_origin) final_registers.(kernel_save_r0) world **
     os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
     tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
       TCBStat (Some (encode_task_status node.(stat))) **
     tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
       TCBStatPend (Some (encode_pend_status node.(statPend))) **
     tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
       TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
     sem_pend_cleanup_frame sg world original.(os_sched_call_stack).(stackLeaseSlot) node **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port critical arch continuations suffix sg handler saved original
    transfer registers heap restored final_registers resumed after frame world Hcall Horigin
    Hdestination Hselected Hselectedsp Hcursor Hcpsr Hr0 Hlr Hsaved Hreads Hpre Hrestore Hsuffix.
  pose proof (proj1 Hreads) as [_ Hstack]; rewrite Hcall in Hstack.
  assert (Hcurrent : task_current_at world saved.(armv7a_continuation_stack).(stackLeaseSlot)
    saved.(armv7a_continuation_stack).(stackLeaseGeneration)).
  { rewrite Hselected. destruct Hdestination as
      [Hhigh [[node [Hnode [Hgeneration Hfields]]] Hrest]].
    split; [exact Hhigh|]. exists node; split; assumption. }
  assert (Hnone : world.(TskState).(parkedTaskStacks)
    (task_stack_key original.(os_sched_call_stack)) = None).
  { rewrite Hstack, Hselected. unfold world, os_int_exit_installed_state.
    cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup. }
  destruct (armv7a_restore_call_resources external platform port continuations
    handler saved original _ heap restored Hcall Hreads Hpre Hrestore) as [Hmemory Hrestored].
  assert (Hinput :
    (kernel_call_execution_owned external platform
       (armv7a_continuation_resumed_call saved original)
       (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
     (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) **
      (armv7a_continuation_world continuations
         (armv7a_call_focus original (armv7a_save_entry_address suffix + 4)
          saved.(armv7a_continuation_lr)) (UCOS2_inv sg) world ** frame))) restored).
  { rewrite Hcpsr.
    assert (Hassoc : forall p q r : Assertion, p ** q ** r |-- p ** (q ** r)).
    { intros; entailer!. }
    exact (Hassoc _ _ _ restored Hrestored). }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix
    sg (armv7a_continuation_resumed_call saved original) registers world restored
    final_registers resumed after _ Hsaved Hinput Hsuffix)
    as [Hstate [Hheap [Hreturn [Hvalue Hpost]]]].
  split; [exact Hstate|]. split; [rewrite <- Hlr; exact Hreturn|]. split; [exact Hvalue|].
  rewrite <- Hstack in Hcurrent.
  destruct Hcurrent as [Hcurrent [node [Hnode Hgeneration]]].
  assert (Hvalid : UCOS2_state_inv sg world).
  { unfold armv7a_continuation_world in Hpre.
    repeat match goal with H : (_ ** _) _ |- _ => destruct H as [? [? [? [? ?]]]] end.
    match goal with H : UCOS2_inv sg world _ |- _ => exact (proj1 H) end. }
  exists node; split; [exact Hgeneration|].
  assert (Hsplit :
    critical_region_masked platform critical sg
      (armv7a_continuation_resumed_call saved original).(os_sched_call_invocation)
      (armv7a_continuation_resumed_call saved original).(os_sched_call_origin)
      final_registers.(kernel_save_r0) world **
    os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
    (task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) **
     (armv7a_continuation_world continuations
        (armv7a_call_focus original (armv7a_save_entry_address suffix + 4)
          saved.(armv7a_continuation_lr)) (UCOS2_inv sg) world ** frame)) |--
    critical_region_masked platform critical sg original.(os_sched_call_invocation)
      original.(os_sched_call_origin) final_registers.(kernel_save_r0) world **
    os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
    tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      TCBStat (Some (encode_task_status node.(stat))) **
    tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      TCBStatPend (Some (encode_pend_status node.(statPend))) **
    tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
      TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
    sem_pend_cleanup_frame sg world original.(os_sched_call_stack).(stackLeaseSlot) node **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame).
  { unfold armv7a_continuation_world.
    sep_apply_l_atomic (sem_pend_cleanup_split sg world
      original.(os_sched_call_stack).(stackLeaseSlot) node Hvalid Hcurrent Hnode).
    unfold armv7a_parked_continuations.
    sep_apply_l_atomic (armv7a_parked_focus_absent_emp _ _ _ continuations
      (armv7a_call_focus original (armv7a_save_entry_address suffix + 4)
        saved.(armv7a_continuation_lr)) world.(TskState).(parkedTaskStacks) Hnone).
    cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
  exact (Hsplit after Hpost).
Qed.

(** The selected SP/caches producer now feeds the actual second-Save
    consumer. Its invocation/PC/LR facts are obtained by taking the focused
    resource; they are NOT additional hypotheses on an arbitrary saved
    descriptor. The continuation clause describes the real restore/suffix
    when it occurs and makes no termination claim. Its SP equation is the
    LDR-SP -> LDM dataflow join, still an explicit source-execution cut.

    This starts at the post-hook heap. An arbitrary handler/hook producer
    for that heap, and the Pend registry/ready protocol, are not proved by
    this theorem and remain necessary for the original canonical which14. *)
Lemma sem_pend_selected_save_continuation :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg handler original transfer return_pc (frame : Assertion) heap,
  let focus := armv7a_call_focus original (armv7a_save_entry_address suffix + 4) return_pc in
  original.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot)
    original.(os_sched_call_stack).(stackLeaseGeneration) ->
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) = task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (UCOS2_inv sg)
      transfer.(os_int_exit_hooked_state) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall registers restored final_registers resumed after,
      saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
      registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      armv7a_save_suffix_transition suffix registers (os_int_exit_installed_state transfer)
        restored final_registers resumed after ->
      resumed = os_int_exit_installed_state transfer /\
      final_registers.(kernel_save_return_word) = Some return_pc /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
      exists node,
        node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
        (critical_region_masked platform critical sg original.(os_sched_call_invocation)
           original.(os_sched_call_origin) final_registers.(kernel_save_r0)
           (os_int_exit_installed_state transfer) **
         os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
         sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
         tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
           TCBStat (Some (encode_task_status node.(stat))) **
         tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
           TCBStatPend (Some (encode_pend_status node.(statPend))) **
         tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot))
           TCBEventPtr (Some (encode_event_link sg node.(eventPtr))) **
         sem_pend_cleanup_frame sg (os_int_exit_installed_state transfer)
           original.(os_sched_call_stack).(stackLeaseSlot) node **
         task_stack_fragments_rep handler.(os_int_exit_handler_stack)
           handler.(os_int_exit_handler_fragments) ** frame) after).
Proof.
  intros external platform port critical arch continuations suffix sg handler original
    transfer return_pc frame heap focus Horigin Hdestination Hkey Haddress Hpre.
  destruct (armv7a_install_take_continuation external platform port continuations
    focus sg transfer _ heap Hdestination Hkey Haddress Hpre)
    as [installed [saved [Hinstall [Hbinding [Hfocused [Hstack [Hfragments
      [Hcurrent Howned]]]]]]]].
  destruct Hfocused as [Hcall [Hcursor Hlr]].
  change (saved.(armv7a_continuation_call) = Some original) in Hcall.
  change (saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4) in Hcursor.
  change (saved.(armv7a_continuation_lr) = return_pc) in Hlr.
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hcall|].
  split; [exact Hcursor|]. split; [exact Hlr|].
  intros registers restored final_registers resumed after Hsp Hcpsr Hr0 Hregisterlr Hsaved
    Hreads Hrestore Hsuffix.
  assert (Hreorder :
    armv7a_continuation_world continuations focus (UCOS2_inv sg)
      (os_int_exit_installed_state transfer) **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (armv7a_continuation_world continuations
       (armv7a_call_focus original (armv7a_save_entry_address suffix + 4)
         saved.(armv7a_continuation_lr)) (UCOS2_inv sg)
       (os_int_exit_installed_state transfer) ** frame)).
  { unfold focus; rewrite Hlr; entailer!. }
  pose proof (sem_pend_restored_save_current_resources external platform port critical arch
    continuations suffix sg handler saved original transfer registers installed restored
    final_registers resumed after frame Hcall Horigin Hdestination Hstack Hsp Hcursor Hcpsr Hr0
    Hregisterlr Hsaved Hreads (Hreorder installed Howned) Hrestore Hsuffix) as Hpost.
  rewrite Hlr in Hpost; exact Hpost.
Qed.

(** User-authorized caller-domain correction. This is the ordinary task
    calling stage, not a permanent invariant and not the poststate of Save.
    The public spatial precondition still owns the actual CPU/context and
    borrowed cells; this pure predicate cannot manufacture those owners. *)
Definition sem_pend_task_call_stage (sg : StableGlobVars)
  (context : OsSchedCallContext) (state : UCOS2_Verify_State) : Prop :=
  kernel_call_task_source context state /\ state.(SchedState).(isRunning) = true /\
  exists node,
    sched_current_ready_at state.(TskState) state.(SchedState)
      context.(os_sched_call_stack).(stackLeaseSlot) node /\
    node.(taskGeneration) = context.(os_sched_call_stack).(stackLeaseGeneration) /\
    node.(curPrio) <> sg.(osLowestPrio) /\ node.(eventPtr) = None /\
    node.(eventMultiWaitEvents) = [] /\ node.(tcbFlagNode) = 0.

(** An actual acquisition-count protocol, not pre-Save count stability.
    It does not require current/ready/Task identity. Environments capable
    of depleting this semaphore cannot prove it just from a positive old
    count. The existing critical family still requires actual source/heap
    binding; this predicate does not establish that binding. *)
Definition sem_pend_nonblocking_acquire (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext)
  (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  forall entry current,
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
    0 < encode_event_cnt_value current.

Definition sem_pend_call_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (pevent : Z)
  (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  sem_pend_task_call_stage sg context before \/
    sem_pend_nonblocking_acquire critical sg context before eid.

Lemma sem_pend_call_admission_early_error : forall critical sg context pevent before eid error,
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = Some error ->
  sem_pend_call_admission critical sg context pevent before eid.
Proof. intros * Herror Hclear; congruence. Qed.

Lemma sem_pend_call_admission_task_entry : forall critical sg context pevent before eid,
  sem_pend_task_call_stage sg context before ->
  sem_pend_call_admission critical sg context pevent before eid.
Proof. intros * Hstage Hclear; left; exact Hstage. Qed.

Lemma sem_pend_call_admission_nonblocking : forall critical sg context pevent before eid,
  sem_pend_nonblocking_acquire critical sg context before eid ->
  sem_pend_call_admission critical sg context pevent before eid.
Proof. intros * Hcount Hclear; right; exact Hcount. Qed.

(** At the real zero-count observation only the task alternative survives.
    Deliberately the conclusion is about BEFORE: transporting it to ENTRY
    requires the actual same-call Save producer, not just an interval. *)
Lemma sem_pend_zero_count_requires_calling_stage :
  forall critical sg context pevent before eid entry current,
  sem_pend_call_admission critical sg context pevent before eid ->
  sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
  mutex_query_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_cnt_value current = 0 -> sem_pend_task_call_stage sg context before.
Proof.
  intros * Hadmit Hclear Hinterval Hlookup Htype Hzero.
  destruct (Hadmit Hclear) as [Hstage|Hpositive]; [exact Hstage|].
  specialize (Hpositive entry current Hinterval Hlookup Htype); lia.
Qed.

(** The literal wait fields depend on the acquired task and semaphore,
    not on a flattened history of the preceding Save. Keep the active
    invocation and current-cache observations from that same task stage. *)
Lemma sem_pend_task_stage_wait_entry : forall sg context entry eid current,
  sem_pend_task_call_stage sg context entry ->
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
  exists node,
    sem_pend_wait_entry sg entry eid current context.(os_sched_call_stack).(stackLeaseSlot) node /\
    context.(os_sched_call_origin) = RunningInvocation
      context.(os_sched_call_stack).(stackLeaseSlot) node.(taskGeneration) /\
    kernel_call_task_source context entry /\
    sched_current_consistency entry.(TskState) entry.(SchedState).
Proof.
  intros sg context entry eid current
    [Hsource [Hrunning [node [Hready [Hgen [Hnonidle [Hevent [Hmulti Hflag]]]]]]]]
    Hvalid Hlookup Htype Hzero Hlayout.
  pose proof Hsource as [Horigin _].
  pose proof (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready) as Hcache.
  destruct Hready as [Hnode [Hcurrent [Hpriority [Hin Hready]]]].
  exists node; split.
  - unfold sem_pend_wait_entry; repeat first [assumption | split].
  - split; [rewrite Hgen; exact Horigin|]. split; assumption.
Qed.

(** Compatibility with the older flat-history annotation. Its extra
    history is only framed into wait_origin; the spatial consumer below
    no longer needs it to obtain the actual TCB fields. *)
Lemma sem_pend_task_stage_wait_origin : forall critical sg context mask saved
  before observed entry eid current,
  sem_pend_task_call_stage sg context entry ->
  sem_query_acquire_facts critical sg context.(os_sched_call_invocation) eid mask saved
    before entry observed current ->
  encode_event_cnt_value current = 0 -> event_object_layout_prop sg eid ->
  exists node,
    sem_pend_wait_origin critical sg context mask saved before observed entry eid current
      context.(os_sched_call_stack).(stackLeaseSlot) node.
Proof.
  intros critical sg context mask saved before observed entry eid current
    Hstage Hacquire Hzero Hlayout.
  pose proof Hacquire as [_ [Hvalid [_ [_ [Hlookup [_ [Htype _]]]]]]].
  destruct (sem_pend_task_stage_wait_entry sg context entry eid current
    Hstage Hvalid Hlookup Htype Hzero Hlayout) as [node Hentry].
  exists node; unfold sem_pend_wait_origin; split; assumption.
Qed.

(** Concrete first-Save branch: the real MRS result is fed to the SAME
    heap's CPSID/DSB/BX transition. No interrupt is represented by this
    branch, and no statement about a general interrupted Save is made.
    Its caller is the Timer initial-C-entry consumer, not a new public
    universal Save postcondition. All caller bytes are framed unchanged. *)
Lemma sem_pend_uninterrupted_first_save_resources :
  forall external platform critical arch
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg context mask state registers heap final_registers final_state after (frame : Assertion),
  registers.(kernel_save_return_word) = None ->
  valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  sem_pend_task_call_stage sg context state ->
  (mutex_query_closed platform critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) mask state **
   os_sched_context_resources external context ** frame) heap ->
  armv7a_save_suffix_transition suffix (kernel_save_read_cpsr registers) state heap
    final_registers final_state after ->
  kernel_call_save_uninterrupted_execution arch registers state heap
    final_registers final_state after /\
  sem_pend_save_facts critical sg context.(os_sched_call_invocation) mask
    final_registers.(kernel_save_r0) state final_state /\
  sem_pend_task_call_stage sg context final_state /\
  (critical_region_masked platform critical sg context.(os_sched_call_invocation)
     context.(os_sched_call_origin) final_registers.(kernel_save_r0) final_state **
   UCOS2_inv sg final_state ** os_sched_context_resources external context ** frame) after.
Proof.
  intros external platform critical arch suffix sg context mask state registers heap
    final_registers final_state after frame Hreturn Hcpsr Hmask Hstage Hpre Hrun.
  assert (Hsplit : mutex_query_closed platform critical sg context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask state **
      os_sched_context_resources external context ** frame |--
    coq_prop (UCOS2_state_inv sg state) &&
    (kernel_call_execution_owned external platform context mask ** (UCOS2_inv sg state ** frame))).
  { rewrite mutex_query_closed_equiv.
    unfold kernel_call_execution_owned, UCOS2_inv; entailer!. }
  destruct (Hsplit heap Hpre) as [Hvalid Howned].
  assert (Hsaved : interrupt_saved_value
    (armv7a_irq_fiq_mask (kernel_save_read_cpsr registers).(kernel_save_cpsr))
    (kernel_save_read_cpsr registers).(kernel_save_r0)).
  { split; [exact Hcpsr|reflexivity]. }
  assert (Hsource : kernel_call_save_uninterrupted_execution arch registers state heap
    final_registers final_state after).
  { unfold kernel_call_save_uninterrupted_execution.
    econstructor; [constructor; [exact Hreturn|reflexivity]|].
    exact (armv7a_save_suffix_source _ _ _ _ suffix _ _ _ _ _ _ Hrun). }
  rewrite <- Hmask in Howned.
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg context
    (kernel_save_read_cpsr registers) state heap final_registers final_state after
    (UCOS2_inv sg state ** frame) Hsaved Howned Hrun)
    as [Hstate [Hmemory [Hlr [Hr0 Hafter]]]].
  subst final_state; split; [exact Hsource|]. split.
  - unfold sem_pend_save_facts; split; [exact Hvalid|].
    split; [constructor|]. split; [rewrite Hr0; split; assumption|exact Hvalid].
  - split; [exact Hstage|].
    assert (Horder : critical_region_masked platform critical sg context.(os_sched_call_invocation)
        context.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
        os_sched_context_resources external context ** (UCOS2_inv sg state ** frame) |--
      critical_region_masked platform critical sg context.(os_sched_call_invocation)
        context.(os_sched_call_origin) final_registers.(kernel_save_r0) state **
        UCOS2_inv sg state ** os_sched_context_resources external context ** frame) by entailer!.
    exact (Horder after Hafter).
Qed.

(** A normally returning last interrupt transfer. The prefix is the SAME
    source-indexed registered trace: its concrete clients supply the field
    projection, while the last real selection supplies ready/current.
    This is a source-cut theorem, not an all-client restriction in Require.
    In particular only this explicitly unchanged-hook branch is covered. *)
Lemma sem_pend_interrupt_transfer_acquires_call_stage :
  forall external port critical clients sg context mask saved before origin irq_entry handler transfer action,
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg context before ->
  (forall client, clients client -> critical.(critical_region_clients) client) ->
  (forall client, clients client -> sem_pend_projected_source_client client) ->
  kernel_resumption_task_source_trace external port clients sg context.(os_sched_call_invocation) None
    context.(os_sched_call_origin) before false origin irq_entry ->
  critical.(critical_region_clients) action ->
  kernel_client_actor action <> Some context.(os_sched_call_invocation) ->
  kernel_client_stops action context.(os_sched_call_invocation) = false ->
  kernel_client_step action sg irq_entry (os_int_exit_installed_state transfer) ->
  timer_public_trace sg irq_entry.(TimerState) (os_int_exit_installed_state transfer).(TimerState) ->
  os_int_exit_transfer_source external port sg handler irq_entry transfer ->
  transfer.(os_int_exit_hooked_state) = os_int_exit_ready_checkpoint true irq_entry ->
  transfer.(os_int_exit_incoming_stack) = context.(os_sched_call_stack) ->
  interrupt_saved_value mask saved ->
  kernel_call_save_source external port critical sg context context mask saved
    before (os_int_exit_installed_state transfer) /\
  sem_pend_task_call_stage sg context (os_int_exit_installed_state transfer).
Proof.
  intros external port critical clients sg context mask saved before origin irq_entry
    handler transfer action Hvalid Hstage Hregistered Hclients Hprefix Hin Hforeign Hstop
    Hstep Htimer Htransfer Hhook Hselected Hsaved.
  pose proof Hstage as [Hcaller [Hrunning [old [Hready [Hg [Hnonidle [He [Hm Hf]]]]]]]].
  pose proof (kernel_resumption_task_source_trace_inclusion external port clients
    critical.(critical_region_clients) sg context.(os_sched_call_invocation) None
    context.(os_sched_call_origin) before false origin irq_entry Hregistered Hprefix) as HregisteredPrefix.
  assert (Hsource : kernel_call_save_source external port critical sg context context
    mask saved before (os_int_exit_installed_state transfer)).
  { eapply kernel_call_save_source_last_interrupt_transfer; try eassumption; try reflexivity.
    rewrite Hselected; exact (proj1 Hcaller). }
  split; [exact Hsource|].
  destruct (kernel_resumption_task_source_trace_erases external port
    critical.(critical_region_clients) sg context.(os_sched_call_invocation) None
    context.(os_sched_call_origin) before false origin irq_entry HregisteredPrefix)
    as [Hinterval _].
  destruct (critical_region_interval_transports_resources critical sg context.(os_sched_call_invocation)
    before irq_entry Hinterval Hvalid) as [HirqValid _].
  pose proof (proj1 (kernel_resumption_task_source_trace_erases external port clients sg
    context.(os_sched_call_invocation) None context.(os_sched_call_origin) before false
    origin irq_entry Hprefix)) as Hresource.
  destruct (sem_pend_resumption_trace_preserves_call_fields clients sg context.(os_sched_call_invocation)
    None before false irq_entry context.(os_sched_call_stack).(stackLeaseSlot) old
    Hclients Hresource Hvalid HirqValid Hrunning (proj1 Hready) Hnonidle (conj He (conj Hm Hf)))
    as [HirqRunning [node [Hnode [HnodeNonidle HnodeNone]]]].
  destruct (os_int_exit_unchanged_hook_destination_ready external port sg handler irq_entry transfer
    HirqValid HirqRunning Htransfer Hhook) as [selected [HselectedReady Hgeneration]].
  rewrite Hselected in HselectedReady, Hgeneration.
  assert (Hlookup : (os_int_exit_installed_state transfer).(TskState).(inUsedTaskStates)
    context.(os_sched_call_stack).(stackLeaseSlot) = Some node).
  { change (transfer.(os_int_exit_hooked_state).(TskState).(inUsedTaskStates)
      context.(os_sched_call_stack).(stackLeaseSlot) = Some node).
    rewrite Hhook, (proj1 (os_int_exit_checkpoint_frame true irq_entry)); exact Hnode. }
  assert (selected = node) by (destruct HselectedReady; congruence); subst selected.
  split; [exact (kernel_call_save_source_preserves_task_source external port critical sg
    context context mask saved before (os_int_exit_installed_state transfer)
    Hvalid Hcaller Hsource)|].
  split.
  - change (transfer.(os_int_exit_hooked_state).(SchedState).(isRunning) = true).
    rewrite Hhook; exact (eq_trans
      (proj2 (proj2 (os_int_exit_checkpoint_current_frame true irq_entry))) HirqRunning).
  - exists node; split; [exact HselectedReady|]. split; [exact Hgeneration|].
    split; [exact HnodeNonidle|exact HnodeNone].
Qed.

(** These specific entry/exit stores change saved SP, nesting, high caches
    and the parked map only. Calling-stage transport here follows their
    actual field definitions; it is not derived from equal priority bytes
    and does not assert that an arbitrary intervening ISR preserves stage. *)
Lemma sem_pend_irq_entry_same_priority_call_stage : forall sg original entry sp fragments,
  sem_pend_task_call_stage sg original entry ->
  sem_pend_task_call_stage sg original
    (os_int_exit_wrapper_restored_state
      (os_int_exit_same_priority_state
        (armv7a_irq_live_parked_state entry original sp fragments))
      original.(os_sched_call_stack)).
Proof.
  intros sg original entry sp fragments
    [[Horigin [Hactive Hcurrent]] [Hrunning [node [Hready [Hgeneration Hfields]]]]].
  pose proof Hready as [Hnode [HcurrentNode [Hpriority [Hin HreadyNode]]]].
  unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
    armv7a_irq_entry_counter_state, os_sched_save_current_sp.
  rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode.
  split.
  - split; [exact Horigin|]. split.
    + change (task_invocation_active
        (glob_task_set_usedtask entry.(TskState) original.(os_sched_call_stack).(stackLeaseSlot)
          (task_set_saved_sp node sp)) original.(os_sched_call_invocation) original.(os_sched_call_origin)).
      eapply glob_task_set_usedtask_preserves_invocation_active; [exact Hnode|reflexivity|exact Hactive].
    + exact Hcurrent.
  - split; [exact Hrunning|]. exists (task_set_saved_sp node sp).
    split.
    + split.
      * change ((if Z.eqb original.(os_sched_call_stack).(stackLeaseSlot)
          original.(os_sched_call_stack).(stackLeaseSlot) then Some (task_set_saved_sp node sp)
          else entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot)) =
          Some (task_set_saved_sp node sp)).
        rewrite Z.eqb_refl; reflexivity.
      * exact (conj HcurrentNode (conj Hpriority (conj Hin HreadyNode))).
    + split; [exact Hgeneration|exact Hfields].
Qed.

(** A production chain for the adjacent entry/ordinary-exit memory
    fragments. The input has the running call and inactive handler stack,
    not a saved capsule or an acquired-stage assertion. Save produces the
    capsule, real counter/SP stores publish it, and the ordinary exit takes
    it back through real current/SP reads before the actual restore/suffix.

    This is deliberately NOT a proof of a BSP/ISR body between those cuts:
    a whole IRQ must establish that actual intervening source/heap join.
    No empty-handler law, generic priority-byte readiness rule, or public
    caller restriction is introduced here. *)
Lemma sem_pend_irq_entry_same_priority_save_resources :
  forall external platform port critical arch
    (abi : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg entry node handler saved publication (frame : Assertion) before saved_heap,
  let original := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus original handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
  let parked := armv7a_irq_live_parked_state entry original saved.(armv7a_continuation_sp)
    saved.(armv7a_continuation_fragments) in
  let resumed := os_int_exit_wrapper_restored_state (os_int_exit_same_priority_state parked)
    original.(os_sched_call_stack) in
  sem_pend_task_call_stage sg original entry -> entry.(IntrState).(intNesting) = 0 ->
  entry.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = original.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region original.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range original.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range original.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  handler.(os_int_exit_interrupted_pc) = armv7a_save_entry_address suffix + 4 ->
  interrupt_exit_requests_schedule true parked.(IntrState) = true ->
  sched_selected_priority parked.(TskState) parked.(SchedState) =
    sched_priority_byte parked.(SchedState).(curSchedPrio) ->
  (os_int_exit_frame_save_pre external platform handler **
    (UCOS2_inv sg entry ** (unmap_table_rep sg ** frame))) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists entry_heap return_heap selected,
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry original.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) saved_heap entry_heap /\
    os_int_exit_masked_same_priority_fragment sg entry_heap return_heap /\
    armv7a_irq_restore_pointer_reads sg return_heap
      (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) saved.(armv7a_continuation_sp) /\
    selected.(armv7a_continuation_call) = Some original /\
    selected.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
    selected.(armv7a_continuation_lr) = saved.(armv7a_continuation_lr) /\
    (forall registers restored final_registers final_state after,
      selected.(armv7a_continuation_sp) = saved.(armv7a_continuation_sp) ->
      registers.(kernel_save_cpsr) = selected.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 selected.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = selected.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) registers.(kernel_save_r0) ->
      armv7a_continuation_restore_reads selected return_heap ->
      armv7a_restore_transition abi handler selected return_heap restored ->
      armv7a_save_suffix_transition suffix registers resumed restored final_registers final_state after ->
      final_state = resumed /\
      final_registers.(kernel_save_return_word) = Some saved.(armv7a_continuation_lr) /\
      sem_pend_task_call_stage sg (armv7a_continuation_resumed_call selected original) final_state /\
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0) final_state **
       os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
       UCOS2_inv sg final_state ** unmap_table_rep sg **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) after).
Proof.
  intros external platform port critical arch abi suffix sg entry node handler saved publication
    frame before saved_heap original focus parked resumed Hstage Hnesting Hnode Hid Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcursor Hschedule Hequal Hpre Hsave.
  pose proof Hstage as [Hcaller [Hrunning [old [Hready [Hgeneration Hfields]]]]].
  assert (old = node) by (destruct Hready; congruence); subst old.
  pose proof (proj1 (proj2 Hready)) as Hcurrent.
  assert (Hopen : os_int_exit_frame_save_pre external platform handler **
      (UCOS2_inv sg entry ** (unmap_table_rep sg ** frame)) |--
    os_int_exit_frame_save_pre external platform handler **
      (armv7a_continuation_world abi focus (UCOS2_inv sg) entry ** (unmap_table_rep sg ** frame))).
  { sep_apply_l_atomic (armv7a_continuation_world_open_absent external platform port abi focus
      sg entry Hnone); entailer!. }
  destruct (armv7a_irq_source_save_deposit external platform port abi sg entry node handler saved
    publication (unmap_table_rep sg ** frame) before saved_heap Hrunning Hnesting Hcurrent Hnode
    Hid Hgeneration Hnone Haddress Hregion Hgeometry Hpublication Hsp (Hopen before Hpre) Hsave)
    as [entry_heap [HsavedCall [HsavedPC [Hwrites [Hentry HparkedOwned]]]]].
  assert (HparkedNode : parked.(TskState).(inUsedTaskStates)
      original.(os_sched_call_stack).(stackLeaseSlot) = Some (task_set_saved_sp node saved.(armv7a_continuation_sp))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; cbn; rewrite Z.eqb_refl; reflexivity. }
  assert (HparkedMap : parked.(TskState).(parkedTaskStacks)
      (task_stack_key original.(os_sched_call_stack)) =
      Some (original.(os_sched_call_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state; apply task_stack_park_fragments_lookup. }
  assert (HparkedSched : parked.(SchedState) = entry.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp; rewrite Hrunning; reflexivity. }
  assert (HparkedRunning : parked.(SchedState).(isRunning) = true)
    by (rewrite HparkedSched; exact Hrunning).
  assert (HparkedCurrent : parked.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot))
    by (rewrite HparkedSched; exact Hcurrent).
  assert (Hnonempty : parked.(SchedState).(readyList) <> nil).
  { rewrite HparkedSched.
    intro Hempty; destruct Hready as [_ [_ [_ [Hin _]]]]; rewrite Hempty in Hin; contradiction. }
  assert (Horder : armv7a_continuation_world abi focus (UCOS2_inv sg) parked **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** (unmap_table_rep sg ** frame)) |--
    armv7a_continuation_world abi focus (UCOS2_inv sg) parked ** unmap_table_rep sg **
      (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)) by entailer!.
  destruct (armv7a_irq_same_priority_takes_continuation external platform port abi focus sg parked
    original.(os_sched_call_stack) saved.(armv7a_continuation_fragments)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) _ entry_heap
    HparkedRunning Hschedule Hnonempty Hequal HparkedCurrent HparkedNode HparkedMap eq_refl Haddress
    (Horder entry_heap HparkedOwned))
    as [return_heap [selected [Hexit [Hreads [Hbinding [Hfocused [Hstack [Hfragments Howned]]]]]]]].
  destruct Hfocused as [Hcall [Hpc Hlr]].
  change (selected.(armv7a_continuation_call) = Some original) in Hcall.
  change (selected.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc)) in Hpc.
  change (selected.(armv7a_continuation_lr) = saved.(armv7a_continuation_lr)) in Hlr.
  exists entry_heap, return_heap, selected; split; [exact Hwrites|]. split; [exact Hentry|].
  split; [exact Hexit|]. split; [exact Hreads|]. split; [exact Hcall|].
  split; [rewrite Hcursor in Hpc; exact Hpc|]. split; [exact Hlr|].
  intros registers restored final_registers final_state after HselectedSP Hcpsr Hr0 HregisterLR
    HsavedValue HframeReads Hrestore Hsuffix.
  assert (HrestoreOrder : armv7a_continuation_world abi focus (UCOS2_inv sg) resumed **
      task_stack_fragments_rep original.(os_sched_call_stack).(stackLeaseRegion)
        saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi selected **
      (unmap_table_rep sg ** (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler **
      task_stack_fragments_rep selected.(armv7a_continuation_stack).(stackLeaseRegion)
        selected.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi selected **
      (armv7a_continuation_world abi focus (UCOS2_inv sg) resumed ** (unmap_table_rep sg ** frame))).
  { rewrite Hstack, Hfragments; entailer!. }
  destruct (armv7a_restore_call_resources external platform port abi handler selected original _
    return_heap restored Hcall HframeReads (HrestoreOrder return_heap Howned) Hrestore)
    as [Hmemory Hrestored].
  assert (HsuffixOwned : (kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call selected original) (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (armv7a_continuation_world abi focus (UCOS2_inv sg) resumed ** (unmap_table_rep sg ** frame)))) restored).
  { rewrite Hcpsr. assert (Hassoc : forall p q r : Assertion, p ** q ** r |-- p ** (q ** r))
      by (intros; entailer!). exact (Hassoc _ _ _ restored Hrestored). }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix sg
    (armv7a_continuation_resumed_call selected original) registers resumed restored final_registers
    final_state after _ HsavedValue HsuffixOwned Hsuffix)
    as [Hstate [HafterMem [Hreturned [Hvalue Hafter]]]].
  subst final_state; split; [reflexivity|]. split; [rewrite HregisterLR, Hlr in Hreturned; exact Hreturned|].
  split.
  - pose proof (sem_pend_irq_entry_same_priority_call_stage sg original entry
      saved.(armv7a_continuation_sp) saved.(armv7a_continuation_fragments) Hstage) as HfinalStage.
    unfold sem_pend_task_call_stage, kernel_call_task_source in *.
    cbn [armv7a_continuation_resumed_call os_sched_call_stack os_sched_call_invocation os_sched_call_origin].
    rewrite Hstack; exact HfinalStage.
  - assert (Habsent : resumed.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = None).
    { unfold resumed, os_int_exit_wrapper_restored_state; apply task_stack_take_lookup. }
    assert (Hfinish : critical_region_masked platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) final_registers.(kernel_save_r0) resumed **
      os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
      (task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (armv7a_continuation_world abi focus (UCOS2_inv sg) resumed ** (unmap_table_rep sg ** frame))) |--
      critical_region_masked platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) final_registers.(kernel_save_r0) resumed **
      os_sched_context_resources external (armv7a_continuation_resumed_call selected original) **
      UCOS2_inv sg resumed ** unmap_table_rep sg **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame).
    { unfold armv7a_continuation_world, armv7a_parked_continuations.
      sep_apply_l_atomic (armv7a_parked_focus_absent_emp _ _ _ abi focus resumed.(TskState).(parkedTaskStacks)
        Habsent); entailer!. }
    exact (Hfinish after Hafter).
Qed.
