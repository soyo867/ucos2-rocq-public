Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The first protected observation is obtained from the actual Save
    history. Readiness is deliberately absent: only the later busy arm
    needs it. Existing handle, owner-use and Idle protocols transport
    their facts over this same interval. *)
Lemma mutex_pend_first_save_split : forall environment critical saved_local sg idle original
  pe before eid observed mask saved,
  UCOS2_state_inv sg before ->
  mutex_pend_api_input critical sg original.(os_sched_call_invocation) pe before eid observed ->
  mutex_pend_api_admission (Some environment) idle original pe before eid ->
  mutex_pend_api_scope (Some environment) critical sg idle original pe before eid ->
  mutex_pend_api_prefix pe before eid ->
  mutex_pend_api_save_output environment critical saved_local sg original mask saved before |--
  EX entered entry current mutex tid caller,
    coq_prop (mutex_pend_first_snapshot environment critical sg idle original entered mask saved
      before entry eid observed current mutex tid caller) &&
    (mutex_pend_masked_frame environment critical saved_local sg entered saved entry entry **
     (event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
     (event_addr sg eid + OSEventPtr_off) # Ptr |-> encode_event_ptr_value sg current **
     sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
     (tcb_field_address (task_slot_addr sg tid) TCBPrio) # UChar |-> caller.(curPrio) **
     mutex_accept_current_frame sg entry eid current tid caller).
Proof.
  intros environment critical saved_local sg idle original pe before eid observed mask saved
    Hvalid Hinput Hadmission Hscope Hprefix.
  pose proof (proj1 (mutex_pend_precritical_continues_iff _ _ _ _) Hprefix)
    as [Hpe [Htype [Hisr Hlock]]].
  destruct Hinput as [Hnull|[Hnonnull [Haddr [Hid [Hslot Hhandle]]]]]; [contradiction|].
  specialize (Hhandle Htype Hisr Hlock).
  destruct (mutex_accept_public_slot_is_mutex before eid observed Hslot Htype)
    as [Hlookup Hmutex_type].
  destruct (Hadmission Hprefix) as [Howned [Hsource Hnonidle]].
  destruct (Hscope Hprefix) as [Huse [Hidle_slot [Hidle [Howner_protocol
    [Hidle_protocol Hclients]]]]].
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hprofile; unfold selected_kernel_profile in Hprofile; tauto. }
  unfold mutex_pend_api_save_output; Intros entered entry.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg original before entered entry)
    by tauto.
  assert (Hsaved : interrupt_saved_value mask saved) by tauto.
  assert (Hrely : sem_pend_save_rely sg before entry) by tauto.
  pose proof Hhistory as [Htrace [Hsame Havailable]].
  pose proof Hsame as [Hi [Ho Hstack]].
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered mask saved before entry).
  { unfold kernel_call_save_source; split; [exact Htrace|].
    split; [exact Hi|]. split; [exact Ho|]. split; assumption. }
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    before entry Hinterval Hvalid) as [Hvalid_entry Hrest].
  assert (Hsource_entry : kernel_call_task_source entered entry).
  { exact (kernel_call_save_source_preserves_task_source _ _ _ _ _ _ _ _ _ _
      Hvalid Hsource Hsave). }
  assert (Hnonidle_entry : mutex_call_non_idle idle entered.(os_sched_call_origin)).
  { rewrite Ho; exact Hnonidle. }
  assert (Huse_entry : mutex_owner_event_unlinked entry.(TskState) entry.(EventState)).
  { assert (Howner_history : mutex_owner_source_history sg before entry).
    { eapply mutex_owner_region_interval_history; [exact Howner_protocol|constructor|exact Hvalid|exact Hinterval]. }
    clear -Howner_history Huse.
    induction Howner_history; [exact Huse|].
    eapply mutex_owner_source_step_preserves_owner_use; eassumption. }
  assert (Hidle_slot_entry : mutex_idle_slot entry.(TskState) idle).
  { exact (mutex_idle_region_interval_preserves_slot _ _ _ _ _ _
      Hidle_protocol Hvalid Hinterval Hidle_slot). }
  assert (Hidle_entry : mutex_idle_excluded idle entry.(EventState)).
  { exact (mutex_idle_region_interval_preserves_exclusion _ _ _ _ _ _
      Hidle_protocol Hvalid Hinterval Hidle). }
  destruct (Hhandle entry Hinterval)
    as [current [Hcurrent [Hgeneration Hcurrent_type]]].
  assert (Hfacts : mutex_accept_acquire_facts critical sg original.(os_sched_call_invocation)
    eid mask saved before entry observed current).
  { unfold mutex_accept_acquire_facts; split; [exact Hinterval|].
    split; [exact Hvalid_entry|]. split; [exact Hsaved|].
    split; [exact Hlookup|]. split; [exact Hcurrent|].
    split; [exact Hmutex_type|]. split; congruence. }
  destruct (mutex_accept_source_current_exists sg entry entered Hsg Hvalid_entry Hsource_entry)
    as [tid [caller Hcaller]].
  unfold task_tcb_init_continuation_restore_input; Intros_p Hcoverage.
  sep_apply_l_atomic (mutex_accept_event_fields_split_full sg entry eid current Hcurrent
    ltac:(congruence)).
  Intros mutex.
  assert (Hsnapshot : mutex_accept_event_snapshot sg entry eid current mutex
    (encode_event_cnt_value current) (encode_event_ptr_value sg current)) by tauto.
  sep_apply_l_atomic (mutex_accept_current_fields_split sg entry eid current tid caller Hcaller).
  Exists entered entry current mutex tid caller.
  assert (Hfirst : mutex_pend_first_snapshot environment critical sg idle original entered mask saved
    before entry eid observed current mutex tid caller).
  { unfold mutex_pend_first_snapshot; tauto. }
  unfold mutex_pend_masked_frame; entailer!.
Qed.

(** Arithmetic consumed by the actual immediate-acquire stores and casts. *)
Lemma mutex_pend_acquire_byte_observations : forall environment critical sg idle original entered
  mask saved before entry eid observed current mutex tid caller,
  mutex_pend_first_snapshot environment critical sg idle original entered mask saved
    before entry eid observed current mutex tid caller ->
  Z.land (encode_event_cnt_value current) 255 = 255 ->
  mutex.(mfOwner) = None /\
  mutex.(mfPCP) = Z.shiftr (encode_event_cnt_value current) 8 /\
  unsigned_last_nbits (Z.shiftr (encode_event_cnt_value current) 8) 8 =
    Z.shiftr (encode_event_cnt_value current) 8 /\
  unsigned_last_nbits caller.(curPrio) 16 = caller.(curPrio) /\
  sg.(osPrioMutexCeilDis) = 255 /\
  Z.lor (Z.land (encode_event_cnt_value current) 65280) caller.(curPrio) =
    mutex.(mfPCP) * 256 + caller.(curPrio).
Proof.
  intros * Hfirst Hlow.
  destruct Hfirst as [_ [_ [_ [Hfacts [_ [_ [_ [_ [_ [Hsnapshot Hcaller]]]]]]]]]].
  pose proof (proj1 (proj2 Hfacts)) as Hvalid.
  destruct (mutex_accept_available_snapshot _ _ _ _ _ _ _ Hvalid Hsnapshot Hlow)
    as [Hnone [Horig [Hcount Hpcp]]].
  assert (Hsg : valid_stable_glob_vars sg).
  { pose proof (proj1 Hvalid) as Hp; unfold selected_kernel_profile in Hp; tauto. }
  assert (Hprio : 0 <= caller.(curPrio) <= 255).
  { unfold mutex_accept_current_task, task_priority_in_range in Hcaller.
    unfold valid_stable_glob_vars in Hsg; lia. }
  assert (Hrange : 0 <= encode_event_cnt_value current <= 65535) by lia.
  split; [exact Hnone|]. split.
  - rewrite Hcount, Z.shiftr_div_pow2 by lia; cbn.
    rewrite Z.add_comm, Z.div_add by lia; cbn; lia.
  - split; [apply mutex_accept_high_byte_cast; exact Hrange|].
    split; [apply mutex_accept_u16_of_byte; exact Hprio|].
    split; [unfold valid_stable_glob_vars in Hsg; tauto|].
    rewrite mutex_accept_replace_low_byte by lia; lia.
Qed.

(** The protected relation includes the ownership stores before returning
    PCP_LOWER, just as the original C branch does. *)
Lemma mutex_pend_snapshot_acquired : forall environment critical sg idle original entered
  mask saved before entry eid observed current mutex tid caller ticks code,
  mutex_pend_first_snapshot environment critical sg idle original entered mask saved
    before entry eid observed current mutex tid caller ->
  Z.land (encode_event_cnt_value current) 255 = 255 ->
  code = encode_os_err_code (mutex_pend_acquire_error sg mutex.(mfPCP) caller.(curPrio)) ->
  mutex_pend_first_acquired sg eid ticks entry code
    (mutex_accept_owned_state entry eid current mutex tid caller.(curPrio)).
Proof.
  intros * Hfirst Hlow Hcode.
  pose proof (proj1 (mutex_pend_acquire_byte_observations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hfirst Hlow)) as Hnone.
  destruct Hfirst as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hsnapshot Hcaller]]]]]]]]]].
  destruct Hsnapshot as [Hlookup [Htype [Hfields _]]].
  destruct Hcaller as [Hcurrent [Hnode _]].
  exists (mutex_pend_acquire_error sg mutex.(mfPCP) caller.(curPrio)).
  split; [exact Hcode|].
  exists current, mutex, tid, caller.
  split; [exact Hlookup|]. split; [exact Htype|]. split; [exact Hfields|].
  split; [exact Hcurrent|]. split; [exact Hnode|].
  rewrite Hnone; split; reflexivity.
Qed.

(** Compose the two actual modular calls with the completed acquire.
    The returned world need not equal the protected checkpoint. *)
Lemma mutex_pend_acquired_api_return : forall environment critical saved_local sg original entered
  mask saved before entry pe eid ticks code checkpoint perr X,
  mutex_pend_api_prefix pe before eid ->
  interrupt_saved_value mask saved ->
  sem_pend_modular_call_history environment critical sg original before entered entry ->
  mutex_pend_first_acquired sg eid ticks entry code checkpoint ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_pend_api_program (Some environment) critical sg original pe eid ticks))
      sem_query_observe_error) X ->
  perr # UChar |-> code **
    mutex_pend_api_restore_output false environment critical saved_local sg entered saved checkpoint |--
  mutex_pend_api_post environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg original mask pe eid ticks perr before X.
Proof.
  intros * Hprefix Hsaved Hfirst Hacquire Hexec.
  unfold mutex_pend_api_restore_output; Intros returned after.
  assert (Hlast : sem_pend_modular_call_history environment critical sg entered checkpoint returned after)
    by tauto.
  assert (Hsem : mutex_pend_api_program (Some environment) critical sg original pe eid ticks before code after).
  { unfold mutex_pend_api_program; rewrite Hprefix.
    destruct Hacquire as [error [Hcode Hcritical]].
    exists entered, entry, (MutexPendAcquired error), checkpoint, returned.
    split; [exact Hfirst|]. split; [exact Hcritical|]. split; assumption. }
  pose proof (mutex_pend_api_safe_return _ _ _ _ _ _ _ _ _ _ _ Hsem Hexec) as Hsafe.
  assert (Hsame : kernel_stack_call_same_call returned original).
  { pose proof (proj1 (proj2 Hfirst)) as H1; pose proof (proj1 (proj2 Hlast)) as H2.
    unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence. }
  rewrite (proj2 Hsaved).
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned environment critical saved_local
    sg returned mask after)).
  unfold mutex_pend_api_post; Exists returned after code; entailer!.
Qed.

(** These are the exact completed stores of the immediate-acquire arm.
    Its task/stack resources are unchanged, even for PCP_LOWER, which is
    returned after ownership has already been acquired. *)
Lemma mutex_pend_acquire_restore_merge : forall environment critical saved_local sg call saved
  entry eid current mutex tid caller,
  UCOS2_state_inv sg entry -> mutex_accept_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_MUTEX -> current.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = None -> mutex_accept_current_task sg entry tid caller ->
  mutex_pend_masked_frame environment critical saved_local sg call saved entry entry **
  (event_addr sg eid + OSEventCnt_off) # UShort |-> (mutex.(mfPCP) * 256 + caller.(curPrio)) **
  (event_addr sg eid + OSEventPtr_off) # Ptr |-> task_slot_addr sg tid **
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  (tcb_field_address (task_slot_addr sg tid) TCBPrio) # UChar |-> caller.(curPrio) **
  mutex_accept_current_frame sg entry eid current tid caller |--
  mutex_pend_api_restore_input false environment critical saved_local sg call saved entry
    (mutex_accept_owned_state entry eid current mutex tid caller.(curPrio)).
Proof.
  intros * Hvalid Hlookup Htype Hfields Hnone Hcaller.
  unfold mutex_pend_masked_frame; Intros_p Hcoverage.
  sep_apply_l_atomic (mutex_accept_acquire_merge_full sg entry eid current mutex tid caller
    Hvalid Hlookup Htype Hfields Hnone Hcaller).
  unfold mutex_pend_api_restore_input, task_tcb_init_continuation_restore_input.
  change (mutex_accept_owned_state entry eid current mutex tid caller.(curPrio)).(TskState)
    with entry.(TskState).
  unfold task_tcb_init_continuation_capsules, mutex_accept_owned_state;
    cbn [replace_EventS TskState]; entailer!.
Qed.
