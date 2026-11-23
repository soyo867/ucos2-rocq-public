Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_call_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_pend_wait_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_wait_return_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** The exact encoded result of the already existing resume relation. *)
Definition mutex_pend_resume_result sg eid resumed code cleaned : Prop :=
  exists result, code = encode_os_err_code result /\
    mutex_pend_resume_critical sg eid resumed result cleaned.

(** A branch-local observation of the existing resume transformer. It
    contains neither a new execution history nor a surviving old handle.
    The timeout constructor below obtains that handle from registration. *)
Definition mutex_pend_cleanup_observation sg resumed eid code cleaning tid node : Prop :=
  sem_pend_cleanup_entry sg cleaning tid node /\
  mutex_pend_resume_result sg eid resumed code
    (event_pend_cleanup_state sg false cleaning tid node).

Lemma mutex_pend_cleanup_observation_result : forall sg resumed eid code cleaning tid node,
  mutex_pend_cleanup_observation sg resumed eid code cleaning tid node ->
  mutex_pend_resume_result sg eid resumed code (event_pend_cleanup_state sg false cleaning tid node).
Proof. intros * H; exact (proj2 H). Qed.

Lemma mutex_pend_resume_cleanup_without_timeout : forall sg resumed eid tid old,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) <> PendTimeout ->
  mutex_pend_cleanup_observation sg resumed eid
    (encode_os_err_code (sem_pend_resume_error (encode_pend_status old.(statPend)))) resumed tid old.
Proof.
  intros sg resumed eid tid old Hentry Hnotimeout.
  destruct Hentry as [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  split.
  - unfold sem_pend_cleanup_entry.
    split; [exact Hvalid|]. split; [exact Hcur|]. split; [exact Hold|].
    split; [destruct old.(statPend); assumption || contradiction|].
    split; [exact Hmulti|]. split; assumption.
  - exists (sem_pend_resume_error (encode_pend_status old.(statPend))).
    split; [reflexivity|]. exists tid, old.
    split; [exact Hcur|]. split; [exact Hold|]. split; [reflexivity|].
    destruct old.(statPend); reflexivity || contradiction.
Qed.

Lemma mutex_pend_resume_timeout_event : forall sg resumed eid tid old,
  sem_pend_resume_entry sg resumed eid tid old ->
  encode_pend_status old.(statPend) <> 0 -> encode_pend_status old.(statPend) <> 2 ->
  old.(statPend) = PendTimeout /\
  exists current, mutex_query_lookup resumed eid current /\ In tid current.(waitList).
Proof.
  intros sg resumed eid tid old [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]] Hnotok Hnotabort.
  assert (Htimeout : old.(statPend) = PendTimeout)
    by (destruct old.(statPend); cbn in *; congruence).
  split; [exact Htimeout|]. rewrite Htimeout in Hregistration.
  eapply sem_pend_resume_timeout_event; eassumption.
Qed.

Lemma mutex_pend_resume_cleanup_timeout : forall sg resumed eid tid old current,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) = PendTimeout ->
  mutex_query_lookup resumed eid current ->
  mutex_pend_cleanup_observation sg resumed eid 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None).
Proof.
  intros sg resumed eid tid old current Hentry Htimeout He.
  destruct Hentry as [Hvalid [Hcur [Hold [[Hmulti [Hflag Hregistration]] Hready]]]].
  rewrite Htimeout in Hregistration.
  destruct (sem_pend_resume_timeout_event sg resumed eid tid old Hvalid Hold Hregistration)
    as [found [Hfound Hin]].
  assert (found = current) by congruence; subst found.
  split.
  - unfold sem_pend_cleanup_entry.
    split; [eapply UCOS2_event_task_remove_preserves_validity; eassumption|].
    split; [exact Hcur|]. split.
    + cbn [event_task_remove_state replace_TskS replace_EventS TskState glob_task_set_usedtask inUsedTaskStates].
      rewrite Z.eqb_refl; reflexivity.
    + split; [reflexivity|]. split; [exact Hmulti|]. split; assumption.
  - exists OS_ERR_TIMEOUT; split; [reflexivity|]. exists tid, old.
    split; [exact Hcur|]. split; [exact Hold|]. rewrite Htimeout.
    split; [reflexivity|]. exists current; auto.
Qed.

(** The acquired state stays the original first Save endpoint even if
    priority inheritance changed the live world before EventTaskWait. *)
Lemma mutex_pend_wait_call_restore_merge : forall environment critical saved_local sg call
  saved acquired inherited eid current tid old timeout,
  mutex_pend_wait_entry sg inherited eid current tid old ->
  task_stack_live_coverage inherited.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  mutex_pend_wait_call_post sg inherited eid current tid old timeout **
  task_tcb_init_continuation_capsules environment saved_local inherited |--
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired
    (event_pend_state sg inherited eid current tid old PendMutex timeout).
Proof.
  intros * Hentry Hcoverage.
  pose proof Hentry as [_ [_ [Hold _]]].
  unfold task_tcb_init_continuation_capsules.
  sep_apply_l_atomic (sem_pend_task_field_update_continuations _ _ _
    environment.(task_stack_call_continuations) (task_create_continuation_local saved_local)
    inherited.(TskState) (task_stack_call_active_key call) tid old
    (task_set_event_ptr (task_prepare_event_wait old PendMutex timeout) (Some eid))
    Hold eq_refl eq_refl Hcoverage).
  sep_apply_l_atomic (mutex_pend_wait_call_merge sg inherited eid current tid old timeout Hentry).
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_continuation_capsules.
  cbn [event_pend_state event_wait_state replace_TskS replace_SchedS replace_EventS TskState
    glob_task_set_usedtask parkedTaskStacks].
  entailer!.
Qed.

Lemma mutex_pend_wait_restore_facts : forall environment critical sg original initial observed eid timeout waiting
  call checkpoint returned current,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg checkpoint ->
  (forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action) ->
  mutex_pend_wait_at sg original initial observed eid timeout waiting call checkpoint ->
  sem_pend_wait_sched_entry sg call checkpoint ->
  sem_pend_modular_call_history environment critical sg call checkpoint returned current ->
  sem_pend_blocking_rely sg checkpoint current ->
  mutex_pend_wait_at sg original initial observed eid timeout waiting returned current /\
  sem_pend_wait_sched_entry sg returned current.
Proof.
  intros * Hlayout Hvalid Hclients Hwait Hentry Hhistory Hrely; split.
  - eapply mutex_pend_wait_at_modular_return; eassumption.
  - eapply sem_pend_wait_sched_entry_modular_return; try eassumption.
    exact (proj1 (proj2 (proj2 Hentry))).
Qed.

Lemma mutex_pend_selected_cleanup_split : forall sg original initial observed eid timeout waiting call resumed,
  mutex_pend_wait_selected_at sg original initial observed eid timeout waiting call resumed ->
  UCOS2_inv sg resumed |--
  EX node, coq_prop (sem_pend_resume_entry sg resumed eid
    original.(os_sched_call_stack).(stackLeaseSlot) node) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) **
   tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStat
     (Some (encode_task_status node.(stat))) **
   tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStatPend
     (Some (encode_pend_status node.(statPend))) **
   tcb_cell (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBEventPtr
     (Some (encode_event_link sg node.(eventPtr))) **
   sem_pend_cleanup_frame sg resumed original.(os_sched_call_stack).(stackLeaseSlot) node).
Proof.
  intros * [_ [node Hentry]].
  pose proof Hentry as [Hvalid [Hcur [Hnode _]]].
  sep_apply_l_atomic (sem_pend_cleanup_split sg resumed _ node Hvalid Hcur Hnode).
  Exists node; entailer!.
Qed.

(** Timeout removes the current registration and then reaches the same
    native cleanup stores. The complete saved-continuation map is
    reindexed only through the actual EventPtr update. *)
Lemma mutex_pend_remove_call_cleanup_split : forall environment saved_local sg call resumed eid current tid old,
  sem_pend_resume_entry sg resumed eid tid old -> old.(statPend) = PendTimeout ->
  mutex_query_lookup resumed eid current -> event_object_layout_prop sg eid ->
  task_stack_live_coverage resumed.(TskState) (task_stack_call_active_key call) ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  event_task_remove_post (task_slot_addr sg tid)
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventGrp")
    &(((event_addr sg eid)) # "os_event" ->ₛ "OSEventTbl")
    (old.(curPrio) / 8) (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio))
    (encode_event_wait_tbl_at_or current.(waitList) resumed.(TskState) (old.(curPrio) / 8))
    (encode_event_wait_grp current.(waitList) resumed.(TskState)) **
  sem_pend_remove_call_frame sg resumed eid current tid old **
  task_tcb_init_continuation_capsules environment saved_local resumed |--
  coq_prop (mutex_pend_cleanup_observation sg resumed eid 10
    (event_task_remove_state resumed eid current tid old) tid (task_set_event_ptr old None) /\
    task_stack_live_coverage (event_task_remove_state resumed eid current tid old).(TskState)
      (task_stack_call_active_key call)) &&
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
   tcb_cell (task_slot_addr sg tid) TCBStat (Some (encode_task_status old.(stat))) **
   tcb_cell (task_slot_addr sg tid) TCBStatPend (Some (encode_pend_status old.(statPend))) **
   tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
   sem_pend_cleanup_frame sg (event_task_remove_state resumed eid current tid old) tid
     (task_set_event_ptr old None) **
   task_tcb_init_continuation_capsules environment saved_local
     (event_task_remove_state resumed eid current tid old)).
Proof.
  intros * Hentry Htimeout He Hlayout Hcoverage.
  pose proof (mutex_pend_resume_cleanup_timeout sg resumed eid tid old current Hentry Htimeout He) as Hcleanup.
  pose proof Hentry as [_ [_ [Hold _]]].
  pose proof (proj1 Hcleanup) as [Hvalid [Hcur [Hnode Hrest]]].
  unfold task_tcb_init_continuation_capsules.
  sep_apply_l_atomic (sem_pend_task_field_update_continuations _ _ _
    environment.(task_stack_call_continuations) (task_create_continuation_local saved_local)
    resumed.(TskState) (task_stack_call_active_key call) tid old (task_set_event_ptr old None)
    Hold eq_refl eq_refl Hcoverage).
  sepcon_assoc_change.
  sep_apply_l_atomic (sem_pend_remove_call_merge sg resumed eid current tid old Hentry Htimeout He Hlayout).
  Intros.
  sep_apply_l_atomic (sem_pend_cleanup_split sg (event_task_remove_state resumed eid current tid old)
    tid (task_set_event_ptr old None) Hvalid Hcur Hnode).
  cbn [event_task_remove_state replace_TskS replace_EventS TskState
    glob_task_set_usedtask parkedTaskStacks task_set_event_ptr stat statPend eventPtr encode_event_link].
  entailer!.
Qed.

Lemma mutex_pend_cleanup_restore_merge : forall environment critical saved_local sg call saved acquired
  resumed eid code cleaning tid node,
  mutex_pend_cleanup_observation sg resumed eid code cleaning tid node ->
  task_stack_live_coverage cleaning.(TskState) (task_stack_call_active_key call) ->
  critical_region_masked environment.(task_stack_call_platform) critical sg
    call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
  os_sched_context_resources environment.(task_stack_call_external) call **
  (sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
   tcb_cell (task_slot_addr sg tid) TCBStat (Some 0) **
   tcb_cell (task_slot_addr sg tid) TCBStatPend (Some 0) **
   tcb_cell (task_slot_addr sg tid) TCBEventPtr (Some 0) **
   sem_pend_cleanup_frame sg cleaning tid node) **
  task_tcb_init_continuation_capsules environment saved_local cleaning |--
  task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired
    (event_pend_cleanup_state sg false cleaning tid node).
Proof.
  intros * [Hentry Hresult] Hcoverage.
  pose proof Hentry as [Hvalid [_ [Hold _]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  unfold task_tcb_init_continuation_capsules.
  sep_apply_l_atomic (sem_pend_task_field_update_continuations _ _ _
    environment.(task_stack_call_continuations) (task_create_continuation_local saved_local)
    cleaning.(TskState) (task_stack_call_active_key call) tid node
    (task_event_pend_cleanup false false node) Hold eq_refl eq_refl Hcoverage).
  sepcon_assoc_change.
  sep_apply_l_atomic (sem_pend_cleanup_merge sg cleaning tid node Hentry).
  unfold task_tcb_init_continuation_restore_input, task_tcb_init_continuation_capsules.
  cbn [event_pend_cleanup_state replace_TskS TskState glob_task_set_usedtask parkedTaskStacks].
  rewrite Hmulti; entailer!.
Qed.
