Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_post_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.lib.sem.
Require Export Ucos2Verify.lib.cross_module_invariants.

Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** V2.93.01 selected source profile, including its real NULL branch. *)
Definition sem_post_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true.

Definition sem_post_lookup (s : UCOS2_Verify_State) (eid : EventID)
  (e : OSEventAbstractState) : Prop := s.(EventState).(inUsedEventStates) eid = Some e.

(** Explicit caller handle lifetime, not a CPU guarantee: foreign clients
    may change the count, waiters, and the rest of the kernel. *)
Definition sem_post_handle_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) : Prop :=
  forall action before after previous,
    critical_region_clients critical action ->
    kernel_client_actor action <> Some invocation ->
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    sem_post_lookup before eid previous ->
    exists current, sem_post_lookup after eid current /\
      current.(eventGeneration) = previous.(eventGeneration) /\
      current.(eventType) = previous.(eventType).

Lemma sem_post_handle_interval_preserves_identity :
  forall critical sg invocation eid before after previous,
  sem_post_handle_protocol critical sg invocation eid ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> sem_post_lookup before eid previous ->
  exists current, sem_post_lookup after eid current /\
    current.(eventGeneration) = previous.(eventGeneration) /\
    current.(eventType) = previous.(eventType).
Proof.
  intros critical sg invocation eid before after previous Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval; revert previous.
  induction Hinterval as
    [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hvalid Hlookup.
  - exists previous; repeat split; assumption || reflexivity.
  - destruct (Hprotocol action before middle previous Hin Hforeign Hvalid Hstep Hlookup)
      as [next [Hnext [Hgeneration Htype]]].
    pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin)
      sg before middle Hvalid Hstep) as Hmiddle.
    destruct (IH next Hmiddle Hnext) as [current [Hcurrent [Hgen Htyp]]].
    exists current; split; [exact Hcurrent|]; split; congruence.
Qed.

(** OS_Sched has its own subsequent acquisition, stack and port obligation.
    This caller obligation is conditional on the real wake arm; it is not
    an executable guard or a demand that ISR/locked/count-only calls schedule. *)
Definition sem_post_acquire_safety (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (eid : EventID) (before : UCOS2_Verify_State) : Prop :=
  forall entry checkpoint,
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    sem_post_critical sg eid entry (OS_ERR_NONE, true) checkpoint ->
    os_sched_acquire_safety external critical sg context checkpoint.

Definition sem_post_acquire_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (eid : EventID) (mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  sem_post_lookup before eid observed /\ sem_post_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_SEM /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration) /\
  (forall checkpoint, sem_post_critical sg eid entry (OS_ERR_NONE, true) checkpoint ->
     os_sched_acquire_safety external critical sg context checkpoint).

Lemma sem_post_save_consequence :
  forall external critical sg context eid mask saved before entry observed,
  sem_post_handle_protocol critical sg context.(os_sched_call_invocation) eid ->
  sem_post_acquire_safety external critical sg context eid before ->
  UCOS2_state_inv sg before -> sem_post_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_SEM ->
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry |-- EX current,
    coq_prop (sem_post_acquire_facts external critical sg context eid mask saved
      before entry observed current) && UCOS2_inv sg entry.
Proof.
  intros external critical sg context eid mask saved before entry observed
    Hprotocol Hsafe Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (sem_post_handle_interval_preserves_identity critical sg
    context.(os_sched_call_invocation) eid before entry observed
    Hprotocol Hinterval Hvalid Hlookup) as [current [Hcurrent [Hgen HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    context.(os_sched_call_invocation) before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : sem_post_acquire_facts external critical sg context eid mask saved
    before entry observed current).
  { unfold sem_post_acquire_facts; split; [exact Hinterval|].
    split; [exact Hentry|]; split; [exact Hsaved|]; split; [exact Hlookup|].
    split; [exact Hcurrent|]; split; [exact Htype|]; split; [congruence|].
    split; [exact Hgen|]; intros checkpoint Hstep; eapply Hsafe; eassumption. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Definition sem_post_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (mask : Z) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (interrupt_platform_running platform context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask **
     critical_region_outside critical sg context.(os_sched_call_invocation) state).

Lemma sem_post_closed_equiv : forall platform critical sg context mask state,
  sem_post_closed platform critical sg context mask state --||--
    (interrupt_platform_running platform context.(os_sched_call_invocation)
      context.(os_sched_call_origin) mask ** UCOS2_inv sg state).
Proof.
  intros; unfold sem_post_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running; unfold UCOS2_inv; split; entailer!.
Qed.

(** The full representation is borrowed for each observation, then closed
    before acquisition. Padding, free images, queues and all other modules
    remain in the same separation-logic frame. *)
Definition sem_post_field_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) (field : EventField) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) node) field **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Lemma sem_post_field_split_full : forall sg state eid node field,
  sem_post_lookup state eid node ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    (event_cell (event_addr sg eid) field ((event_image sg state.(TskState) node) field) **
     sem_post_field_frame sg state eid node field).
Proof.
  intros sg state eid node field Hlookup Hfield.
  rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState)
    eid node Hlookup).
  unfold used_event_rep.
  sep_apply_l_atomic (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) node) field Hfield).
  unfold sem_post_field_frame; entailer!.
Qed.

Lemma sem_post_field_merge_full : forall sg state eid node field,
  UCOS2_state_inv sg state -> sem_post_lookup state eid node ->
  In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
  event_cell (event_addr sg eid) field ((event_image sg state.(TskState) node) field) **
    sem_post_field_frame sg state eid node field |-- UCOS2_inv sg state.
Proof.
  intros sg state eid node field Hvalid Hlookup Hfield; unfold sem_post_field_frame.
  sep_apply_l_atomic (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_image sg state.(TskState) node) field Hfield).
  fold (used_event_rep sg state.(TskState) eid node).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState)
    eid node Hlookup).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

Definition sem_post_type_frame sg state eid node :=
  sem_post_field_frame sg state eid node EventTypeField.
Definition sem_post_group_frame sg state eid node :=
  sem_post_field_frame sg state eid node EventGrpField.
Definition sem_post_group (entry : UCOS2_Verify_State) (current : OSEventAbstractState) : Z :=
  encode_event_wait_grp current.(waitList) entry.(TskState).

Definition sem_post_count_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : Assertion :=
  sem_rep_no_count sg entry.(TskState) eid current **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  queue_storage_rep sg entry.(EventState) ** UCOS2_raw_rep_missing_event_queue sg entry.

Lemma sem_post_count_split_full : forall sg entry eid current,
  sem_post_lookup entry eid current -> current.(eventType) = OS_EVENT_TYPE_SEM ->
  UCOS2_inv sg entry |--
    coq_prop (UCOS2_state_inv sg entry /\ 0 <= encode_event_cnt_value current <= 65535) &&
    ((event_addr sg eid + OSEventCnt_off) # UShort |-> encode_event_cnt_value current **
     sem_post_count_frame sg entry eid current).
Proof.
  intros sg entry eid current Hlookup Htype.
  rewrite UCOS2_inv_split_event_queue; Intros.
  match goal with Hvalid : UCOS2_state_inv sg entry |- _ =>
    pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]] end.
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields;
    [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  sep_apply_l_atomic (sem_rep_split_count sg entry.(TskState) eid current fields Htype Hfields).
  rewrite Hcount; unfold sem_post_count_frame; destruct Hpayload as [Hrange Hwait]; entailer!.
Qed.

Definition sem_post_count_checkpoint (entry : UCOS2_Verify_State)
  (eid : EventID) (current : OSEventAbstractState) : UCOS2_Verify_State :=
  if Z.ltb (encode_event_cnt_value current) 65535
  then sem_count_update_state entry eid current (encode_event_cnt_value current + 1) else entry.

Definition sem_post_stored_count (current : OSEventAbstractState) : Z :=
  let count := encode_event_cnt_value current in
  if Z.ltb count 65535 then count + 1 else count.

Definition sem_post_count_error (current : OSEventAbstractState) : OSErrCode :=
  if Z.ltb (encode_event_cnt_value current) 65535 then OS_ERR_NONE else OS_ERR_SEM_OVF.

Lemma sem_post_count_checkpoint_critical : forall sg entry eid current,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_group entry current = 0 ->
  sem_post_critical sg eid entry (sem_post_count_error current, false)
    (sem_post_count_checkpoint entry eid current).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hempty.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload _]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields;
    [|contradiction].
  exists current; split; [exact Hlookup|].
  unfold sem_post_group in Hempty; rewrite Hempty, Z.eqb_refl.
  exists fields; split; [exact Hfields|].
  unfold sem_post_count_checkpoint, sem_post_count_error, encode_event_cnt_value.
  rewrite Htype, Hfields; destruct (Z.ltb fields.(semCount) 65535); split; reflexivity.
Qed.

Lemma sem_post_count_merge_checkpoint : forall sg entry eid current,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_group entry current = 0 ->
  (event_addr sg eid + OSEventCnt_off) # UShort |-> sem_post_stored_count current **
    sem_post_count_frame sg entry eid current |--
    UCOS2_inv sg (sem_post_count_checkpoint entry eid current).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hempty.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [_ [Hpayload [_ Hentries]]]]]] _]]]].
  specialize (Hpayload eid current Hlookup); unfold event_payload_consistency in Hpayload.
  rewrite Htype in Hpayload; destruct current.(semFields) as [fields|] eqn:Hfields;
    [|contradiction].
  assert (Hcount : encode_event_cnt_value current = fields.(semCount)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields; reflexivity. }
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg entry.(TskState)
    current.(waitList) (proj1 (Hentries eid current Hlookup))) Hempty) as Hlist.
  unfold sem_post_stored_count, sem_post_count_checkpoint, sem_post_count_frame.
  rewrite Hcount; destruct (Z.ltb fields.(semCount) 65535) eqn:Hroom.
  - assert (Hupdated : sem_fields_consistency current.(waitList)
      {| semCount := fields.(semCount) + 1 |}).
    { rewrite Hlist in Hpayload |- *; apply sem_increment_preserves_consistency;
        [exact Hpayload|apply Z.ltb_lt; exact Hroom]. }
    sep_apply_l_atomic (UCOS2_inv_merge_sem_count sg entry eid current
      (fields.(semCount) + 1) Hvalid Hlookup Htype Hupdated); entailer!.
  - sep_apply_l_atomic (sem_rep_merge_count sg entry.(TskState) eid current fields Htype Hfields).
    sep_apply_l_atomic (event_raw_rep_merge_eid sg entry.(TskState) entry.(EventState)
      eid current Hlookup).
    rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.

(** The original invocation's ordinary return follows OS_Sched's verified
    return contract, including a fresh acquisition and possible later
    resumption. A retired invocation is not fabricated as a C return. *)
Definition sem_post_call_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent : addr) : program UCOS2_Verify_State Z :=
  fun before returned final =>
    (pevent = 0 /\ returned = encode_os_err_code OS_ERR_PEVENT_NULL /\ final = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\
      sem_post_lookup before eid observed /\
      ((observed.(eventType) <> OS_EVENT_TYPE_SEM /\
        returned = encode_os_err_code OS_ERR_EVENT_TYPE /\ final = before) \/
       (observed.(eventType) = OS_EVENT_TYPE_SEM /\ exists entry current error requests checkpoint,
        critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
        sem_post_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
        current.(eventGeneration) = observed.(eventGeneration) /\
        sem_post_critical sg eid entry (error, requests) checkpoint /\
        returned = encode_os_err_code error /\
        if requests then exists selected resumed,
          critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected /\
          os_sched_c_return external critical sg selected context resumed final
        else final = checkpoint))).

Definition sem_post_call_input (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent : addr)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/
  (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
   sem_post_lookup before eid observed /\
   (observed.(eventType) = OS_EVENT_TYPE_SEM ->
    sem_post_handle_protocol critical sg context.(os_sched_call_invocation) eid /\
    sem_post_acquire_safety external critical sg context eid before)).

Definition observe_sem_post_error (error : Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret error.

Lemma sem_post_safe_return : forall (c : program UCOS2_Verify_State Z) before after error X,
  c before error after ->
  safeExec (LastSeen before) (bind (atomic_cmd c) observe_sem_post_error) X ->
  safeExec (LastSeen after) (StateRelMonad.ret error) X.
Proof.
  intros c before after error X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c) (LastSeen before) (LastSeen after) error).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P0 HP0.
    exists (RTrans_Abs after); split.
    - exists before, after; split; [apply HP0; exact I|].
      split; [exact Hsem|intro state; split; trivial].
    - intro state; split; trivial. }
  exact (highstepbind_derive _ _ _ error (LastSeen after) Hatomic X Hexec).
Qed.

Definition sem_post_call_post_prop external critical sg context pevent before error after : Prop :=
  sem_post_call_program external critical sg context pevent before error after.

Definition sem_post_return_resources (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context resumed : OsSchedCallContext) (mask : Z)
  (after : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) mask **
  critical_region_outside critical sg context.(os_sched_call_invocation) after **
  os_sched_context_resources external resumed ** unmap_table_rep sg.

(** Match the generated Ensure convention for heap-independent [coq_prop]:
    its spatial frame carries the established source/continuation facts,
    while every concrete return resource remains explicitly required. *)
Definition sem_post_call_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask pevent : Z)
  (before : UCOS2_Verify_State) (error : Z)
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop) : Assertion :=
  EX after, EX resumed,
    coq_prop (sem_post_call_program external critical sg context pevent before error after /\
      UCOS2_state_inv sg after /\ safeExec (LastSeen after) (StateRelMonad.ret error) X) **
    sem_post_return_resources external platform critical sg context resumed mask after.

Lemma sem_post_sched_return_preserves_validity :
  forall external critical sg context checkpoint selected resumed final,
  UCOS2_state_inv sg checkpoint ->
  os_sched_acquire_safety external critical sg context checkpoint ->
  critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected ->
  os_sched_c_return external critical sg selected context resumed final ->
  UCOS2_state_inv sg final.
Proof.
  intros external critical sg context checkpoint selected resumed final Hvalid Hsafe Hinterval Hreturn.
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    context.(os_sched_call_invocation) checkpoint selected Hinterval Hvalid)) as Hselected.
  pose proof (os_sched_ready_checkpoint_preserves_validity sg selected Hselected) as Hprefix.
  unfold os_sched_c_return in Hreturn.
  destruct (os_sched_requests_switch selected) eqn:Hswitch.
  - exact (os_sched_switch_outcome_preserves_validity external critical sg selected context
      (OsSchedOriginalResumed resumed final) Hprefix
      (proj2 (Hsafe selected Hinterval) Hswitch) Hreturn).
  - destruct Hreturn as [_ ->]; exact Hprefix.
Qed.

Definition sem_post_wake_result (sg : StableGlobVars) (eid : EventID)
  (entry after : UCOS2_Verify_State) (priority : Z) : Prop :=
  event_task_rdy sg entry eid PendSem 0 PendOK = Some (priority, after).

Definition sem_post_critical_result (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (error requests : Z) (checkpoint : UCOS2_Verify_State) : Prop :=
  exists (code : OSErrCode) (requested : bool),
    error = encode_os_err_code code /\ requests = (if requested then 1 else 0) /\
    sem_post_critical sg eid entry (code, requested) checkpoint.

Lemma sem_post_wake_result_critical : forall sg eid entry current after priority,
  sem_post_lookup entry eid current -> sem_post_group entry current <> 0 ->
  sem_post_wake_result sg eid entry after priority ->
  sem_post_critical sg eid entry (OS_ERR_NONE, true) after.
Proof.
  intros sg eid entry current after priority Hlookup Hgroup Hwake.
  exists current; split; [exact Hlookup|].
  unfold sem_post_group in Hgroup; rewrite (proj2 (Z.eqb_neq _ _) Hgroup).
  split; [reflexivity|]; exists priority; exact Hwake.
Qed.

Lemma sem_post_call_null_return : forall external critical sg context before,
  sem_post_call_program external critical sg context 0 before
    (encode_os_err_code OS_ERR_PEVENT_NULL) before.
Proof. intros; left; repeat split; reflexivity. Qed.

Lemma sem_post_call_wrong_type_return : forall external critical sg context pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_post_lookup before eid observed -> observed.(eventType) <> OS_EVENT_TYPE_SEM ->
  sem_post_call_program external critical sg context pe before
    (encode_os_err_code OS_ERR_EVENT_TYPE) before.
Proof.
  intros; right; split; [assumption|]; exists eid, observed.
  split; [assumption|]; split; [assumption|]; split; [assumption|].
  left; repeat split; assumption || reflexivity.
Qed.

Lemma sem_post_call_protected_return :
  forall external critical sg context pe before eid observed mask saved entry current
    error requests checkpoint final,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_post_acquire_facts external critical sg context eid mask saved before entry observed current ->
  sem_post_critical sg eid entry (error, requests) checkpoint ->
  (if requests then exists selected resumed,
     critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected /\
     os_sched_c_return external critical sg selected context resumed final
   else final = checkpoint) ->
  sem_post_call_program external critical sg context pe before (encode_os_err_code error) final.
Proof.
  intros external critical sg context pe before eid observed mask saved entry current
    error requests checkpoint final Hnonzero Haddr Hid
    [Hinterval [Hvalid [Hsaved [Hbefore [Hcurrent [Htype [Hsem [Hgen Hsafe]]]]]]]] Hstep Hreturn.
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hbefore|].
  right; split; [exact Htype|]; exists entry, current, error, requests, checkpoint.
  split; [exact Hinterval|]; split; [exact Hcurrent|]; split; [exact Hsem|].
  split; [exact Hgen|]; split; [exact Hstep|]; split; [reflexivity|exact Hreturn].
Qed.

(** Actual residual of the raw OS_EventTaskRdy call. The priority table is
    lent to the callee; no second table or TCB image is hidden in this frame. *)
Definition sem_post_task_frame (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (tid : TaskID) : Assertion :=
  store_map_missing_i (used_task_rep sg) tasks.(inUsedTaskStates) tid **
  task_free_storage_rep sg tasks.(taskLifecycle).(taskFreeStorage) tasks.(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error tasks.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg tasks.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> tasks.(taskCount) ** task_reg_allocator_rep sg tasks.

Lemma sem_post_task_storage_split : forall sg tasks tid old,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tasks.(inUsedTaskStates) tid = Some old ->
  task_public_storage sg tasks |--
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg old) **
  store_prio_tbl sg tasks.(prioTbl) ** sem_post_task_frame sg tasks tid.
Proof.
  intros sg tasks tid old Hmulti Hprofile Hold.
  sep_apply_l_atomic (task_public_storage_split_task sg tasks tid old Hold).
  rewrite used_task_rep_tcb64, task_slot_addr_tcb64 by assumption.
  unfold task_public_storage_without_task, task_public_storage_without_used_map,
    sem_post_task_frame; entailer!.
Qed.

Lemma sem_post_task_storage_merge : forall sg tasks tid new,
  sg.(osKernelConfig).(cfgEventMultiEnabled) = false ->
  sg.(osKernelConfig).(cfgTaskProfile) = false ->
  tcb64_storage_rep (task_slot_addr sg tid) (task_tcb64_image sg new) **
  store_prio_tbl sg tasks.(prioTbl) ** sem_post_task_frame sg tasks tid |--
  task_public_storage sg (glob_task_set_usedtask tasks tid new).
Proof.
  intros sg tasks tid new Hmulti Hprofile.
  rewrite task_slot_addr_tcb64 by assumption.
  rewrite <- used_task_rep_tcb64 by assumption.
  eapply derivable1_trans; [|apply task_public_storage_merge_updated_task].
  unfold sem_post_task_frame, task_public_storage_without_task,
    task_public_storage_without_used_map; entailer!.
Qed.

Definition sem_post_wake_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (tid : TaskID) : Assertion :=
  sem_post_task_frame sg entry.(TskState) tid **
  sched_physical_rep sg entry.(SchedState) **
  event_raw_rep_no_eid sg entry.(TskState) entry.(EventState) eid **
  UCOS2_raw_rep_missing_task_storage_sched_event sg entry.

Lemma sem_post_wake_split_full : forall sg entry eid current,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM -> sem_post_group entry current <> 0 ->
  event_object_layout_prop sg eid ->
  UCOS2_inv sg entry ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg entry.(TskState) eid current tid old) &&
    (event_task_rdy_pre sg entry.(TskState) eid current tid old 1 0
      (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
      (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
     sem_post_wake_frame sg entry eid tid).
Proof.
  intros sg entry eid current Hvalid Hlookup Htype Hnonempty Hlayout.
  pose proof Hvalid as [Hprofile [Htasks [_ [Hevents _]]]].
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct current.(waitList) as [|tid tail] eqn:Hlist;
    [contradiction Hnonempty; unfold sem_post_group; rewrite Hlist; reflexivity|].
  destruct (event_wake_head sg entry eid current tid tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [old [Hold [Hstep [Hafter Hlast]]]].
  pose proof Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  assert (Hentry : event_task_rdy_entry sg entry.(TskState) eid current tid old).
  { unfold event_task_rdy_entry; split; [exact Hsg|]; split; [exact Hlayout|].
    split; [exact Hmulti|]; split; [exact Htasks|]; split; [exact (Hentries eid current Hlookup)|].
    split; [rewrite Hlist; reflexivity|exact Hold]. }
  rewrite UCOS2_inv_open_task_storage_sched_event; Intros.
  sep_apply_l_atomic (sem_post_task_storage_split sg entry.(TskState) tid old Hmulti Hprofiling Hold).
  sep_apply_l_atomic (event_raw_rep_split_eid sg entry.(TskState) entry.(EventState)
    eid current Hlookup).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv.
  Exists tid old; unfold event_task_rdy_pre, sem_post_wake_frame, used_event_rep.
  entailer!; unfold sched_row_values; reflexivity.
Qed.

Lemma sem_post_wake_merge_full : forall sg entry eid current tid old priority,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  event_task_rdy_entry sg entry.(TskState) eid current tid old ->
  event_task_rdy_post sg entry.(TskState) eid current tid old 0 1 0
    (encode_ready_grp entry.(SchedState).(readyList) entry.(TskState))
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg entry eid tid |-- EX after,
    coq_prop (sem_post_wake_result sg eid entry after priority) &&
    (UCOS2_inv sg after ** unmap_table_rep sg).
Proof.
  intros sg entry eid current tid old priority Hvalid Hlookup Htype Hentry.
  pose proof Hentry as [Hsg [Hlayout [Hmulti [Htasks [Hwait [Hhead Hold]]]]]].
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (event_task_rdy_selection sg entry.(TskState) eid current tid old Hentry)
    as [_ [_ [_ [Hprio _]]]].
  assert (Hkind : event_type_to_pend_type current.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct current.(waitList) as [|head tail] eqn:Hlist; [discriminate|].
  inversion Hhead; subst head.
  destruct (event_wake_head sg entry eid current tid tail PendSem 0 PendOK
    Hvalid Hlookup Hkind Hlist) as [found [Hfound [Hstep [Hafter Hlast]]]].
  assert (found = old) by congruence; subst found.
  unfold event_task_rdy_post, sem_post_wake_frame; Intros.
  assert (Hreturned : priority = old.(curPrio)) by tauto; subst priority.
  rewrite (event_task_rdy_typed_image_eq sg old 0 1 0 PendSem PendOK eq_refl eq_refl).
  rewrite (event_task_rdy_scheduler_group_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold).
  rewrite (event_task_rdy_scheduler_rows_eq sg entry.(TskState) entry.(SchedState) tid old _ Hold Hprio).
  sep_apply_l_atomic (sem_post_task_storage_merge sg entry.(TskState) tid
    (task_event_wake_single old PendSem 0 PendOK) Hmulti Hprofiling).
  fold (used_event_rep sg entry.(TskState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  sep_apply_l_atomic (event_raw_rep_merge_updated_eid sg entry.(TskState) entry.(EventState) eid
    (event_set_wait_list current (remove_Z_eqb tid current.(waitList)))).
  rewrite <- sched_rows_array_equiv.
  rewrite <- (sched_wake_by_status_physical_rep_eq sg entry.(TskState) entry.(SchedState) tid
    (task_status_clear_wait (encode_task_status old.(stat)) 1)).
  assert (Hstatus : task_status_clear_wait (encode_task_status old.(stat)) 1 =
    encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat)).
  { change (task_status_clear_wait (encode_task_status old.(stat)) 1 =
      encode_task_status (task_clear_pending_status old.(stat) PendSem)).
    rewrite task_clear_pending_status_encoding; reflexivity. }
  rewrite Hstatus.
  assert (Hindex : forall s, sched_raw_rep sg entry.(TskState) s =
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendSem 0 PendOK)) s).
  { intro s; apply sched_raw_rep_priority_ext; intros slot Hin.
    simpl; destruct (Z.eqb slot tid) eqn:E; [apply Z.eqb_eq in E; subst slot; rewrite Hold|]; reflexivity. }
  set (woken_sched := sched_wake_by_status sg entry.(TskState) entry.(SchedState) tid
    (encode_task_status (task_event_wake_single old PendSem 0 PendOK).(stat))).
  assert (Hsched :
    sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp woken_sched.(readyList) entry.(TskState) **
    sched_rows_rep sg entry.(TskState) woken_sched.(readyList) [0;1;2;3;4;5;6;7] **
    sched_physical_rep sg woken_sched |--
    sched_raw_rep sg (glob_task_set_usedtask entry.(TskState) tid
      (task_event_wake_single old PendSem 0 PendOK)) woken_sched).
  { rewrite <- Hindex; unfold sched_raw_rep; reflexivity. }
  sep_apply_l_atomic Hsched.
  pose proof (UCOS2_inv_merge_event_wake sg entry eid current tid old PendSem 0 PendOK
    Hvalid Hlookup ltac:(rewrite Hlist; left; reflexivity) Hold Hkind) as Hmerge.
  cbn zeta in Hmerge.
  cbn [event_wake_state replace_SchedS replace_EventS replace_TskS
    TskState SchedState EventState] in Hmerge.
  fold woken_sched in Hmerge.
  sep_apply_l_atomic Hmerge.
  Exists (event_wake_state sg entry eid current tid old PendSem 0 PendOK).
  unfold sem_post_wake_result; entailer!.
Qed.

Lemma sem_post_closed_return : forall external platform critical sg context mask pe before after error X,
  sem_post_call_program external critical sg context pe before error after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_post_call_program external critical sg context pe)) observe_sem_post_error) X ->
  sem_post_closed platform critical sg context mask after **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  sem_post_call_post external platform critical sg context mask pe before error X.
Proof.
  intros external platform critical sg context mask pe before after error X Hstep Hexec.
  pose proof (sem_post_safe_return _ _ _ _ _ Hstep Hexec) as Hreturn.
  unfold sem_post_closed; Intros.
  unfold sem_post_call_post; Exists after context.
  unfold sem_post_return_resources; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold;
    apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma sem_post_count_return :
  forall external platform critical sg context mask pe before eid observed saved entry current
    checkpoint error X,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_post_acquire_facts external critical sg context eid mask saved before entry observed current ->
  sem_post_critical_result sg eid entry error 0 checkpoint ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_post_call_program external critical sg context pe)) observe_sem_post_error) X ->
  sem_post_closed platform critical sg context mask checkpoint **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  sem_post_call_post external platform critical sg context mask pe before error X.
Proof.
  intros external platform critical sg context mask pe before eid observed saved entry current
    checkpoint error X Hnonzero Haddr Hid Hfacts [code [requests [Herror [Hrequests Hstep]]]] Hexec.
  destruct requests; [discriminate|].
  apply sem_post_closed_return; [|exact Hexec].
  rewrite Herror; eapply sem_post_call_protected_return; eauto; reflexivity.
Qed.

Lemma sem_post_scheduled_return :
  forall external platform critical sg context mask pe before eid observed saved entry current
    checkpoint X,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_post_acquire_facts external critical sg context eid mask saved before entry observed current ->
  sem_post_critical_result sg eid entry 0 1 checkpoint ->
  UCOS2_state_inv sg checkpoint ->
  os_sched_acquire_safety external critical sg context checkpoint ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_post_call_program external critical sg context pe)) observe_sem_post_error) X ->
  os_sched_post external platform critical sg context mask checkpoint |--
    sem_post_call_post external platform critical sg context mask pe before 0 X.
Proof.
  intros external platform critical sg context mask pe before eid observed saved entry current
    checkpoint X Hnonzero Haddr Hid Hfacts [code [requests [Herror [Hrequests Hstep]]]]
    Hvalid Hsafe Hexec.
  destruct requests; [|discriminate].
  unfold os_sched_post; Intros selected final resumed.
  match goal with H : _ /\ os_sched_c_return _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hinterval Hreturn] end.
  pose proof (sem_post_sched_return_preserves_validity external critical sg context
    checkpoint selected resumed final Hvalid Hsafe Hinterval Hreturn) as Hfinal.
  assert (Hcall : sem_post_call_program external critical sg context pe before 0 final).
  { rewrite Herror; eapply sem_post_call_protected_return; try eassumption.
    exists selected, resumed; split; assumption. }
  pose proof (sem_post_safe_return _ _ _ _ _ Hcall Hexec) as HexecFinal.
  unfold sem_post_call_post; Exists final resumed.
  unfold sem_post_return_resources; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold;
    apply derivable1s_coq_prop_r; tauto].
Qed.
