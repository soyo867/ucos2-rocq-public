Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.VC.code.sem.spec.sem_del_call_helpers.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_abort_spec.
Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Definition sem_pend_abort_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgSafetyCritical) = false.

Definition sem_pend_abort_error_cell (p : addr) : Assertion := p # UChar |->_ .

Definition sem_pend_abort_critical_ready (sg : StableGlobVars) (eid : EventID) (opt : Z)
  (entry : UCOS2_Verify_State) (count : Z) (checkpoint : UCOS2_Verify_State) : Prop :=
  sem_pend_abort_critical sg eid opt entry (count, (OS_ERR_PEND_ABORT, true)) checkpoint.

(** Scheduling safety is required only for actual critical endpoints that
    request OS_Sched. No task-only, ISR, lock, or valid-option guard is added. *)
Definition sem_pend_abort_acquire_safety (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (eid : EventID) (opt : Z)
  (before : UCOS2_Verify_State) : Prop :=
  forall entry count checkpoint,
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    sem_pend_abort_critical sg eid opt entry (count, (OS_ERR_PEND_ABORT, true)) checkpoint ->
    os_sched_acquire_safety external critical sg context checkpoint.

(** The full Event layout is consumed only by a real wake call, not NULL,
    wrong-type/FREE, or a SEM with no waiters at its actual acquired entry. *)
Definition sem_pend_abort_wake_layout (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext)
  (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  forall entry current,
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    sem_post_lookup entry eid current -> sem_post_group entry current <> 0 ->
    event_object_layout_prop sg eid.

Definition sem_pend_abort_call_input (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent opt : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/ (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 3 ->
      sem_post_handle_protocol critical sg context.(os_sched_call_invocation) eid /\
      sem_pend_abort_acquire_safety external critical sg context eid opt before)).

Lemma sem_pend_abort_call_input_nonnull :
  forall external critical sg context pe opt before eid observed,
  sem_pend_abort_call_input external critical sg context pe opt before eid observed -> pe <> 0 ->
  pe = event_addr sg eid /\ valid_event_id sg eid /\ sem_query_public_slot before eid observed /\
  (event_slot_type_value before.(EventState) eid = 3 ->
    sem_post_handle_protocol critical sg context.(os_sched_call_invocation) eid /\
    sem_pend_abort_acquire_safety external critical sg context eid opt before).
Proof. intros * [Hzero|[_ Hlive]] Hnonzero; [contradiction|exact Hlive]. Qed.

Definition sem_pend_abort_acquire_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (eid : EventID) (opt mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  sem_post_lookup before eid observed /\ sem_post_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_SEM /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration) /\
  (forall count checkpoint,
    sem_pend_abort_critical sg eid opt entry (count, (OS_ERR_PEND_ABORT, true)) checkpoint ->
    os_sched_acquire_safety external critical sg context checkpoint).

Lemma sem_pend_abort_save_consequence :
  forall external critical sg context eid opt mask saved before entry observed,
  sem_post_handle_protocol critical sg context.(os_sched_call_invocation) eid ->
  sem_pend_abort_acquire_safety external critical sg context eid opt before ->
  UCOS2_state_inv sg before -> sem_post_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_SEM ->
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry |-- EX current,
    coq_prop (sem_pend_abort_acquire_facts external critical sg context eid opt mask saved
      before entry observed current) && UCOS2_inv sg entry.
Proof.
  intros * Hprotocol Hsafe Hvalid Hlookup Htype Hinterval Hsaved.
  destruct (sem_post_handle_interval_preserves_identity critical sg
    context.(os_sched_call_invocation) eid before entry observed
    Hprotocol Hinterval Hvalid Hlookup) as [current [Hcurrent [Hgen HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    context.(os_sched_call_invocation) before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : sem_pend_abort_acquire_facts external critical sg context eid opt mask saved
      before entry observed current).
  { unfold sem_pend_abort_acquire_facts.
    split; [exact Hinterval|]; split; [exact Hentry|]; split; [exact Hsaved|].
    split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
    split; [congruence|]; split; [exact Hgen|].
    intros count checkpoint Hstep; eapply Hsafe; eassumption. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Lemma sem_pend_abort_restore_consequence :
  forall external platform critical sg context eid opt mask saved before entry observed current checkpoint,
  sem_pend_abort_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  UCOS2_state_inv sg checkpoint ->
  interrupt_platform_running platform context.(os_sched_call_invocation)
    context.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg context.(os_sched_call_invocation) checkpoint |--
  sem_post_closed platform critical sg context mask checkpoint.
Proof.
  intros * [_ [_ [[Hsaved Hmask] _]]] Hvalid.
  rewrite Hmask; unfold sem_post_closed; entailer!.
Qed.

Lemma sem_pend_abort_acquired_event_id :
  forall external critical sg context eid opt mask saved before entry observed current,
  sem_pend_abort_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  valid_event_id sg eid.
Proof.
  intros * [_ [Hvalid [_ [_ [Hlookup _]]]]].
  pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
  exact (proj1 (event_pool_used_not_free sg entry.(EventState) eid current Hpool Hlookup)).
Qed.

Lemma sem_pend_abort_group_split : forall sg state eid node,
  sem_post_lookup state eid node ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state /\ 0 <= sem_post_group state node <= 255) &&
    ((event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group state node **
     sem_post_group_frame sg state eid node).
Proof.
  intros * Hlookup.
  pose proof (sem_post_field_split_full sg state eid node EventGrpField Hlookup
    ltac:(simpl; tauto)) as Hsplit.
  cbn [event_cell event_image event_field_offset] in Hsplit.
  sep_apply_l_atomic Hsplit; Intros.
  prop_apply_p (store_uchar_range (event_addr sg eid + OSEventGrp_off)
    (encode_event_wait_grp node.(waitList) state.(TskState))).
  unfold OSEventGrp_off, sem_post_group_frame, sem_post_group; entailer!.
Qed.

Lemma sem_pend_abort_group_merge : forall sg state eid node,
  UCOS2_state_inv sg state -> sem_post_lookup state eid node ->
  (event_addr sg eid + OSEventGrp_off) # UChar |-> sem_post_group state node **
    sem_post_group_frame sg state eid node |-- UCOS2_inv sg state.
Proof.
  intros * Hvalid Hlookup.
  pose proof (sem_post_field_merge_full sg state eid node EventGrpField Hvalid Hlookup
    ltac:(simpl; tauto)) as Hmerge.
  cbn [event_cell event_image event_field_offset] in Hmerge.
  exact Hmerge.
Qed.

(** Literal call order: NULL, Type, fresh Save, counted critical action,
    Restore, then (if requested) the actual scheduler return, then perr.
    The free-slot case remains an actual Type error, not a used-only precondition. *)
Definition sem_pend_abort_call_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent opt : Z) : program UCOS2_Verify_State (Z * Z) :=
  fun before result final =>
    (pevent = 0 /\ result = (0, 4) /\ final = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\ sem_query_public_slot before eid observed /\
      ((event_slot_type_value before.(EventState) eid <> 3 /\ result = (0, 1) /\ final = before) \/
       (sem_post_lookup before eid observed /\ observed.(eventType) = OS_EVENT_TYPE_SEM /\
        exists entry current count code requests checkpoint,
          critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
          sem_post_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
          current.(eventGeneration) = observed.(eventGeneration) /\
          sem_pend_abort_critical sg eid opt entry (count, (code, requests)) checkpoint /\
          result = (count, encode_os_err_code code) /\
          if requests then exists selected resumed,
            critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected /\
            os_sched_c_return external critical sg selected context resumed final
          else final = checkpoint))).

Definition sem_pend_abort_observe_call (result : Z * Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret (fst result).

Lemma sem_pend_abort_safe_return : forall (c : program UCOS2_Verify_State (Z * Z)) before after ret err X,
  c before (ret, err) after ->
  safeExec (LastSeen before) (bind (atomic_cmd c) sem_pend_abort_observe_call) X ->
  safeExec (LastSeen after) (StateRelMonad.ret ret) X.
Proof. exact sem_del_call_safe_return. Qed.

Definition sem_pend_abort_call_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask pevent opt perr : Z)
  (before : UCOS2_Verify_State) (ret : Z)
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop) : Assertion :=
  EX after, EX resumed, EX err,
    coq_prop (sem_pend_abort_call_program external critical sg context pevent opt before (ret, err) after /\
      UCOS2_state_inv sg after /\ safeExec (LastSeen after) (StateRelMonad.ret ret) X) **
    perr # UChar |-> err **
    sem_post_return_resources external platform critical sg context resumed mask after.

Lemma sem_pend_abort_call_null_return : forall external critical sg context opt before,
  sem_pend_abort_call_program external critical sg context 0 opt before (0, 4) before.
Proof. intros; left; auto. Qed.

Lemma sem_pend_abort_call_wrong_type_return : forall external critical sg context pe opt before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_pend_abort_call_program external critical sg context pe opt before (0, 1) before.
Proof.
  intros * Hnonzero Haddr Hid Hslot Htype; right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hslot|]; left; auto.
Qed.

Lemma sem_pend_abort_call_protected_return :
  forall external critical sg context pe opt before eid observed mask saved entry current
    count code requests checkpoint final,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_pend_abort_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  sem_pend_abort_critical sg eid opt entry (count, (code, requests)) checkpoint ->
  (if requests then exists selected resumed,
     critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected /\
     os_sched_c_return external critical sg selected context resumed final
   else final = checkpoint) ->
  sem_pend_abort_call_program external critical sg context pe opt before (count, encode_os_err_code code) final.
Proof.
  intros * Hnonzero Haddr Hid
    [Hinterval [Hvalid [Hsaved [Hbefore [Hcurrent [Htype [Hsem [Hgen Hsafe]]]]]]]] Hstep Hreturn.
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [left; exact Hbefore|].
  right; split; [exact Hbefore|]; split; [exact Htype|].
  exists entry, current, count, code, requests, checkpoint.
  split; [exact Hinterval|]; split; [exact Hcurrent|]; split; [exact Hsem|].
  split; [exact Hgen|]; split; [exact Hstep|]; split; [reflexivity|exact Hreturn].
Qed.

Lemma sem_pend_abort_closed_return :
  forall external platform critical sg context mask pe opt perr before after ret err X,
  sem_pend_abort_call_program external critical sg context pe opt before (ret, err) after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_abort_call_program external critical sg context pe opt)) sem_pend_abort_observe_call) X ->
  perr # UChar |-> err ** sem_post_closed platform critical sg context mask after **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  sem_pend_abort_call_post external platform critical sg context mask pe opt perr before ret X.
Proof.
  intros * Hstep Hexec.
  pose proof (sem_pend_abort_safe_return _ _ _ _ _ _ Hstep Hexec) as Hreturn.
  unfold sem_post_closed; Intros.
  unfold sem_pend_abort_call_post; Exists after context err.
  unfold sem_post_return_resources; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold;
    apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma sem_pend_abort_no_waiter_critical : forall sg eid opt entry current,
  sem_post_lookup entry eid current -> sem_post_group entry current = 0 ->
  sem_pend_abort_critical sg eid opt entry (0, (OS_ERR_NONE, false)) entry.
Proof.
  intros * Hlookup Hzero; exists current; split; [exact Hlookup|].
  unfold sem_post_group in Hzero; rewrite Hzero; simpl; auto.
Qed.

Lemma sem_pend_abort_nonscheduled_return :
  forall external platform critical sg context mask pe opt perr before eid observed saved entry current X,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_pend_abort_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  sem_pend_abort_critical sg eid opt entry (0, (OS_ERR_NONE, false)) entry ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_abort_call_program external critical sg context pe opt)) sem_pend_abort_observe_call) X ->
  perr # UChar |-> 0 ** sem_post_closed platform critical sg context mask entry **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  sem_pend_abort_call_post external platform critical sg context mask pe opt perr before 0 X.
Proof.
  intros * Hnonzero Haddr Hid Hfacts Hstep Hexec.
  apply sem_pend_abort_closed_return; [|exact Hexec].
  change (sem_pend_abort_call_program external critical sg context pe opt before
    (0, encode_os_err_code OS_ERR_NONE) entry).
  eapply sem_pend_abort_call_protected_return; eauto; reflexivity.
Qed.

Lemma sem_pend_abort_scheduled_return :
  forall external platform critical sg context mask pe opt perr before eid observed saved entry current
    checkpoint count X,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_pend_abort_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  sem_pend_abort_critical sg eid opt entry (count, (OS_ERR_PEND_ABORT, true)) checkpoint ->
  UCOS2_state_inv sg checkpoint -> os_sched_acquire_safety external critical sg context checkpoint ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_pend_abort_call_program external critical sg context pe opt)) sem_pend_abort_observe_call) X ->
  perr # UChar |-> 14 ** os_sched_post external platform critical sg context mask checkpoint |--
  sem_pend_abort_call_post external platform critical sg context mask pe opt perr before count X.
Proof.
  intros * Hnonzero Haddr Hid Hfacts Hstep Hvalid Hsafe Hexec.
  unfold os_sched_post; Intros selected final resumed.
  match goal with H : _ /\ os_sched_c_return _ _ _ _ _ _ _ |- _ =>
    destruct H as [Hinterval Hreturn] end.
  pose proof (sem_post_sched_return_preserves_validity external critical sg context
    checkpoint selected resumed final Hvalid Hsafe Hinterval Hreturn) as Hfinal.
  assert (Hcall : sem_pend_abort_call_program external critical sg context pe opt before (count, 14) final).
  { change (sem_pend_abort_call_program external critical sg context pe opt before
      (count, encode_os_err_code OS_ERR_PEND_ABORT) final).
    eapply sem_pend_abort_call_protected_return with
      (mask := mask) (saved := saved) (entry := entry) (current := current)
      (observed := observed) (eid := eid) (requests := true) (checkpoint := checkpoint);
      try eassumption.
    exists selected, resumed; split; assumption. }
  pose proof (sem_pend_abort_safe_return _ _ _ _ _ _ Hcall Hexec) as HexecFinal.
  unfold sem_pend_abort_call_post; Exists final resumed 14.
  unfold sem_post_return_resources; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold;
    apply derivable1s_coq_prop_r; tauto].
Qed.

(** The proof log records the priorities actually returned by each helper;
    the C counter equals its length under the proved current Task-pool bound. *)
Inductive sem_pend_abort_prefix (sg : StableGlobVars) (eid : EventID)
  : UCOS2_Verify_State -> list Priority -> UCOS2_Verify_State -> Prop :=
| sem_pend_abort_prefix_nil : forall entry, sem_pend_abort_prefix sg eid entry [] entry
| sem_pend_abort_prefix_snoc : forall entry priorities state node priority next,
    sem_pend_abort_prefix sg eid entry priorities state ->
    sem_post_lookup state eid node -> sem_post_group state node <> 0 ->
    event_task_rdy sg state eid PendSem 0 PendAbort = Some (priority, next) ->
    sem_pend_abort_prefix sg eid entry (priorities ++ [priority]) next.

Lemma sem_pend_abort_prefix_complete : forall sg eid entry priorities state,
  sem_pend_abort_prefix sg eid entry priorities state -> forall tail final,
  event_broadcast sg eid PendSem 0 PendAbort state tail final ->
  event_broadcast sg eid PendSem 0 PendAbort entry (priorities ++ tail) final.
Proof.
  intros sg eid entry priorities state Hprefix; induction Hprefix; intros rest final Htail.
  - exact Htail.
  - rewrite <- app_assoc; cbn [app].
    apply IHHprefix; eapply event_broadcast_next; eassumption.
Qed.

Definition sem_pend_abort_loop_facts (sg : StableGlobVars) (eid : EventID)
  (entry : UCOS2_Verify_State) (initial : OSEventAbstractState)
  (state : UCOS2_Verify_State) (node : OSEventAbstractState) (count : Z) : Prop :=
  exists priorities, sem_pend_abort_prefix sg eid entry priorities state /\
    sem_post_lookup entry eid initial /\ sem_post_lookup state eid node /\
    initial.(eventType) = OS_EVENT_TYPE_SEM /\ node.(eventType) = OS_EVENT_TYPE_SEM /\
    UCOS2_state_inv sg entry /\ UCOS2_state_inv sg state /\
    count = Z.of_nat (length priorities) /\
    Z.of_nat (length initial.(waitList)) = count + Z.of_nat (length node.(waitList)) /\
    Z.of_nat (length initial.(waitList)) <= 255.

Lemma sem_pend_abort_loop_start : forall sg eid entry current,
  UCOS2_state_inv sg entry -> sem_post_lookup entry eid current ->
  current.(eventType) = OS_EVENT_TYPE_SEM ->
  sem_pend_abort_loop_facts sg eid entry current entry current 0.
Proof.
  intros * Hvalid Hlookup Htype.
  pose proof (event_waiter_count_le_task_count sg entry eid current Hvalid Hlookup) as Hwaiters.
  pose proof (task_count_in_pool_range sg entry.(TskState)
    (proj1 Hvalid) (proj1 (proj2 Hvalid))) as Htasks.
  exists []; split; [constructor|].
  split; [exact Hlookup|]; split; [exact Hlookup|].
  split; [exact Htype|]; split; [exact Htype|].
  split; [exact Hvalid|]; split; [exact Hvalid|].
  split; [reflexivity|]; split; [lia|lia].
Qed.

Lemma sem_pend_abort_loop_bound : forall sg eid entry initial state node count,
  sem_pend_abort_loop_facts sg eid entry initial state node count -> 0 <= count <= 255.
Proof.
  intros * [priorities [_ [_ [_ [_ [_ [_ [_ [Hcount [Hlength Hbound]]]]]]]]]].
  lia.
Qed.

Lemma sem_pend_abort_loop_nonempty_bound : forall sg eid entry initial state node count,
  sem_pend_abort_loop_facts sg eid entry initial state node count ->
  sem_post_group state node <> 0 -> 0 <= count < 255.
Proof.
  intros * [priorities [_ [_ [_ [_ [_ [_ [_ [Hcount [Hlength Hbound]]]]]]]]]] Hgroup.
  destruct node.(waitList) as [|head tail] eqn:Hlist.
  - exfalso; apply Hgroup; unfold sem_post_group; rewrite Hlist; reflexivity.
  - cbn [length] in Hlength; rewrite Nat2Z.inj_succ in Hlength; lia.
Qed.

Lemma sem_pend_abort_loop_step : forall sg eid entry initial state node count priority next,
  sem_pend_abort_loop_facts sg eid entry initial state node count ->
  sem_post_group state node <> 0 -> sem_del_wake_result sg eid state next priority ->
  exists next_node, sem_pend_abort_loop_facts sg eid entry initial next next_node (count + 1).
Proof.
  intros * [priorities [Hprefix [Hentry [Hnode [Htype0 [Htype [Hvalid0 [Hvalid [Hcount [Hlength Hbound]]]]]]]]]]
    Hgroup Hstep.
  assert (Hkind : event_type_to_pend_type node.(eventType) = Some PendSem)
    by (rewrite Htype; reflexivity).
  destruct (event_wake_decompose sg state eid node PendSem 0 PendAbort priority next
    Hvalid Hnode Hkind Hgroup Hstep)
    as [head [tail [old [Hlist [Hold [Hpriority [Hnext [HvalidNext HnodeNext]]]]]]]].
  exists (event_set_wait_list node tail), (priorities ++ [priority]).
  split; [eapply sem_pend_abort_prefix_snoc; eassumption|].
  split; [exact Hentry|]; split; [exact HnodeNext|]; split; [exact Htype0|].
  split; [exact Htype|]; split; [exact Hvalid0|]; split; [exact HvalidNext|].
  split.
  - rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; cbn; lia.
  - split; [|exact Hbound].
    rewrite Hlist in Hlength; cbn [length] in Hlength; rewrite Nat2Z.inj_succ in Hlength.
    cbn [event_set_wait_list waitList]; lia.
Qed.

Lemma sem_pend_abort_broadcast_critical : forall sg eid entry initial state node count,
  sem_pend_abort_loop_facts sg eid entry initial state node count ->
  sem_post_group entry initial <> 0 -> sem_post_group state node = 0 ->
  sem_pend_abort_critical sg eid 1 entry (count, (OS_ERR_PEND_ABORT, true)) state.
Proof.
  intros * [priorities [Hprefix [Hentry [Hnode [Htype0 [Htype [Hvalid0 [Hvalid [Hcount [Hlength Hbound]]]]]]]]]]
    Hnonzero Hzero.
  exists initial; split; [exact Hentry|].
  unfold sem_post_group in Hnonzero; rewrite (proj2 (Z.eqb_neq _ _) Hnonzero); simpl.
  exists priorities; split.
  - pose proof (sem_pend_abort_prefix_complete sg eid entry priorities state Hprefix [] state
      (event_broadcast_done sg eid PendSem 0 PendAbort state node Hnode Hzero)) as Hcomplete.
    rewrite app_nil_r in Hcomplete; exact Hcomplete.
  - rewrite event_pend_abort_count_eq_length; [rewrite Hcount; reflexivity|lia].
Qed.

Lemma sem_pend_abort_single_critical : forall sg eid opt entry current priority next,
  sem_post_lookup entry eid current -> sem_post_group entry current <> 0 -> opt <> 1 ->
  sem_del_wake_result sg eid entry next priority ->
  sem_pend_abort_critical sg eid opt entry (1, (OS_ERR_PEND_ABORT, true)) next.
Proof.
  intros * Hlookup Hgroup Hopt Hstep; exists current; split; [exact Hlookup|].
  unfold sem_post_group in Hgroup.
  rewrite (proj2 (Z.eqb_neq _ _) Hgroup), (proj2 (Z.eqb_neq _ _) Hopt).
  exists priority; split; [exact Hstep|reflexivity].
Qed.

(** Full-resource consequence of the real raw OS_EventTaskRdy contract.
    Split/merge uses the already proved abort-status implementation, retaining
    every Event/Queue/global residual rather than manufacturing a new heap. *)
Lemma sem_pend_abort_wake_split : forall sg eid entry initial state node count,
  sem_pend_abort_loop_facts sg eid entry initial state node count ->
  sem_post_group state node <> 0 -> event_object_layout_prop sg eid ->
  UCOS2_inv sg state ** unmap_table_rep sg |-- EX tid, EX old,
    coq_prop (event_task_rdy_entry sg state.(TskState) eid node tid old) &&
    (event_task_rdy_pre sg state.(TskState) eid node tid old 1 2
      (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (sched_row_values state.(TskState) state.(SchedState).(readyList)) **
     sem_post_wake_frame sg state eid tid).
Proof.
  intros * [priorities [_ [_ [Hlookup [_ [Htype [_ [Hvalid _]]]]]]]] Hgroup Hlayout.
  apply sem_del_wake_split_full; assumption.
Qed.

Lemma sem_pend_abort_wake_merge : forall sg eid entry initial state node count tid old priority,
  sem_pend_abort_loop_facts sg eid entry initial state node count ->
  sem_post_group state node <> 0 ->
  event_task_rdy_entry sg state.(TskState) eid node tid old ->
  event_task_rdy_post sg state.(TskState) eid node tid old 0 1 2
    (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
    (sched_row_values state.(TskState) state.(SchedState).(readyList)) priority **
  sem_post_wake_frame sg state eid tid |-- EX next, EX next_node,
    coq_prop (sem_del_wake_result sg eid state next priority /\
      sem_pend_abort_loop_facts sg eid entry initial next next_node (count + 1) /\
      0 <= count < 255) && (UCOS2_inv sg next ** unmap_table_rep sg).
Proof.
  intros * Hfacts Hgroup Hentry.
  pose proof Hfacts as [priorities [_ [_ [Hlookup [_ [Htype [_ [Hvalid _]]]]]]]].
  pose proof (sem_pend_abort_loop_nonempty_bound sg eid entry initial state node count Hfacts Hgroup) as Hcount.
  sep_apply_l_atomic (sem_del_wake_merge_full sg state eid node tid old priority
    Hvalid Hlookup Htype Hentry).
  Intros next.
  match goal with Hstep : sem_del_wake_result sg eid state next priority |- _ =>
    destruct (sem_pend_abort_loop_step sg eid entry initial state node count priority next Hfacts Hgroup Hstep)
      as [next_node Hnext] end.
  Exists next next_node; entailer!.
Qed.
