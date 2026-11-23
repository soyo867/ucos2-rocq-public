Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From AUXLib Require Import Axioms Feq ListLib VMap.
Require Export Ucos2Verify.VC.code.sem.spec.sem_post_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_delete_spec.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.queue_core.
Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected V2.93.01 source: argument check, no safety/IEC or names.
    The conditional source bodies remain in the original carrier. *)
Definition sem_del_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgSafetyCritical) = false /\
  sg.(osKernelConfig).(cfgSafetyCriticalIEC) = false /\
  sg.(osKernelConfig).(cfgEventNames) = false.

Definition sem_del_lookup := sem_post_lookup.
Definition sem_del_closed := sem_post_closed.
Definition sem_del_type_frame := sem_post_type_frame.
Definition sem_del_group_frame := sem_post_group_frame.
Definition sem_del_group := sem_post_group.
Definition sem_del_handle_protocol := sem_post_handle_protocol.
Definition sem_del_int_nesting (s : UCOS2_Verify_State) : Z := s.(IntrState).(intNesting).

(** This is the caller/platform scheduling obligation, conditional exactly
    on the body requesting OS_Sched. It is not a C branch or post-validity guard. *)
Definition sem_del_acquire_safety (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (eid : EventID) (opt : Z)
  (before : UCOS2_Verify_State) : Prop :=
  forall entry pointer code checkpoint,
    critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    sem_delete_critical sg eid opt entry (pointer, (code, true)) checkpoint ->
    os_sched_acquire_safety external critical sg context checkpoint.

Definition sem_del_acquire_facts (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (eid : EventID) (opt mask saved : Z)
  (before entry : UCOS2_Verify_State) (observed current : OSEventAbstractState) : Prop :=
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved /\
  sem_del_lookup before eid observed /\ sem_del_lookup entry eid current /\
  observed.(eventType) = OS_EVENT_TYPE_SEM /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
  current.(eventGeneration) = observed.(eventGeneration) /\
  sem_del_int_nesting before = 0 /\
  (forall pointer code checkpoint,
    sem_delete_critical sg eid opt entry (pointer, (code, true)) checkpoint ->
    os_sched_acquire_safety external critical sg context checkpoint).

Lemma sem_del_save_consequence :
  forall external critical sg context eid opt mask saved before entry observed,
  sem_del_handle_protocol critical sg context.(os_sched_call_invocation) eid ->
  sem_del_acquire_safety external critical sg context eid opt before ->
  UCOS2_state_inv sg before -> sem_del_lookup before eid observed ->
  observed.(eventType) = OS_EVENT_TYPE_SEM -> sem_del_int_nesting before = 0 ->
  critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry |-- EX current,
    coq_prop (sem_del_acquire_facts external critical sg context eid opt mask saved
      before entry observed current) && UCOS2_inv sg entry.
Proof.
  intros external critical sg context eid opt mask saved before entry observed
    Hprotocol Hsafe Hvalid Hlookup Htype Hnesting Hinterval Hsaved.
  destruct (sem_post_handle_interval_preserves_identity critical sg
    context.(os_sched_call_invocation) eid before entry observed
    Hprotocol Hinterval Hvalid Hlookup) as [current [Hcurrent [Hgen HcurrentType]]].
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    context.(os_sched_call_invocation) before entry Hinterval Hvalid)) as Hentry.
  assert (Hfacts : sem_del_acquire_facts external critical sg context eid opt mask saved
    before entry observed current).
  { unfold sem_del_acquire_facts; split; [exact Hinterval|].
    split; [exact Hentry|]; split; [exact Hsaved|]; split; [exact Hlookup|].
    split; [exact Hcurrent|]; split; [exact Htype|]; split; [congruence|].
    split; [exact Hgen|]; split; [exact Hnesting|].
    intros pointer code checkpoint Hstep; eapply Hsafe; eassumption. }
  Exists current; unfold UCOS2_inv; entailer!.
Qed.

Definition sem_del_int_frame (sg : StableGlobVars) (state : UCOS2_Verify_State) : Assertion :=
  interrupt_inv_no_int_nesting sg state.(IntrState) ** UCOS2_raw_rep_missing_interrupt sg state.

Lemma sem_del_int_split : forall sg state,
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
    (sg.(g_OSIntNesting) # UChar |-> sem_del_int_nesting state ** sem_del_int_frame sg state).
Proof.
  intros; unfold UCOS2_inv; Intros.
  rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state,
    sem_del_int_frame, sem_del_int_nesting, interrupt_inv_no_int_nesting; entailer!.
Qed.

Lemma sem_del_int_merge : forall sg state,
  UCOS2_state_inv sg state ->
  sg.(g_OSIntNesting) # UChar |-> sem_del_int_nesting state ** sem_del_int_frame sg state |--
  UCOS2_inv sg state.
Proof.
  intros; unfold UCOS2_inv; rewrite (UCOS2_raw_rep_split_module sg state InterruptModule).
  cbn [UCOS2_module_rep]; unfold interrupt_inv, store_int_state,
    sem_del_int_frame, sem_del_int_nesting, interrupt_inv_no_int_nesting; entailer!.
Qed.

Definition sem_del_call_program (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent opt : Z) : program UCOS2_Verify_State (Z * Z) :=
  fun before result final =>
    (pevent = 0 /\ result = (pevent, 4) /\ final = before) \/
    (pevent <> 0 /\ exists eid observed,
      pevent = event_addr sg eid /\ valid_event_id sg eid /\ sem_del_lookup before eid observed /\
      ((observed.(eventType) <> OS_EVENT_TYPE_SEM /\ result = (pevent, 1) /\ final = before) \/
       (observed.(eventType) = OS_EVENT_TYPE_SEM /\
        ((0 < sem_del_int_nesting before /\ result = (pevent, 15) /\ final = before) \/
         (sem_del_int_nesting before = 0 /\ exists entry current pointer code requests checkpoint,
           critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
           sem_del_lookup entry eid current /\ current.(eventType) = OS_EVENT_TYPE_SEM /\
           current.(eventGeneration) = observed.(eventGeneration) /\
           sem_delete_critical sg eid opt entry (pointer, (code, requests)) checkpoint /\
           result = (pointer, encode_os_err_code code) /\
           if requests then exists selected resumed,
             critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected /\
             os_sched_c_return external critical sg selected context resumed final
           else final = checkpoint))))).

Definition sem_del_call_input (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (pevent opt : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pevent = 0 \/ (pevent <> 0 /\ pevent = event_addr sg eid /\ valid_event_id sg eid /\
    sem_del_lookup before eid observed /\
    (observed.(eventType) = OS_EVENT_TYPE_SEM -> sem_del_int_nesting before = 0 ->
      sem_del_handle_protocol critical sg context.(os_sched_call_invocation) eid /\
      sem_del_acquire_safety external critical sg context eid opt before)).

Definition observe_sem_del_call (result : Z * Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret (fst result).

Lemma sem_del_call_safe_return : forall (c : program UCOS2_Verify_State (Z * Z)) before after ret err X,
  c before (ret, err) after ->
  safeExec (LastSeen before) (bind (atomic_cmd c) observe_sem_del_call) X ->
  safeExec (LastSeen after) (StateRelMonad.ret ret) X.
Proof.
  intros c before after ret err X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd c) (LastSeen before) (LastSeen after) (ret, err)).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P0 HP0.
    exists (RTrans_Abs after); split.
    - exists before, after; split; [apply HP0; exact I|].
      split; [exact Hsem|intro state; split; trivial].
    - intro state; split; trivial. }
  exact (highstepbind_derive _ _ _ (ret, err) (LastSeen after) Hatomic X Hexec).
Qed.

Definition sem_del_call_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (mask pevent opt perr : Z)
  (before : UCOS2_Verify_State) (ret : Z)
  (X : Z -> (UCOS2_Verify_State -> Prop) -> Prop) : Assertion :=
  EX after, EX resumed, EX err,
    coq_prop (sem_del_call_program external critical sg context pevent opt before (ret, err) after /\
      UCOS2_state_inv sg after /\ safeExec (LastSeen after) (StateRelMonad.ret ret) X) **
    perr # UChar |-> err **
    sem_post_return_resources external platform critical sg context resumed mask after.

Definition sem_del_critical_result (sg : StableGlobVars) (eid : EventID) (opt : Z)
  (entry : UCOS2_Verify_State) (pointer error requests : Z) (checkpoint : UCOS2_Verify_State) : Prop :=
  exists (code : OSErrCode) (requested : bool),
    error = encode_os_err_code code /\ requests = (if requested then 1 else 0) /\
    sem_delete_critical sg eid opt entry (pointer, (code, requested)) checkpoint.

Lemma sem_del_call_protected_return :
  forall external critical sg context pe opt before eid observed mask saved entry current
    pointer code requests checkpoint final,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_del_acquire_facts external critical sg context eid opt mask saved before entry observed current ->
  sem_delete_critical sg eid opt entry (pointer, (code, requests)) checkpoint ->
  (if requests then exists selected resumed,
     critical_region_interval critical sg context.(os_sched_call_invocation) checkpoint selected /\
     os_sched_c_return external critical sg selected context resumed final
   else final = checkpoint) ->
  sem_del_call_program external critical sg context pe opt before (pointer, encode_os_err_code code) final.
Proof.
  intros external critical sg context pe opt before eid observed mask saved entry current
    pointer code requests checkpoint final Hnonzero Haddr Hid
    [Hinterval [Hvalid [Hsaved [Hbefore [Hcurrent [Htype [Hsem [Hgen [Hnesting Hsafe]]]]]]]]] Hstep Hreturn.
  right; split; [exact Hnonzero|]; exists eid, observed.
  split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hbefore|].
  right; split; [exact Htype|]; right; split; [exact Hnesting|].
  exists entry, current, pointer, code, requests, checkpoint.
  split; [exact Hinterval|]; split; [exact Hcurrent|]; split; [exact Hsem|].
  split; [exact Hgen|]; split; [exact Hstep|]; split; [reflexivity|exact Hreturn].
Qed.

Lemma sem_del_closed_return : forall external platform critical sg context mask pe opt perr before after ret err X,
  sem_del_call_program external critical sg context pe opt before (ret, err) after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (sem_del_call_program external critical sg context pe opt)) observe_sem_del_call) X ->
  perr # UChar |-> err ** sem_del_closed platform critical sg context mask after **
    os_sched_context_resources external context ** unmap_table_rep sg |--
  sem_del_call_post external platform critical sg context mask pe opt perr before ret X.
Proof.
  intros external platform critical sg context mask pe opt perr before after ret err X Hstep Hexec.
  pose proof (sem_del_call_safe_return _ _ _ _ _ _ Hstep Hexec) as Hreturn.
  unfold sem_del_closed, sem_post_closed; Intros.
  unfold sem_del_call_post; Exists after context err.
  unfold sem_post_return_resources; entailer!.
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold;
    apply derivable1s_coq_prop_r; tauto].
Qed.

(** The loop prefix contains only actual abort calls; closing it with the
    current zero bitmap yields the native complete broadcast relation. *)
Inductive sem_del_abort_prefix (sg : StableGlobVars) (eid : EventID)
  : UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| sem_del_abort_prefix_refl : forall state, sem_del_abort_prefix sg eid state state
| sem_del_abort_prefix_step : forall entry state node priority next,
    sem_del_abort_prefix sg eid entry state -> sem_del_lookup state eid node ->
    sem_del_group state node <> 0 ->
    event_task_rdy sg state eid PendSem 0 PendAbort = Some (priority, next) ->
    sem_del_abort_prefix sg eid entry next.

Lemma sem_del_abort_prefix_complete : forall sg eid entry state,
  sem_del_abort_prefix sg eid entry state -> forall priorities final,
  event_broadcast sg eid PendSem 0 PendAbort state priorities final ->
  exists complete, event_broadcast sg eid PendSem 0 PendAbort entry complete final.
Proof.
  intros sg eid entry state Hprefix; induction Hprefix; intros priorities final Htail.
  - exists priorities; exact Htail.
  - eapply IHHprefix. eapply event_broadcast_next; eassumption.
Qed.

Definition sem_del_waiting (entry : UCOS2_Verify_State) (node : OSEventAbstractState) (waiting : Z) : Prop :=
  (sem_del_group entry node = 0 /\ waiting = 0) \/
  (sem_del_group entry node <> 0 /\ waiting = 1).

Definition sem_del_loop_facts (sg : StableGlobVars) (eid : EventID)
  (entry state : UCOS2_Verify_State) (node : OSEventAbstractState) : Prop :=
  sem_del_abort_prefix sg eid entry state /\ sem_del_lookup state eid node /\
  node.(eventType) = OS_EVENT_TYPE_SEM /\ UCOS2_state_inv sg state.

Definition sem_del_recycle_rest_fields (named : bool) : list EventField :=
  [EventPadding1; EventPadding2; EventPadding3; EventGrpField;
   EventTbl0; EventTbl1; EventTbl2; EventTbl3; EventTbl4; EventTbl5; EventTbl6; EventTbl7; EventPadding19] ++
  if named then [EventNameField] else [].
Definition sem_del_recycle_rest (named : bool) (base : addr) (image : EventStorage) : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell base) (sem_del_recycle_rest_fields named) image.

Lemma sem_del_recycle_storage_split : forall named base image,
  event_storage_rep named base image --||--
  event_cell base EventTypeField (image EventTypeField) **
  event_cell base EventPtrField (image EventPtrField) **
  event_cell base EventCntField (image EventCntField) ** sem_del_recycle_rest named base image.
Proof.
  intros named base image.
  assert (Horder : event_storage_rep named base image =
    EventFieldStorage.store_fields EventField_eq_dec (event_cell base)
      (EventTypeField :: EventPtrField :: EventCntField :: sem_del_recycle_rest_fields named) image).
  { unfold event_storage_rep, EventFieldStorage.store_fields; f_equal.
    apply functional_extensionality; intro field; destruct named, field; reflexivity. }
  assert (Hnd : NoDup (EventTypeField :: EventPtrField :: EventCntField :: sem_del_recycle_rest_fields named)).
  { destruct named; unfold sem_del_recycle_rest_fields; simpl.
    all: repeat (apply NoDup_cons; [simpl; intuition discriminate|]); apply NoDup_nil. }
  rewrite Horder.
  do 3 (lazymatch type of Hnd with | NoDup (?field :: ?rest) =>
    rewrite (EventFieldStorage.store_fields_cons _ _ EventField_eq_dec (event_cell base) rest image field Hnd);
    apply NoDup_cons_iff in Hnd; destruct Hnd as [_ Hnd] end).
  unfold sem_del_recycle_rest; split; entailer!.
Qed.

Lemma sem_del_recycle_rest_image_eq : forall sg named base free image,
  sem_del_recycle_rest named base (event_recycle_image sg free image) =
  sem_del_recycle_rest named base image.
Proof.
  intros; unfold sem_del_recycle_rest, EventFieldStorage.store_fields; f_equal.
  apply functional_extensionality; intro field; destruct named, field; reflexivity.
Qed.

Definition sem_del_recycle_frame (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (eid : EventID) (node : OSEventAbstractState) : Assertion :=
  sem_del_recycle_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
    (event_image sg state.(TskState) node) **
  store_map_missing_i (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) eid **
  event_free_storage_rep sg state.(EventState) **
  queue_storage_rep sg state.(EventState) ** UCOS2_raw_rep_missing_event_queue sg state.

Definition sem_del_free_head (sg : StableGlobVars) (state : UCOS2_Verify_State) : Z :=
  event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)).

Lemma sem_del_recycle_split : forall sg state eid node,
  sem_del_lookup state eid node -> UCOS2_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
  (event_cell (event_addr sg eid) EventTypeField (Some (encode_event_type node.(eventType))) **
   event_cell (event_addr sg eid) EventPtrField (Some (encode_event_ptr_value sg node)) **
   event_cell (event_addr sg eid) EventCntField (Some (encode_event_cnt_value node)) **
   sg.(g_OSEventFreeList) # Ptr |-> sem_del_free_head sg state ** sem_del_recycle_frame sg state eid node).
Proof.
  intros sg state eid node Hlookup; rewrite UCOS2_inv_split_event_queue; Intros.
  sep_apply_l_atomic (event_raw_rep_split_eid sg state.(TskState) state.(EventState) eid node Hlookup).
  unfold used_event_rep; rewrite sem_del_recycle_storage_split.
  unfold event_raw_rep_no_eid, event_free_root_rep, sem_del_recycle_frame, sem_del_free_head.
  cbn [event_image]; entailer!.
Qed.

Lemma sem_del_recycle_merge : forall sg state eid node,
  UCOS2_state_inv sg state -> sem_del_lookup state eid node ->
  node.(eventType) = OS_EVENT_TYPE_SEM -> sem_del_group state node = 0 ->
  event_cell (event_addr sg eid) EventTypeField (Some 0) **
  event_cell (event_addr sg eid) EventPtrField (Some (sem_del_free_head sg state)) **
  event_cell (event_addr sg eid) EventCntField (Some 0) **
  sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid ** sem_del_recycle_frame sg state eid node |--
  UCOS2_inv sg (event_delete_recycle_state sg state eid node).
Proof.
  intros sg state eid node Hvalid Hlookup Htype Hzero.
  pose proof Hvalid as [_ [_ [_ [[_ [_ [_ [Hfields [_ [_ Hentries]]]]]] _]]]].
  assert (Hnone : node.(queueFields) = None).
  { apply non_queue_event_has_no_queue_fields; [exact (Hfields eid node Hlookup)|rewrite Htype; discriminate]. }
  pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) node.(waitList)
    (proj1 (Hentries eid node Hlookup))) Hzero) as Hempty.
  unfold sem_del_recycle_frame.
  rewrite <- (sem_del_recycle_rest_image_eq sg sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) state.(EventState).(unUsedEventStates) (event_image sg state.(TskState) node)).
  pose proof (proj2 (sem_del_recycle_storage_split sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) (event_recycle_image sg state.(EventState).(unUsedEventStates)
      (event_image sg state.(TskState) node)))) as Hstorage.
  change (event_cell (event_addr sg eid) EventTypeField (Some 0) **
    event_cell (event_addr sg eid) EventPtrField (Some (sem_del_free_head sg state)) **
    event_cell (event_addr sg eid) EventCntField (Some 0) **
    sem_del_recycle_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_recycle_image sg state.(EventState).(unUsedEventStates) (event_image sg state.(TskState) node)) |--
    event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
      (event_recycle_image sg state.(EventState).(unUsedEventStates) (event_image sg state.(TskState) node))) in Hstorage.
  eapply derivable1_trans with (y :=
    (event_cell (event_addr sg eid) EventTypeField (Some 0) **
     event_cell (event_addr sg eid) EventPtrField (Some (sem_del_free_head sg state)) **
     event_cell (event_addr sg eid) EventCntField (Some 0) **
     sem_del_recycle_rest sg.(osKernelConfig).(cfgEventNames) (event_addr sg eid)
       (event_recycle_image sg state.(EventState).(unUsedEventStates) (event_image sg state.(TskState) node))) **
    (sg.(g_OSEventFreeList) # Ptr |-> event_addr sg eid **
     store_map_missing_i (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) eid **
     event_free_storage_rep sg state.(EventState) ** queue_storage_rep sg state.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg state)).
  { entailer!. }
  eapply derivable1_trans; [apply derivable1_sepcon_mono; [exact Hstorage|reflexivity]|].
  unfold event_delete_recycle_state.
  eapply derivable1_trans; [|apply UCOS2_inv_merge_event_recycle with (node := node); eauto;
    rewrite Htype; discriminate].
  entailer!.
Qed.
