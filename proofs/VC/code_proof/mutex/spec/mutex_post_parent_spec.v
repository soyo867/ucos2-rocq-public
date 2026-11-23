Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Require Export Coq.micromega.Lia.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.RelationClasses.
Require Export SetsClass.SetsClass.
From AUXLib Require Export ListLib.
Require Export SumLib.ZRange.
From SimpleC.SL Require Export CArch Mem ConAssertion.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.helpers.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.lib.field_storage.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.queue_core.
Require Export Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.kernel_heap_execution.
Require Export Ucos2Verify.lib.kernel_heap_storage.
Require Export Ucos2Verify.lib.kernel_heap_observation.
Require Export Ucos2Verify.lib.mutex.
Require Export Ucos2Verify.lib.cross_module_invariants.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.array_abstraction.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_task_rdy_spec.
Require Export Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Export Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
(** Native parent diagnostic interface. [mutex_post_logical_closed] has
    ONLY the existing logical STS and execution token: it is deliberately
    not equated with raw kernel ownership. The C entry loan and final
    return cuts remain obligations, not rules or assumptions of this
    module. Consequently this is not yet a usable public call contract. *)
Definition mutex_post_logical_closed (platform : InterruptPlatformResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
  (mask : Z) (state : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  Ucos2Verify.lib.ucos2_rules_lib.OutsideCritical sg state.

(** Annotation names avoid the original header's identically named C
    integer macros; these are definitions, not a second enum or contract. *)
Definition mutex_post_kind : OSEventType := OS_EVENT_TYPE_MUTEX.
Definition mutex_post_success : OSErrCode := OS_ERR_NONE.
Definition mutex_post_not_owner_error : OSErrCode := OS_ERR_NOT_MUTEX_OWNER.
Definition mutex_post_pcp_error : OSErrCode := OS_ERR_PCP_LOWER.

Definition mutex_post_native_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pevent : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  UCOS2_state_inv sg before /\
  (before.(IntrState).(intNesting) > 0 \/ pevent = 0 \/
   (pevent = event_addr sg eid /\ valid_event_id sg eid /\
    mutex_query_lookup before eid observed /\
    (observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
      mutex_query_handle_protocol critical sg invocation eid /\
      mutex_owner_event_unlinked before.(TskState) before.(EventState) /\
      (forall action initial final,
        critical_region_clients critical action ->
        UCOS2_state_inv sg initial ->
        mutex_owner_event_unlinked initial.(TskState) initial.(EventState) ->
        kernel_client_step action sg initial final ->
        mutex_owner_event_unlinked final.(TskState) final.(EventState))))).

Definition mutex_post_nesting_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : Assertion :=
  interrupt_inv_no_int_nesting sg state.(IntrState) **
  UCOS2_raw_rep_missing_interrupt sg state.

Definition mutex_post_native_owner_store_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (image : EventStorage)
  (priority : Z) : Assertion :=
  event_storage_without_field sg.(osKernelConfig).(cfgEventNames)
    (event_addr sg eid) image EventPtrField **
  store_prio_tbl_missing_i sg state.(TskState).(prioTbl) priority **
  mutex_post_event_table_frame sg state eid.

Definition mutex_post_native_caller (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (state : UCOS2_Verify_State) (call : OsSchedCallContext)
  (caller : TaskID) (node : TaskAbstractState) : Prop :=
  call.(os_sched_call_invocation) = invocation /\
  call.(os_sched_call_origin) = origin /\
  state.(SchedState).(curTaskID) = Some caller /\
  state.(TskState).(inUsedTaskStates) caller = Some node.

(** Keep the actual C result in the array-read expression.  Packaging the
    two proved equalities prevents the annotation matcher from replacing
    that local before matching its memory cell; the proof unfolds them. *)
Definition mutex_post_wake_selection (tasks : Glob_TaskAbstractState)
  (waiter : TaskID) (waiting : TaskAbstractState) (priority : Z) : Prop :=
  priority = waiting.(curPrio) /\ tasks.(prioTbl) priority = PTTask waiter.

Definition mutex_post_native_after_schedule (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (call : OsSchedCallContext)
  (committed after : UCOS2_Verify_State) : Prop :=
  exists acquired returned,
    critical_region_interval critical sg invocation committed acquired /\
    os_sched_c_return external critical sg acquired call returned after.

Definition mutex_post_native_result (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (pevent : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState)
  (code : Z) (after : UCOS2_Verify_State) : Prop :=
  (exists err,
    mutex_post_before_save_error pevent (encode_event_type observed.(eventType))
      before.(IntrState).(intNesting) = Some err /\
    code = encode_os_err_code err /\ after = before) \/
  (mutex_post_before_save_error pevent (encode_event_type observed.(eventType))
     before.(IntrState).(intNesting) = None /\
   exists entry current call caller node err scheduled committed,
    critical_region_interval critical sg invocation before entry /\
    mutex_query_lookup entry eid current /\
    current.(eventType) = OS_EVENT_TYPE_MUTEX /\
    current.(eventGeneration) = observed.(eventGeneration) /\
    mutex_post_native_caller sg invocation origin entry call caller node /\
    mutex_post_critical sg eid caller entry err scheduled committed /\
    code = encode_os_err_code err /\
    match scheduled with
    | false => after = committed
    | true => mutex_post_native_after_schedule external critical sg invocation call committed after
    end).

Definition mutex_post_native_program external critical sg invocation origin pevent eid observed
  : program UCOS2_Verify_State Z :=
  fun before code after =>
    mutex_post_native_result external critical sg invocation origin pevent before eid observed code after.

Definition mutex_post_native_observe (code : Z)
  : program (UCOS2_Verify_State -> Prop) Z :=
  fun initial result final => result = code /\ final = initial.

Lemma mutex_post_native_input_lookup : forall critical sg invocation pe before eid observed,
  mutex_post_native_input critical sg invocation pe before eid observed ->
  before.(IntrState).(intNesting) <= 0 -> pe <> 0 ->
  pe = event_addr sg eid /\ valid_event_id sg eid /\ mutex_query_lookup before eid observed.
Proof.
  intros critical sg invocation pe before eid observed [_ [Hisr | [Hnull | [Hpe [Hid [He _]]]]]] Hnest Hnonzero;
    try lia; exact (conj Hpe (conj Hid He)).
Qed.

Lemma mutex_post_native_cold_result : forall external critical sg invocation origin pe before eid observed err,
  mutex_post_before_save_error pe (encode_event_type observed.(eventType)) before.(IntrState).(intNesting) = Some err ->
  mutex_post_native_result external critical sg invocation origin pe before eid observed
    (encode_os_err_code err) before.
Proof. intros; left; exists err; auto. Qed.

Lemma mutex_post_native_critical_result : forall external critical sg invocation origin pe before eid observed
  acquired current call caller node err scheduled committed after,
  mutex_post_before_save_error pe (encode_event_type observed.(eventType)) before.(IntrState).(intNesting) = None ->
  critical_region_interval critical sg invocation before acquired ->
  mutex_query_lookup acquired eid current -> current.(eventType) = OS_EVENT_TYPE_MUTEX ->
  current.(eventGeneration) = observed.(eventGeneration) ->
  mutex_post_native_caller sg invocation origin acquired call caller node ->
  mutex_post_critical sg eid caller acquired err scheduled committed ->
  (if scheduled then mutex_post_native_after_schedule external critical sg invocation call committed after
   else after = committed) ->
  mutex_post_native_result external critical sg invocation origin pe before eid observed
    (encode_os_err_code err) after.
Proof.
  intros; right; split; [assumption|].
  exists acquired, current, call, caller, node, err, scheduled, committed.
  repeat first [assumption | split]; reflexivity.
Qed.

Lemma mutex_post_native_safe_return : forall external critical sg invocation origin pe before eid observed code after X,
  mutex_post_native_result external critical sg invocation origin pe before eid observed code after ->
  safeExec (LastSeen before)
    (Monad.bind (atomic_cmd (mutex_post_native_program external critical sg invocation origin pe eid observed))
      mutex_post_native_observe) X ->
  safeExec (LastSeen after) (StateRelMonad.ret code) X.
Proof.
  intros external critical sg invocation origin pe before eid observed code after X Hresult Hexec.
  assert (Hatomic : hs_eval
    (atomic_cmd (mutex_post_native_program external critical sg invocation origin pe eid observed))
    (LastSeen before) (LastSeen after) code).
  { unfold hs_eval, LastSeen, atomic_cmd.
    intros P HP; exists (RTrans_Abs after); split; [|reflexivity].
    exists before, after; split; [apply HP; exact I|].
    split; [exact Hresult|reflexivity]. }
  pose proof (highstepbind_derive _ _ _ code (LastSeen after) Hatomic X Hexec) as Hobserve.
  eapply (highstependret_derive (mutex_post_native_observe code) (LastSeen after) code
    (fun _ => LastSeen after)); [|exact Hobserve].
  intros P HP; exists P; split; [split; reflexivity|exact HP].
Qed.

Lemma mutex_post_type_cast_eq : forall kind,
  unsigned_last_nbits (encode_event_type kind) 32 = encode_event_type kind.
Proof. intros []; reflexivity. Qed.

Lemma mutex_post_commit_rep_merge : forall sg state eid event,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some event ->
  mutex_post_commit_rep sg state eid (event_image sg state.(TskState) event) |-- UCOS2_inv sg state.
Proof.
  intros sg state eid event Hvalid He.
  unfold mutex_post_commit_rep; rewrite mutex_post_event_table_frame_merge.
  unfold mutex_post_event_frame; fold (used_event_rep sg state.(TskState) eid event).
  sep_apply_l_atomic (event_raw_rep_merge_eid sg state.(TskState) state.(EventState) eid event He).
  rewrite UCOS2_inv_split_event_queue; entailer!.
Qed.
