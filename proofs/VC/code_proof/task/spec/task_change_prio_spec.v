Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_disabled_spec.
Require Export Ucos2Verify.lib.kernel_program_storage.
Require Export Ucos2Verify.lib.task_stack Ucos2Verify.lib.event_pool.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_continuation_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Export MonadLib.StateRelMonad.safeexec_lib.
Require Import SumLib.ZRange.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Import Monad UCOS2_C_Rules TaskStateDef SchedStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected V2.93.01 OSTaskChangePrio, with the reviewed post-SELF Idle
    protection and current-target OSPrioCur repair. The shared Sem transformer
    now includes that actual conditional cache store and retains its wait
    projection; the older ordered Sem critical relation still predates the Idle guard. Neither relation by itself states
    the whole API's Restore/OSRunning/Scheduler return. *)
Definition task_change_prio_selected_effect (sg : StableGlobVars)
  (selected newprio : Priority) : program UCOS2_Verify_State OSErrCode :=
  fun entry result after =>
    if Z.eqb selected sg.(osLowestPrio) then
      result = OS_ERR_PRIO_INVALID /\ after = entry
    else
      match entry.(TskState).(prioTbl) selected with
      | PTFree => result = OS_ERR_PRIO /\ after = entry
      | PTReserved => result = OS_ERR_TASK_NOT_EXIST /\ after = entry
      | PTTask tid => exists old,
          entry.(TskState).(inUsedTaskStates) tid = Some old /\
          result = OS_ERR_NONE /\
          after = task_change_priority_state sg entry tid old selected newprio
      end.

Definition task_change_prio_critical (sg : StableGlobVars)
  (requested newprio : Priority) : program UCOS2_Verify_State OSErrCode :=
  fun entry result after =>
    match entry.(TskState).(prioTbl) newprio with
    | PTReserved | PTTask _ => result = OS_ERR_PRIO_EXIST /\ after = entry
    | PTFree => exists selected,
        task_change_priority_selection sg entry requested selected /\
        task_change_prio_selected_effect sg selected newprio entry result after
    end.

Definition task_change_prio_critical_code sg requested newprio entry result after : Prop :=
  exists error, task_change_prio_critical sg requested newprio entry error after /\
    result = encode_os_err_code error.

(** Already approved application protocol, required only if the real
    acquired state reaches a live mutation. It adds no C test and places no
    owner restriction on argument/new-slot/Idle/NULL/reserved errors or on
    ordinary Mutex waiters. Environment intervals must preserve this
    admission at the same acquired endpoint; entry facts alone do not. *)
Definition task_change_prio_owner_protocol (sg : StableGlobVars)
  (requested newprio : Priority) (entry : UCOS2_Verify_State) : Prop :=
  entry.(TskState).(prioTbl) newprio = PTFree ->
  forall selected tid,
    task_change_priority_selection sg entry requested selected ->
    selected <> sg.(osLowestPrio) ->
    entry.(TskState).(prioTbl) selected = PTTask tid ->
    task_holds_no_mutex entry.(EventState) tid.

Definition task_change_prio_self_protocol sg requested newprio entry : Prop :=
  requested = sg.(osPrioSelf) -> entry.(TskState).(prioTbl) newprio = PTFree ->
  exists tid current, entry.(SchedState).(curTaskID) = Some tid /\
    entry.(TskState).(inUsedTaskStates) tid = Some current.

Lemma task_change_prio_selection_deterministic : forall sg entry requested left right,
  task_change_priority_selection sg entry requested left ->
  task_change_priority_selection sg entry requested right -> left = right.
Proof.
  intros sg entry requested left right Hleft Hright.
  destruct Hleft as [[Hself [i [a [Hi [Ha ->]]]]]|[Hnot ->]];
    destruct Hright as [[Hself' [j [b [Hj [Hb ->]]]]]|[Hnot' ->]];
    congruence.
Qed.

Lemma task_change_prio_new_slot_occupied : forall sg requested newprio entry result after,
  entry.(TskState).(prioTbl) newprio <> PTFree ->
  task_change_prio_critical sg requested newprio entry result after <->
  result = OS_ERR_PRIO_EXIST /\ after = entry.
Proof.
  intros; unfold task_change_prio_critical;
    destruct (entry.(TskState).(prioTbl) newprio); tauto.
Qed.

Lemma task_change_prio_resolved_idle : forall sg requested newprio entry,
  entry.(TskState).(prioTbl) newprio = PTFree ->
  task_change_priority_selection sg entry requested sg.(osLowestPrio) ->
  task_change_prio_critical sg requested newprio entry OS_ERR_PRIO_INVALID entry.
Proof.
  intros sg requested newprio entry Hfree Hselected.
  unfold task_change_prio_critical; rewrite Hfree.
  exists sg.(osLowestPrio); split; [exact Hselected|].
  unfold task_change_prio_selected_effect; rewrite Z.eqb_refl; auto.
Qed.

Lemma task_change_prio_selected_effect_deterministic :
  forall sg selected newprio entry code1 after1 code2 after2,
  task_change_prio_selected_effect sg selected newprio entry code1 after1 ->
  task_change_prio_selected_effect sg selected newprio entry code2 after2 ->
  code1 = code2 /\ after1 = after2.
Proof.
  intros sg selected newprio entry code1 after1 code2 after2 Hfirst Hsecond.
  unfold task_change_prio_selected_effect in *.
  destruct (Z.eqb selected sg.(osLowestPrio)); [intuition congruence|].
  destruct (entry.(TskState).(prioTbl) selected); try (intuition congruence).
  destruct Hfirst as [a [Ha [-> ->]]], Hsecond as [b [Hb [-> ->]]].
  assert (a = b) by congruence; subst b; auto.
Qed.

Lemma task_change_prio_critical_deterministic :
  forall sg requested newprio entry code1 after1 code2 after2,
  task_change_prio_critical sg requested newprio entry code1 after1 ->
  task_change_prio_critical sg requested newprio entry code2 after2 ->
  code1 = code2 /\ after1 = after2.
Proof.
  intros sg requested newprio entry code1 after1 code2 after2 Hfirst Hsecond.
  unfold task_change_prio_critical in *.
  destruct (entry.(TskState).(prioTbl) newprio); try (intuition congruence).
  destruct Hfirst as [left [Hleft Hfirst]], Hsecond as [right [Hright Hsecond]].
  pose proof (task_change_prio_selection_deterministic sg entry requested left right
    Hleft Hright) as ->.
  eapply task_change_prio_selected_effect_deterministic; eassumption.
Qed.

Lemma task_change_prio_live_selected_priority : forall sg entry tid old selected,
  UCOS2_state_inv sg entry ->
  entry.(TskState).(inUsedTaskStates) tid = Some old ->
  task_holds_no_mutex entry.(EventState) tid ->
  task_priority_in_range sg selected ->
  entry.(TskState).(prioTbl) selected = PTTask tid -> selected = old.(curPrio).
Proof.
  intros sg entry tid old selected Hvalid Hold Howner Hrange Htable.
  destruct Hvalid as [_ [_ [_ [_ [[[_ [_ Halias]] _] _]]]]].
  eapply mutex_unowned_task_alias_eq_current;
    [exact Halias|exact Hold|exact Howner|split; assumption].
Qed.

Lemma task_change_prio_live_distinct_priority : forall tasks tid selected newprio,
  tasks.(prioTbl) selected = PTTask tid -> tasks.(prioTbl) newprio = PTFree ->
  selected <> newprio.
Proof. intros tasks tid selected newprio Hselected Hnew E; subst; congruence. Qed.

Lemma task_change_prio_updated_task_fields : forall old newprio,
  let updated := mutex_priority_task old newprio in
  updated.(curPrio) = newprio /\ updated.(taskID) = old.(taskID) /\
  updated.(taskGeneration) = old.(taskGeneration) /\
  updated.(nextTCB) = old.(nextTCB) /\ updated.(prevTCB) = old.(prevTCB) /\
  updated.(stat) = old.(stat) /\ updated.(statPend) = old.(statPend) /\
  updated.(dly) = old.(dly) /\ updated.(eventPtr) = old.(eventPtr) /\
  updated.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) /\
  updated.(msg) = old.(msg) /\ updated.(tcbFlagNode) = old.(tcbFlagNode).
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_change_prio_state_module_frames : forall sg entry tid old selected newprio,
  let after := task_change_priority_state sg entry tid old selected newprio in
  after.(IntrState) = entry.(IntrState) /\
  after.(TickState) = entry.(TickState) /\
  after.(FlagState) = entry.(FlagState) /\
  after.(MemoryState) = entry.(MemoryState) /\
  after.(TimerState) = entry.(TimerState) /\
  after.(StatsState) = entry.(StatsState) /\
  after.(ControlState) = entry.(ControlState) /\
  after.(NameState) = entry.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_change_prio_state_sched_caches : forall sg entry tid old selected newprio,
  let after := task_change_priority_state sg entry tid old selected newprio in
  after.(SchedState).(curTaskID) = entry.(SchedState).(curTaskID) /\
  after.(SchedState).(curSchedPrio) =
    task_change_priority_cached_priority entry.(SchedState) tid newprio /\
  after.(SchedState).(highRdyTid) = entry.(SchedState).(highRdyTid) /\
  after.(SchedState).(highRdyPrio) = entry.(SchedState).(highRdyPrio) /\
  after.(SchedState).(ctxSwCtr) = entry.(SchedState).(ctxSwCtr) /\
  after.(SchedState).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intros; unfold after, task_change_priority_state, task_change_priority_ready,
    task_change_priority_current_cache, task_change_priority_cached_priority.
  destruct (Z.eqb
    (Z.land (encode_ready_tbl_at_or entry.(SchedState).(readyList)
      entry.(TskState) (old.(curPrio) / 8)) (tcb_bit_x_of_prio old.(curPrio))) 0);
    repeat split; reflexivity.
Qed.

(** The two source callers share the same kernel heap. Only the Task
    caller has a task allocation lease and parked continuations. A generic
    view keeps its actual handler/boot/locked origin through the call. *)
Inductive TaskChangePrioExecution : Type :=
| TaskChangePrioTask (call : OsSchedCallContext)
| TaskChangePrioGeneric (view : OsExecutionView).

Definition task_change_prio_view (execution : TaskChangePrioExecution)
  : OsExecutionView :=
  match execution with
  | TaskChangePrioTask call => os_sched_execution_view call
  | TaskChangePrioGeneric view => view
  end.

Definition task_change_prio_call_source (execution : TaskChangePrioExecution)
  (state : UCOS2_Verify_State) : Prop :=
  match execution with
  | TaskChangePrioTask call =>
      kernel_call_task_source call state /\ kernel_call_stack_available call state /\
      (state.(SchedState).(isRunning) = true -> state.(SchedState).(readyList) <> [])
  | TaskChangePrioGeneric view =>
      state.(SchedState).(isRunning) = false \/ sched_disabled_entry_source view state
  end.

(** Exactly the approved C completed-call control relation. Application
    admission is stated separately at the actual acquired endpoint below;
    an entry-time owner fact must not eliminate a later error branch. *)
Definition task_change_prio_completed_rely (_ _ : Priority) := kernel_call_control_rely.

Definition task_change_prio_closed environment saved_local critical sg execution mask state
  : Assertion :=
  match execution with
  | TaskChangePrioTask call =>
      os_sched_continuation_pre environment saved_local kernel_program_inv sg call mask state
  | TaskChangePrioGeneric view =>
      coq_prop (UCOS2_state_inv sg state) &&
      (sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask state ** unmap_table_rep sg)
  end.

Definition task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state
  : Assertion :=
  match execution with
  | TaskChangePrioTask call =>
      coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
      (critical_region_masked environment.(task_stack_call_platform) critical sg
        call.(os_sched_call_invocation) call.(os_sched_call_origin) saved acquired **
       os_sched_context_resources environment.(task_stack_call_external) call **
       store_parked_continuations
         (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
           state.(TskState) (task_create_continuation_local saved_local))
         state.(TskState).(parkedTaskStacks))
  | TaskChangePrioGeneric view =>
      critical_region_masked environment.(task_stack_call_platform) critical sg
        view.(os_execution_invocation) view.(os_execution_origin) saved acquired **
      os_execution_view_resources environment.(task_stack_call_external) view
  end.

Definition task_change_prio_masked environment saved_local critical sg execution saved acquired state
  : Assertion :=
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state **
  kernel_program_inv sg state.

Definition task_change_prio_save_interval environment critical sg
  original returned mask saved before acquired : Prop :=
  match original, returned with
  | TaskChangePrioTask first, TaskChangePrioTask last =>
      kernel_call_save_source environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical sg first last mask saved before acquired /\
      kernel_call_normal_return first before last acquired
  | TaskChangePrioGeneric first, TaskChangePrioGeneric last =>
      last = first /\ interrupt_saved_value mask saved /\
      critical_region_interval critical sg first.(os_execution_invocation) before acquired
  | _, _ => False
  end.

Definition task_change_prio_save_source environment critical sg requested newprio
  original returned mask saved before acquired : Prop :=
  task_change_prio_completed_rely requested newprio sg before acquired /\
  task_change_prio_save_interval environment critical sg
    original returned mask saved before acquired.

Definition task_change_prio_restore_interval environment critical sg
  original returned released current : Prop :=
  match original, returned with
  | TaskChangePrioTask first, TaskChangePrioTask last =>
      kernel_resumption_task_source_trace environment.(task_stack_call_external)
        environment.(task_stack_call_port) critical.(critical_region_clients) sg
        first.(os_sched_call_invocation) None first.(os_sched_call_origin) released false
        last.(os_sched_call_origin) current /\ kernel_call_normal_return first released last current
  | TaskChangePrioGeneric first, TaskChangePrioGeneric last =>
      last = first /\
      critical_region_interval critical sg first.(os_execution_invocation) released current
  | _, _ => False
  end.

Definition task_change_prio_restore_source environment critical sg
  original returned released current : Prop :=
  kernel_call_control_rely sg released current /\
  task_change_prio_restore_interval environment critical sg original returned released current.

(** Explicit C-environment assumptions for completed calls. Only actual
    Save/Restore intervals occur here. No own transformer, post-invariant,
    future scheduler cut or arbitrary continuation assertion is assumed. *)
Definition task_change_prio_environment environment critical sg requested newprio
  execution : Prop :=
  (forall original returned mask saved before acquired,
    UCOS2_state_inv sg before ->
    task_change_prio_save_interval environment critical sg
      original returned mask saved before acquired ->
    task_change_prio_completed_rely requested newprio sg before acquired) /\
  (forall original returned released current,
    UCOS2_state_inv sg released ->
    task_change_prio_restore_interval environment critical sg original returned released current ->
    kernel_call_control_rely sg released current) /\
  match execution with
  | TaskChangePrioTask _ => kernel_sched_ready_clients critical
  | TaskChangePrioGeneric view => sched_disabled_completed_clients critical view
  end.

Definition task_change_prio_admission environment critical sg requested newprio execution mask before : Prop :=
  task_change_priority_argument_error sg requested newprio = None ->
  task_change_prio_call_source execution before /\
  (forall returned saved acquired,
    task_change_prio_save_interval environment critical sg execution returned mask saved before acquired ->
    task_change_prio_owner_protocol sg requested newprio acquired /\
    task_change_prio_self_protocol sg requested newprio acquired).

Definition task_change_prio_static sg : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  event_table_layout_prop sg /\ kernel_tcb_stack_field_layout sg /\
  sg.(g_OSTCBTbl) mod 4 = 0.

(** The source's reserved pointer is 1. Positive pool addresses alone do
    not distinguish it from slot zero; use only the alignment projection
    already present at the selected TCB initialization layout boundary. *)
Lemma task_change_prio_alignment_from_init_layout : forall sg,
  init_tcb_list_layout sg -> sg.(g_OSTCBTbl) mod 4 = 0.
Proof. intros sg [_ [_ [_ [Halign _]]]]; exact Halign. Qed.

Lemma task_change_prio_slot_not_reserved : forall sg tid,
  task_change_prio_static sg -> task_slot_addr sg tid <> 1.
Proof.
  intros sg tid [Hconfig [_ [_ Halign]]] Hreserved.
  apply Z.mod_divide in Halign; [|lia].
  destruct Halign as [multiple Hmultiple].
  unfold task_slot_addr in Hreserved; rewrite Hconfig in Hreserved.
  cbn in Hreserved; lia.
Qed.

Definition task_change_prio_live sg state requested selected newprio tid node : Prop :=
  UCOS2_state_inv sg state /\
  task_change_priority_selection sg state requested selected /\
  state.(TskState).(prioTbl) newprio = PTFree /\
  state.(TskState).(prioTbl) selected = PTTask tid /\
  state.(TskState).(inUsedTaskStates) tid = Some node /\
  task_holds_no_mutex state.(EventState) tid /\
  selected = node.(curPrio) /\ 0 <= selected < 63 /\ 0 <= newprio < 63 /\
  selected <> newprio.

Definition task_change_prio_save_post environment saved_local critical sg requested newprio
  original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_change_prio_save_source environment critical sg requested newprio
      original returned mask saved before acquired) &&
    task_change_prio_masked environment saved_local critical sg returned saved acquired acquired.

Definition task_change_prio_restore_post environment saved_local critical sg original saved released
  : Assertion :=
  EX returned current,
    coq_prop (task_change_prio_restore_source environment critical sg
      original returned released current) &&
    task_change_prio_closed environment saved_local critical sg returned
      (armv7a_irq_fiq_mask saved) current.

Definition task_change_prio_scheduler_pre environment saved_local critical sg execution mask before
  : Assertion :=
  match execution with
  | TaskChangePrioTask call =>
      coq_prop (kernel_sched_ready_clients critical) &&
      os_sched_continuation_call_pre environment saved_local kernel_program_inv sg call mask before
  | TaskChangePrioGeneric view =>
      coq_prop (sched_disabled_completed_clients critical view /\
        UCOS2_state_inv sg before /\ sched_disabled_entry_source view before) &&
      (sched_disabled_closed environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask before ** unmap_table_rep sg)
  end.

Definition task_change_prio_scheduler_post environment saved_local critical sg execution mask before
  : Assertion :=
  match execution with
  | TaskChangePrioTask call =>
      os_sched_continuation_history_return_post environment critical saved_local
        kernel_program_inv sg call mask before
  | TaskChangePrioGeneric view =>
      sched_disabled_contextual_post environment.(task_stack_call_external)
        environment.(task_stack_call_platform) critical sg view mask before ** unmap_table_rep sg
  end.

(** The checkpoint records the own operation. The resource post records
    the real Restore and optional Scheduler return. In particular it does
    not assert that an intervening environment kept the target alive or
    retained its new priority, and it does not assert eventual return. *)
Definition task_change_prio_post environment saved_local critical sg requested newprio
  original mask before result : Assertion :=
  match task_change_priority_argument_error sg requested newprio with
  | Some error => coq_prop (result = encode_os_err_code error) &&
      task_change_prio_closed environment saved_local critical sg original mask before
  | None => EX saved acquired_execution acquired released restored_execution restored,
      coq_prop (
        task_change_prio_save_source environment critical sg requested newprio
          original acquired_execution mask saved before acquired /\
        UCOS2_state_inv sg acquired /\ UCOS2_state_inv sg released /\
        task_change_prio_critical_code sg requested newprio acquired result released /\
        task_change_prio_restore_source environment critical sg
          acquired_execution restored_execution released restored /\
        interrupt_saved_value mask saved) &&
      (if (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool then
        task_change_prio_scheduler_post environment saved_local critical sg restored_execution mask restored
       else task_change_prio_closed environment saved_local critical sg restored_execution mask restored)
  end.

(** Normal-return history at the checked C Scheduler boundary.  Task
    calls retain the actual Save/body/Restore checkpoints, including the
    segmented IRQ histories supported by the source producers.  The
    returned context is kept distinct from the input context: same-call
    is not record equality.  Generic disabled calls retain their own
    execution view.  Neither branch asserts that a future return exists. *)
Definition task_change_prio_scheduler_result environment critical sg
  original returned mask before current : Prop :=
  match original, returned with
  | TaskChangePrioTask first, TaskChangePrioTask last =>
      os_sched_continuation_call_history environment critical sg first mask before last current
  | TaskChangePrioGeneric first, TaskChangePrioGeneric last =>
      last = first /\ exists saved acquired,
        sched_disabled_completed_clients critical first /\
        critical_region_interval critical sg first.(os_execution_invocation) before acquired /\
        interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
        sched_disabled_context_rely first sg before acquired /\
        sched_disabled_entry_source first acquired /\
        sched_disabled_protected_identity acquired /\
        critical_region_interval critical sg first.(os_execution_invocation) acquired current /\
        sched_disabled_context_rely first sg acquired current /\
        sched_disabled_context_rely first sg before current /\
        UCOS2_state_inv sg current /\ sched_disabled_entry_source first current
  | _, _ => False
  end.

(** Whole-call program at the approved C modular boundary.
    Argument errors precede Save.  The critical relation checks destination,
    resolves SELF, protects Idle, and records the exact own update.  Restore
    and the actual running test precede the optional Scheduler.  Its final
    state is the returned world, not the own-update checkpoint.  The
    Scheduler history and closed resource post use the same returned
    context and current state; no flat-trace collapse is required. *)
Definition task_change_prio_program environment critical sg requested newprio
  original mask : program UCOS2_Verify_State Z :=
  fun before result current =>
    match task_change_priority_argument_error sg requested newprio with
    | Some error => result = encode_os_err_code error /\ current = before
    | None => exists saved acquired_execution acquired released restored_execution restored,
        task_change_prio_save_source environment critical sg requested newprio
          original acquired_execution mask saved before acquired /\
        task_change_prio_critical_code sg requested newprio acquired result released /\
        task_change_prio_restore_source environment critical sg
          acquired_execution restored_execution released restored /\
        interrupt_saved_value mask saved /\
        (if (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool then
          exists returned, task_change_prio_scheduler_result environment critical sg
            restored_execution returned mask restored current
         else current = restored)
    end.

Definition task_change_prio_safe_exec environment critical sg requested newprio
  original mask before (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before)
    (task_change_prio_program environment critical sg requested newprio original mask) X.

(** Keep the complete historical/resource post, and associate the very same
    returned kernel heap with the endpoint used by safeExec and arbitrary X.
    The conjunction is logical, not a duplicate separating ownership. *)
Definition task_change_prio_safe_post environment saved_local critical sg requested newprio
  original mask before result (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  task_change_prio_post environment saved_local critical sg requested newprio
    original mask before result &&
  (EX returned current,
    coq_prop (task_change_prio_program environment critical sg requested newprio
      original mask before result current /\
      safeExec (eq current) (ret result) X) &&
    task_change_prio_closed environment saved_local critical sg returned mask current).

Lemma task_change_prio_generic_scheduler_post_result :
  forall environment saved_local critical sg view mask before,
  task_change_prio_scheduler_post environment saved_local critical sg
    (TaskChangePrioGeneric view) mask before |--
  EX current,
    coq_prop (task_change_prio_scheduler_result environment critical sg
      (TaskChangePrioGeneric view) (TaskChangePrioGeneric view) mask before current) &&
    task_change_prio_closed environment saved_local critical sg (TaskChangePrioGeneric view) mask current.
Proof.
  intros environment saved_local critical sg view mask before.
  unfold task_change_prio_scheduler_post, sched_disabled_contextual_post.
  Intros saved acquired current.
  Exists current.
  unfold task_change_prio_scheduler_result, task_change_prio_closed.
  entailer!.
  exists saved, acquired; exact H.
Qed.

Lemma task_change_prio_scheduler_post_result :
  forall environment saved_local critical sg original mask before,
  task_change_prio_scheduler_post environment saved_local critical sg original mask before |--
  EX returned current,
    coq_prop (task_change_prio_scheduler_result environment critical sg
      original returned mask before current) &&
    task_change_prio_closed environment saved_local critical sg returned mask current.
Proof.
  intros environment saved_local critical sg [call|view] mask before.
  - unfold task_change_prio_scheduler_post, os_sched_continuation_history_return_post.
    Intros returned current.
    Exists (TaskChangePrioTask returned) current.
    unfold task_change_prio_scheduler_result, task_change_prio_closed,
      os_sched_continuation_pre; entailer!; tauto.
  - sep_apply_l_atomic (task_change_prio_generic_scheduler_post_result
      environment saved_local critical sg view mask before).
    Intros current; Exists (TaskChangePrioGeneric view) current; entailer!.
Qed.

Lemma task_change_prio_program_no_scheduler_return :
  forall environment critical sg requested newprio original mask before result saved
    acquired_execution acquired released restored_execution restored,
  task_change_priority_argument_error sg requested newprio = None ->
  task_change_prio_save_source environment critical sg requested newprio
    original acquired_execution mask saved before acquired ->
  task_change_prio_critical_code sg requested newprio acquired result released ->
  task_change_prio_restore_source environment critical sg
    acquired_execution restored_execution released restored ->
  interrupt_saved_value mask saved ->
  (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool = false ->
  task_change_prio_program environment critical sg requested newprio original mask before result restored.
Proof.
  intros environment critical sg requested newprio original mask before result saved
    acquired_execution acquired released restored_execution restored
    Hargument Hsave Heffect Hrestore Hsaved Hschedule.
  unfold task_change_prio_program; rewrite Hargument.
  exists saved, acquired_execution, acquired, released, restored_execution, restored.
  refine (conj Hsave (conj Heffect (conj Hrestore (conj Hsaved _)))).
  rewrite Hschedule; reflexivity.
Qed.

Lemma task_change_prio_program_scheduler_return :
  forall environment critical sg requested newprio original mask before result saved
    acquired_execution acquired released restored_execution restored returned current,
  task_change_priority_argument_error sg requested newprio = None ->
  task_change_prio_save_source environment critical sg requested newprio
    original acquired_execution mask saved before acquired ->
  task_change_prio_critical_code sg requested newprio acquired result released ->
  task_change_prio_restore_source environment critical sg
    acquired_execution restored_execution released restored ->
  interrupt_saved_value mask saved ->
  (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool = true ->
  task_change_prio_scheduler_result environment critical sg restored_execution returned mask restored current ->
  task_change_prio_program environment critical sg requested newprio original mask before result current.
Proof.
  intros environment critical sg requested newprio original mask before result saved
    acquired_execution acquired released restored_execution restored returned current
    Hargument Hsave Heffect Hrestore Hsaved Hschedule Hscheduler.
  unfold task_change_prio_program; rewrite Hargument.
  exists saved, acquired_execution, acquired, released, restored_execution, restored.
  refine (conj Hsave (conj Heffect (conj Hrestore (conj Hsaved _)))).
  rewrite Hschedule; exists returned; exact Hscheduler.
Qed.

Lemma task_change_prio_post_result :
  forall environment saved_local critical sg requested newprio original mask before result,
  task_change_prio_post environment saved_local critical sg requested newprio
    original mask before result |--
  EX returned current,
    coq_prop (task_change_prio_program environment critical sg requested newprio
      original mask before result current) &&
    task_change_prio_closed environment saved_local critical sg returned mask current.
Proof.
  intros environment saved_local critical sg requested newprio original mask before result.
  unfold task_change_prio_post.
  destruct (task_change_priority_argument_error sg requested newprio) as [error|] eqn:Hargument.
  - Intros; Exists original before.
    unfold task_change_prio_program; rewrite Hargument; entailer!.
  - Intros saved acquired_execution acquired released restored_execution restored.
    destruct H as [Hsave [Hacquired [Hreleased [Heffect [Hrestore Hsaved]]]]].
    destruct (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool eqn:Hschedule.
    + sep_apply_l_atomic (task_change_prio_scheduler_post_result
        environment saved_local critical sg restored_execution mask restored).
      Intros returned current; Exists returned current; entailer!.
      eapply task_change_prio_program_scheduler_return; eassumption.
    + Exists restored_execution restored; entailer!.
      eapply task_change_prio_program_no_scheduler_return; eassumption.
Qed.

Lemma task_change_prio_post_error_result :
  forall environment saved_local critical sg requested newprio original mask before result,
  result <> 0 ->
  task_change_prio_post environment saved_local critical sg requested newprio
    original mask before result |--
  EX returned current,
    coq_prop (task_change_prio_program environment critical sg requested newprio
      original mask before result current) &&
    task_change_prio_closed environment saved_local critical sg returned mask current.
Proof.
  intros environment saved_local critical sg requested newprio original mask before result Herror.
  assert (Hzero : Z.eqb result 0 = false) by (apply Z.eqb_neq; exact Herror).
  unfold task_change_prio_post.
  destruct (task_change_priority_argument_error sg requested newprio) as [error|] eqn:Hargument.
  - Intros. Exists original before.
    unfold task_change_prio_program; rewrite Hargument; entailer!.
  - Intros saved acquired_execution acquired released restored_execution restored.
    destruct H as [Hsave [Hacquired [Hreleased [Heffect [Hrestore Hsaved]]]]].
    rewrite Hzero; cbn.
    Exists restored_execution restored.
    entailer!.
    eapply task_change_prio_program_no_scheduler_return; try eassumption.
    rewrite Hzero; reflexivity.
Qed.

Lemma task_change_prio_safe_return :
  forall environment critical sg requested newprio original mask before result current X,
  task_change_prio_program environment critical sg requested newprio
    original mask before result current ->
  task_change_prio_safe_exec environment critical sg requested newprio original mask before X ->
  safeExec (eq current) (ret result) X.
Proof.
  intros environment critical sg requested newprio original mask before result current X Hstep Hsafe.
  eapply highstependret_derive with
    (c1 := task_change_prio_program environment critical sg requested newprio original mask)
    (P := eq before) (P' := fun _ => eq current).
  - intros state Hstate; subst state. exists current; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

(** This common return bridge covers all ordered error paths, successful
    no-Scheduler returns, and both Task and Generic Scheduler returns.
    The source result, arbitrary X and returned resources are associated
    with one endpoint on the same heap. *)
Lemma task_change_prio_post_safe_return :
  forall environment saved_local critical sg requested newprio original mask before result X,
  task_change_prio_safe_exec environment critical sg requested newprio original mask before X ->
  task_change_prio_post environment saved_local critical sg requested newprio
    original mask before result |--
  task_change_prio_safe_post environment saved_local critical sg requested newprio
    original mask before result X.
Proof.
  intros environment saved_local critical sg requested newprio original mask before result X Hsafe.
  unfold task_change_prio_safe_post.
  apply _derivable1_andp_intros; [entailer!|].
  sep_apply_l_atomic (task_change_prio_post_result environment saved_local critical sg
    requested newprio original mask before result).
  Intros returned current; Exists returned current; entailer!.
  eapply task_change_prio_safe_return; eassumption.
Qed.

(** Error returns do not call Scheduler.  This bridge keeps the exact
    acquired/Restore history already present in the original post. *)
Lemma task_change_prio_post_error_safe_return :
  forall environment saved_local critical sg requested newprio original mask before result X,
  result <> 0 ->
  task_change_prio_safe_exec environment critical sg requested newprio original mask before X ->
  task_change_prio_post environment saved_local critical sg requested newprio
    original mask before result |--
  task_change_prio_safe_post environment saved_local critical sg requested newprio
    original mask before result X.
Proof.
  intros environment saved_local critical sg requested newprio original mask before result X Herror Hsafe.
  unfold task_change_prio_safe_post.
  apply _derivable1_andp_intros; [entailer!|].
  sep_apply_l_atomic (task_change_prio_post_error_result environment saved_local critical sg
    requested newprio original mask before result Herror).
  Intros returned current.
  Exists returned current.
  entailer!.
  eapply task_change_prio_safe_return; eassumption.
Qed.

Lemma task_change_prio_no_scheduler_safe_return :
  forall environment saved_local critical sg requested newprio original mask before result saved
    acquired_execution acquired released restored_execution restored X,
  task_change_priority_argument_error sg requested newprio = None ->
  task_change_prio_save_source environment critical sg requested newprio
    original acquired_execution mask saved before acquired ->
  UCOS2_state_inv sg acquired -> UCOS2_state_inv sg released ->
  task_change_prio_critical_code sg requested newprio acquired result released ->
  task_change_prio_restore_source environment critical sg
    acquired_execution restored_execution released restored ->
  interrupt_saved_value mask saved ->
  (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool = false ->
  task_change_prio_safe_exec environment critical sg requested newprio original mask before X ->
  task_change_prio_closed environment saved_local critical sg restored_execution mask restored |--
  task_change_prio_safe_post environment saved_local critical sg requested newprio
    original mask before result X.
Proof.
  intros environment saved_local critical sg requested newprio original mask before result saved
    acquired_execution acquired released restored_execution restored X
    Hargument Hsave Hacquired Hreleased Heffect Hrestore Hsaved Hschedule Hsafe.
  assert (Hstep : task_change_prio_program environment critical sg requested newprio
    original mask before result restored).
  { eapply task_change_prio_program_no_scheduler_return; eassumption. }
  pose proof (task_change_prio_safe_return _ _ _ _ _ _ _ _ _ _ _ Hstep Hsafe) as Hreturn.
  unfold task_change_prio_safe_post; apply _derivable1_andp_intros.
  - unfold task_change_prio_post; rewrite Hargument.
    Exists saved acquired_execution acquired released restored_execution restored.
    rewrite Hschedule; entailer!.
  - Exists restored_execution restored; entailer!.
Qed.

Lemma task_change_prio_generic_scheduler_safe_return :
  forall environment saved_local critical sg requested newprio original mask before result saved
    acquired_execution acquired released view restored X,
  task_change_priority_argument_error sg requested newprio = None ->
  task_change_prio_save_source environment critical sg requested newprio
    original acquired_execution mask saved before acquired ->
  UCOS2_state_inv sg acquired -> UCOS2_state_inv sg released ->
  task_change_prio_critical_code sg requested newprio acquired result released ->
  task_change_prio_restore_source environment critical sg
    acquired_execution (TaskChangePrioGeneric view) released restored ->
  interrupt_saved_value mask saved ->
  (Z.eqb result 0 && restored.(SchedState).(isRunning))%bool = true ->
  task_change_prio_safe_exec environment critical sg requested newprio original mask before X ->
  task_change_prio_scheduler_post environment saved_local critical sg
    (TaskChangePrioGeneric view) mask restored |--
  task_change_prio_safe_post environment saved_local critical sg requested newprio
    original mask before result X.
Proof.
  intros environment saved_local critical sg requested newprio original mask before result saved
    acquired_execution acquired released view restored X
    Hargument Hsave Hacquired Hreleased Heffect Hrestore Hsaved Hschedule Hsafe.
  unfold task_change_prio_safe_post; apply _derivable1_andp_intros.
  - unfold task_change_prio_post; rewrite Hargument.
    Exists saved acquired_execution acquired released (TaskChangePrioGeneric view) restored.
    rewrite Hschedule; entailer!.
  - sep_apply_l_atomic (task_change_prio_generic_scheduler_post_result
      environment saved_local critical sg view mask restored).
    Intros current.
    assert (Hstep : task_change_prio_program environment critical sg requested newprio
      original mask before result current).
    { eapply task_change_prio_program_scheduler_return; eassumption. }
    pose proof (task_change_prio_safe_return _ _ _ _ _ _ _ _ _ _ _ Hstep Hsafe) as Hreturn.
    Exists (TaskChangePrioGeneric view) current; entailer!.
Qed.

Definition task_change_prio_addresses sg table current group rows running
  int_nesting lock_nesting high_prio current_prio high_tcb counter unmap : Prop :=
  sg.(g_OSTCBPrioTbl) = table /\ sg.(g_OSTCBCur) = current /\
  sg.(g_OSRdyGrp) = group /\ sg.(g_OSRdyTbl) = rows /\ sg.(g_OSRunning) = running /\
  os_sched_global_addresses sg int_nesting lock_nesting high_prio current_prio
    high_tcb table counter unmap group rows.

Definition task_change_prio_table_frame environment saved_local critical sg execution saved acquired
  state : Assertion :=
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state **
  UCOS2_raw_rep_missing_priority_table sg state ** unmap_table_rep sg.

Definition task_change_prio_table sg state : list Z :=
  map (fun p => prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) p)) (Zrange 0 64).

Definition task_change_prio_updated_table sg state tid node selected newprio : list Z :=
  task_change_prio_table sg (task_change_priority_state sg state tid node selected newprio).

Definition task_change_prio_ready_rows state : list Z :=
  map (encode_ready_tbl_at_or state.(SchedState).(readyList) state.(TskState)) (Zrange 0 8).

Definition task_change_prio_ready_group state : Z :=
  encode_ready_grp state.(SchedState).(readyList) state.(TskState).

Definition task_change_prio_running state : Z :=
  if state.(SchedState).(isRunning) then 1 else 0.

Definition task_change_prio_current state tid node : Prop :=
  state.(SchedState).(curTaskID) = Some tid /\
  state.(TskState).(inUsedTaskStates) tid = Some node.

Definition task_change_prio_self_frame environment saved_local critical sg execution saved acquired
  state tid node : Assertion :=
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state **
  task_public_storage_without_field sg state.(TskState) tid node (TCBCommonField TCBPrio) **
  sg.(g_OSRdyGrp) # UChar |-> task_change_prio_ready_group state **
  sched_rows_rep sg state.(TskState) state.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> task_change_prio_running state **
  UCOS2_raw_rep_missing_task_storage_sched sg state ** unmap_table_rep sg.

Definition task_change_prio_tcb_rest sg tid node : Assertion :=
  tcb64_fields_rep (task_slot_addr sg tid)
    (remove TCBField_eq_dec TCBEventPtr mutex_priority_unchanged_fields)
    (task_tcb64_image sg node).

Definition task_change_prio_work_frame environment saved_local critical sg execution saved acquired
  state tid node : Assertion :=
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state **
  task_change_prio_tcb_rest sg tid node **
  store_map_missing_i (used_task_rep sg) state.(TskState).(inUsedTaskStates) tid **
  task_free_storage_rep sg state.(TskState).(taskLifecycle).(taskFreeStorage)
    state.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error state.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg state.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> state.(TskState).(taskCount) **
  task_reg_allocator_rep sg state.(TskState) ** sched_physical_rep sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state ** unmap_table_rep sg.

(** Residual of the two current cells exposed for the actual identity test
    and conditional priority write. It contains all unrelated scheduler cells. *)
Definition task_change_prio_sched_physical_without_current sg scheduler : Assertion :=
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte scheduler.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg scheduler.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> scheduler.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if scheduler.(isRunning) then 1 else 0).

Definition task_change_prio_work_frame_without_current
  environment saved_local critical sg execution saved acquired state tid node : Assertion :=
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state **
  task_change_prio_tcb_rest sg tid node **
  store_map_missing_i (used_task_rep sg) state.(TskState).(inUsedTaskStates) tid **
  task_free_storage_rep sg state.(TskState).(taskLifecycle).(taskFreeStorage)
    state.(TskState).(unUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error state.(TskState).(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg state.(TskState).(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> state.(TskState).(taskCount) **
  task_reg_allocator_rep sg state.(TskState) **
  task_change_prio_sched_physical_without_current sg state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched_event sg state ** unmap_table_rep sg.

Lemma task_change_prio_work_frame_split_current :
  forall environment saved_local critical sg execution saved acquired state tid node,
  task_change_prio_work_frame environment saved_local critical sg execution saved acquired state tid node |--
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  task_change_prio_work_frame_without_current
    environment saved_local critical sg execution saved acquired state tid node.
Proof.
  intros; unfold task_change_prio_work_frame, task_change_prio_work_frame_without_current,
    sched_physical_rep, task_change_prio_sched_physical_without_current; entailer!.
Qed.

Lemma task_change_prio_work_frame_merge_current :
  forall environment saved_local critical sg execution saved acquired state tid node,
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(SchedState).(curSchedPrio) **
  task_change_prio_work_frame_without_current
    environment saved_local critical sg execution saved acquired state tid node |--
  task_change_prio_work_frame environment saved_local critical sg execution saved acquired state tid node.
Proof.
  intros; unfold task_change_prio_work_frame, task_change_prio_work_frame_without_current,
    sched_physical_rep, task_change_prio_sched_physical_without_current; entailer!.
Qed.

Lemma task_change_prio_sched_physical_merge_updated_current :
  forall sg state tid old selected destination,
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |->
    sched_priority_byte (task_change_priority_cached_priority state.(SchedState) tid destination) **
  task_change_prio_sched_physical_without_current sg state.(SchedState) |--
  sched_physical_rep sg
    (task_change_priority_state sg state tid old selected destination).(SchedState).
Proof.
  intros sg state tid old selected destination.
  destruct (task_change_prio_state_sched_caches sg state tid old selected destination)
    as [Hcurrent [Hpriority [Hhigh [Hhighprio [Hcounter Hrunning]]]]].
  unfold sched_physical_rep, task_change_prio_sched_physical_without_current.
  rewrite Hcurrent, Hpriority, Hhigh, Hhighprio, Hcounter, Hrunning; entailer!.
Qed.

Definition task_change_prio_event_rows state e : list Z :=
  map (encode_event_wait_tbl_at_or e.(waitList) state.(TskState)) (Zrange 0 8).

Definition task_change_prio_event_live state node eid e : Prop :=
  node.(eventPtr) = Some eid /\ state.(EventState).(inUsedEventStates) eid = Some e.

Definition task_change_prio_event_group state e : Z :=
  encode_event_wait_grp e.(waitList) state.(TskState).

Definition task_change_prio_event_frame sg state eid e : Assertion :=
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
    [EventTypeField; EventPadding1; EventPadding2; EventPadding3; EventPtrField;
     EventCntField; EventPadding19] (event_image sg state.(TskState) e) **
  event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid.

Definition task_change_prio_event_storage sg state node newprio : Assertion :=
  match node.(eventPtr) with
  | None => event_raw_rep sg state.(TskState) state.(EventState)
  | Some eid => EX e,
      coq_prop (state.(EventState).(inUsedEventStates) eid = Some e) &&
      ((event_addr sg eid + 10) # UChar |->
        mutex_priority_group (task_change_prio_event_rows state e)
          (task_change_prio_event_group state e) (tcb_y_of_prio node.(curPrio))
          (tcb_bit_x_of_prio node.(curPrio)) (tcb_bit_y_of_prio node.(curPrio)) newprio **
       UCharArray.full (event_addr sg eid + 11) 8
         (mutex_priority_rows (task_change_prio_event_rows state e)
           (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) newprio) **
       task_change_prio_event_frame sg state eid e)
  end.

Definition task_change_prio_event_pointer sg node : Z :=
  match node.(eventPtr) with None => 0 | Some eid => event_addr sg eid end.

Definition task_change_prio_closed_without_running environment saved_local critical sg execution mask state
  : Assertion :=
  match execution with
  | TaskChangePrioTask call =>
      coq_prop (task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) /\
        UCOS2_state_inv sg state) &&
      (kernel_call_execution_owned environment.(task_stack_call_external)
         environment.(task_stack_call_platform) call mask **
       UCOS2_raw_rep_missing_running sg state ** unmap_table_rep sg **
       store_parked_continuations
         (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
           state.(TskState) (task_create_continuation_local saved_local))
         state.(TskState).(parkedTaskStacks))
  | TaskChangePrioGeneric view =>
      coq_prop (UCOS2_state_inv sg state) &&
      (interrupt_platform_running environment.(task_stack_call_platform)
         view.(os_execution_invocation) view.(os_execution_origin) mask **
       critical_region_outside_without_running critical sg view.(os_execution_invocation) state **
       os_execution_view_resources environment.(task_stack_call_external) view ** unmap_table_rep sg)
  end.

Require Import Coq.Sorting.Permutation Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Lemma priority_coordinates_eq__priority_arithmetic : forall priority,
  0 <= priority < 64 ->
  unsigned_last_nbits (Z.shiftr priority 3) 8 = tcb_y_of_prio priority /\
  Z.land priority 7 = tcb_x_of_prio priority /\
  0 <= tcb_y_of_prio priority < 8 /\
  0 <= tcb_x_of_prio priority < 8 /\
  unsigned_last_nbits (Z.shiftl 1 (tcb_y_of_prio priority)) 8 =
    tcb_bit_y_of_prio priority /\
  unsigned_last_nbits (Z.shiftl 1 (tcb_x_of_prio priority)) 8 =
    tcb_bit_x_of_prio priority.
Proof.
  intros priority Hp.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding priority Hp)
    as [Hx [Hy [Hand Hshift]]].
  assert (Hdiv : Z.shiftr priority 3 = tcb_y_of_prio priority).
  { rewrite Z.shiftr_div_pow2 by lia; reflexivity. }
  rewrite Hdiv, (unsigned_last_nbits_eq (tcb_y_of_prio priority) 8) by (cbn; lia).
  rewrite !shift_one_unsigned_byte_eq__priority_encoding by assumption.
  unfold tcb_bit_y_of_prio, tcb_bit_x_of_prio; tauto.
Qed.
Lemma priority_table_writes_eq__priority_arithmetic :
  forall sg state tid node selected destination,
  0 <= selected < 64 -> 0 <= destination < 64 ->
  ListLib.Base.Positional.replace_Znth destination (task_slot_addr sg tid)
    (ListLib.Base.Positional.replace_Znth selected 0 (task_change_prio_table sg state)) =
  task_change_prio_updated_table sg state tid node selected destination.
Proof.
  intros sg state tid node selected destination Hselected Hdestination.
  assert (Hlength : forall current, Zlength (task_change_prio_table sg current) = 64).
  { intros; unfold task_change_prio_table; rewrite Zlength_correct, map_length; reflexivity. }
  assert (Hpoint : forall i, 0 <= i < 64 ->
    ListLib.Base.Positional.Znth i (ListLib.Base.Positional.replace_Znth destination (task_slot_addr sg tid)
      (ListLib.Base.Positional.replace_Znth selected 0 (task_change_prio_table sg state))) 0 =
    ListLib.Base.Positional.Znth i (task_change_prio_updated_table sg state tid node selected destination) 0).
  { intros i Hi.
    unfold task_change_prio_updated_table.
    unfold task_change_prio_table at 2.
    rewrite prio_table_values_Znth by exact Hi.
    change (ListLib.Base.Positional.Znth i (ListLib.Base.Positional.replace_Znth destination (task_slot_addr sg tid)
      (ListLib.Base.Positional.replace_Znth selected 0 (task_change_prio_table sg state))) 0 = prio_tbl_entry_to_addr sg
      (if Z.eqb i destination then PTTask tid else
       if Z.eqb i selected then PTFree else state.(TskState).(prioTbl) i)).
    destruct (Z.eq_dec i destination) as [->|Hnew].
    - rewrite ListLib.Base.Positional.Znth_replace_Znth_Same by (rewrite AUXLib.ListLib.Zlength_replace_Znth, Hlength; lia).
      rewrite Z.eqb_refl; reflexivity.
    - rewrite ListLib.Base.Positional.Znth_replace_Znth_Diff by
        (try rewrite AUXLib.ListLib.Zlength_replace_Znth, Hlength; lia).
      rewrite (proj2 (Z.eqb_neq _ _) Hnew).
      destruct (Z.eq_dec i selected) as [->|Hold].
      + rewrite ListLib.Base.Positional.Znth_replace_Znth_Same by (rewrite Hlength; lia).
        rewrite Z.eqb_refl; reflexivity.
      + rewrite ListLib.Base.Positional.Znth_replace_Znth_Diff by (try rewrite Hlength; lia).
        rewrite (proj2 (Z.eqb_neq _ _) Hold).
        unfold task_change_prio_table; apply prio_table_values_Znth; assumption. }
  apply (AUXLib.ListLib.list_eq_nth Z _ _ 0).
  - apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    rewrite !AUXLib.ListLib.Zlength_replace_Znth, Hlength.
    unfold task_change_prio_updated_table; rewrite Hlength; reflexivity.
  - intros n Hn.
    assert (Hn64 : 0 <= Z.of_nat n < 64).
    { apply Nat2Z.inj_lt in Hn.
      rewrite <- Zlength_correct in Hn.
      rewrite !AUXLib.ListLib.Zlength_replace_Znth, Hlength in Hn; lia. }
    specialize (Hpoint (Z.of_nat n) Hn64).
    unfold ListLib.Base.Positional.Znth in Hpoint; rewrite Nat2Z.id in Hpoint; exact Hpoint.
Qed.
Lemma ready_rows_length__priority_arithmetic : forall state,
  Zlength (task_change_prio_ready_rows state) = 8.
Proof.
  intros; unfold task_change_prio_ready_rows.
  rewrite Zlength_correct, map_length; reflexivity.
Qed.
Lemma ready_rows_in_range__priority_arithmetic : forall state i,
  0 <= i < 8 -> 0 <= ListLib.Base.Positional.Znth i (task_change_prio_ready_rows state) 0 < 256.
Proof.
  intros state i Hi.
  apply (ZRange.Forall_Znth_Zlength (fun value => 0 <= value < 256)).
  - apply Forall_forall; intros value Hin.
    unfold task_change_prio_ready_rows in Hin.
    apply in_map_iff in Hin; destruct Hin as [row [<- Hin]].
    apply encode_ready_tbl_or_in_range.
  - rewrite ready_rows_length__priority_arithmetic; exact Hi.
Qed.
Lemma ready_cleared_row_in_range__priority_arithmetic :
  forall state old_y old_bitx,
  0 <= old_y < 8 ->
  0 <= mutex_priority_cleared_row (task_change_prio_ready_rows state) old_y old_bitx < 256.
Proof.
  intros; apply mutex_priority_cleared_row_in_range__ready_bitmap_stages.
  apply ready_rows_in_range__priority_arithmetic; assumption.
Qed.
Lemma ready_replaced_rows_in_range__priority_arithmetic :
  forall state old_y old_bitx i,
  0 <= old_y < 8 -> 0 <= i < 8 ->
  0 <= ListLib.Base.Positional.Znth i (ListLib.Base.Positional.replace_Znth old_y
    (mutex_priority_cleared_row (task_change_prio_ready_rows state) old_y old_bitx)
    (task_change_prio_ready_rows state)) 0 < 256.
Proof.
  intros state old_y old_bitx i Hold Hi.
  destruct (Z.eq_dec old_y i) as [->|Hneq].
  - rewrite ListLib.Base.Positional.Znth_replace_Znth_Same by
      (rewrite ready_rows_length__priority_arithmetic; lia).
    apply ready_cleared_row_in_range__priority_arithmetic; assumption.
  - rewrite ListLib.Base.Positional.Znth_replace_Znth_Diff by
      (try rewrite ready_rows_length__priority_arithmetic; lia).
    apply ready_rows_in_range__priority_arithmetic; assumption.
Qed.
Lemma ready_group_in_range__priority_arithmetic : forall sg state,
  UCOS2_state_inv sg state -> 0 <= task_change_prio_ready_group state < 256.
Proof.
  intros sg state Hvalid.
  destruct Hvalid as [[Hstable Hprofile] [Htasks Hrest]].
  destruct Hstable as [_ [_ [_ [_ [_ [Hlowest Hstable]]]]]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hrange Htasks]]]]]]]].
  unfold task_change_prio_ready_group.
  apply encode_ready_grp_in_range.
  intros tid node Hin Hnode.
  pose proof (Hrange tid node Hnode) as Hp.
  unfold task_priority_in_range in Hp; rewrite Hlowest in Hp.
  split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma task_change_prio_event_rows_length__event_rows : forall state e,
  Zlength (task_change_prio_event_rows state e) = 8.
Proof.
  intros; unfold task_change_prio_event_rows.
  change (ZRange.Zrange 0 8) with [0;1;2;3;4;5;6;7]; reflexivity.
Qed.
Lemma task_change_prio_event_rows_index__event_rows : forall state e y,
  0 <= y < 8 ->
  ListLib.Base.Positional.Znth y (task_change_prio_event_rows state e) 0 =
    encode_ready_tbl_at_or e.(waitList) state.(TskState) y.
Proof.
  intros state e y Hy.
  change (ListLib.Base.Positional.Znth y (sched_row_values state.(TskState) e.(waitList)) 0 =
    encode_ready_tbl_at_or e.(waitList) state.(TskState) y).
  apply sched_row_values_Znth; exact Hy.
Qed.
Lemma task_change_prio_event_rows_in_range__event_rows : forall state e y,
  0 <= y < 8 -> 0 <= ListLib.Base.Positional.Znth y (task_change_prio_event_rows state e) 0 < 256.
Proof.
  intros; rewrite task_change_prio_event_rows_index__event_rows by assumption.
  apply encode_ready_tbl_or_in_range.
Qed.
Lemma task_change_prio_event_group_in_range__event_rows : forall sg state eid e,
  UCOS2_state_inv sg state -> state.(EventState).(inUsedEventStates) eid = Some e ->
  0 <= task_change_prio_event_group state e < 256.
Proof.
  intros sg state eid e [[Hstable _] [_ [_ [Hevents _]]]] Hget.
  destruct Hstable as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (Hentries eid e Hget) as [[_ [_ Hmembers]] _].
  change (0 <= encode_ready_grp e.(waitList) state.(TskState) < 2 ^ 8).
  apply encode_ready_grp_in_range; intros tid node Hin Hnode.
  destruct (Hmembers tid Hin) as [other [Hother Hprio]].
  rewrite Hnode in Hother; injection Hother as Heq; subst other.
  unfold valid_task_prio in Hprio.
  split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma bitmap_relocated_rows_unsigned_eq__event_rows :
  forall rows old_y old_bitx priority,
  Zlength rows = 8 -> 0 <= old_y < 8 -> 0 <= priority < 64 ->
  (forall y, 0 <= y < 8 -> 0 <= ListLib.Base.Positional.Znth y rows 0 < 256) ->
  Z.land (ListLib.Base.Positional.Znth old_y rows 0) old_bitx <> 0 ->
  ListLib.Base.Positional.replace_Znth (tcb_y_of_prio priority)
    (Z.lor (SimpleC.SL.IntLib.unsigned_last_nbits (ListLib.Base.Positional.Znth (tcb_y_of_prio priority)
       (ListLib.Base.Positional.replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bitx) rows) 0) 8)
      (SimpleC.SL.IntLib.unsigned_last_nbits (tcb_bit_x_of_prio priority) 8))
    (ListLib.Base.Positional.replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bitx) rows) =
  mutex_priority_rows rows old_y old_bitx priority.
Proof.
  intros rows old_y old_bitx priority Hlen Hold Hp Hrows Hpresent.
  assert (Hwas : mutex_priority_was_ready rows old_y old_bitx = true).
  { unfold mutex_priority_was_ready; apply negb_true_iff, Z.eqb_neq; exact Hpresent. }
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding priority Hp)
    as [Hx [Hy _]].
  pose proof (mutex_priority_removed_rows_in_range__ready_bitmap_stages
    rows old_y old_bitx (tcb_y_of_prio priority) Hlen Hold Hrows Hy) as Hrange.
  unfold mutex_priority_removed_rows in Hrange; rewrite Hwas in Hrange.
  rewrite (SimpleC.SL.IntLib.unsigned_last_nbits_eq _ 8 Hrange).
  unfold tcb_bit_x_of_prio.
  rewrite shift_one_unsigned_byte_eq__priority_encoding by exact Hx.
  unfold mutex_priority_rows, mutex_priority_removed_rows; rewrite Hwas; reflexivity.
Qed.
Lemma bitmap_cleared_row_unsigned_eq__event_rows : forall rows old_y old_bitx,
  Zlength rows = 8 -> 0 <= old_y < 8 ->
  0 <= ListLib.Base.Positional.Znth old_y rows 0 < 256 ->
  SimpleC.SL.IntLib.unsigned_last_nbits (ListLib.Base.Positional.Znth old_y
    (ListLib.Base.Positional.replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bitx) rows) 0) 32 =
  mutex_priority_cleared_row rows old_y old_bitx.
Proof.
  intros rows old_y old_bitx Hlen Hy Hrow.
  rewrite ListLib.Base.Positional.Znth_replace_Znth_Same by lia.
  apply SimpleC.SL.IntLib.unsigned_last_nbits_eq.
  pose proof (mutex_priority_cleared_row_in_range__ready_bitmap_stages rows old_y old_bitx Hrow).
  change (0 <= mutex_priority_cleared_row rows old_y old_bitx < 4294967296); lia.
Qed.
Lemma task_change_prio_event_pointer_zero__event_rows :
  forall sg state requested selected priority tid node,
  task_change_prio_live sg state requested selected priority tid node ->
  task_change_prio_event_pointer sg node = 0 -> node.(eventPtr) = None.
Proof.
  intros sg state requested selected priority tid node
    [Hinv [_ [_ [_ [Hnode _]]]]] Hzero.
  destruct Hinv as [Hprofile [_ [_ [Hevents [Hcross _]]]]].
  unfold task_change_prio_event_pointer in Hzero.
  destruct node.(eventPtr) as [eid|] eqn:Hptr; [|reflexivity].
  destruct (cross_module_invariants.task_event_reference_has_waiter
    sg state tid node eid Hcross Hnode Hptr) as [e [Hget Hin]].
  destruct (event_pool_used_not_free sg state.(EventState) eid e (proj1 Hevents) Hget)
    as [[Heid _] _].
  pose proof (valid_stable_address_pos sg sg.(g_OSEventTbl) (proj1 Hprofile)
    (or_introl eq_refl)) as Hbase.
  pose proof (event_object_size_positive sg.(osKernelConfig)) as Hsize.
  unfold event_addr, event_pool_addr in Hzero; nia.
Qed.
Lemma event_waiter_priority_bit_present__event_rows : forall ids tasks tid node,
  In tid ids -> tasks.(inUsedTaskStates) tid = Some node -> 0 <= node.(curPrio) ->
  Z.land (encode_ready_tbl_at_or ids tasks (tcb_y_of_prio node.(curPrio)))
    (tcb_bit_x_of_prio node.(curPrio)) <> 0.
Proof.
  intros ids tasks tid node Hin Hnode Hp.
  apply in_split in Hin; destruct Hin as [before [after Hids]]; subst ids.
  rewrite (encode_ready_tbl_or_permutation (before ++ tid :: after)
    (tid :: before ++ after) tasks (tcb_y_of_prio node.(curPrio))).
  - apply sched_tbl_head_bit; assumption.
  - apply Permutation_sym, Permutation_middle.
Qed.
Lemma event_storage_split_bitmap__event_rows : forall sg tasks eid e,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  used_event_rep sg tasks eid e |--
  UCharArray.full (event_addr sg eid + 11) 8
    (map (encode_event_wait_tbl_at_or e.(waitList) tasks) (ZRange.Zrange 0 8)) **
  (event_addr sg eid + 10) # UChar |-> encode_event_wait_grp e.(waitList) tasks **
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
    [EventTypeField; EventPadding1; EventPadding2; EventPadding3;
     EventPtrField; EventCntField; EventPadding19] (event_image sg tasks e).
Proof.
  intros sg tasks eid e Hnames.
  unfold used_event_rep, event_storage_rep; rewrite Hnames.
  assert (Horder : EventFieldStorage.store_fields EventField_eq_dec
    (event_cell (event_addr sg eid)) (event_fields false) (event_image sg tasks e) =
    EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
      [EventGrpField; EventTbl0; EventTbl1; EventTbl2; EventTbl3;
       EventTbl4; EventTbl5; EventTbl6; EventTbl7; EventTypeField; EventPadding1;
       EventPadding2; EventPadding3; EventPtrField; EventCntField; EventPadding19]
      (event_image sg tasks e)).
  { unfold EventFieldStorage.store_fields; f_equal.
    apply functional_extensionality; intros []; reflexivity. }
  rewrite Horder.
  do 9 (match goal with
  | |- ?lhs |-- _ => match lhs with
    | context [EventFieldStorage.store_fields EventField_eq_dec ?cell (?f :: ?fs) ?image] =>
      sep_apply_l_atomic (proj1 (EventFieldStorage.store_fields_cons EventField (option Z)
        EventField_eq_dec cell fs image f
        ltac:(repeat constructor; simpl; intuition discriminate)))
    end
  end).
  change (ZRange.Zrange 0 8) with [0;1;2;3;4;5;6;7].
  unfold UCharArray.full, store_array.
  cbn [ZRange.Zrange map store_array_rec StoreUCharAsElement.storeA event_cell event_image event_field_offset].
  rewrite sizeof_uchar; simpl.
  assert (Hoffset : forall n, event_addr sg eid + 11 + n = event_addr sg eid + (11 + n)) by (intros; lia).
  repeat rewrite Hoffset; cbn; entailer!.
Qed.
Lemma task_change_prio_profile_constants__task_state :
  forall sg state, UCOS2_state_inv sg state ->
  sg.(osLowestPrio) = 63 /\ sg.(osPrioSelf) = 255.
Proof.
  intros sg state [Hprofile _].
  destruct Hprofile as [Hvalid _].
  unfold valid_stable_glob_vars in Hvalid; tauto.
Qed.
Lemma task_change_prio_table_split__task_state :
  forall environment saved_local critical sg execution saved acquired state,
  task_change_prio_masked environment saved_local critical sg execution saved acquired state |--
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_change_prio_table sg state) **
  task_change_prio_table_frame environment saved_local critical sg execution saved acquired state.
Proof.
  intros; unfold task_change_prio_masked, kernel_program_inv, kernel_program_rep,
    task_change_prio_table_frame, task_change_prio_table.
  Intros. rewrite UCOS2_raw_rep_priority_table_equiv.
  unfold store_prio_tbl; entailer!.
Qed.
Lemma task_change_prio_table_merge__task_state :
  forall environment saved_local critical sg execution saved acquired state,
  UCOS2_state_inv sg state ->
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_change_prio_table sg state) **
  task_change_prio_table_frame environment saved_local critical sg execution saved acquired state |--
  task_change_prio_masked environment saved_local critical sg execution saved acquired state.
Proof.
  intros; unfold task_change_prio_masked, kernel_program_inv, kernel_program_rep,
    task_change_prio_table_frame, task_change_prio_table.
  rewrite UCOS2_raw_rep_priority_table_equiv.
  unfold store_prio_tbl; entailer!.
Qed.
Lemma task_change_prio_live_slot_positive__task_state :
  forall sg state tid node, UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some node -> 0 < task_slot_addr sg tid.
Proof.
  intros sg state tid node [Hprofile [Htasks _]] Hnode.
  assert (Haddresses : Forall (fun a => 0 < a) (stable_global_addresses sg)).
  { unfold selected_kernel_profile, valid_stable_glob_vars,
      valid_stable_global_addresses in Hprofile; tauto. }
  assert (Hbase : 0 < sg.(g_OSTCBTbl)).
  { rewrite Forall_forall in Haddresses; apply Haddresses.
    unfold stable_global_addresses; simpl; tauto. }
  destruct Htasks as [[Hdomain _] _].
  assert (Hslot : task_slot_in_range sg tid).
  { apply Hdomain; left; exists node; exact Hnode. }
  destruct Hslot as [Htid _]. unfold task_slot_addr, tcb_configured_size.
  destruct (cfgEventMultiEnabled (osKernelConfig sg)),
    (cfgTaskProfile (osKernelConfig sg)); cbn; lia.
Qed.
(** The live target is a non-NULL configured TCB slot. Therefore the
    actual protected pointer comparison has exactly the identity test used
    by the transformer, including the generic/None-current case. *)
Lemma task_change_prio_current_pointer_eq_iff : forall sg state tid node,
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  (task_slot_addr sg tid = encode_task_link sg state.(SchedState).(curTaskID) <->
    state.(SchedState).(curTaskID) = Some tid).
Proof.
  intros sg state tid node Hvalid Hnode.
  destruct state.(SchedState).(curTaskID) as [current|]; cbn [encode_task_link].
  - split.
    + intro Haddress; apply task_slot_addr_injective in Haddress; congruence.
    + intro Hidentity; inversion Hidentity; reflexivity.
  - split; [|discriminate]. intro Hnull.
    pose proof (task_change_prio_live_slot_positive__task_state sg state tid node Hvalid Hnode); lia.
Qed.

Lemma task_change_prio_current_cache_byte_eq : forall sg state tid node newprio,
  UCOS2_state_inv sg state ->
  state.(TskState).(inUsedTaskStates) tid = Some node ->
  sched_priority_byte (task_change_priority_cached_priority state.(SchedState) tid newprio) =
    if Z.eqb (task_slot_addr sg tid) (encode_task_link sg state.(SchedState).(curTaskID))
    then newprio else sched_priority_byte state.(SchedState).(curSchedPrio).
Proof.
  intros sg state tid node newprio Hvalid Hnode.
  unfold task_change_priority_cached_priority.
  destruct state.(SchedState).(curTaskID) as [current|]; cbn [encode_task_link].
  - destruct (Z.eq_dec tid current) as [->|Hother].
    + rewrite !Z.eqb_refl; reflexivity.
    + rewrite (proj2 (Z.eqb_neq tid current) Hother).
      rewrite (proj2 (Z.eqb_neq (task_slot_addr sg tid) (task_slot_addr sg current))).
      * reflexivity.
      * intro Haddress; apply task_slot_addr_injective in Haddress; contradiction.
  - assert (Hnonzero : task_slot_addr sg tid <> 0).
    { pose proof (task_change_prio_live_slot_positive__task_state sg state tid node Hvalid Hnode); lia. }
    rewrite (proj2 (Z.eqb_neq (task_slot_addr sg tid) 0) Hnonzero); reflexivity.
Qed.

Lemma task_change_prio_table_zero_is_free__task_state :
  forall sg state priority, UCOS2_state_inv sg state -> 0 <= priority < 64 ->
  ListLib.Base.Positional.Znth priority (task_change_prio_table sg state) 0 = 0 ->
  state.(TskState).(prioTbl) priority = PTFree.
Proof.
  intros sg state priority Hvalid Hrange Hzero.
  unfold task_change_prio_table in Hzero.
  rewrite prio_table_values_Znth in Hzero by exact Hrange.
  destruct (state.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry; try reflexivity;
    cbn [prio_tbl_entry_to_addr] in Hzero; try discriminate.
  pose proof (task_change_prio_profile_constants__task_state
    sg state Hvalid) as [Hlowest _].
  assert (Hindex : task_priority_in_range sg priority) by
    (unfold task_priority_in_range; lia).
  pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Hslots _]] _].
  specialize (Hslots priority Hindex); rewrite Hentry in Hslots.
  destruct Hslots as [node Hnode].
  pose proof (task_change_prio_live_slot_positive__task_state
    sg state tid node Hvalid Hnode); lia.
Qed.
Lemma task_change_prio_self_split__task_state :
  forall environment saved_local critical sg execution saved acquired state tid node,
  task_change_prio_current state tid node ->
  task_change_prio_masked environment saved_local critical sg execution saved acquired state |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
  task_change_prio_self_frame environment saved_local critical sg execution saved acquired state tid node.
Proof.
  intros environment saved_local critical sg execution saved acquired state tid node [Hcurrent Hnode].
  unfold task_change_prio_masked, kernel_program_inv, kernel_program_rep.
  Intros.
  unfold UCOS2_raw_rep, task_shared_rep.
  sep_apply (task_public_storage_split_field sg state.(TskState) tid node
    (TCBCommonField TCBPrio) Hnode (tcb_configured_common_field_in _ _ _)).
  unfold task_change_prio_self_frame, UCOS2_raw_rep_missing_task_storage_sched,
    sched_raw_rep, sched_physical_rep, task_change_prio_ready_group,
    task_change_prio_running.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell].
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.
Lemma task_change_prio_self_merge__task_state :
  forall environment saved_local critical sg execution saved acquired state tid node,
  UCOS2_state_inv sg state -> task_change_prio_current state tid node ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
  task_change_prio_self_frame environment saved_local critical sg execution saved acquired state tid node |--
  task_change_prio_masked environment saved_local critical sg execution saved acquired state.
Proof.
  intros environment saved_local critical sg execution saved acquired state tid node Hvalid [Hcurrent Hnode].
  pose proof (task_public_storage_merge_field sg state.(TskState) tid node
    (TCBCommonField TCBPrio) Hnode (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell] in Hmerge.
  unfold task_change_prio_self_frame.
  unfold task_change_prio_masked, kernel_program_inv, kernel_program_rep,
    UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched,
    sched_raw_rep, sched_physical_rep, task_change_prio_ready_group,
    task_change_prio_running.
  rewrite Hcurrent; cbn [encode_task_link].
  entailer!; exact Hmerge.
Qed.
Lemma task_change_prio_tcb_split__task_state :
  forall sg tid node, task_change_prio_static sg ->
  used_task_rep sg tid node |--
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBY # UChar |-> tcb_y_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBX # UChar |-> tcb_x_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |-> tcb_bit_y_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |-> tcb_bit_x_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |-> task_change_prio_event_pointer sg node **
  task_change_prio_tcb_rest sg tid node.
Proof.
  intros sg tid node Hstatic.
  destruct Hstatic as [Hconfig _].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hconfig; reflexivity).
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hconfig; reflexivity).
  rewrite used_task_rep_tcb64 by assumption.
  rewrite <- task_slot_addr_tcb64 by assumption.
  rewrite <- mutex_priority_reordered_fields.
  unfold tcb64_fields_rep at 1.
  do 5 (rewrite TaskFieldStorage.store_fields_cons at 1 by
    (unfold mutex_priority_unchanged_fields;
      repeat (apply NoDup_cons; [simpl; intuition discriminate|]); constructor)).
  fold (tcb64_fields_rep (task_slot_addr sg tid) mutex_priority_unchanged_fields
    (task_tcb64_image sg node)).
  sep_apply (tcb64_fields_rep_split mutex_priority_unchanged_fields
    (task_slot_addr sg tid) (task_tcb64_image sg node) TCBEventPtr).
  - unfold task_change_prio_tcb_rest, task_change_prio_event_pointer.
    cbn [tcb_cell task_tcb64_image].
    entailer!.
  - unfold mutex_priority_unchanged_fields; simpl; tauto.
  - unfold mutex_priority_unchanged_fields;
      repeat (apply NoDup_cons; [simpl; intuition discriminate|]); constructor.
Qed.
Lemma task_change_prio_work_split__task_state :
  forall environment saved_local critical sg execution saved acquired state tid node,
  task_change_prio_static sg -> state.(TskState).(inUsedTaskStates) tid = Some node ->
  task_change_prio_masked environment saved_local critical sg execution saved acquired state |--
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_change_prio_table sg state) **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_change_prio_ready_rows state) **
  sg.(g_OSRdyGrp) # UChar |-> task_change_prio_ready_group state **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBY # UChar |-> tcb_y_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBX # UChar |-> tcb_x_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |-> tcb_bit_y_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |-> tcb_bit_x_of_prio node.(curPrio) **
  tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |-> task_change_prio_event_pointer sg node **
  event_raw_rep sg state.(TskState) state.(EventState) **
  task_change_prio_work_frame environment saved_local critical sg execution saved acquired state tid node.
Proof.
  intros environment saved_local critical sg execution saved acquired state tid node Hstatic Hnode.
  unfold task_change_prio_masked, kernel_program_inv, kernel_program_rep.
  Intros. unfold UCOS2_raw_rep, task_shared_rep.
  sep_apply (task_public_storage_split_task sg state.(TskState) tid node Hnode).
  sep_apply (task_change_prio_tcb_split__task_state sg tid node Hstatic).
  unfold task_public_storage_without_task, task_public_storage_without_used_map,
    task_change_prio_work_frame, UCOS2_raw_rep_missing_task_storage_sched_event,
    sched_raw_rep, store_prio_tbl, task_change_prio_table,
    task_change_prio_ready_rows, task_change_prio_ready_group.
  rewrite sched_rows_array_equiv.
  unfold sched_row_values; entailer!.
Qed.
Lemma task_change_prio_used_map_live_iff__task_state :
  forall tasks tid old selected destination slot,
  tasks.(inUsedTaskStates) tid = Some old ->
  (exists node, (task_change_priority_tasks tasks tid old selected destination).(inUsedTaskStates)
    slot = Some node) <-> exists node, tasks.(inUsedTaskStates) slot = Some node.
Proof.
  intros; apply (glob_task_set_usedtask_live_iff tasks tid old
    (mutex_priority_task old destination) slot); assumption.
Qed.
Lemma task_change_prio_used_map_origin__task_state :
  forall tasks tid old selected destination slot node,
  (task_change_priority_tasks tasks tid old selected destination).(inUsedTaskStates) slot = Some node ->
  (slot = tid /\ node = mutex_priority_task old destination) \/
  (slot <> tid /\ tasks.(inUsedTaskStates) slot = Some node).
Proof.
  intros tasks tid old selected destination slot node Hnode.
  cbn [task_change_priority_tasks glob_task_set_usedtask inUsedTaskStates] in Hnode.
  destruct (Z.eqb slot tid) eqn:Heq.
  - apply Z.eqb_eq in Heq; left; split; congruence.
  - apply Z.eqb_neq in Heq; right; auto.
Qed.
Lemma task_change_prio_tasks_preserves_in_range__task_state :
  forall sg tasks tid old selected destination,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some old ->
  selected = old.(curPrio) -> tasks.(prioTbl) destination = PTFree ->
  task_priority_in_range sg destination ->
  task_in_range sg (task_change_priority_tasks tasks tid old selected destination).
Proof.
  intros sg tasks tid old selected destination
    [Hpool [Hactive [Hfree [Hreservations [Hgenerations [Hregistered [Hunique [Hpriority Hrest]]]]]]]]
    Hold Hselected Hdestination Hrange.
  assert (Hcurrent : tasks.(prioTbl) selected = PTTask tid) by
    (rewrite Hselected; apply Hregistered; exact Hold).
  assert (Hreg : task_current_prio_registered
    (task_change_priority_tasks tasks tid old selected destination)).
  { intros slot node Hnode.
    destruct (task_change_prio_used_map_origin__task_state
      tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hother Hbefore]].
    - cbn [task_change_priority_tasks mutex_priority_task prioTbl curPrio].
      rewrite Z.eqb_refl; reflexivity.
    - pose proof (Hregistered slot node Hbefore) as Hslot.
      cbn [task_change_priority_tasks prioTbl].
      destruct (Z.eqb node.(curPrio) destination) eqn:Hnew.
      + apply Z.eqb_eq in Hnew; rewrite Hnew, Hdestination in Hslot; discriminate.
      + destruct (Z.eqb node.(curPrio) selected) eqn:Holdprio; [|exact Hslot].
        apply Z.eqb_eq in Holdprio; rewrite Holdprio, Hcurrent in Hslot.
        injection Hslot as Hslot; congruence. }
  split.
  - destruct Hpool as [Hdomain [Hused [Hprivate [Hnd [Hstorage HreservationUnique]]]]].
    split.
    + intro slot; cbn [task_change_priority_tasks unUsedTaskStates].
      rewrite task_change_prio_used_map_live_iff__task_state by exact Hold.
      exact (Hdomain slot).
    + split.
      * intros slot node Hnode.
        destruct (task_change_prio_used_map_origin__task_state
          tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hother Hbefore]].
        -- exact (Hused tid old Hold).
        -- exact (Hused slot node Hbefore).
      * split; [exact Hprivate|]. split; [exact Hnd|].
        split; [exact Hstorage|exact HreservationUnique].
  - split.
    + destruct Hactive as [Hnd [Hhead [Hcount [Hcover Hlinks]]]].
      split; [exact Hnd|]. split; [exact Hhead|]. split; [exact Hcount|]. split.
      * intro slot; rewrite task_change_prio_used_map_live_iff__task_state
          by exact Hold; exact (Hcover slot).
      * change (task_active_links (glob_task_set_usedtask tasks tid
          (mutex_priority_task old destination)).(inUsedTaskStates) None
          tasks.(taskLifecycle).(taskActiveOrder)).
        eapply task_active_links_update; [exact Hold|reflexivity|reflexivity|reflexivity|exact Hlinks].
    + split; [exact Hfree|]. split.
      * destruct Hreservations as [Hentries HreservationUnique]; split; [|exact HreservationUnique].
        intros priority entry Hentry.
        destruct (Hentries priority entry Hentry) as [Hp [Hreserved Hinvocation]].
        split; [exact Hp|]. split; [|exact Hinvocation].
        cbn [task_change_priority_tasks prioTbl].
        destruct (Z.eqb priority destination) eqn:Hnew.
        -- apply Z.eqb_eq in Hnew; subst priority; congruence.
        -- destruct (Z.eqb priority selected) eqn:Holdprio; [|exact Hreserved].
           apply Z.eqb_eq in Holdprio; subst priority; congruence.
      * split.
        -- destruct Hgenerations as [Hlive Hother]; split; [|exact Hother].
           intros slot node Hnode.
           destruct (task_change_prio_used_map_origin__task_state
             tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
           ++ exact (Hlive tid old Hold).
           ++ exact (Hlive slot node Hbefore).
        -- split; [exact Hreg|]. split.
           ++ apply task_registration_implies_priority_unique; exact Hreg.
           ++ split; [|exact Hrest]. intros slot node Hnode.
              destruct (task_change_prio_used_map_origin__task_state
                tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
              ** exact Hrange.
              ** exact (Hpriority slot node Hbefore).
Qed.
Lemma task_change_prio_other_aliases_iff__task_state :
  forall sg tasks tid old selected destination other,
  tasks.(prioTbl) selected = PTTask tid -> tasks.(prioTbl) destination = PTFree ->
  other <> tid -> forall priority,
  task_priority_alias sg tasks.(prioTbl) other priority <->
  task_priority_alias sg (task_change_priority_tasks tasks tid old selected destination).(prioTbl)
    other priority.
Proof.
  intros sg tasks tid old selected destination other Hselected Hdestination Hother priority.
  unfold task_priority_alias; cbn [task_change_priority_tasks prioTbl].
  destruct (Z.eqb priority destination) eqn:Hnew.
  - apply Z.eqb_eq in Hnew; subst priority; rewrite Hdestination; intuition congruence.
  - destruct (Z.eqb priority selected) eqn:Holdprio; [|reflexivity].
    apply Z.eqb_eq in Holdprio; subst priority; rewrite Hselected; intuition congruence.
Qed.
Lemma task_change_prio_mutex_claims_avoid_slots__task_state :
  forall sg state tid old selected destination,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  state.(TskState).(prioTbl) selected = PTTask tid ->
  state.(TskState).(prioTbl) destination = PTFree -> task_priority_in_range sg destination ->
  task_holds_no_mutex state.(EventState) tid ->
  forall mid node fields,
  state.(EventState).(inUsedEventStates) mid = Some node ->
  node.(eventType) = OS_EVENT_TYPE_MUTEX -> node.(mutexFields) = Some fields ->
  mutex_pcp_enabled sg fields -> fields.(mfPCP) <> selected /\ fields.(mfPCP) <> destination.
Proof.
  intros sg state tid old selected destination Hvalid Hold Hselected Hdestination Hrange
    Howner mid node fields Hnode Htype Hfields Henabled.
  destruct Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Hslots _]] [_ [_ [Hprotocol _]]]].
  split.
  - intro Heq.
    destruct (Hprotocol mid node fields Hnode Htype Hfields) as [_ [_ [Hdisabled|[_ Hslot]]]].
    + contradiction.
    + rewrite Heq, Hselected in Hslot.
      destruct Hslot as [Hreserved|[owner [Howned Htable]]]; [discriminate|].
      injection Htable as Htable; subst owner.
      exact (Howner mid node fields Hnode Htype Hfields Howned).
  - intro Heq. specialize (Hslots destination Hrange); rewrite Hdestination in Hslots.
    apply Hslots; exists mid, node, fields; repeat split; assumption.
Qed.
Lemma task_change_prio_task_mutex_invariants__task_state :
  forall sg state tid old selected destination,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  selected = old.(curPrio) -> state.(TskState).(prioTbl) selected = PTTask tid ->
  state.(TskState).(prioTbl) destination = PTFree -> task_priority_in_range sg destination ->
  task_holds_no_mutex state.(EventState) tid ->
  let tasks := task_change_priority_tasks state.(TskState) tid old selected destination in
  task_mutex_priotbl_consistency sg tasks state.(EventState) /\
  mutex_owner_snapshot_in_range sg tasks state.(EventState) /\
  mutex_protocol_consistency sg (replace_TskS tasks state) /\
  pending_mutex_consistency sg tasks state.(EventState).
Proof.
  intros sg state tid old selected destination Hvalid Hold Hselected Htable Hfree Hrange Howner tasks.
  pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [HtableInv [Hsnapshots [_ [Hprotocol _]]]].
  pose proof (UCOS2_state_inv_pending_mutex sg state Hvalid) as Hpending.
  destruct HtableInv as [Hreservations [Hslots Haliases]].
  assert (Hother : forall other, other <> tid -> forall priority,
    task_priority_alias sg state.(TskState).(prioTbl) other priority <->
    task_priority_alias sg tasks.(prioTbl) other priority).
  { intros; apply task_change_prio_other_aliases_iff__task_state;
      assumption. }
  assert (Htarget : forall priority,
    task_priority_alias sg tasks.(prioTbl) tid priority <-> priority = destination).
  { intro priority; unfold tasks, task_priority_alias.
    cbn [task_change_priority_tasks prioTbl].
    destruct (Z.eqb priority destination) eqn:Hnew.
    - apply Z.eqb_eq in Hnew; subst priority; split; auto.
    - apply Z.eqb_neq in Hnew; split; [|contradiction]. intros [Hp Hentry].
      destruct (Z.eqb priority selected) eqn:Holdprio; [discriminate|].
      assert (Heq : priority = old.(curPrio)).
      { eapply mutex_unowned_task_alias_eq_current;
          [exact Haliases|exact Hold|exact Howner|split; assumption]. }
      apply Z.eqb_neq in Holdprio; congruence. }
  assert (Hclaims := task_change_prio_mutex_claims_avoid_slots__task_state
    sg state tid old selected destination Hvalid Hold Htable Hfree Hrange Howner).
  split.
  - split; [exact Hreservations|]. split.
    + intros priority Hp; unfold tasks; cbn [task_change_priority_tasks prioTbl].
      destruct (Z.eqb priority destination) eqn:Hnew.
      * exists (mutex_priority_task old destination); simpl; rewrite Z.eqb_refl; reflexivity.
      * destruct (Z.eqb priority selected) eqn:Holdprio.
        -- apply Z.eqb_eq in Holdprio; subst priority.
           intros [mid [node [fields [Hnode [Htype [Hfields [Henabled Heq]]]]]]].
           destruct (Hclaims mid node fields Hnode Htype Hfields Henabled); contradiction.
        -- specialize (Hslots priority Hp).
           destruct (prioTbl (TskState state) priority) as [| |other]; try exact Hslots.
           apply (proj2 (task_change_prio_used_map_live_iff__task_state
             state.(TskState) tid old selected destination other Hold)); exact Hslots.
    + intros slot node Hnode.
      destruct (task_change_prio_used_map_origin__task_state
        state.(TskState) tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
      * exists destination; split.
        -- split; [apply Htarget; reflexivity|]. intros priority Hp; apply Htarget in Hp; lia.
        -- split.
           ++ split; [apply Htarget; reflexivity|]. intros priority Hp; apply Htarget in Hp.
              cbn [mutex_priority_task curPrio]; lia.
           ++ intros priority Hp; left; apply Htarget; exact Hp.
      * destruct (Haliases slot node Hbefore) as [base [Hbase [Heffective HclaimsOld]]].
        exists base; split.
        -- eapply task_base_priority_alias_ext; [apply Hother; exact Hneq|exact Hbase].
        -- split.
           ++ eapply task_effective_priority_alias_ext; [apply Hother; exact Hneq|exact Heffective].
           ++ intros priority Hp; apply HclaimsOld; apply Hother; assumption.
  - split.
    + intros mid node fields owner Hnode Htype Hfields Howned.
      assert (Hneq : owner <> tid) by
        (intro Heq; subst owner; exact (Howner mid node fields Hnode Htype Hfields Howned)).
      destruct (Hsnapshots mid node fields owner Hnode Htype Hfields Howned)
        as [owner_node [base [snapshot [HownerNode [Hbase HrestSnapshot]]]]].
      exists owner_node, base, snapshot; split.
      * unfold tasks; cbn [task_change_priority_tasks glob_task_set_usedtask inUsedTaskStates].
        rewrite (proj2 (Z.eqb_neq owner tid) Hneq); exact HownerNode.
      * split; [|exact HrestSnapshot].
        eapply task_base_priority_alias_ext; [apply Hother; exact Hneq|exact Hbase].
    + split.
      * intros mid node fields Hnode Htype Hfields.
        destruct (Hprotocol mid node fields Hnode Htype Hfields) as [Hpcp [Howned Hslot]].
        split; [exact Hpcp|]. split; [exact Howned|].
        destruct Hslot as [Hdisabled|[Henabled Hslot]]; [left; exact Hdisabled|].
        right; split; [exact Henabled|].
        destruct (Hclaims mid node fields Hnode Htype Hfields Henabled) as [Holdneq Hnewneq].
        unfold tasks; cbn [replace_TskS TskState task_change_priority_tasks prioTbl].
        rewrite (proj2 (Z.eqb_neq fields.(mfPCP) destination) Hnewneq),
          (proj2 (Z.eqb_neq fields.(mfPCP) selected) Holdneq); exact Hslot.
      * apply (pending_mutex_consistency_table_transport sg state.(TskState) tasks state.(EventState));
          [|intros; reflexivity|exact Hpending].
        intros priority Hclaim; unfold tasks; cbn [task_change_priority_tasks prioTbl].
        destruct (Z.eqb priority destination) eqn:Hnew.
        -- apply Z.eqb_eq in Hnew; subst priority; exfalso.
           exact (pending_mutex_consistency_free_slot_excludes_claim sg state.(TskState)
             state.(EventState) destination Hpending Hfree Hclaim).
        -- destruct (Z.eqb priority selected) eqn:Holdprio; [|reflexivity].
           apply Z.eqb_eq in Holdprio; subst priority; exfalso.
           exact (pending_mutex_consistency_task_slot_excludes_claim sg state.(TskState)
             state.(EventState) selected tid Hpending Htable Hclaim).
Qed.
Lemma task_change_prio_used_map_other__task_state :
  forall tasks tid old selected destination slot, slot <> tid ->
  (task_change_priority_tasks tasks tid old selected destination).(inUsedTaskStates) slot =
    tasks.(inUsedTaskStates) slot.
Proof.
  intros; cbn [task_change_priority_tasks glob_task_set_usedtask inUsedTaskStates].
  rewrite (proj2 (Z.eqb_neq slot tid) H); reflexivity.
Qed.
Lemma task_change_prio_bitmap_membership__task_state :
  forall tasks ids tid old,
  tasks.(inUsedTaskStates) tid = Some old -> 0 <= old.(curPrio) ->
  NoDup ids -> task_priority_unique tasks ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node ->
    0 <= node.(curPrio)) ->
  (Z.land (encode_ready_tbl_at_or ids tasks (old.(curPrio) / 8))
    (tcb_bit_x_of_prio old.(curPrio)) <> 0 <-> In tid ids).
Proof.
  intros tasks ids tid old Hold Hprio Hnd Hunique Hranges; split.
  - intros Hbit. destruct (in_dec Z.eq_dec tid ids) as [Hin|Habsent]; [exact Hin|].
    exfalso; apply Hbit; unfold tcb_bit_x_of_prio, tcb_x_of_prio; rewrite Z.land_comm.
    apply sched_bit_disjoint_tbl_or; [exact Hprio|reflexivity|exact Hranges|].
    intros slot node Hin Hnode Hsame.
    assert (slot = tid) by (eapply Hunique; eauto); subst slot; contradiction.
  - intro Hin; unfold tcb_bit_x_of_prio, tcb_x_of_prio.
    rewrite (encode_ready_tbl_or_permutation ids (tid :: helpers.remove_Z_eqb tid ids)
      tasks (old.(curPrio) / 8) (helpers.remove_Z_eqb_perm_cons tid ids Hin Hnd)).
    apply sched_tbl_head_bit; assumption.
Qed.
Lemma task_change_prio_reordered_membership__task_state :
  forall key tid ids, In tid ids -> forall slot,
  In slot (helpers.insert_sorted_by key tid (helpers.remove_Z_eqb tid ids)) <-> In slot ids.
Proof.
  intros key tid ids Hin slot; rewrite helpers.insert_sorted_by_in; cbn; split.
  - intros [Heq|Hmember]; [subst slot; exact Hin|eapply helpers.remove_Z_eqb_in; exact Hmember].
  - intro Hmember; destruct (Z.eq_dec slot tid) as [->|Hneq]; [left; reflexivity|].
    right; apply helpers.remove_Z_eqb_in_neq; assumption.
Qed.
Lemma task_change_prio_reordered_canonical__task_state :
  forall sg tasks ids tid old selected destination (priority_valid : Priority -> Prop),
  (NoDup ids /\ helpers.strictly_sorted_by (wait_prio_key sg tasks) ids /\
    forall slot, In slot ids -> exists node, tasks.(inUsedTaskStates) slot = Some node /\
      priority_valid node.(curPrio)) ->
  task_priority_unique (task_change_priority_tasks tasks tid old selected destination) ->
  priority_valid destination ->
  let updated := task_change_priority_tasks tasks tid old selected destination in
  let reordered := helpers.insert_sorted_by (wait_prio_key sg updated) tid (helpers.remove_Z_eqb tid ids) in
  NoDup reordered /\ helpers.strictly_sorted_by (wait_prio_key sg updated) reordered /\
    forall slot, In slot reordered -> exists node, updated.(inUsedTaskStates) slot = Some node /\
      priority_valid node.(curPrio).
Proof.
  intros sg tasks ids tid old selected destination priority_valid
    [Hnd [Hsorted Hmembers]] Hunique Hrange updated; cbn zeta.
  assert (Hget : updated.(inUsedTaskStates) tid = Some (mutex_priority_task old destination)).
  { unfold updated; apply task_change_priority_tasks_lookup. }
  assert (Hother : forall slot, In slot (helpers.remove_Z_eqb tid ids) ->
    updated.(inUsedTaskStates) slot = tasks.(inUsedTaskStates) slot).
  { intros slot Hin; apply task_change_prio_used_map_other__task_state.
    intro Heq; subst slot; exact (helpers.remove_Z_eqb_notin tid ids Hin). }
  split.
  - apply helpers.insert_sorted_by_preserves_NoDup;
      [apply helpers.remove_Z_eqb_NoDup; exact Hnd|apply helpers.remove_Z_eqb_notin].
  - split.
    + apply helpers.insert_sorted_by_preserves.
      * eapply helpers.strictly_sorted_by_key_eq_on;
          [|apply helpers.remove_Z_eqb_strictly_sorted_by; exact Hsorted].
        intros slot Hin; unfold wait_prio_key; rewrite Hother by exact Hin; reflexivity.
      * intros slot Hin Heq.
        destruct (Hmembers slot (helpers.remove_Z_eqb_in tid slot ids Hin)) as [node [Hnode Hprio]].
        assert (Hupdated : updated.(inUsedTaskStates) slot = Some node)
          by (rewrite Hother by exact Hin; exact Hnode).
        unfold wait_prio_key in Heq; rewrite Hupdated, Hget in Heq.
        assert (slot = tid) by (eapply Hunique; [exact Hupdated|exact Hget|exact Heq]).
        subst slot; exact (helpers.remove_Z_eqb_notin tid ids Hin).
    + intros slot Hin; apply helpers.insert_sorted_by_in in Hin; cbn in Hin.
      destruct Hin as [Heq|Hin].
      * subst slot; exists (mutex_priority_task old destination); split; assumption.
      * destruct (Hmembers slot (helpers.remove_Z_eqb_in tid slot ids Hin)) as [node [Hnode Hprio]].
        exists node; split; [rewrite Hother by exact Hin; exact Hnode|exact Hprio].
Qed.
Lemma task_change_prio_unlisted_canonical__task_state :
  forall sg tasks ids tid old selected destination (priority_valid : Priority -> Prop),
  ~ In tid ids ->
  (NoDup ids /\ helpers.strictly_sorted_by (wait_prio_key sg tasks) ids /\
    forall slot, In slot ids -> exists node, tasks.(inUsedTaskStates) slot = Some node /\
      priority_valid node.(curPrio)) ->
  let updated := task_change_priority_tasks tasks tid old selected destination in
  NoDup ids /\ helpers.strictly_sorted_by (wait_prio_key sg updated) ids /\
    forall slot, In slot ids -> exists node, updated.(inUsedTaskStates) slot = Some node /\
      priority_valid node.(curPrio).
Proof.
  intros sg tasks ids tid old selected destination priority_valid Habsent [Hnd [Hsort Hmembers]];
    cbn zeta.
  assert (Hlookup : forall slot, In slot ids ->
    (task_change_priority_tasks tasks tid old selected destination).(inUsedTaskStates) slot =
      tasks.(inUsedTaskStates) slot).
  { intros; apply task_change_prio_used_map_other__task_state; congruence. }
  split; [exact Hnd|]. split.
  - eapply helpers.strictly_sorted_by_key_eq_on; [|exact Hsort].
    intros; unfold wait_prio_key; rewrite Hlookup by assumption; reflexivity.
  - intros; rewrite Hlookup by assumption; apply Hmembers; assumption.
Qed.
Lemma task_change_prio_ready_from_canonical__task_state :
  forall sg tasks scheduler tid old selected destination after,
  tasks.(inUsedTaskStates) tid = Some old -> sched_ready_in_range sg tasks scheduler ->
  (NoDup after.(readyList) /\
    helpers.strictly_sorted_by (wait_prio_key sg (task_change_priority_tasks tasks tid old selected destination))
      after.(readyList) /\
    forall slot, In slot after.(readyList) -> exists node,
      (task_change_priority_tasks tasks tid old selected destination).(inUsedTaskStates) slot = Some node /\
      task_priority_in_range sg node.(curPrio)) ->
  (forall slot, In slot after.(readyList) <-> In slot scheduler.(readyList)) ->
  sched_ready_in_range sg (task_change_priority_tasks tasks tid old selected destination) after.
Proof.
  intros sg tasks scheduler tid old selected destination after Hold
    [Hmembers [Hsorted [Hcomplete Hnd]]] [HndNew [HsortedNew HmembersNew]] Hmembership.
  split.
  - intros slot Hin.
    destruct (HmembersNew slot Hin) as [node [Hnode Hrange]].
    exists node; split; [exact Hnode|]. split; [exact Hrange|].
    destruct (Hmembers slot (proj1 (Hmembership slot) Hin)) as [before [Hbefore [_ Hready]]].
    destruct (task_change_prio_used_map_origin__task_state
      tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hneq HbeforeNode]].
    + rewrite Hold in Hbefore; injection Hbefore as Hbefore; subst before; exact Hready.
    + assert (node = before) by congruence; subst node; exact Hready.
  - split; [exact HsortedNew|]. split; [|exact HndNew].
    intros slot node Hnode Hready; apply Hmembership.
    destruct (task_change_prio_used_map_origin__task_state
      tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
    + eapply Hcomplete; [exact Hold|exact Hready].
    + eapply Hcomplete; eassumption.
Qed.
Lemma task_change_prio_ready_preserves_in_range__task_state :
  forall sg tasks scheduler tid old selected destination,
  tasks.(inUsedTaskStates) tid = Some old -> task_priority_in_range sg old.(curPrio) ->
  task_priority_in_range sg destination -> task_priority_unique tasks ->
  task_priority_unique (task_change_priority_tasks tasks tid old selected destination) ->
  sched_in_range sg tasks scheduler ->
  let updated := task_change_priority_tasks tasks tid old selected destination in
  sched_in_range sg updated (task_change_priority_ready sg tasks scheduler tid old updated).
Proof.
  intros sg tasks scheduler tid old selected destination Hold Holdrange Hrange Hunique HuniqueNew
    [Hready Hmetadata] updated.
  pose proof Hready as [Hmembers [Hsort [Hcomplete Hnd]]].
  assert (Hcanonical : NoDup scheduler.(readyList) /\
    helpers.strictly_sorted_by (wait_prio_key sg tasks) scheduler.(readyList) /\
    forall slot, In slot scheduler.(readyList) -> exists node,
      tasks.(inUsedTaskStates) slot = Some node /\ task_priority_in_range sg node.(curPrio)).
  { split; [exact Hnd|]. split; [exact Hsort|].
    intros slot Hin; destruct (Hmembers slot Hin) as [node [Hnode [Hp _]]]; eauto. }
  assert (Hranges : forall slot node, In slot scheduler.(readyList) ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)).
  { intros slot node Hin Hnode; destruct (Hmembers slot Hin) as [found [Hfound [Hp _]]].
    assert (found = node) by congruence; subst found; exact (proj1 Hp). }
  pose proof (task_change_prio_bitmap_membership__task_state
    tasks scheduler.(readyList) tid old Hold (proj1 Holdrange) Hnd Hunique Hranges) as Hbit.
  unfold task_change_priority_ready.
  destruct (Z.eqb (Z.land (encode_ready_tbl_at_or scheduler.(readyList) tasks
    (old.(curPrio) / 8)) (tcb_bit_x_of_prio old.(curPrio))) 0) eqn:Htest.
  - apply Z.eqb_eq in Htest.
    assert (Habsent : ~ In tid scheduler.(readyList)) by (intro Hin; apply Hbit in Hin; contradiction).
    split; [|exact Hmetadata].
    eapply task_change_prio_ready_from_canonical__task_state;
      [exact Hold|exact Hready| |intros; reflexivity].
    apply task_change_prio_unlisted_canonical__task_state; assumption.
  - apply Z.eqb_neq in Htest.
    assert (Hin : In tid scheduler.(readyList)) by (apply Hbit; exact Htest).
    split; [|exact Hmetadata].
    eapply task_change_prio_ready_from_canonical__task_state;
      [exact Hold|exact Hready| |].
    + cbn [sched_set_ready readyList].
      apply task_change_prio_reordered_canonical__task_state; assumption.
    + cbn [sched_set_ready readyList].
      apply task_change_prio_reordered_membership__task_state; exact Hin.
Qed.
Lemma task_change_prio_waiter_resource_unavailable__task_state :
  forall sg node tid, event_payload_consistency sg node -> In tid node.(waitList) ->
  event_wait_resource_unavailable node.
Proof.
  intros sg node tid Hpayload Hin.
  assert (Hnonempty : node.(waitList) <> []) by (intro E; rewrite E in Hin; contradiction).
  unfold event_payload_consistency in Hpayload; unfold event_wait_resource_unavailable.
  destruct node.(eventType); try contradiction.
  - destruct node.(semFields); [exact (proj2 Hpayload Hnonempty)|contradiction].
  - destruct node.(mutexFields); [|contradiction]. intros Hnone.
    apply Hnonempty; exact (proj2 Hpayload Hnone).
  - destruct node.(mboxFields); [exact (proj2 Hpayload Hnonempty)|contradiction].
  - destruct node.(queueFields); [|contradiction].
    unfold queue_fields_consistency in Hpayload; tauto.
Qed.
Lemma task_change_prio_event_reorder_consistency__task_state :
  forall sg tasks tid old selected destination eid event,
  tasks.(inUsedTaskStates) tid = Some old ->
  In tid event.(waitList) -> event_wait_entry_consistency sg tasks eid event ->
  task_priority_unique (task_change_priority_tasks tasks tid old selected destination) ->
  valid_task_prio sg destination ->
  let updated := task_change_priority_tasks tasks tid old selected destination in
  event_wait_entry_consistency sg updated eid (event_insert_waiter sg updated event tid).
Proof.
  intros sg tasks tid old selected destination eid event Hold Hin
    [Hcanonical Hphase] Hunique Hrange updated.
  split.
  - apply task_change_prio_reordered_canonical__task_state; assumption.
  - cbn [event_insert_waiter event_set_wait_list eventType].
    destruct (event_type_to_pend_type event.(eventType)) as [kind|] eqn:Hkind.
    + intros slot Hmember.
      apply task_change_prio_reordered_membership__task_state
        in Hmember; [|exact Hin].
      destruct (Hphase slot Hmember) as [node [Hnode [Hptr [Hmulti Hlinked]]]].
      destruct (Z.eq_dec slot tid) as [->|Hneq].
      * rewrite Hold in Hnode; injection Hnode as Hnode; subst node.
        exists (mutex_priority_task old destination); split.
        -- unfold updated; apply task_change_priority_tasks_lookup.
        -- split; [exact Hptr|]. split; [exact Hmulti|exact Hlinked].
      * exists node; split.
        -- unfold updated; rewrite task_change_prio_used_map_other__task_state
             by exact Hneq; exact Hnode.
        -- auto.
    + rewrite Hphase in Hin; contradiction.
Qed.
Lemma task_change_prio_event_unlisted_consistency__task_state :
  forall sg tasks tid old selected destination eid event,
  ~ In tid event.(waitList) -> event_wait_entry_consistency sg tasks eid event ->
  event_wait_entry_consistency sg (task_change_priority_tasks tasks tid old selected destination) eid event.
Proof.
  intros sg tasks tid old selected destination eid event Habsent Hentry.
  eapply event_wait_entry_task_lookup_ext; [|exact Hentry].
  intros slot Hin; apply task_change_prio_used_map_other__task_state; congruence.
Qed.
Lemma task_change_prio_events_lookup_origin__task_state :
  forall sg events tasks tid old,
  (forall eid node, old.(eventPtr) = Some eid -> events.(inUsedEventStates) eid = Some node ->
    In tid node.(waitList)) ->
  forall eid node,
  (task_change_priority_events sg events tasks tid old).(inUsedEventStates) eid = Some node ->
  exists before, events.(inUsedEventStates) eid = Some before /\
    node = event_set_wait_list before node.(waitList) /\
    (forall slot, In slot node.(waitList) <-> In slot before.(waitList)).
Proof.
  intros sg events tasks tid old Hmember eid node Hnode.
  unfold task_change_priority_events in Hnode.
  destruct old.(eventPtr) as [target|] eqn:Hptr;
    [destruct (events.(inUsedEventStates) target) as [event|] eqn:Hevent|].
  - cbn [update_event_field_raw inUsedEventStates] in Hnode.
    destruct (Z.eqb eid target) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst eid; injection Hnode as Hnode; subst node.
      exists event; split; [exact Hevent|]. split; [reflexivity|].
      apply task_change_prio_reordered_membership__task_state.
      eapply Hmember; [first [exact Hptr | reflexivity]|exact Hevent].
    + exists node; split; [exact Hnode|]. split;
        [symmetry; apply event_set_wait_list_put_back|intros; reflexivity].
  - exists node; split; [exact Hnode|]. split;
      [symmetry; apply event_set_wait_list_put_back|intros; reflexivity].
  - exists node; split; [exact Hnode|]. split;
      [symmetry; apply event_set_wait_list_put_back|intros; reflexivity].
Qed.
Lemma task_change_prio_events_lookup_forward__task_state :
  forall sg events tasks tid old eid before,
  events.(inUsedEventStates) eid = Some before ->
  exists node, (task_change_priority_events sg events tasks tid old).(inUsedEventStates) eid = Some node /\
    node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields).
Proof.
  intros sg events tasks tid old eid before Hbefore; unfold task_change_priority_events.
  destruct old.(eventPtr) as [target|];
    [destruct (events.(inUsedEventStates) target) as [event|] eqn:Hevent|].
  - cbn [update_event_field_raw inUsedEventStates].
    destruct (Z.eqb eid target) eqn:Heq.
    + apply Z.eqb_eq in Heq; subst eid.
      assert (event = before) by congruence; subst event.
      eexists; repeat split; reflexivity.
    + exists before; auto.
  - exists before; auto.
  - exists before; auto.
Qed.
Lemma task_change_prio_events_preserves_in_range__task_state :
  forall sg state tid old selected destination,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_priority_unique (task_change_priority_tasks state.(TskState) tid old selected destination) ->
  valid_task_prio sg destination ->
  let tasks := task_change_priority_tasks state.(TskState) tid old selected destination in
  let events := task_change_priority_events sg state.(EventState) tasks tid old in
  event_in_range sg tasks events /\
  task_event_reference_backlink_consistency tasks events /\
  task_event_reference_closure tasks events.
Proof.
  intros sg state tid old selected destination Hvalid Hold Hunique Hrange tasks events.
  pose proof Hvalid as [_ [_ [_ [Hevents [Hcross _]]]]].
  destruct Hcross as [_ [_ [Hwaiting _]]].
  destruct Hwaiting as [Hentries [Hbacklinks Hclosure]].
  assert (Hmember : forall eid node, old.(eventPtr) = Some eid ->
    state.(EventState).(inUsedEventStates) eid = Some node -> In tid node.(waitList)).
  { intros; eapply Hbacklinks; [exact Hold|eassumption|left; assumption]. }
  assert (Habsent : forall eid node,
    state.(EventState).(inUsedEventStates) eid = Some node ->
    old.(eventPtr) <> Some eid -> ~ In tid node.(waitList)).
  { intros eid node Hnode Hptr Hin.
    destruct (event_waiter_task_fields sg state.(TskState) eid node tid
      (Hentries eid node Hnode) Hin) as [found [kind [Hfound [_ [Hreference _]]]]].
    assert (found = old) by congruence; subst found; contradiction. }
  assert (HentriesNew : forall eid node, events.(inUsedEventStates) eid = Some node ->
    event_wait_entry_consistency sg tasks eid node).
  { intros eid node Hnode; unfold events, task_change_priority_events in Hnode.
    destruct old.(eventPtr) as [target|] eqn:Hptr.
    - destruct (state.(EventState).(inUsedEventStates) target) as [event|] eqn:Hevent.
      + cbn [update_event_field_raw inUsedEventStates] in Hnode.
        destruct (Z.eqb eid target) eqn:Heq.
        * apply Z.eqb_eq in Heq; subst eid; injection Hnode as Hnode; subst node.
          apply task_change_prio_event_reorder_consistency__task_state;
            [exact Hold|eapply Hmember; eauto|apply Hentries; exact Hevent|exact Hunique|exact Hrange].
        * apply Z.eqb_neq in Heq.
          apply task_change_prio_event_unlisted_consistency__task_state;
            [eapply Habsent; [exact Hnode|congruence]|apply Hentries; exact Hnode].
      + destruct (proj1 (Hclosure tid old Hold) target Hptr) as [event Hevent']; congruence.
    - apply task_change_prio_event_unlisted_consistency__task_state;
        [eapply Habsent; [exact Hnode|congruence]|apply Hentries; exact Hnode]. }
  assert (Hbase : event_in_range_with_wait sg state.(EventState) (fun _ _ => True)).
  { destruct Hevents as [Hpool [Hfree [Hidentity [Hfields [Hpayload [Hqueue _]]]]]].
    split; [exact Hpool|]. split; [exact Hfree|]. split; [exact Hidentity|].
    split; [exact Hfields|]. split; [exact Hpayload|]. split; [exact Hqueue|].
    intros; exact I. }
  assert (HbaseNew : event_in_range_with_wait sg events (fun _ _ => True)).
  { unfold events, task_change_priority_events.
    destruct old.(eventPtr) as [target|] eqn:Hptr; [|exact Hbase].
    destruct (state.(EventState).(inUsedEventStates) target) as [event|] eqn:Hevent;
      [|exact Hbase].
    pose proof Hevents as [_ [_ [_ [Hfields [Hpayload _]]]]].
    assert (Hunavailable : event_wait_resource_unavailable event).
    { eapply task_change_prio_waiter_resource_unavailable__task_state;
        [eapply Hpayload; exact Hevent|eapply Hmember; eauto]. }
    eapply event_update_preserves_in_range_with_wait;
      [exact Hbase|exact Hevent|reflexivity| | |reflexivity|exact I].
    - apply event_insert_waiter_preserves_fields; [eapply Hfields; exact Hevent|exact Hunavailable].
    - apply event_insert_waiter_preserves_payload; [eapply Hpayload; exact Hevent|exact Hunavailable]. }
  assert (HtaskOrigin : forall slot node, tasks.(inUsedTaskStates) slot = Some node ->
    exists before, state.(TskState).(inUsedTaskStates) slot = Some before /\
      node.(eventPtr) = before.(eventPtr) /\
      node.(eventMultiWaitEvents) = before.(eventMultiWaitEvents)).
  { intros slot node Hnode.
    destruct (task_change_prio_used_map_origin__task_state
      state.(TskState) tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
    - exists old; split; [exact Hold|]; split; reflexivity.
    - exists node; split; [exact Hbefore|]; split; reflexivity. }
  split.
  - destruct HbaseNew as [Hpool [Hfree [Hidentity [Hfields [Hpayload [Hqueue _]]]]]].
    split; [exact Hpool|]. split; [exact Hfree|]. split; [exact Hidentity|].
    split; [exact Hfields|]. split; [exact Hpayload|]. split; [exact Hqueue|exact HentriesNew].
  - split.
    + intros slot node eid event Hnode Hevent Hreference.
      destruct (HtaskOrigin slot node Hnode) as [before [Hbefore [Hptr Hmulti]]].
      destruct (task_change_prio_events_lookup_origin__task_state
        sg state.(EventState) tasks tid old Hmember eid event Hevent)
        as [old_event [HoldEvent [_ Hmembership]]].
      apply Hmembership; eapply Hbacklinks; [exact Hbefore|exact HoldEvent|].
      rewrite Hptr, Hmulti in Hreference; exact Hreference.
    + intros slot node Hnode.
      destruct (HtaskOrigin slot node Hnode) as [before [Hbefore [Hptr Hmulti]]].
      destruct (Hclosure slot before Hbefore) as [Hsingle Hmany]; split.
      * intros eid Hreference; rewrite Hptr in Hreference.
        destruct (Hsingle eid Hreference) as [event Hevent].
        destruct (task_change_prio_events_lookup_forward__task_state
          sg state.(EventState) tasks tid old eid event Hevent) as [after [Hafter _]].
        exists after; exact Hafter.
      * intros eid Hreference; rewrite Hmulti in Hreference.
        destruct (Hmany eid Hreference) as [event Hevent].
        destruct (task_change_prio_events_lookup_forward__task_state
          sg state.(EventState) tasks tid old eid event Hevent) as [after [Hafter _]].
        exists after; exact Hafter.
Qed.
Lemma cross_module_consistency_event_wait_membership_transport__task_state : forall sg s events
    (waiting_before waiting_after : Prop),
  (forall slot node, events.(inUsedEventStates) slot = Some node ->
    node.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists before, s.(EventState).(inUsedEventStates) slot = Some before /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
      (forall slot, In slot node.(waitList) <-> In slot before.(waitList))) ->
  (forall slot before, s.(EventState).(inUsedEventStates) slot = Some before ->
    before.(eventType) = OS_EVENT_TYPE_MUTEX ->
    exists node, events.(inUsedEventStates) slot = Some node /\
      node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields)) ->
  waiting_after ->
  event_mutex_lease_view events = event_mutex_lease_view s.(EventState) ->
  cross_module_consistency_with_wait sg s waiting_before ->
  cross_module_consistency_with_wait sg (replace_EventS events s) waiting_after.
Proof.
  intros sg s events waiting_before waiting_after Horigin Hforward Hwaiting Hleases
    [Htable [Hsnapshot [_ [Hprotocol [Hunique [Hflag Htimer]]]]]].
  assert (Hclaims : forall p,
    (exists mid node m, events.(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) <->
    (exists mid node m, s.(EventState).(inUsedEventStates) mid = Some node /\
      node.(eventType) = OS_EVENT_TYPE_MUTEX /\ node.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p)).
  { intro p; split; intros [mid [node [m [Hnode [Hty [Hm Hclaim]]]]]].
    - destruct (Horigin mid node Hnode Hty) as [before [Hb [Ht [Hf _]]]].
      exists mid, before, m; split; [exact Hb|]; split; [congruence|]; split; [congruence|exact Hclaim].
    - destruct (Hforward mid node Hnode Hty) as [after [Ha [Ht Hf]]].
      exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim]. }
  change (cross_module_consistency_with_wait sg (replace_EventS events s) waiting_after).
  unfold cross_module_consistency_with_wait; split.
  - destruct Htable as [Hcreator [Hslots Halias]]; split.
    + intros p entry Hentry Hclaim; apply (Hcreator p entry Hentry); apply Hclaims; exact Hclaim.
    + split.
      * intros p Hp; specialize (Hslots p Hp); cbn [replace_EventS TskState EventState].
        destruct (s.(TskState).(prioTbl) p).
        -- intro Hclaim; apply Hslots; apply Hclaims; exact Hclaim.
        -- destruct Hslots as [Hreservation|[Hclaim|Hpending]].
           ++ left; exact Hreservation.
           ++ right; left; apply Hclaims; exact Hclaim.
           ++ right; right; unfold pending_mutex_priority_claim in *; rewrite Hleases; exact Hpending.
        -- exact Hslots.
      * eapply mutex_priority_alias_consistency_ext; [reflexivity|reflexivity| |exact Halias].
        intros owner p [mid [node [m [Hnode [Hty [Hm Hclaim]]]]]].
        destruct (Hforward mid node Hnode Hty) as [after [Ha [Ht Hf]]].
        exists mid, after, m; split; [exact Ha|]; split; [congruence|]; split; [congruence|exact Hclaim].
  - split.
    + intros mid node m owner Hnode Hty Hm Howner.
      destruct (Horigin mid node Hnode Hty) as [before [Hb [Ht [Hf Hw]]]].
      destruct (Hsnapshot mid before m owner Hb ltac:(congruence) ltac:(congruence) Howner)
        as [t [base [saved [Htask [Hbase [Hsaved [Hrange [Hbound [Habsent Hpcp]]]]]]]]].
      exists t, base, saved; split; [exact Htask|]; split; [exact Hbase|]; split; [exact Hsaved|];
        split; [exact Hrange|]; split; [exact Hbound|].
      split; [|exact Hpcp]. intro Hin; apply Habsent; apply Hw; exact Hin.
    + split.
      * exact Hwaiting.
      * split.
        -- intros mid node m Hnode Hty Hm.
           destruct (Horigin mid node Hnode Hty) as [before [Hb [Ht [Hf _]]]].
           exact (Hprotocol mid before m Hb ltac:(congruence) ltac:(congruence)).
        -- split.
           ++ intros mid1 node1 m1 mid2 node2 m2 Hn1 Ht1 Hm1 Hn2 Ht2 Hm2 Hp Hnonzero.
              destruct (Horigin mid1 node1 Hn1 Ht1) as [before1 [Hb1 [Ht1' [Hm1' _]]]].
              destruct (Horigin mid2 node2 Hn2 Ht2) as [before2 [Hb2 [Ht2' [Hm2' _]]]].
              eapply Hunique; [exact Hb1| | |exact Hb2| | |exact Hp|exact Hnonzero]; congruence.
           ++ split; [exact Hflag|exact Htimer].
Qed.
Lemma task_change_prio_preserves_idle_tail__task_state :
  forall sg tasks tid old selected destination,
  tasks.(inUsedTaskStates) tid = Some old -> old.(curPrio) <> sg.(osLowestPrio) ->
  destination <> sg.(osLowestPrio) -> task_idle_tail sg tasks ->
  task_idle_tail sg (task_change_priority_tasks tasks tid old selected destination).
Proof.
  intros sg tasks tid old selected destination Hold Hnotidle Hdestination
    [prefix [idle [node [Horder [Hnode [Hpriority Hothers]]]]]].
  assert (Hdifferent : idle <> tid) by (intro Heq; subst idle; congruence).
  exists prefix, idle, node; split; [exact Horder|]. split.
  - rewrite task_change_prio_used_map_other__task_state by exact Hdifferent;
      exact Hnode.
  - split; [exact Hpriority|]. intros slot other Hin Hother.
    destruct (task_change_prio_used_map_origin__task_state
      tasks tid old selected destination slot other Hother) as [[-> ->]|[Hneq Hbefore]].
    + exact Hdestination.
    + eapply Hothers; eassumption.
Qed.
Lemma task_change_prio_preserves_state_inv__task_state :
  forall sg state requested tid old selected destination,
  task_change_prio_live sg state requested selected destination tid old ->
  UCOS2_state_inv sg (task_change_priority_state sg state tid old selected destination).
Proof.
  intros sg state requested tid old selected destination
    [Hvalid [Hselection [Hfree [Htable [Hold [Howner [Hselected [Holdrange [Hnewrange Hdistinct]]]]]]]]].
  pose proof Hvalid as [Hprofile [Htasks [Hsched [Hevents [Hcross
    [Hidle [Hbits [Hflagconfig [Hmemory [Htimerconfig [Hstats [Hcontrol [Hnames [Hroots [Hstacks Hpending]]]]]]]]]]]]]]].
  pose proof (task_change_prio_profile_constants__task_state
    sg state Hvalid) as [Hlowest _].
  set (tasks := task_change_priority_tasks state.(TskState) tid old selected destination).
  set (events := task_change_priority_events sg state.(EventState) tasks tid old).
  set (scheduler := task_change_priority_current_cache
    (task_change_priority_ready sg state.(TskState) state.(SchedState) tid old tasks) tid destination).
  assert (Hdestination : task_priority_in_range sg destination) by
    (unfold task_priority_in_range; lia).
  assert (Holdpriority : task_priority_in_range sg old.(curPrio)) by
    (unfold task_priority_in_range; lia).
  assert (Hstrict : valid_task_prio sg destination) by (unfold valid_task_prio; lia).
  assert (HtasksNew : task_in_range sg tasks).
  { apply task_change_prio_tasks_preserves_in_range__task_state; assumption. }
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]].
  pose proof HtasksNew as [_ [_ [_ [_ [_ [_ [HuniqueNew _]]]]]]].
  pose proof (task_change_prio_ready_preserves_in_range__task_state
    sg state.(TskState) state.(SchedState) tid old selected destination Hold Holdpriority
    Hdestination Hunique HuniqueNew Hsched) as HreadySched.
  assert (HschedNew : sched_in_range sg tasks scheduler).
  { apply task_change_priority_current_cache_preserves_in_range;
      [exact Hdestination|exact HreadySched]. }
  pose proof (task_change_prio_task_mutex_invariants__task_state
    sg state tid old selected destination Hvalid Hold Hselected Htable Hfree Hdestination Howner)
    as [HtableNew [HsnapshotNew [HprotocolNew HpendingTask]]].
  pose proof (task_change_prio_events_preserves_in_range__task_state
    sg state tid old selected destination Hvalid Hold HuniqueNew Hstrict)
    as [HeventsNew [HbacklinksNew HclosureNew]].
  destruct Hcross as [_ [_ [Hwaiting [_ [HpcpUnique [Hflag Htimer]]]]]].
  destruct Hwaiting as [Hentries [Hbacklinks Hclosure]].
  assert (Hmember : forall eid node, old.(eventPtr) = Some eid ->
    state.(EventState).(inUsedEventStates) eid = Some node -> In tid node.(waitList)).
  { intros; eapply Hbacklinks; [exact Hold|eassumption|left; assumption]. }
  assert (Horigin : forall eid node, events.(inUsedEventStates) eid = Some node ->
    node.(eventType) = OS_EVENT_TYPE_MUTEX -> exists before,
    state.(EventState).(inUsedEventStates) eid = Some before /\
    node.(eventType) = before.(eventType) /\ node.(mutexFields) = before.(mutexFields) /\
    (forall slot, In slot node.(waitList) <-> In slot before.(waitList))).
  { intros eid node Hnode Htype.
    destruct (task_change_prio_events_lookup_origin__task_state
      sg state.(EventState) tasks tid old Hmember eid node Hnode) as [before [Hbefore [Heq Hin]]].
    exists before; split; [exact Hbefore|]. split; [rewrite Heq; reflexivity|].
    split; [rewrite Heq; reflexivity|exact Hin]. }
  assert (Hforward : forall eid before, state.(EventState).(inUsedEventStates) eid = Some before ->
    before.(eventType) = OS_EVENT_TYPE_MUTEX -> exists node,
    events.(inUsedEventStates) eid = Some node /\ node.(eventType) = before.(eventType) /\
    node.(mutexFields) = before.(mutexFields)).
  { intros; eapply task_change_prio_events_lookup_forward__task_state;
      eassumption. }
  assert (Hleases : event_mutex_lease_view events = event_mutex_lease_view state.(EventState)).
  { unfold events, task_change_priority_events.
    destruct old.(eventPtr) as [eid|]; [destruct (state.(EventState).(inUsedEventStates) eid)|];
      reflexivity. }
  assert (HcrossTask : cross_module_consistency_with_wait sg (replace_TskS tasks state) True).
  { split; [exact HtableNew|]. split; [exact HsnapshotNew|]. split; [exact I|].
    split; [exact HprotocolNew|]. split; [exact HpcpUnique|]. split; [|exact Htimer].
    change (task_flag_waiter_consistency sg
      (glob_task_set_usedtask state.(TskState) tid (mutex_priority_task old destination)) state.(FlagState)).
    eapply task_flag_waiter_consistency_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|reflexivity|intros; assumption|intros; assumption|exact Hflag]. }
  assert (HwaitingNew : event_wait_object_consistency sg (replace_EventS events (replace_TskS tasks state))).
  { split.
    - exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HeventsNew)))))).
    - split; [exact HbacklinksNew|exact HclosureNew]. }
  pose proof (cross_module_consistency_event_wait_membership_transport__task_state
    sg (replace_TskS tasks state) events True
    (event_wait_object_consistency sg (replace_EventS events (replace_TskS tasks state)))
    Horigin Hforward HwaitingNew Hleases HcrossTask) as HcrossEvents.
  assert (Hrunning : scheduler.(isRunning) = state.(SchedState).(isRunning)).
  { unfold scheduler, task_change_priority_current_cache, task_change_priority_ready;
      destruct (Z.eqb _ 0); reflexivity. }
  assert (HcrossNew : cross_module_consistency sg
    (replace_SchedS scheduler (replace_EventS events (replace_TskS tasks state)))).
  { apply cross_module_consistency_sched_frame; [exact Hrunning|exact HcrossEvents]. }
  assert (HpendingNew : pending_mutex_consistency sg tasks events).
  { eapply pending_mutex_consistency_event_transport; [exact Hleases| |exact HpendingTask].
    intros eid node Hnode Htype.
    destruct (Horigin eid node Hnode Htype) as [before [Hbefore [HtypeEq [Hfields _]]]].
    exists before; split; [exact Hbefore|]; split; congruence. }
  assert (Hnodes : forall slot node, tasks.(inUsedTaskStates) slot = Some node ->
    exists before, state.(TskState).(inUsedTaskStates) slot = Some before /\
      node.(taskID) = before.(taskID) /\ node.(taskGeneration) = before.(taskGeneration) /\
      node.(tcbStkPtr) = before.(tcbStkPtr)).
  { intros slot node Hnode.
    destruct (task_change_prio_used_map_origin__task_state
      state.(TskState) tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
    - exists old; split; [exact Hold|]; repeat split; reflexivity.
    - exists node; split; [exact Hbefore|]; repeat split; reflexivity. }
  change (UCOS2_state_inv sg (replace_SchedS scheduler (replace_EventS events (replace_TskS tasks state)))).
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  cbn [replace_SchedS replace_EventS replace_TskS TskState SchedState EventState
    FlagState MemoryState TimerState StatsState ControlState NameState].
  split; [exact Hprofile|]. split; [exact HtasksNew|]. split; [exact HschedNew|].
  split; [exact HeventsNew|]. split; [exact HcrossNew|]. split.
  - intro Hr; rewrite Hrunning in Hr.
    apply task_change_prio_preserves_idle_tail__task_state;
      [exact Hold|lia|lia|apply Hidle; exact Hr].
  - split.
    + change (task_reserved_bits_clear sg
        (glob_task_set_usedtask state.(TskState) tid (mutex_priority_task old destination))).
      apply task_reserved_bits_clear_update_task; [exact Hbits|exact (Hbits tid old Hold)].
    + split; [exact Hflagconfig|]. split; [exact Hmemory|]. split; [exact Htimerconfig|].
      split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|]. split.
      * eapply kernel_names.kernel_names_valid_frame; [exact Hroots|reflexivity| | |intros; assumption|intros; assumption|intros; assumption].
        -- apply task_update_name_references with (old := old); [exact Hold|reflexivity].
        -- intros name [eid [node [Hnode Hname]]].
           destruct (task_change_prio_events_lookup_origin__task_state
             sg state.(EventState) tasks tid old Hmember eid node Hnode)
             as [before [Hbefore [Heq _]]].
           exists eid, before; split; [exact Hbefore|rewrite Heq in Hname; exact Hname].
      * split; [|exact HpendingNew].
        eapply parked_stacks_consistent_transport; [|exact Hnodes|exact Hstacks].
        intros; assumption.
Qed.
Lemma task_change_prio_preserves_call_source__task_state :
  forall sg state execution tid old selected destination,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_change_prio_call_source execution state ->
  task_change_prio_call_source execution (task_change_priority_state sg state tid old selected destination).
Proof.
  intros sg state execution tid old selected destination Hold Hsource.
  pose proof (task_change_prio_state_sched_caches sg state tid old selected destination)
    as [Hcurrent [_ [_ [_ [_ Hrunning]]]]].
  destruct execution as [call|view].
  - destruct Hsource as [[Horigin [Hactive Hcur]] [Havailable Hready]].
    split.
    + split; [exact Horigin|]. split.
      * change (task_invocation_active
          (glob_task_set_usedtask state.(TskState) tid (mutex_priority_task old destination))
          call.(os_sched_call_invocation) call.(os_sched_call_origin)).
        eapply glob_task_set_usedtask_preserves_invocation_active;
          [exact Hold|reflexivity|exact Hactive].
      * unfold task_execution_current in *.
        destruct call.(os_sched_call_origin); [exact I|rewrite Hcurrent; exact Hcur].
    + split; [exact Havailable|]. intros Hr.
      rewrite Hrunning in Hr; specialize (Hready Hr).
      cbn [task_change_priority_state replace_SchedS SchedState
        task_change_priority_current_cache readyList].
      unfold task_change_priority_ready; destruct (Z.eqb _ 0); [exact Hready|].
      cbn [sched_set_ready readyList]. intro Hempty.
      assert (Hin : In tid (helpers.insert_sorted_by
        (wait_prio_key sg (task_change_priority_tasks state.(TskState) tid old selected destination))
        tid (helpers.remove_Z_eqb tid state.(SchedState).(readyList))))
        by (apply helpers.insert_sorted_by_in; left; reflexivity).
      rewrite Hempty in Hin; contradiction.
  - destruct Hsource as [Hstopped|[Hisr|Hlocked]].
    + left; rewrite Hrunning; exact Hstopped.
    + right; left; destruct Hisr as [handler [interrupted [Hcontext [Hr Hnest]]]].
      exists handler, interrupted; split; [exact Hcontext|]. split; [rewrite Hrunning; exact Hr|exact Hnest].
    + right; right; exact Hlocked.
Qed.
Lemma task_change_prio_preserves_stack_live_sp__task_state :
  forall tasks tid old selected destination key sp,
  tasks.(inUsedTaskStates) tid = Some old -> task_stack_live_sp tasks key sp ->
  task_stack_live_sp (task_change_priority_tasks tasks tid old selected destination) key sp.
Proof.
  intros tasks tid old selected destination key sp Hold Hlive node Hnode Hgeneration.
  destruct (task_change_prio_used_map_origin__task_state
    tasks tid old selected destination (fst key) node Hnode) as [[Heq ->]|[Hneq Hbefore]].
  - apply (Hlive old); [rewrite Heq; exact Hold|exact Hgeneration].
  - apply (Hlive node); assumption.
Qed.
Lemma task_change_prio_preserves_stack_coverage__task_state :
  forall tasks tid old selected destination active,
  tasks.(inUsedTaskStates) tid = Some old -> task_stack_live_coverage tasks active ->
  task_stack_live_coverage (task_change_priority_tasks tasks tid old selected destination) active.
Proof.
  intros tasks tid old selected destination active Hold Hcoverage slot node Hnode.
  destruct (task_change_prio_used_map_origin__task_state
    tasks tid old selected destination slot node Hnode) as [[-> ->]|[Hneq Hbefore]].
  - exact (Hcoverage tid old Hold).
  - exact (Hcoverage slot node Hbefore).
Qed.
Lemma task_change_prio_saved_continuations_transport__task_state :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    local tasks tid old selected destination,
  tasks.(inUsedTaskStates) tid = Some old ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) tasks.(parkedTaskStacks) |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi (task_change_priority_tasks tasks tid old selected destination) local)
    tasks.(parkedTaskStacks).
Proof.
  intros external platform port abi local tasks tid old selected destination Hold.
  apply TaskFieldStorage.store_map_mono; intros key payload Hpayload.
  unfold kernel_saved_continuation_entry; Intros descriptor.
  assert (Hlive : task_stack_live_sp
    (task_change_priority_tasks tasks tid old selected destination) key descriptor.(armv7a_continuation_sp)).
  { eapply task_change_prio_preserves_stack_live_sp__task_state;
      [exact Hold|tauto]. }
  Exists descriptor; entailer!.
Qed.
Lemma task_change_prio_masked_frame_transport__task_state :
  forall environment saved_local critical sg execution saved acquired state tid old selected destination,
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state |--
  task_change_prio_masked_frame environment saved_local critical sg execution saved acquired
    (task_change_priority_state sg state tid old selected destination).
Proof.
  intros environment saved_local critical sg execution saved acquired state tid old selected destination Hold.
  destruct execution as [call|view]; [|reflexivity].
  unfold task_change_prio_masked_frame; Intros.
  assert (Hcoverage : task_stack_live_coverage
    (task_change_priority_tasks state.(TskState) tid old selected destination) (task_stack_call_active_key call)).
  { eapply task_change_prio_preserves_stack_coverage__task_state;
      [exact Hold|eassumption]. }
  sep_apply (task_change_prio_saved_continuations_transport__task_state
    _ _ _ environment.(task_stack_call_continuations) (task_create_continuation_local saved_local)
    state.(TskState) tid old selected destination Hold).
  entailer!.
Qed.
Lemma task_change_prio_reordered_encoding__task_state :
  forall tasks ids tid old selected destination key,
  tasks.(inUsedTaskStates) tid = Some old -> 0 <= old.(curPrio) < 64 ->
  0 <= destination < 64 -> NoDup ids -> task_priority_unique tasks ->
  (forall slot node, In slot ids -> tasks.(inUsedTaskStates) slot = Some node ->
    0 <= node.(curPrio) < 64) -> In tid ids ->
  let updated := task_change_priority_tasks tasks tid old selected destination in
  let reordered := helpers.insert_sorted_by key tid (helpers.remove_Z_eqb tid ids) in
  sched_row_values updated reordered =
    mutex_priority_rows (sched_row_values tasks ids) (tcb_y_of_prio old.(curPrio))
      (tcb_bit_x_of_prio old.(curPrio)) destination /\
  encode_ready_grp reordered updated =
    mutex_priority_group (sched_row_values tasks ids) (encode_ready_grp ids tasks)
      (tcb_y_of_prio old.(curPrio)) (tcb_bit_x_of_prio old.(curPrio))
      (tcb_bit_y_of_prio old.(curPrio)) destination.
Proof.
  intros tasks ids tid old selected destination key Hold Holdrange Hrange Hnd Hunique Hranges Hin
    updated reordered.
  assert (Holdrow : 0 <= old.(curPrio) / 8 < 8) by
    (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  assert (Hnewrow : 0 <= destination / 8 < 8) by
    (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  assert (Hnonnegative : forall slot node, In slot ids ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)).
  { intros; exact (proj1 (Hranges slot node H H0)). }
  assert (Hrows : forall slot node, In slot ids ->
    tasks.(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio) / 8 < 8).
  { intros; specialize (Hranges slot node H H0).
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hget : updated.(inUsedTaskStates) tid = Some (mutex_priority_task old destination))
    by (unfold updated; apply task_change_priority_tasks_lookup).
  assert (Hother : forall slot, In slot (helpers.remove_Z_eqb tid ids) ->
    option_map curPrio (updated.(inUsedTaskStates) slot) =
    option_map curPrio (tasks.(inUsedTaskStates) slot)).
  { intros slot Hmember; unfold updated.
    rewrite task_change_prio_used_map_other__task_state;
      [reflexivity|intro Heq; subst slot; exact (helpers.remove_Z_eqb_notin tid ids Hmember)]. }
  destruct (sched_encoding_priority_ext (helpers.remove_Z_eqb tid ids) updated tasks Hother)
    as [HgroupExt HtableExt].
  assert (HremoveTable : forall row,
    encode_ready_tbl_at_or (helpers.remove_Z_eqb tid ids) updated row =
    if Z.eqb row (old.(curPrio) / 8)
    then Z.land (encode_ready_tbl_at_or ids tasks row)
      (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) mod 8))) 8)
    else encode_ready_tbl_at_or ids tasks row).
  { intro row; rewrite HtableExt.
    destruct (Z.eqb row (old.(curPrio) / 8)) eqn:Heq.
    - apply Z.eqb_eq in Heq; subst row.
      eapply encode_ready_tbl_or_remove_selected_row_any; eauto; lia.
    - eapply encode_ready_tbl_or_remove_other_row; [exact Hold|apply Z.eqb_neq in Heq; congruence]. }
  assert (HremoveRows : sched_row_values updated (helpers.remove_Z_eqb tid ids) =
    ListLib.Base.Positional.replace_Znth (old.(curPrio) / 8)
      (Z.land (encode_ready_tbl_at_or ids tasks (old.(curPrio) / 8))
        (unsigned_last_nbits (Z.lnot (Z.shiftl 1 (old.(curPrio) mod 8))) 8))
      (sched_row_values tasks ids)).
  { unfold sched_row_values; cbn [map].
    rewrite (HremoveTable 0), (HremoveTable 1), (HremoveTable 2), (HremoveTable 3),
      (HremoveTable 4), (HremoveTable 5), (HremoveTable 6), (HremoveTable 7).
    set (row := old.(curPrio) / 8) in *.
    assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
      row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
    repeat destruct Hcases as [Hcases|Hcases]; rewrite Hcases; reflexivity. }
  assert (HaddTable : forall row, encode_ready_tbl_at_or reordered updated row =
    if Z.eqb (destination / 8) row
    then Z.lor (encode_ready_tbl_at_or (helpers.remove_Z_eqb tid ids) updated row)
      (Z.shiftl 1 (destination mod 8))
    else encode_ready_tbl_at_or (helpers.remove_Z_eqb tid ids) updated row).
  { intro row.
    pose proof (encode_ready_tbl_insert_remove updated key tid (helpers.remove_Z_eqb tid ids)
      (mutex_priority_task old destination) row Hget) as Hinsert.
    rewrite helpers.remove_Z_eqb_notin_eq in Hinsert by apply helpers.remove_Z_eqb_notin.
    exact Hinsert. }
  assert (HaddRows : sched_row_values updated reordered =
    ListLib.Base.Positional.replace_Znth (destination / 8)
      (Z.lor (encode_ready_tbl_at_or (helpers.remove_Z_eqb tid ids) updated (destination / 8))
        (Z.shiftl 1 (destination mod 8))) (sched_row_values updated (helpers.remove_Z_eqb tid ids))).
  { unfold sched_row_values; cbn [map].
    rewrite (HaddTable 0), (HaddTable 1), (HaddTable 2), (HaddTable 3),
      (HaddTable 4), (HaddTable 5), (HaddTable 6), (HaddTable 7).
    set (row := destination / 8) in *.
    assert (Hcases : row = 0 \/ row = 1 \/ row = 2 \/ row = 3 \/
      row = 4 \/ row = 5 \/ row = 6 \/ row = 7) by lia.
    repeat destruct Hcases as [Hcases|Hcases]; rewrite Hcases; reflexivity. }
  assert (HaddGroup : encode_ready_grp reordered updated =
    Z.lor (encode_ready_grp (helpers.remove_Z_eqb tid ids) updated) (Z.shiftl 1 (destination / 8))).
  { pose proof (encode_ready_grp_insert_remove updated key tid (helpers.remove_Z_eqb tid ids)
      (mutex_priority_task old destination) Hget) as Hinsert.
    rewrite helpers.remove_Z_eqb_notin_eq in Hinsert by apply helpers.remove_Z_eqb_notin.
    exact Hinsert. }
  assert (Htest : Z.eqb
    (Z.land (ListLib.Base.Positional.Znth (tcb_y_of_prio old.(curPrio)) (sched_row_values tasks ids) 0)
      (tcb_bit_x_of_prio old.(curPrio))) 0 = false).
  { apply Z.eqb_neq; rewrite sched_row_values_Znth by exact Holdrow.
    apply (proj2 (task_change_prio_bitmap_membership__task_state
      tasks ids tid old Hold (proj1 Holdrange) Hnd Hunique Hnonnegative)); exact Hin. }
  split.
  - unfold mutex_priority_rows, mutex_priority_removed_rows, mutex_priority_was_ready.
    rewrite Htest; cbn [negb].
    rewrite HaddRows.
    rewrite <- (sched_row_values_Znth updated (helpers.remove_Z_eqb tid ids)
      (destination / 8) Hnewrow).
    rewrite HremoveRows.
    unfold mutex_priority_cleared_row, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio.
    rewrite sched_row_values_Znth by exact Holdrow; reflexivity.
  - unfold mutex_priority_group, mutex_priority_was_ready; rewrite Htest; cbn [negb].
    rewrite HaddGroup, HgroupExt.
    rewrite (encode_ready_grp_remove_waiter_any ids tasks tid old
      (proj1 Holdrange) Holdrow Hnd Hold Hunique Hnonnegative Hrows).
    unfold ready_group_after_relocation, mutex_priority_cleared_row,
      tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio, tcb_bit_y_of_prio.
    rewrite sched_row_values_Znth by exact Holdrow; reflexivity.
Qed.
Lemma task_change_prio_ready_encoding__task_state :
  forall sg state requested tid old selected destination,
  task_change_prio_live sg state requested selected destination tid old ->
  let after := task_change_priority_state sg state tid old selected destination in
  task_change_prio_ready_rows after = mutex_priority_rows (task_change_prio_ready_rows state)
    (tcb_y_of_prio old.(curPrio)) (tcb_bit_x_of_prio old.(curPrio)) destination /\
  task_change_prio_ready_group after = mutex_priority_group (task_change_prio_ready_rows state)
    (task_change_prio_ready_group state) (tcb_y_of_prio old.(curPrio))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) destination.
Proof.
  intros sg state requested tid old selected destination Hlive after.
  destruct Hlive as [Hvalid [_ [_ [_ [Hold [_ [Hselected [Holdrange [Hrange _]]]]]]]]].
  pose proof (task_change_prio_profile_constants__task_state
    sg state Hvalid) as [Hlowest _].
  pose proof Hvalid as [_ [Htasks [[Hready _] _]]].
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  destruct Hready as [Hmembers [Hsorted [Hcomplete Hnd]]].
  assert (Hranges : forall slot node, In slot state.(SchedState).(readyList) ->
    state.(TskState).(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio) < 64).
  { intros; specialize (Hpriorities slot node H0); unfold task_priority_in_range in Hpriorities; lia. }
  assert (Hrow : 0 <= old.(curPrio) / 8 < 8) by
    (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
  assert (Hnonnegative : forall slot node, In slot state.(SchedState).(readyList) ->
    state.(TskState).(inUsedTaskStates) slot = Some node -> 0 <= node.(curPrio)).
  { intros; exact (proj1 (Hranges slot node H H0)). }
  pose proof (task_change_prio_bitmap_membership__task_state
    state.(TskState) state.(SchedState).(readyList) tid old Hold ltac:(lia) Hnd Hunique Hnonnegative)
    as Hmembership.
  change (sched_row_values (task_change_priority_tasks state.(TskState) tid old selected destination)
      (task_change_priority_ready sg state.(TskState) state.(SchedState) tid old
        (task_change_priority_tasks state.(TskState) tid old selected destination)).(readyList) =
    mutex_priority_rows (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (tcb_y_of_prio old.(curPrio)) (tcb_bit_x_of_prio old.(curPrio)) destination /\
    encode_ready_grp (task_change_priority_ready sg state.(TskState) state.(SchedState) tid old
      (task_change_priority_tasks state.(TskState) tid old selected destination)).(readyList)
      (task_change_priority_tasks state.(TskState) tid old selected destination) =
    mutex_priority_group (sched_row_values state.(TskState) state.(SchedState).(readyList))
      (encode_ready_grp state.(SchedState).(readyList) state.(TskState))
      (tcb_y_of_prio old.(curPrio)) (tcb_bit_x_of_prio old.(curPrio))
      (tcb_bit_y_of_prio old.(curPrio)) destination).
  unfold task_change_priority_ready.
  destruct (Z.eqb (Z.land (encode_ready_tbl_at_or state.(SchedState).(readyList) state.(TskState)
    (old.(curPrio) / 8)) (tcb_bit_x_of_prio old.(curPrio))) 0) eqn:Htest.
  - assert (Habsent : ~ In tid state.(SchedState).(readyList)) by
      (intro Hin; apply Hmembership in Hin; apply Z.eqb_eq in Htest; contradiction).
    destruct (sched_encoding_priority_ext state.(SchedState).(readyList)
      (task_change_priority_tasks state.(TskState) tid old selected destination) state.(TskState)
      ltac:(intros slot Hin; rewrite task_change_prio_used_map_other__task_state
        by congruence; reflexivity)) as [Hgroup Hrows].
    unfold mutex_priority_rows, mutex_priority_group, mutex_priority_was_ready.
    rewrite sched_row_values_Znth by exact Hrow.
    unfold tcb_y_of_prio.
    rewrite Htest; cbn [negb].
    split; [unfold sched_row_values; apply map_ext; exact Hrows|exact Hgroup].
  - apply task_change_prio_reordered_encoding__task_state;
      [exact Hold|lia|lia|exact Hnd|exact Hunique|exact Hranges|].
    apply Hmembership; apply Z.eqb_neq; exact Htest.
Qed.
Lemma task_change_prio_event_encoding__task_state :
  forall sg state requested tid old selected destination eid event,
  task_change_prio_live sg state requested selected destination tid old ->
  state.(EventState).(inUsedEventStates) eid = Some event -> In tid event.(waitList) ->
  let updated := task_change_priority_tasks state.(TskState) tid old selected destination in
  let after := event_insert_waiter sg updated event tid in
  sched_row_values updated after.(waitList) =
    mutex_priority_rows (task_change_prio_event_rows state event) (tcb_y_of_prio old.(curPrio))
      (tcb_bit_x_of_prio old.(curPrio)) destination /\
  encode_event_wait_grp after.(waitList) updated =
    mutex_priority_group (task_change_prio_event_rows state event) (task_change_prio_event_group state event)
      (tcb_y_of_prio old.(curPrio)) (tcb_bit_x_of_prio old.(curPrio))
      (tcb_bit_y_of_prio old.(curPrio)) destination.
Proof.
  intros sg state requested tid old selected destination eid event Hlive Hevent Hin updated after.
  destruct Hlive as [Hvalid [_ [_ [_ [Hold [_ [Hselected [Holdrange [Hrange _]]]]]]]]].
  pose proof (task_change_prio_profile_constants__task_state
    sg state Hvalid) as [Hlowest _].
  pose proof Hvalid as [_ [Htasks [_ [Hevents _]]]].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [Hunique [Hpriorities _]]]]]]]].
  destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (Hentries eid event Hevent) as [[Hnd _] _].
  apply task_change_prio_reordered_encoding__task_state;
    [exact Hold|lia|lia|exact Hnd|exact Hunique| |exact Hin].
  intros slot node Hmember Hnode; specialize (Hpriorities slot node Hnode).
  unfold task_priority_in_range in Hpriorities; lia.
Qed.
Lemma task_change_prio_event_unlisted__task_state :
  forall sg state tid old eid event,
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  old.(eventPtr) <> Some eid -> ~ In tid event.(waitList).
Proof.
  intros sg state tid old eid event Hvalid Hold Hevent Hptr Hin.
  destruct Hvalid as [_ [_ [_ [Hevents _]]]].
  destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]].
  destruct (event_waiter_task_fields sg state.(TskState) eid event tid
    (Hentries eid event Hevent) Hin) as [node [kind [Hnode [_ [Hreference _]]]]].
  assert (node = old) by congruence; subst node; contradiction.
Qed.
Lemma task_change_prio_event_unlisted_image_eq__task_state :
  forall sg tasks tid old selected destination event,
  ~ In tid event.(waitList) ->
  event_image sg tasks event =
  event_image sg (task_change_priority_tasks tasks tid old selected destination) event.
Proof.
  intros sg tasks tid old selected destination event Habsent.
  destruct (event_wait_encoding_priority_ext event.(waitList) tasks
    (task_change_priority_tasks tasks tid old selected destination)
    ltac:(intros slot Hin; rewrite task_change_prio_used_map_other__task_state
      by congruence; reflexivity)) as [Hgroup Hrows].
  apply functional_extensionality; intros []; cbn [event_image]; rewrite ?Hgroup, ?Hrows; reflexivity.
Qed.
Lemma event_raw_rep_no_eid_change_task_index__task_state :
  forall sg before after events eid,
  (forall other node, other <> eid -> events.(inUsedEventStates) other = Some node ->
    event_image sg before node = event_image sg after node) ->
  event_raw_rep_no_eid sg before events eid |-- event_raw_rep_no_eid sg after events eid.
Proof.
  intros sg before after events eid Himages.
  unfold event_raw_rep_no_eid, store_map_missing_i; Intros ids.
  assert (Hdomain : forall other, In other ids <->
    (exists node, events.(inUsedEventStates) other = Some node) /\ other <> eid) by assumption.
  assert (Hmap :
    map (fun other => match events.(inUsedEventStates) other with
      | Some node => used_event_rep sg before other node | None => emp end) ids =
    map (fun other => match events.(inUsedEventStates) other with
      | Some node => used_event_rep sg after other node | None => emp end) ids).
  { apply map_ext_in; intros other Hin.
    destruct (events.(inUsedEventStates) other) as [node|] eqn:Hnode; [|reflexivity].
    unfold used_event_rep; rewrite (Himages other node ltac:(apply Hdomain in Hin; tauto) Hnode);
      reflexivity. }
  Exists ids; rewrite Hmap; entailer!.
Qed.
Lemma task_change_prio_event_storage_merge__task_state :
  forall sg before_tasks tasks eid event tid,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  (event_addr sg eid + 10) # UChar |->
    encode_event_wait_grp (event_insert_waiter sg tasks event tid).(waitList) tasks **
  UCharArray.full (event_addr sg eid + 11) 8
    (sched_row_values tasks (event_insert_waiter sg tasks event tid).(waitList)) **
  EventFieldStorage.store_fields EventField_eq_dec (event_cell (event_addr sg eid))
    [EventTypeField; EventPadding1; EventPadding2; EventPadding3; EventPtrField;
     EventCntField; EventPadding19] (event_image sg before_tasks event) |--
  used_event_rep sg tasks eid (event_insert_waiter sg tasks event tid).
Proof.
  intros sg before_tasks tasks eid event tid Hnamed.
  unfold used_event_rep, event_storage_rep, event_fields; rewrite Hnamed; cbn [app].
  repeat rewrite EventFieldStorage.store_fields_cons by
    (repeat (apply NoDup_cons; [simpl; intuition discriminate|]); constructor).
  rewrite !EventFieldStorage.store_fields_nil.
  unfold sched_row_values, UCharArray.full, store_array.
  cbn [map store_array_rec StoreUCharAsElement.storeA event_cell event_field_offset event_image].
  rewrite sizeof_uchar; simpl.
  repeat rewrite <- Z.add_assoc; cbn.
  unfold encode_event_ptr_value, verification_slice_encode_event_ptr_value, encode_event_cnt_value,
    encode_event_wait_tbl_at_or, encode_ready_tbl_at_or.
  cbn [event_insert_waiter event_set_wait_list eventType mutexFields semFields mboxFields queueFields waitList].
  entailer!.
Qed.
Lemma task_change_prio_queue_storage_transport__task_state :
  forall sg events tasks tid old,
  queue_core.queue_storage_rep sg events |--
  queue_core.queue_storage_rep sg (task_change_priority_events sg events tasks tid old).
Proof.
  intros; unfold task_change_priority_events.
  destruct old.(eventPtr) as [eid|]; [|reflexivity].
  destruct (events.(inUsedEventStates) eid) as [event|] eqn:Hevent; [|reflexivity].
  apply queue_core.queue_set_event_wait_list_preserves_storage; exact Hevent.
Qed.
Lemma task_change_prio_raw_frame_transport__task_state :
  forall sg state tid old selected destination,
  UCOS2_raw_rep_missing_task_storage_sched_event sg state |--
  UCOS2_raw_rep_missing_task_storage_sched_event sg
    (task_change_priority_state sg state tid old selected destination).
Proof.
  intros; unfold UCOS2_raw_rep_missing_task_storage_sched_event.
  cbn [task_change_priority_state replace_SchedS replace_EventS replace_TskS TskState EventState
    IntrState TickState FlagState MemoryState TimerState StatsState ControlState NameState
    task_change_priority_tasks parkedTaskStacks].
  sep_apply task_change_prio_queue_storage_transport__task_state.
  entailer!.
Qed.
Lemma task_change_prio_tcb_merge_updated__task_state :
  forall sg tid old destination, task_change_prio_static sg ->
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> destination **
  tcb_field_address (task_slot_addr sg tid) TCBY # UChar |-> tcb_y_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBX # UChar |-> tcb_x_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |-> tcb_bit_y_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |-> tcb_bit_x_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |-> task_change_prio_event_pointer sg old **
  task_change_prio_tcb_rest sg tid old |-- used_task_rep sg tid (mutex_priority_task old destination).
Proof.
  intros sg tid old destination [Hconfig _].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hconfig; reflexivity).
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hconfig; reflexivity).
  rewrite used_task_rep_tcb64 by assumption.
  rewrite <- task_slot_addr_tcb64 by assumption.
  rewrite <- mutex_priority_reordered_fields.
  unfold tcb64_fields_rep at 1.
  do 5 (rewrite TaskFieldStorage.store_fields_cons at 1 by
    (unfold mutex_priority_unchanged_fields;
      repeat (apply NoDup_cons; [simpl; intuition discriminate|]); constructor)).
  fold (tcb64_fields_rep (task_slot_addr sg tid) mutex_priority_unchanged_fields
    (task_tcb64_image sg (mutex_priority_task old destination))).
  assert (Hrest : tcb64_fields_rep (task_slot_addr sg tid) mutex_priority_unchanged_fields
      (task_tcb64_image sg (mutex_priority_task old destination)) =
    tcb64_fields_rep (task_slot_addr sg tid) mutex_priority_unchanged_fields (task_tcb64_image sg old)).
  { change (mutex_priority_tcb_rest (task_slot_addr sg tid)
      (task_tcb64_image sg (mutex_priority_task old destination)) =
    mutex_priority_tcb_rest (task_slot_addr sg tid) (task_tcb64_image sg old)).
    rewrite <- mutex_priority_image_task_eq; apply mutex_priority_rest_updated. }
  rewrite Hrest.
  cbn [tcb_cell task_tcb64_image mutex_priority_task curPrio].
  unfold task_change_prio_tcb_rest, task_change_prio_event_pointer.
  entailer!.
  pose proof (tcb64_fields_rep_merge mutex_priority_unchanged_fields
    (task_slot_addr sg tid) (task_tcb64_image sg old) TCBEventPtr
    ltac:(unfold mutex_priority_unchanged_fields;
      repeat (apply NoDup_cons; [simpl; intuition discriminate|]); constructor)
    ltac:(unfold mutex_priority_unchanged_fields; simpl; tauto)) as Hmerge.
  exact Hmerge.
Qed.
Lemma task_change_prio_event_raw_merge__task_state :
  forall sg state requested tid old selected destination,
  task_change_prio_static sg -> task_change_prio_live sg state requested selected destination tid old ->
  let tasks := task_change_priority_tasks state.(TskState) tid old selected destination in
  task_change_prio_event_storage sg state old destination |--
  event_raw_rep sg tasks (task_change_priority_events sg state.(EventState) tasks tid old).
Proof.
  intros sg state requested tid old selected destination Hstatic Hlive tasks.
  pose proof Hlive as [Hvalid [_ [_ [_ [Hold _]]]]].
  assert (Hnamed : sg.(osKernelConfig).(cfgEventNames) = false) by
    (destruct Hstatic as [Hconfig _]; rewrite Hconfig; reflexivity).
  unfold task_change_prio_event_storage, task_change_priority_events.
  destruct old.(eventPtr) as [eid|] eqn:Hptr.
  - Intros event.
    assert (Hevent : state.(EventState).(inUsedEventStates) eid = Some event) by assumption.
    rewrite Hevent.
    assert (Hin : In tid event.(waitList)).
    { pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
      destruct Hcross as [_ [_ [[_ [Hbacklinks _]] _]]].
      eapply Hbacklinks; [exact Hold|exact Hevent|left; exact Hptr]. }
    destruct (task_change_prio_event_encoding__task_state
      sg state requested tid old selected destination eid event Hlive Hevent Hin) as [Hrows Hgroup].
    rewrite <- Hrows, <- Hgroup.
    unfold task_change_prio_event_frame.
    assert (Hframe : event_raw_rep_no_eid sg state.(TskState) state.(EventState) eid |--
      event_raw_rep_no_eid sg tasks state.(EventState) eid).
    { apply event_raw_rep_no_eid_change_task_index__task_state.
      intros other node Hneq Hnode.
      apply task_change_prio_event_unlisted_image_eq__task_state.
      eapply task_change_prio_event_unlisted__task_state;
        [exact Hvalid|exact Hold|exact Hnode|congruence]. }
    sep_apply_r_atomic (event_raw_rep_merge_updated_eid sg tasks state.(EventState) eid
      (event_insert_waiter sg tasks event tid)).
    sepcon_right_assoc; sep_apply_r_atomic Hframe.
    sepcon_right_assoc.
    sep_apply_r_atomic (task_change_prio_event_storage_merge__task_state
      sg state.(TskState) tasks eid event tid Hnamed); entailer!.
  - assert (Hencoding : event_raw_encoding_agrees state.(TskState) tasks state.(EventState)).
    { intros eid event Hevent; apply event_wait_encoding_priority_ext.
      intros slot Hmember; unfold tasks.
      rewrite task_change_prio_used_map_other__task_state; [reflexivity|].
      intro Heq; subst slot.
      eapply task_change_prio_event_unlisted__task_state;
        [exact Hvalid|exact Hold|exact Hevent|congruence|exact Hmember]. }
    rewrite (event_raw_rep_change_task_index sg state.(TskState) tasks state.(EventState) Hencoding).
    reflexivity.
Qed.
Lemma task_change_prio_work_merge_updated__task_state :
  forall environment saved_local critical sg execution saved acquired state requested tid old selected destination,
  task_change_prio_static sg -> task_change_prio_live sg state requested selected destination tid old ->
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (task_change_prio_updated_table sg state tid old selected destination) **
  UCharArray.full sg.(g_OSRdyTbl) 8
    (mutex_priority_rows (task_change_prio_ready_rows state) (tcb_y_of_prio old.(curPrio))
      (tcb_bit_x_of_prio old.(curPrio)) destination) **
  sg.(g_OSRdyGrp) # UChar |-> mutex_priority_group (task_change_prio_ready_rows state)
    (task_change_prio_ready_group state) (tcb_y_of_prio old.(curPrio))
    (tcb_bit_x_of_prio old.(curPrio)) (tcb_bit_y_of_prio old.(curPrio)) destination **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> destination **
  tcb_field_address (task_slot_addr sg tid) TCBY # UChar |-> tcb_y_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBX # UChar |-> tcb_x_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBBitY # UChar |-> tcb_bit_y_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBBitX # UChar |-> tcb_bit_x_of_prio destination **
  tcb_field_address (task_slot_addr sg tid) TCBEventPtr # Ptr |-> task_change_prio_event_pointer sg old **
  task_change_prio_event_storage sg state old destination **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |->
    sched_priority_byte (task_change_priority_cached_priority state.(SchedState) tid destination) **
  task_change_prio_work_frame_without_current
    environment saved_local critical sg execution saved acquired state tid old |--
  task_change_prio_masked environment saved_local critical sg execution saved acquired
    (task_change_priority_state sg state tid old selected destination).
Proof.
  intros environment saved_local critical sg execution saved acquired state requested tid old selected destination
    Hstatic Hlive.
  pose proof Hlive as [_ [_ [_ [_ [Hold _]]]]].
  set (after := task_change_priority_state sg state tid old selected destination).
  assert (Hvalid : UCOS2_state_inv sg after) by
    (eapply task_change_prio_preserves_state_inv__task_state; exact Hlive).
  assert (Hmasked : task_change_prio_masked_frame environment saved_local critical sg execution saved acquired state |--
    task_change_prio_masked_frame environment saved_local critical sg execution saved acquired after).
  { apply task_change_prio_masked_frame_transport__task_state; exact Hold. }
  assert (Hraw : UCOS2_raw_rep_missing_task_storage_sched_event sg state |--
    UCOS2_raw_rep_missing_task_storage_sched_event sg after).
  { apply task_change_prio_raw_frame_transport__task_state. }
  assert (Hevent : task_change_prio_event_storage sg state old destination |--
    event_raw_rep sg after.(TskState) after.(EventState)).
  { eapply task_change_prio_event_raw_merge__task_state;
      [exact Hstatic|exact Hlive]. }
  assert (Hmap : store_map_missing_i (used_task_rep sg) state.(TskState).(inUsedTaskStates) tid **
    used_task_rep sg tid (mutex_priority_task old destination) |--
    store_map (used_task_rep sg) after.(TskState).(inUsedTaskStates)).
  { rewrite (store_map_missing_i_equiv (used_task_rep sg)
      state.(TskState).(inUsedTaskStates) after.(TskState).(inUsedTaskStates) tid).
    - apply store_map_merge; apply task_change_priority_tasks_lookup.
    - intros slot Hneq; symmetry; apply task_change_prio_used_map_other__task_state;
        exact Hneq. }
  assert (Hphysical :
    sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) **
    sg.(g_OSPrioCur) # UChar |->
      sched_priority_byte (task_change_priority_cached_priority state.(SchedState) tid destination) **
    task_change_prio_sched_physical_without_current sg state.(SchedState) |--
    sched_physical_rep sg after.(SchedState)).
  { apply task_change_prio_sched_physical_merge_updated_current. }
  destruct (task_change_prio_ready_encoding__task_state
    sg state requested tid old selected destination Hlive) as [Hrows Hgroup].
  change (sched_row_values after.(TskState) after.(SchedState).(readyList) =
    mutex_priority_rows (task_change_prio_ready_rows state) (tcb_y_of_prio old.(curPrio))
      (tcb_bit_x_of_prio old.(curPrio)) destination) in Hrows.
  change (encode_ready_grp after.(SchedState).(readyList) after.(TskState) =
    mutex_priority_group (task_change_prio_ready_rows state) (task_change_prio_ready_group state)
      (tcb_y_of_prio old.(curPrio)) (tcb_bit_x_of_prio old.(curPrio))
      (tcb_bit_y_of_prio old.(curPrio)) destination) in Hgroup.
  unfold task_change_prio_masked; fold after.
  rewrite kernel_program_inv_split_unmap, UCOS2_inv_open_task_storage_sched_event.
  entailer!.
  unfold task_change_prio_work_frame_without_current.
  sepcon_right_assoc.
  sep_apply_r_atomic Hmasked.
  sep_apply_r_atomic Hraw.
  sep_apply_r_atomic Hevent.
  unfold task_public_storage, store_used_task_map.
  sepcon_right_assoc.
  sep_apply_r_atomic Hmap.
  sepcon_right_assoc.
  sep_apply_r_atomic (task_change_prio_tcb_merge_updated__task_state
    sg tid old destination Hstatic).
  unfold sched_raw_rep; rewrite sched_rows_array_equiv, Hrows, Hgroup.
  sepcon_right_assoc.
  sep_apply_r_atomic Hphysical.
  unfold store_prio_tbl, task_change_prio_updated_table, task_change_prio_table.
  unfold task_reg_allocator_rep.
  entailer!.
  unfold after.
  cbn [task_change_priority_state replace_SchedS replace_EventS replace_TskS TskState
    task_change_priority_tasks taskLifecycle unUsedTaskStates tcbListHead taskCount taskRegNextID].
  entailer!.
Qed.
Lemma task_change_prio_live_critical_code__task_state :
  forall sg state requested tid old selected destination,
  task_change_prio_live sg state requested selected destination tid old ->
  task_change_prio_critical_code sg requested destination state 0
    (task_change_priority_state sg state tid old selected destination).
Proof.
  intros sg state requested tid old selected destination
    [Hvalid [Hselection [Hfree [Htable [Hold [_ [_ [Hrange _]]]]]]]].
  pose proof (task_change_prio_profile_constants__task_state
    sg state Hvalid) as [Hlowest _].
  exists OS_ERR_NONE; split; [|reflexivity].
  unfold task_change_prio_critical; rewrite Hfree.
  exists selected; split; [exact Hselection|].
  unfold task_change_prio_selected_effect.
  assert (Hnotidle : Z.eqb selected sg.(osLowestPrio) = false) by
    (apply Z.eqb_neq; lia).
  rewrite Hnotidle, Htable; exists old; auto.
Qed.
Lemma task_change_prio_argument_valid__call_boundaries : forall sg state requested newprio,
  UCOS2_state_inv sg state -> task_change_prio_static sg ->
  (requested < 63 \/ requested = 255) -> newprio < 63 ->
  task_change_priority_argument_error sg requested newprio = None.
Proof.
  intros sg state requested newprio Hvalid [Hconfig _] Hrequested Hnew.
  pose proof (proj1 (proj1 Hvalid)) as Hsg.
  assert (Hlowest : sg.(osLowestPrio) = 63) by (unfold valid_stable_glob_vars in Hsg; tauto).
  assert (Hself : sg.(osPrioSelf) = 255) by (unfold valid_stable_glob_vars in Hsg; tauto).
  unfold task_change_priority_argument_error; rewrite Hconfig, Hlowest, Hself.
  cbn [selected_kernel_configuration cfgArgumentChecks].
  assert (Hold : ((63 <=? requested) && negb (requested =? 255))%bool = false).
  { destruct Hrequested as [Hlt|Heq].
    - assert (Hltb : (63 <=? requested) = false) by (apply Z.leb_gt; lia).
      rewrite Hltb; reflexivity.
    - subst requested; reflexivity. }
  assert (Hnewb : (63 <=? newprio) = false) by (apply Z.leb_gt; lia).
  rewrite Hold, Hnewb; reflexivity.
Qed.
Lemma task_change_prio_argument_new_invalid__call_boundaries : forall sg state requested newprio,
  UCOS2_state_inv sg state -> task_change_prio_static sg -> 63 <= newprio ->
  task_change_priority_argument_error sg requested newprio = Some OS_ERR_PRIO_INVALID.
Proof.
  intros sg state requested newprio Hvalid [Hconfig _] Hnew.
  pose proof (proj1 (proj1 Hvalid)) as Hsg.
  assert (Hlowest : sg.(osLowestPrio) = 63) by (unfold valid_stable_glob_vars in Hsg; tauto).
  unfold task_change_priority_argument_error; rewrite Hconfig, Hlowest.
  cbn [selected_kernel_configuration cfgArgumentChecks].
  assert (Hnewb : (63 <=? newprio) = true) by (apply Z.leb_le; lia).
  rewrite Hnewb; destruct (Z.leb 63 requested && negb (Z.eqb requested sg.(osPrioSelf)))%bool;
    reflexivity.
Qed.
Lemma task_change_prio_argument_old_invalid__call_boundaries : forall sg state requested newprio,
  UCOS2_state_inv sg state -> task_change_prio_static sg ->
  63 <= requested -> requested <> 255 ->
  task_change_priority_argument_error sg requested newprio = Some OS_ERR_PRIO_INVALID.
Proof.
  intros sg state requested newprio Hvalid [Hconfig _] Hold Hnotself.
  pose proof (proj1 (proj1 Hvalid)) as Hsg.
  assert (Hlowest : sg.(osLowestPrio) = 63) by (unfold valid_stable_glob_vars in Hsg; tauto).
  assert (Hself : sg.(osPrioSelf) = 255) by (unfold valid_stable_glob_vars in Hsg; tauto).
  unfold task_change_priority_argument_error; rewrite Hconfig, Hlowest, Hself.
  cbn [selected_kernel_configuration cfgArgumentChecks].
  assert (Holdb : (63 <=? requested) = true) by (apply Z.leb_le; lia).
  assert (Hselfb : (requested =? 255) = false) by (apply Z.eqb_neq; assumption).
  rewrite Holdb, Hselfb; reflexivity.
Qed.
Lemma task_change_prio_closed_implies_invariant__call_boundaries :
  forall environment saved_local critical sg execution mask state,
  task_change_prio_closed environment saved_local critical sg execution mask state |--
  (coq_prop (UCOS2_state_inv sg state) &&
   task_change_prio_closed environment saved_local critical sg execution mask state)%sac.
Proof.
  intros; destruct execution; cbn [task_change_prio_closed].
  - unfold os_sched_continuation_pre, kernel_continuation_call_closed,
      kernel_continuation_inv, kernel_program_inv; entailer!.
  - entailer!.
Qed.
Lemma task_change_prio_closed_split_running__call_boundaries :
  forall environment saved_local critical sg execution mask state,
  task_change_prio_closed environment saved_local critical sg execution mask state --||--
  (sg.(g_OSRunning) # UChar |-> task_change_prio_running state **
   task_change_prio_closed_without_running environment saved_local critical sg execution mask state)%sac.
Proof.
  intros; destruct execution; unfold task_change_prio_running;
    cbn [task_change_prio_closed task_change_prio_closed_without_running].
  - unfold os_sched_continuation_pre, kernel_continuation_call_closed,
      kernel_continuation_inv, kernel_program_inv, kernel_program_rep.
    rewrite UCOS2_raw_rep_split_running; split; entailer!.
  - unfold sched_disabled_closed, critical_region_outside.
    split; entailer!.
Qed.
Lemma task_change_prio_save_transports_call_source__call_boundaries :
  forall environment critical sg requested newprio original returned mask saved before acquired,
  UCOS2_state_inv sg before ->
  task_change_prio_environment environment critical sg requested newprio original ->
  task_change_prio_call_source original before ->
  task_change_prio_save_source environment critical sg requested newprio
    original returned mask saved before acquired ->
  task_change_prio_environment environment critical sg requested newprio returned /\
  interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired /\
  task_change_prio_call_source returned acquired.
Proof.
  intros environment critical sg requested newprio original returned mask saved before acquired
    Hvalid Henv Hsource [Hrely Hinterval].
  destruct original as [first|first], returned as [last|last];
    cbn [task_change_prio_save_interval] in Hinterval; try contradiction.
  - destruct Hinterval as [Hsave Hnormal].
    pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave)
      as Hregion.
    destruct (critical_region_interval_transports_resources critical sg
      first.(os_sched_call_invocation) before acquired Hregion Hvalid) as [Hvalid' _].
    destruct Henv as [Hsave_env [Hrestore_env Hclients]].
    destruct Hsource as [Htask [Havailable Hready]].
    split; [exact (conj Hsave_env (conj Hrestore_env Hclients))|].
    split; [exact (proj2 (proj2 (proj2 (proj2 Hsave))))|].
    split; [exact Hvalid'|].
    split.
    + exact (kernel_call_save_source_preserves_task_source
        environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical sg first last mask saved before acquired Hvalid Htask Hsave).
    + split; [exact (proj2 Hnormal Havailable)|].
      intro Hrunning; eapply critical_region_interval_preserves_sched_ready;
        [exact Hclients|exact Hregion|exact Hvalid|].
      apply Hready; rewrite <- (proj1 Hrely); exact Hrunning.
  - destruct Hinterval as [Heq [Hsaved Hregion]]; subst last.
    destruct (critical_region_interval_transports_resources critical sg
      first.(os_execution_invocation) before acquired Hregion Hvalid) as [Hvalid' _].
    split; [exact Henv|]. split; [exact Hsaved|]. split; [exact Hvalid'|].
    destruct Hsource as [Hnot_running|Hdisabled].
    + left; rewrite (proj1 Hrely); exact Hnot_running.
    + right; eapply sched_disabled_context_rely_preserves_entry_source;
        [|exact Hdisabled].
      exact (proj2 (sched_disabled_interval_preserves_context critical sg first
        first.(os_execution_invocation) before acquired (proj2 (proj2 Henv)) Hvalid Hregion)).
Qed.
Lemma task_change_prio_restore_transports_call_source__call_boundaries :
  forall environment critical sg requested newprio original returned released current,
  UCOS2_state_inv sg released ->
  task_change_prio_environment environment critical sg requested newprio original ->
  task_change_prio_call_source original released ->
  task_change_prio_restore_source environment critical sg original returned released current ->
  task_change_prio_environment environment critical sg requested newprio returned /\
  task_change_prio_call_source returned current.
Proof.
  intros environment critical sg requested newprio original returned released current
    Hvalid Henv Hsource [Hrely Hinterval].
  destruct original as [first|first], returned as [last|last];
    cbn [task_change_prio_restore_interval] in Hinterval; try contradiction.
  - destruct Hinterval as [Htrace Hnormal].
    destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
      as [Hregion _].
    destruct Henv as [Hsave_env [Hrestore_env Hclients]].
    destruct Hsource as [Htask [Havailable Hready]].
    split; [exact (conj Hsave_env (conj Hrestore_env Hclients))|].
    split.
    + apply (proj2 (task_tcb_init_stack_same_call_source_iff last first current (proj1 Hnormal))).
      exact (task_tcb_init_stack_registered_source_preserved
        environment.(task_stack_call_external) environment.(task_stack_call_port)
        critical sg first last released current Hvalid (proj1 Hnormal) Htrace Htask).
    + split; [exact (proj2 Hnormal Havailable)|].
      intro Hrunning; eapply critical_region_interval_preserves_sched_ready;
        [exact Hclients|exact Hregion|exact Hvalid|].
      apply Hready; rewrite <- (proj1 Hrely); exact Hrunning.
  - destruct Hinterval as [Heq Hregion]; subst last.
    split; [exact Henv|].
    destruct Hsource as [Hnot_running|Hdisabled].
    + left; rewrite (proj1 Hrely); exact Hnot_running.
    + right; eapply sched_disabled_context_rely_preserves_entry_source;
        [|exact Hdisabled].
      exact (proj2 (sched_disabled_interval_preserves_context critical sg first
        first.(os_execution_invocation) released current (proj2 (proj2 Henv)) Hvalid Hregion)).
Qed.
Lemma task_change_prio_closed_implies_scheduler_pre__call_boundaries :
  forall environment saved_local critical sg execution mask state requested newprio,
  task_change_prio_static sg ->
  task_change_prio_environment environment critical sg requested newprio execution ->
  task_change_prio_call_source execution state -> state.(SchedState).(isRunning) = true ->
  task_change_prio_closed environment saved_local critical sg execution mask state |--
  task_change_prio_scheduler_pre environment saved_local critical sg execution mask state.
Proof.
  intros environment saved_local critical sg execution mask state requested newprio
    Hstatic Henv Hsource Hrunning.
  destruct execution as [call|view].
  - cbn [task_change_prio_closed task_change_prio_scheduler_pre].
    unfold os_sched_continuation_call_pre, os_sched_continuation_pre,
      kernel_continuation_call_closed, kernel_continuation_inv, kernel_program_inv.
    Intros.
    assert (Hvalid : UCOS2_state_inv sg state) by assumption.
    destruct Hsource as [Htask [Havailable Hready]].
    assert (Hcut : os_sched_call_cut sg call state).
    { apply os_sched_call_cut_from_source; try assumption.
      - apply Hready; exact Hrunning.
      - exact (kernel_call_task_source_stack_field_address sg call state
          (proj1 (proj2 (proj2 Hstatic))) Hvalid Htask). }
    pose proof (proj2 (proj2 Henv)) as Hclients.
    entailer!.
  - cbn [task_change_prio_closed task_change_prio_scheduler_pre].
    Intros.
    assert (Hdisabled : sched_disabled_entry_source view state).
    { destruct Hsource as [Hnot_running|Hdisabled]; [congruence|exact Hdisabled]. }
    pose proof (proj2 (proj2 Henv)) as Hclients.
    entailer!.
Qed.
Lemma task_change_prio_priority_constants__return_contract : forall sg state,
  UCOS2_state_inv sg state -> sg.(osLowestPrio) = 63 /\ sg.(osPrioSelf) = 255.
Proof.
  intros sg state [[Hstable _] _].
  unfold valid_stable_glob_vars in Hstable; tauto.
Qed.
Lemma task_change_prio_arguments_valid__return_contract : forall sg state requested newprio,
  UCOS2_state_inv sg state -> (requested < 63 \/ requested = 255) -> newprio < 63 ->
  task_change_priority_argument_error sg requested newprio = None.
Proof.
  intros sg state requested newprio Hstate Hrequested Hnew.
  destruct (task_change_prio_priority_constants__return_contract sg state Hstate)
    as [Hlowest Hself].
  unfold task_change_priority_argument_error; rewrite Hlowest, Hself.
  assert (Hnewb : (63 <=? newprio) = false) by (apply Z.leb_gt; lia).
  rewrite Hnewb; destruct sg.(osKernelConfig).(cfgArgumentChecks); [|reflexivity].
  destruct Hrequested as [Hrequested | ->].
  - assert (Holdb : (63 <=? requested) = false) by (apply Z.leb_gt; lia).
    rewrite Holdb; reflexivity.
  - reflexivity.
Qed.
Lemma mapped_Zrange_nth__return_contract : forall (f : Z -> Z) n low index default,
  (index < n)%nat ->
  nth index (map f (Zrange_aux low n)) default = f (low + Z.of_nat index).
Proof.
  intros f n; induction n as [|n IH]; intros low index default Hindex; [lia|].
  destruct index as [|index].
  - cbn; f_equal; lia.
  - cbn; rewrite IH by lia; f_equal; lia.
Qed.
Lemma task_change_prio_table_lookup__return_contract : forall sg state p,
  0 <= p < 64 ->
  ListLib.Base.Positional.Znth p (task_change_prio_table sg state) 0 =
    prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) p).
Proof.
  intros sg state p Hp; unfold task_change_prio_table, ListLib.Base.Positional.Znth, Zrange.
  rewrite mapped_Zrange_nth__return_contract by lia.
  rewrite Z2Nat.id by lia; reflexivity.
Qed.
Lemma task_change_prio_table_null_is_free__return_contract : forall sg state p,
  UCOS2_state_inv sg state -> task_change_prio_static sg -> 0 <= p < 64 ->
  ListLib.Base.Positional.Znth p (task_change_prio_table sg state) 0 = 0 ->
  state.(TskState).(prioTbl) p = PTFree.
Proof.
  intros sg state p Hstate [Hconfig Hstatic] Hp Hnull.
  rewrite task_change_prio_table_lookup__return_contract in Hnull by exact Hp.
  destruct (state.(TskState).(prioTbl) p) as [| |tid] eqn:Hentry;
    [reflexivity|discriminate|].
  destruct (task_change_prio_priority_constants__return_contract sg state Hstate)
    as [Hlowest _].
  destruct Hstate as [[Hstable Hprofile] [Htasks [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Hslots _]] _].
  specialize (Hslots p ltac:(unfold task_priority_in_range; rewrite Hlowest; lia)).
  rewrite Hentry in Hslots; destruct Hslots as [node Hnode].
  destruct Htasks as [[Hpool _] _].
  assert (Htid : task_slot_in_range sg tid).
  { apply (proj2 (Hpool tid)); left; eauto. }
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  cbn [prio_tbl_entry_to_addr] in Hnull.
  unfold task_slot_addr in Hnull; rewrite Hconfig in Hnull; cbn in Hnull.
  unfold task_slot_in_range in Htid; lia.
Qed.
Lemma task_change_prio_table_reserved_is_reserved__return_contract : forall sg state p,
  task_change_prio_static sg -> 0 <= p < 64 ->
  ListLib.Base.Positional.Znth p (task_change_prio_table sg state) 0 = 1 ->
  state.(TskState).(prioTbl) p = PTReserved.
Proof.
  intros sg state p Hstatic Hp Hreserved.
  rewrite task_change_prio_table_lookup__return_contract in Hreserved by exact Hp.
  destruct (state.(TskState).(prioTbl) p) as [| |tid];
    [discriminate|reflexivity|].
  exfalso; eapply task_change_prio_slot_not_reserved; eassumption.
Qed.
Lemma task_change_prio_closed_merge_running__return_contract :
  forall environment saved_local critical sg execution mask state,
  sg.(g_OSRunning) # UChar |-> task_change_prio_running state **
    task_change_prio_closed_without_running environment saved_local critical sg execution mask state
  |-- task_change_prio_closed environment saved_local critical sg execution mask state.
Proof.
  intros; destruct execution; cbn [task_change_prio_closed_without_running task_change_prio_closed].
  - unfold os_sched_continuation_pre, kernel_continuation_call_closed,
      kernel_continuation_inv, kernel_program_inv, kernel_program_rep.
    rewrite UCOS2_raw_rep_split_running.
    unfold task_change_prio_running; entailer!.
  - unfold sched_disabled_closed, critical_region_outside, task_change_prio_running.
    entailer!.
Qed.
Lemma task_change_prio_error_restore_post__return_contract :
  forall environment saved_local critical sg requested newprio original mask before
    saved acquired_execution acquired released result,
  task_change_priority_argument_error sg requested newprio = None ->
  task_change_prio_save_source environment critical sg requested newprio
    original acquired_execution mask saved before acquired ->
  UCOS2_state_inv sg acquired -> UCOS2_state_inv sg released ->
  task_change_prio_critical_code sg requested newprio acquired result released ->
  interrupt_saved_value mask saved -> result <> 0 ->
  task_change_prio_restore_post environment saved_local critical sg acquired_execution saved released
  |-- task_change_prio_post environment saved_local critical sg requested newprio original mask before result.
Proof.
  intros environment saved_local critical sg requested newprio original mask before
    saved acquired_execution acquired released result Harguments Hsave Hacquired Hreleased
    Heffect Hsaved Hresult.
  unfold task_change_prio_restore_post; Intros restored_execution restored.
  unfold task_change_prio_post; rewrite Harguments.
  Exists saved acquired_execution acquired released restored_execution restored.
  assert (Hzero : (result =? 0) = false) by (apply Z.eqb_neq; exact Hresult).
  rewrite Hzero; cbn [andb].
  pose proof (proj2 Hsaved) as Hmask; rewrite Hmask.
  entailer!.
Qed.
