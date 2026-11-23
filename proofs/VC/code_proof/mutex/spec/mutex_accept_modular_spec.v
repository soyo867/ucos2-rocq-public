Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Export Ucos2Verify.VC.code.mutex.spec.mutex_accept_call_spec.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Export Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Export Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Export Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Extend the historical used-ECB contract only by the source's free-ECB
    type-error branch. The existing exact protected semantics is reused. *)
Definition mutex_accept_public_input (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (observed : OSEventAbstractState) : Prop :=
  pe = 0 \/ (pe <> 0 /\ pe = event_addr sg eid /\ valid_event_id sg eid /\
    sem_query_public_slot before eid observed /\
    (event_slot_type_value before.(EventState) eid = 4 -> before.(IntrState).(intNesting) <= 0 ->
      mutex_accept_handle_protocol critical sg invocation eid)).

Definition mutex_accept_public_program critical sg invocation pe
  : program UCOS2_Verify_State (Z * Z) :=
  fun before result after =>
    mutex_accept_call_program critical sg invocation pe before result after \/
    (pe <> 0 /\ exists eid,
      pe = event_addr sg eid /\ valid_event_id sg eid /\
      before.(EventState).(inUsedEventStates) eid = None /\
      In eid before.(EventState).(unUsedEventStates) /\ result = (1, 0) /\ after = before).

Definition mutex_accept_public_post critical sg invocation pe before code value after : Prop :=
  mutex_accept_public_program critical sg invocation pe before (code, value) after.

Lemma mutex_accept_public_input_slot : forall critical sg invocation pe before eid observed,
  mutex_accept_public_input critical sg invocation pe before eid observed -> pe <> 0 ->
  pe = event_addr sg eid /\ valid_event_id sg eid /\ sem_query_public_slot before eid observed /\
  (event_slot_type_value before.(EventState) eid = 4 -> before.(IntrState).(intNesting) <= 0 ->
    mutex_accept_handle_protocol critical sg invocation eid).
Proof. intros; unfold mutex_accept_public_input in H; tauto. Qed.

Lemma mutex_accept_public_slot_is_mutex : forall state eid observed,
  sem_query_public_slot state eid observed -> event_slot_type_value state.(EventState) eid = 4 ->
  mutex_accept_lookup state eid observed /\ observed.(eventType) = OS_EVENT_TYPE_MUTEX.
Proof.
  intros state eid observed [Hused|[Hnone Hfree]] Htype;
    unfold event_slot_type_value in Htype.
  - unfold mutex_query_lookup in Hused; rewrite Hused in Htype.
    split; [exact Hused|apply mutex_accept_encoded_type_is_mutex; exact Htype].
  - rewrite Hnone in Htype; discriminate.
Qed.

Lemma mutex_accept_public_wrong_type_return : forall critical sg invocation pe before eid observed,
  pe <> 0 -> pe = event_addr sg eid -> valid_event_id sg eid ->
  sem_query_public_slot before eid observed -> event_slot_type_value before.(EventState) eid <> 4 ->
  mutex_accept_public_program critical sg invocation pe before (1, 0) before.
Proof.
  intros critical sg invocation pe before eid observed Hpe Haddr Hid [Hused|[Hnone Hfree]] Htype.
  - left; eapply mutex_accept_call_wrong_type_return; try eassumption.
    intro E; apply Htype; unfold event_slot_type_value, mutex_query_lookup in *;
      rewrite Hused, E; reflexivity.
  - right; split; [exact Hpe|]; exists eid.
    split; [exact Haddr|]; split; [exact Hid|]; split; [exact Hnone|].
    split; [exact Hfree|]; split; reflexivity.
Qed.

Lemma mutex_accept_public_safe_return :
  forall critical sg invocation pe before after code value X,
  mutex_accept_public_program critical sg invocation pe before (code, value) after ->
  safeExec (LastSeen before)
    (bind (atomic_cmd (mutex_accept_public_program critical sg invocation pe)) mutex_accept_observe_result) X ->
  safeExec (LastSeen after) (@StateRelMonad.ret (UCOS2_Verify_State -> Prop) Z value) X.
Proof.
  intros critical sg invocation pe before after code value X Hsem Hexec.
  assert (Hatomic : hs_eval (atomic_cmd (mutex_accept_public_program critical sg invocation pe))
    (LastSeen before) (LastSeen after) (code, value)).
  { unfold hs_eval, LastSeen, atomic_cmd; intros P HP.
    exists (RTrans_Abs after); split; [|intro state; split; trivial].
    exists before, after; split; [apply HP; exact I|].
    split; [exact Hsem|intro state; split; trivial]. }
  pose proof (highstepbind_derive _ _ _ (code, value) (LastSeen after) Hatomic X Hexec) as Hobs.
  eapply (highstependret_derive (mutex_accept_observe_result (code, value)) (LastSeen after) value
    (fun _ => LastSeen after)); [|exact Hobs].
  unfold hs_eval, LastSeen; intros P HP; exists P; split; [split; reflexivity|exact HP].
Qed.

(** Accept uses the existing call/continuation world. No Scheduler call,
    ready premise or additional platform law is introduced. Only the
    non-error caller has a task source; NULL, free/type and ISR returns
    retain their original input domain. *)
Definition mutex_accept_call_admission (call : OsSchedCallContext)
  (pe : Z) (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 4 ->
  before.(IntrState).(intNesting) <= 0 -> kernel_call_task_source call before.

Definition mutex_accept_call_binding (environment : TaskStackCallEnvironment)
  (platform : InterruptPlatformResources) (original : OsSchedCallContext)
  (invocation : nat) (origin : TaskInvocationOrigin) : Prop :=
  environment.(task_stack_call_platform) = platform /\
  original.(os_sched_call_invocation) = invocation /\
  original.(os_sched_call_origin) = origin.

Definition mutex_accept_call_support (environment : TaskStackCallEnvironment)
  saved_local (sg : StableGlobVars) original state : Assertion :=
  EX call,
    coq_prop (task_tcb_init_stack_same_call call original /\
      task_stack_live_coverage state.(TskState) (task_stack_call_active_key call)) &&
    (os_sched_context_resources environment.(task_stack_call_external) call **
     store_parked_continuations
       (kernel_saved_continuation_entry environment.(task_stack_call_continuations)
         state.(TskState) (task_create_continuation_local saved_local))
       state.(TskState).(parkedTaskStacks)).

Definition mutex_accept_current_exists sg state : Prop :=
  exists tid task, mutex_accept_current_task sg state tid task.

Definition mutex_accept_call_acquire_facts critical sg invocation eid mask saved
  before acquired observed current : Prop :=
  mutex_accept_acquire_facts critical sg invocation eid mask saved before acquired observed current /\
  mutex_accept_current_exists sg acquired.

Lemma mutex_accept_source_current_exists : forall sg state call,
  valid_stable_glob_vars sg -> UCOS2_state_inv sg state ->
  kernel_call_task_source call state -> mutex_accept_current_exists sg state.
Proof.
  intros sg state call Hsg Hvalid Hsource.
  destruct (kernel_call_task_source_current_at call state Hsource)
    as [Hcurrent [node [Hnode Hgeneration]]].
  exists call.(os_sched_call_stack).(stackLeaseSlot), node.
  apply mutex_accept_current_task_from_lookup; assumption.
Qed.

Lemma mutex_accept_call_support_event_update : forall environment saved_local sg original
  state eid observed mutex tid priority,
  mutex_accept_call_support environment saved_local sg original state =
  mutex_accept_call_support environment saved_local sg original
    (mutex_accept_owned_state state eid observed mutex tid priority).
Proof. reflexivity. Qed.

Lemma mutex_accept_call_support_closed : forall environment platform critical saved_local sg
  original invocation origin mask state,
  mutex_accept_call_binding environment platform original invocation origin ->
  mutex_accept_closed platform critical sg invocation origin mask state **
    mutex_accept_call_support environment saved_local sg original state |--
  EX call,
    coq_prop (task_tcb_init_stack_same_call call original /\ UCOS2_state_inv sg state) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      UCOS2_inv (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key call) call mask state.
Proof.
  intros environment platform critical saved_local sg original invocation origin mask state
    [Hplatform [Hi Ho]].
  subst platform.
  rewrite mutex_accept_closed_equiv.
  unfold mutex_accept_call_support; Intros call.
  destruct H as [Hsame Hcoverage].
  pose proof Hsame as [Hci [Hco Hcs]].
  Exists call.
  unfold kernel_continuation_call_closed, kernel_call_execution_owned, kernel_continuation_inv.
  rewrite Hci, Hco, Hi, Ho.
  unfold UCOS2_inv at 1; Intros_p Hvalid.
  unfold UCOS2_inv; entailer!.
Qed.

Lemma mutex_accept_modular_save_pre : forall environment platform (critical : CriticalRegionResources) saved_local sg
  original invocation origin mask state,
  mutex_accept_call_binding environment platform original invocation origin ->
  (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg state) **
    mutex_accept_call_support environment saved_local sg original state |--
  EX call,
    coq_prop (task_tcb_init_stack_same_call call original /\ UCOS2_state_inv sg state) &&
    kernel_continuation_call_closed environment.(task_stack_call_continuations)
      UCOS2_inv (task_create_continuation_local saved_local) sg
      (task_stack_call_active_key call) call mask state.
Proof.
  intros; rewrite <- (mutex_accept_closed_equiv platform critical sg invocation origin mask state).
  apply mutex_accept_call_support_closed; assumption.
Qed.

Lemma mutex_accept_call_closed_support : forall environment platform critical saved_local sg
  original call invocation origin mask state,
  mutex_accept_call_binding environment platform original invocation origin ->
  task_tcb_init_stack_same_call call original ->
  kernel_continuation_call_closed environment.(task_stack_call_continuations)
    UCOS2_inv (task_create_continuation_local saved_local) sg
    (task_stack_call_active_key call) call mask state |--
  mutex_accept_closed platform critical sg invocation origin mask state **
    mutex_accept_call_support environment saved_local sg original state.
Proof.
  intros environment platform critical saved_local sg original call invocation origin mask state
    [Hplatform [Hi Ho]] Hsame.
  subst platform.
  pose proof Hsame as [Hci [Hco Hcs]].
  rewrite mutex_accept_closed_equiv.
  unfold kernel_continuation_call_closed, kernel_call_execution_owned, kernel_continuation_inv;
    Intros_p Hcoverage.
  unfold mutex_accept_call_support; Exists call.
  rewrite Hci, Hco, Hi, Ho; entailer!.
Qed.

(** This is a consequence of the shared, explicit platform contract and
    its existing registered C-source trace. Current/live comes from that
    source theorem; it is not an extra platform Ensure. *)
Lemma mutex_accept_modular_save_post : forall environment platform critical saved_local sg
  original call invocation origin eid mask saved before observed,
  mutex_accept_call_binding environment platform original invocation origin ->
  task_tcb_init_stack_same_call call original ->
  valid_stable_glob_vars sg -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before ->
  mutex_accept_handle_protocol critical sg invocation eid ->
  mutex_accept_lookup before eid observed -> observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    UCOS2_inv (task_create_continuation_local saved_local) critical
    (fun _ _ _ => True) sg call mask saved before |--
  EX acquired current,
    coq_prop (mutex_accept_call_acquire_facts critical sg invocation eid mask saved
      before acquired observed current) &&
    (critical_region_masked platform critical sg invocation origin saved acquired **
     UCOS2_inv sg acquired ** mutex_accept_call_support environment saved_local sg original acquired).
Proof.
  intros environment platform critical saved_local sg original call invocation origin eid mask saved
    before observed Hbinding Hsame Hsg Hvalid Hsource Hprotocol Hlookup Htype.
  destruct Hbinding as [Hplatform [Hi Ho]].
  subst platform.
  assert (Hcallsource : kernel_call_task_source call before).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff call original before Hsame)); exact Hsource. }
  unfold kernel_call_modular_save_post; Intros returned acquired.
  destruct H as [Hsave [Hnormal Hrely]].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  pose proof (kernel_call_save_source_preserves_task_source _ _ _ _ _ _ _ _ _ _
    Hvalid Hcallsource Hsave) as Hreturnedsource.
  pose proof Hsame as [Hci [Hco Hcs]].
  rewrite Hci, Hi in Hinterval.
  destruct (critical_region_interval_transports_resources critical sg invocation
    before acquired Hinterval Hvalid) as [Hacquired _].
  destruct (mutex_accept_handle_interval_preserves_identity critical sg invocation eid
    before acquired observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgeneration Hcurrenttype]]].
  assert (Hreturned : task_tcb_init_stack_same_call returned original).
  { destruct (proj1 Hnormal) as [Hri [Hro Hrs]].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Hfacts : mutex_accept_call_acquire_facts critical sg invocation eid mask saved
    before acquired observed current).
  { split.
    - unfold mutex_accept_acquire_facts.
      destruct Hsave as [_ [_ [_ [_ Hsaved]]]].
      split; [exact Hinterval|]; split; [exact Hacquired|]; split; [exact Hsaved|].
      split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
      split; [congruence|exact Hgeneration].
    - eapply mutex_accept_source_current_exists; eassumption. }
  Exists acquired current.
  unfold kernel_continuation_call_masked, kernel_continuation_inv; Intros_p Hcoverage.
  unfold mutex_accept_call_support; Exists returned.
  destruct Hreturned as [Hri [Hro Hrs]].
  rewrite Hri, Hro, Hi, Ho.
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.

Definition mutex_accept_call_return environment platform critical saved_local sg original
  invocation origin mask checkpoint : Assertion :=
  EX current,
    coq_prop (critical_region_interval critical sg invocation checkpoint current) &&
    (mutex_accept_closed platform critical sg invocation origin mask current **
     mutex_accept_call_support environment saved_local sg original current).

Lemma mutex_accept_call_return_refl : forall environment platform critical saved_local sg original
  invocation origin mask state,
  mutex_accept_closed platform critical sg invocation origin mask state **
    mutex_accept_call_support environment saved_local sg original state |--
  mutex_accept_call_return environment platform critical saved_local sg original invocation origin mask state.
Proof.
  intros; unfold mutex_accept_call_return; Exists state.
  assert (Hinterval : critical_region_interval critical sg invocation state state).
  { unfold critical_region_interval; constructor. }
  entailer!.
Qed.

Lemma mutex_accept_modular_restore_pre : forall environment platform critical saved_local sg
  original invocation origin saved acquired checkpoint,
  mutex_accept_call_binding environment platform original invocation origin ->
  critical_region_masked platform critical sg invocation origin saved acquired **
    UCOS2_inv sg checkpoint ** mutex_accept_call_support environment saved_local sg original checkpoint |--
  EX call,
    coq_prop (task_tcb_init_stack_same_call call original) &&
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      UCOS2_inv (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key call) call saved acquired checkpoint.
Proof.
  intros environment platform critical saved_local sg original invocation origin saved acquired checkpoint
    [Hplatform [Hi Ho]].
  subst platform.
  unfold mutex_accept_call_support; Intros call.
  destruct H as [Hsame Hcoverage].
  pose proof Hsame as [Hci [Hco Hcs]].
  Exists call; unfold kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite Hci, Hco, Hi, Ho; entailer!.
Qed.

Lemma mutex_accept_modular_restore_post : forall environment platform critical saved_local sg
  original call invocation origin mask checkpoint,
  mutex_accept_call_binding environment platform original invocation origin ->
  task_tcb_init_stack_same_call call original ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    UCOS2_inv (task_create_continuation_local saved_local) critical
    (fun _ _ _ => True) sg call mask checkpoint |--
  mutex_accept_call_return environment platform critical saved_local sg original
    invocation origin mask checkpoint.
Proof.
  intros environment platform critical saved_local sg original call invocation origin mask checkpoint
    Hbinding Hsame.
  unfold kernel_call_modular_restore_post; Intros returned current.
  destruct H as [Htrace [Hnormal Hrely]].
  assert (Hreturned : task_tcb_init_stack_same_call returned original).
  { destruct (proj1 Hnormal) as [Hri [Hro Hrs]], Hsame as [Hi [Ho Hs]].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Hinterval : critical_region_interval critical sg invocation checkpoint current).
  { pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace))
      as Hinterval.
    rewrite (proj1 Hsame), (proj1 (proj2 Hbinding)) in Hinterval; exact Hinterval. }
  sep_apply_l_atomic (mutex_accept_call_closed_support environment platform critical saved_local sg
    original returned invocation origin mask current Hbinding Hreturned).
  unfold mutex_accept_call_return; Exists current; entailer!.
Qed.
