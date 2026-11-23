Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.lib.atomic_ops_lib Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_publication_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Import UCOS2_C_Rules.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** [idle] is the actual TCB slot published by OS_InitTaskIdle, not a new
    state field. Effective priority alone is not a stable task identity:
    inheritance may change it. The selected empty Idle hook justifies the
    explicit application protocol below; no C rejection or platform fact
    is invented. Both owners AND waiters must exclude that slot. *)
Definition mutex_event_idle_excluded (idle : TaskID) (event : OSEventAbstractState) : Prop :=
  event.(eventType) = OS_EVENT_TYPE_MUTEX ->
    (forall mutex owner, event.(mutexFields) = Some mutex ->
      mutex.(mfOwner) = Some owner -> owner <> idle) /\
    ~ In idle event.(waitList).

Definition mutex_idle_excluded (idle : TaskID) (events : Glob_EventAbstractState) : Prop :=
  forall eid event, events.(inUsedEventStates) eid = Some event ->
    mutex_event_idle_excluded idle event.

Definition mutex_idle_task (sg : StableGlobVars) (tasks : Glob_TaskAbstractState)
  (idle : TaskID) : Prop :=
  exists node, tasks.(inUsedTaskStates) idle = Some node /\
    node.(curPrio) = sg.(osLowestPrio).

(** This excludes only the actual Idle task, not Boot. A task-only Acquire
    or Wait additionally consumes the existing kernel_call_task_source;
    Create/Query/Del and early errors do not gain a new task-call premise. *)
Definition mutex_call_non_idle (idle : TaskID) (origin : TaskInvocationOrigin) : Prop :=
  match origin with BootInvocation => True | RunningInvocation tid _ => tid <> idle end.

(** The first actual Idle publication fixes the last slot of the real
    active list. Later task publication prepends; Mutex updates retain
    this order. Running-state validity already identifies that last TCB
    as lowest-priority, so no extra priority-write restriction is needed. *)
Definition mutex_idle_slot (tasks : Glob_TaskAbstractState) (idle : TaskID) : Prop :=
  exists prefix, tasks.(taskLifecycle).(taskActiveOrder) = prefix ++ [idle].

Lemma task_tcb_init_first_publication_idle_slot :
  forall sg args invocation acquired current slot image,
  current.(TskState).(taskLifecycle).(taskActiveOrder) = [] ->
  mutex_idle_slot
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState) slot.
Proof.
  intros sg args invocation acquired current slot image Hempty; exists [].
  change (slot :: current.(TskState).(taskLifecycle).(taskActiveOrder) = [slot]); rewrite Hempty; reflexivity.
Qed.

Lemma task_commit_preserves_mutex_idle_slot : forall tasks idle p invocation node,
  mutex_idle_slot tasks idle -> mutex_idle_slot (task_commit tasks p invocation node) idle.
Proof.
  intros tasks idle p invocation node [prefix Hprefix]; exists (node.(taskID) :: prefix).
  change (node.(taskID) :: tasks.(taskLifecycle).(taskActiveOrder) = (node.(taskID) :: prefix) ++ [idle]).
  rewrite Hprefix; reflexivity.
Qed.

Lemma task_tcb_init_publication_preserves_mutex_idle_slot :
  forall sg args invocation acquired current slot image idle,
  mutex_idle_slot current.(TskState) idle ->
  mutex_idle_slot
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState) idle.
Proof. intros; apply task_commit_preserves_mutex_idle_slot; assumption. Qed.

Lemma mutex_idle_slot_active_order_frame : forall before after idle,
  after.(taskLifecycle).(taskActiveOrder) = before.(taskLifecycle).(taskActiveOrder) ->
  mutex_idle_slot before idle -> mutex_idle_slot after idle.
Proof. intros before after idle Heq [prefix Hprefix]; exists prefix; congruence. Qed.

Lemma task_update_preserves_mutex_idle_slot : forall tasks idle tid node,
  mutex_idle_slot tasks idle -> mutex_idle_slot (glob_task_set_usedtask tasks tid node) idle.
Proof. intros; exact H. Qed.

Lemma mutex_running_idle_slot_task : forall sg state idle,
  UCOS2_state_inv sg state -> mutex_idle_slot state.(TskState) idle ->
  state.(SchedState).(isRunning) = true -> mutex_idle_task sg state.(TskState) idle.
Proof.
  intros sg state idle [_ [_ [_ [_ [_ [Htail _]]]]]] [prefix Hprefix] Hrunning.
  destruct (Htail Hrunning) as [other_prefix [other [node [Horder [Hnode [Hpriority Hothers]]]]]].
  rewrite Hprefix in Horder; apply app_inj_tail in Horder; destruct Horder as [_ Heq]; subst other.
  exists node; auto.
Qed.

Lemma mutex_idle_excluded_empty : forall idle events,
  (forall eid, events.(inUsedEventStates) eid = None) -> mutex_idle_excluded idle events.
Proof. intros idle events Hempty eid event Hget; rewrite Hempty in Hget; discriminate. Qed.

Lemma mutex_boot_idle_excluded : forall idle sg task_name flag_name memory_name names,
  mutex_idle_excluded idle
    (UCOS2_boot_state sg task_name flag_name memory_name names).(EventState).
Proof. intros; apply mutex_idle_excluded_empty; intros; reflexivity. Qed.

Lemma mutex_idle_excluded_event_map_eq : forall idle before after,
  after.(inUsedEventStates) = before.(inUsedEventStates) ->
  mutex_idle_excluded idle before -> mutex_idle_excluded idle after.
Proof. intros idle before after Heq Huse eid event Hget; rewrite Heq in Hget; eauto. Qed.

Lemma mutex_idle_excluded_update_event : forall idle events eid event,
  mutex_idle_excluded idle events -> mutex_event_idle_excluded idle event ->
  mutex_idle_excluded idle (update_event_field_raw events eid event).
Proof.
  intros idle events eid event Huse Hnew mid found Hget.
  cbn [update_event_field_raw inUsedEventStates] in Hget.
  destruct (Z.eqb mid eid); [injection Hget as <-; exact Hnew|eapply Huse; exact Hget].
Qed.

Lemma mutex_idle_excluded_owner : forall idle events eid event mutex owner,
  mutex_idle_excluded idle events -> events.(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> owner <> idle.
Proof. intros; eapply (proj1 (H eid event H0 H1)); eassumption. Qed.

Lemma mutex_idle_excluded_waiter : forall idle events eid event waiter,
  mutex_idle_excluded idle events -> events.(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> In waiter event.(waitList) -> waiter <> idle.
Proof. intros idle events eid event waiter Huse Hget Htype Hin Heq; subst waiter.
  exact (proj2 (Huse eid event Hget Htype) Hin). Qed.

(** Publication binds the named slot to the actual initialized TCB.
    Existing startup/heap boundaries are unchanged. *)
Lemma task_tcb_init_published_mutex_idle_task : forall sg args invocation acquired current slot image,
  args.(initPrio) = sg.(osLowestPrio) ->
  mutex_idle_task sg
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState) slot.
Proof.
  intros sg args invocation acquired current slot image Hprio.
  exists (task_set_links (task_tcb_init_commit_node args acquired slot image)
    current.(TskState).(tcbListHead) None).
  split.
  - exact (proj1 (task_commit_publication_fields_eq current.(TskState) args.(initPrio)
      invocation (task_tcb_init_commit_node args acquired slot image))).
  - exact Hprio.
Qed.

Lemma mutex_idle_task_base_priority : forall sg tasks idle,
  task_in_range sg tasks -> mutex_idle_task sg tasks idle ->
  task_base_priority sg tasks.(prioTbl) idle sg.(osLowestPrio).
Proof.
  intros sg tasks idle [_ [_ [_ [_ [_ [Hregistered [_ [Hrange _]]]]]]]]
    [node [Hnode Hprio]].
  split.
  - split; [rewrite <- Hprio; eapply Hrange; eassumption|].
    rewrite <- Hprio; eapply Hregistered; eassumption.
  - intros p [Hp _]; exact (proj2 Hp).
Qed.

Lemma mutex_non_idle_priority : forall sg tasks idle tid node,
  task_in_range sg tasks -> mutex_idle_task sg tasks idle ->
  tasks.(inUsedTaskStates) tid = Some node -> tid <> idle ->
  node.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros sg tasks idle tid node [_ [_ [_ [_ [_ [_ [Hunique _]]]]]]]
    [idle_node [Hidle Hprio]] Hnode Hdifferent Heq.
  apply Hdifferent; eapply Hunique; [exact Hnode|exact Hidle|congruence].
Qed.

Lemma mutex_owner_non_idle_priority : forall sg state idle eid event mutex owner node,
  UCOS2_state_inv sg state -> mutex_idle_task sg state.(TskState) idle ->
  mutex_idle_excluded idle state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> state.(TskState).(inUsedTaskStates) owner = Some node ->
  node.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros sg state idle eid event mutex owner node Hvalid Hidle Huse He Htype Hfields Howner Hnode.
  eapply mutex_non_idle_priority; [exact (proj1 (proj2 Hvalid))|exact Hidle|exact Hnode|].
  eapply mutex_idle_excluded_owner; eassumption.
Qed.

Lemma mutex_owner_non_idle_priority_when_running : forall sg state idle eid event mutex owner node,
  UCOS2_state_inv sg state -> mutex_idle_slot state.(TskState) idle ->
  mutex_idle_excluded idle state.(EventState) ->
  state.(EventState).(inUsedEventStates) eid = Some event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  mutex.(mfOwner) = Some owner -> state.(TskState).(inUsedTaskStates) owner = Some node ->
  state.(SchedState).(isRunning) = true -> node.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros; eapply mutex_owner_non_idle_priority; try eassumption.
  eapply mutex_running_idle_slot_task; eassumption.
Qed.

Lemma event_pend_preserves_mutex_idle_slot : forall sg state idle eid event tid node kind timeout,
  mutex_idle_slot state.(TskState) idle ->
  mutex_idle_slot (event_pend_state sg state eid event tid node kind timeout).(TskState) idle.
Proof. intros; exact H. Qed.

Lemma event_wake_preserves_mutex_idle_slot : forall sg state idle eid event tid node kind message result,
  mutex_idle_slot state.(TskState) idle ->
  mutex_idle_slot (event_wake_state sg state eid event tid node kind message result).(TskState) idle.
Proof. intros; exact H. Qed.

Lemma mutex_idle_task_update_other : forall sg tasks idle tid node,
  tid <> idle -> mutex_idle_task sg tasks idle ->
  mutex_idle_task sg (glob_task_set_usedtask tasks tid node) idle.
Proof.
  intros sg tasks idle tid node Hne [old [Hget Hprio]].
  exists old; split; [|exact Hprio].
  assert (Hdifferent : idle <> tid) by congruence.
  cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite (proj2 (Z.eqb_neq idle tid) Hdifferent); exact Hget.
Qed.

Lemma owner_acquire_update_preserves_idle_excluded : forall idle events eid event mutex tid priority,
  events.(inUsedEventStates) eid = Some event -> tid <> idle ->
  mutex_idle_excluded idle events ->
  mutex_idle_excluded idle (owner_acquire_update events eid event mutex tid priority).
Proof.
  intros idle events eid event mutex tid priority Hget Hnonidle Huse.
  apply mutex_idle_excluded_update_event; [exact Huse|].
  intros Htype; split.
  - intros held owner Hfields Howner; injection Hfields as <-; cbn in Howner;
      injection Howner as <-; exact Hnonidle.
  - exact (proj2 (Huse eid event Hget Htype)).
Qed.

Lemma mutex_release_event_preserves_idle_excluded : forall idle before after,
  mutex_release_event_prop before after -> mutex_event_idle_excluded idle after.
Proof.
  intros idle before after (mutex & owner & priority & Htype & Hfields & Howner & Hpriority & Hwait & ->).
  intros _; split; [intros held tid Hfields' Howner'; injection Hfields' as <-; discriminate|simpl; tauto].
Qed.

Lemma mutex_handover_event_preserves_idle_excluded : forall idle before after owner priority,
  mutex_event_idle_excluded idle before ->
  mutex_handover_event_prop before after owner priority -> mutex_event_idle_excluded idle after.
Proof.
  intros idle before after owner priority Huse
    (mutex & old_owner & old_priority & rest & Htype & Hfields & Howner & Hpriority & Hwait & ->).
  destruct (Huse Htype) as [_ Hnone]; rewrite Hwait in Hnone.
  intros _; split.
  - intros held tid Hfields' Howner'; injection Hfields' as <-; cbn in Howner';
      injection Howner' as <-; intro Heq; apply Hnone; left; exact Heq.
  - intros Hin; apply Hnone; right; exact Hin.
Qed.

Lemma event_pend_preserves_idle_excluded : forall idle sg state eid event tid node kind timeout,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  (event.(eventType) = OS_EVENT_TYPE_MUTEX -> tid <> idle) ->
  mutex_idle_excluded idle state.(EventState) ->
  mutex_idle_excluded idle (event_pend_state sg state eid event tid node kind timeout).(EventState).
Proof.
  intros idle sg state eid event tid node kind timeout Hget Hnonidle Huse.
  apply mutex_idle_excluded_update_event; [exact Huse|].
  intros Htype; split.
  - exact (proj1 (Huse eid event Hget Htype)).
  - intro Hin; apply event_insert_waiter_membership in Hin.
    destruct Hin as [Heq|Hin]; [apply (Hnonidle Htype); congruence|exact (proj2 (Huse eid event Hget Htype) Hin)].
Qed.

Lemma event_wake_preserves_idle_excluded : forall idle sg state eid event tid node kind message result,
  state.(EventState).(inUsedEventStates) eid = Some event ->
  mutex_idle_excluded idle state.(EventState) ->
  mutex_idle_excluded idle (event_wake_state sg state eid event tid node kind message result).(EventState).
Proof.
  intros idle sg state eid event tid node kind message result Hget Huse.
  apply mutex_idle_excluded_update_event; [exact Huse|].
  intros Htype; split; [exact (proj1 (Huse eid event Hget Htype))|].
  intro Hin; apply (proj2 (Huse eid event Hget Htype)); eapply remove_Z_eqb_in; exact Hin.
Qed.

Lemma mutex_accept_acquire_preserves_idle_excluded : forall idle state eid event mutex tid priority,
  mutex_accept_lookup state eid event -> tid <> idle -> mutex_idle_excluded idle state.(EventState) ->
  mutex_idle_excluded idle (mutex_accept_owned_state state eid event mutex tid priority).(EventState).
Proof. intros; eapply owner_acquire_update_preserves_idle_excluded; eassumption. Qed.

Lemma mutex_accept_acquire_preserves_idle_task : forall sg idle state eid event mutex tid priority,
  mutex_idle_task sg state.(TskState) idle ->
  mutex_idle_task sg (mutex_accept_owned_state state eid event mutex tid priority).(TskState) idle.
Proof. intros; assumption. Qed.

Lemma mutex_call_source_non_idle : forall idle call state tid,
  kernel_call_task_source call state -> mutex_call_non_idle idle call.(os_sched_call_origin) ->
  state.(SchedState).(curTaskID) = Some tid -> tid <> idle.
Proof.
  intros idle call state tid Hsource Hnonidle Hcurrent.
  destruct (kernel_call_task_source_current_at call state Hsource) as [Hcur [node Hnode]].
  destruct Hsource as [Horigin _]; unfold mutex_call_non_idle in Hnonidle;
    rewrite Horigin in Hnonidle; congruence.
Qed.

Lemma mutex_save_source_non_idle : forall idle external port critical sg original returned mask saved before entry,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  mutex_call_non_idle idle original.(os_sched_call_origin) ->
  kernel_call_save_source external port critical sg original returned mask saved before entry ->
  forall tid, entry.(SchedState).(curTaskID) = Some tid -> tid <> idle.
Proof.
  intros idle external port critical sg original returned mask saved before entry Hvalid Hcaller Hnonidle Hsource tid Hcurrent.
  eapply mutex_call_source_non_idle; [eapply kernel_call_save_source_preserves_task_source; eassumption| |exact Hcurrent].
  destruct Hsource as [_ [_ [Horigin _]]]; rewrite Horigin; exact Hnonidle.
Qed.

Lemma mutex_idle_task_fields_frame : forall sg tasks idle tid old new,
  tasks.(inUsedTaskStates) tid = Some old -> new.(curPrio) = old.(curPrio) ->
  mutex_idle_task sg tasks idle -> mutex_idle_task sg (glob_task_set_usedtask tasks tid new) idle.
Proof.
  intros sg tasks idle tid old new Hold Hpriority [node [Hnode Hlowest]].
  destruct (Z.eq_dec idle tid) as [->|Hdifferent].
  - exists new; split.
    + cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    + assert (node = old) by congruence; subst node; congruence.
  - exists node; split; [|exact Hlowest].
    cbn [glob_task_set_usedtask inUsedTaskStates]; rewrite (proj2 (Z.eqb_neq idle tid) Hdifferent); exact Hnode.
Qed.

Lemma task_commit_preserves_mutex_idle_task : forall sg tasks idle p invocation node,
  tasks.(inUsedTaskStates) node.(taskID) = None -> mutex_idle_task sg tasks idle ->
  mutex_idle_task sg (task_commit tasks p invocation node) idle.
Proof.
  intros sg tasks idle p invocation node Hfresh [old [Hold Hprio]].
  destruct (task_commit_transports_old_fields tasks p invocation node idle old Hfresh Hold)
    as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|].
  pose proof (f_equal curPrio Hfields) as Hpriority; cbn [task_set_links curPrio] in Hpriority; congruence.
Qed.

Lemma task_tcb_init_publication_preserves_mutex_idle_task :
  forall sg args invocation origin acquired current slot image idle,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  mutex_idle_task sg current.(TskState) idle ->
  mutex_idle_task sg
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState) idle.
Proof.
  intros sg args invocation origin acquired current slot image idle Hvalid Hbinding Hidle.
  pose proof (task_tcb_init_commit_binding_identity args invocation origin
    acquired current slot image Hbinding) as Hidentity.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  destruct (task_private_excludes_public sg current.(TskState) slot
    (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hfresh _].
  apply task_commit_preserves_mutex_idle_task; assumption.
Qed.

Lemma event_pend_preserves_mutex_idle_task : forall sg state idle eid event tid node kind timeout,
  state.(TskState).(inUsedTaskStates) tid = Some node -> mutex_idle_task sg state.(TskState) idle ->
  mutex_idle_task sg (event_pend_state sg state eid event tid node kind timeout).(TskState) idle.
Proof. intros; eapply mutex_idle_task_fields_frame; [eassumption|reflexivity|eassumption]. Qed.

Lemma event_wake_preserves_mutex_idle_task : forall sg state idle eid event tid node kind message result,
  state.(TskState).(inUsedTaskStates) tid = Some node -> mutex_idle_task sg state.(TskState) idle ->
  mutex_idle_task sg (event_wake_state sg state eid event tid node kind message result).(TskState) idle.
Proof. intros; eapply mutex_idle_task_fields_frame; [eassumption|reflexivity|eassumption]. Qed.

(** All protected return values are retained, including acquisition followed
    by OS_ERR_PCP_LOWER. The caller identity is consumed only in the branch
    that actually reads OSTCBCur and writes the owner. *)
Lemma mutex_accept_protected_result_preserves_idle_excluded :
  forall sg idle eid entry event code value after,
  mutex_idle_excluded idle entry.(EventState) -> mutex_accept_lookup entry eid event ->
  (forall tid, entry.(SchedState).(curTaskID) = Some tid -> tid <> idle) ->
  mutex_accept_protected_result sg eid entry event code value after ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros sg idle eid entry event code value after Hidle Hlookup Hcaller
    [mutex [Hfields [[Hbusy [Hcode [Hvalue ->]]]|[Hfree [tid [node [Hcurrent [Hnode [Hvalue [-> Hcode]]]]]]]]]].
  - exact Hidle.
  - eapply mutex_accept_acquire_preserves_idle_excluded; [exact Hlookup|eapply Hcaller; exact Hcurrent|exact Hidle].
Qed.

Lemma mutex_accept_source_result_preserves_idle_excluded :
  forall idle external port critical sg original returned mask saved before entry eid event code value after,
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  mutex_call_non_idle idle original.(os_sched_call_origin) ->
  kernel_call_save_source external port critical sg original returned mask saved before entry ->
  mutex_idle_excluded idle entry.(EventState) -> mutex_accept_lookup entry eid event ->
  mutex_accept_protected_result sg eid entry event code value after ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros; eapply mutex_accept_protected_result_preserves_idle_excluded; try eassumption.
  eapply mutex_save_source_non_idle; eassumption.
Qed.

Lemma mutex_event_fields_preserve_idle_excluded : forall idle before after,
  after.(eventType) = before.(eventType) -> after.(mutexFields) = before.(mutexFields) ->
  (forall tid, In tid after.(waitList) -> In tid before.(waitList)) ->
  mutex_event_idle_excluded idle before -> mutex_event_idle_excluded idle after.
Proof.
  intros idle before after Htype Hfields Hsubset Huse Hmutex.
  destruct (Huse ltac:(congruence)) as [Howner Hwait]; split.
  - intros fields owner Hlookup Howned; eapply Howner; [rewrite <- Hfields; exact Hlookup|exact Howned].
  - intro Hin; apply Hwait; apply Hsubset; exact Hin.
Qed.

Lemma atomic_mutex_acquire_preserves_idle_excluded : forall idle eid tid priority before after,
  tid <> idle -> atomic_mutex_acquire eid tid priority before tt after ->
  mutex_idle_excluded idle before.(EventState) -> mutex_idle_excluded idle after.(EventState).
Proof.
  intros idle eid tid priority before after Hnonidle Hstep Huse.
  destruct Hstep as (event & acquired & mutex & owned & node & He & Htype & Hfields & Hfree &
    Hcur & Hnode & Hpriority & Hready & -> & -> & ->).
  eapply owner_acquire_update_preserves_idle_excluded; eassumption.
Qed.

Lemma atomic_mutex_release_preserves_idle_excluded : forall idle sg eid before after,
  atomic_mutex_release sg eid before tt after -> mutex_idle_excluded idle before.(EventState) ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros idle sg eid before after Hstep Huse.
  destruct Hstep as (event & released & mutex & empty & owner & events & tasks &
    He & Htype & Hfields & Hwait & Howner & -> & -> & -> & -> & ->).
  apply mutex_idle_excluded_update_event; [exact Huse|].
  intros _; split.
  - intros held tid Hfields' Howner'; injection Hfields' as <-; discriminate.
  - change (~ In idle event.(waitList)); rewrite Hwait; simpl; tauto.
Qed.

Lemma atomic_mutex_handover_preserves_idle_excluded : forall idle sg eid before tid after,
  atomic_mutex_release_with_handover sg eid before tid after ->
  mutex_idle_excluded idle before.(EventState) -> mutex_idle_excluded idle after.(EventState).
Proof.
  intros idle sg eid before tid after Hstep Huse.
  destruct Hstep as (event & handed & mutex & owned & owner & old & awakened & events & tasks &
    scheduler & scheduled & ready & rest & He & Htype & Hfields & Howner & Hwait & Hold &
    Hawakened & Howned & Hhanded & Hevents & Hscheduler & Hready & Hscheduled & Htasks & Hafter).
  pose proof (proj2 (Huse eid event He Htype)) as Hnone; rewrite Hwait in Hnone.
  subst after tasks scheduled ready scheduler events handed owned awakened.
  apply mutex_idle_excluded_update_event; [exact Huse|].
  intros _; split.
  - intros held new_owner Hfields' Howner'; injection Hfields' as <-; cbn in Howner';
      injection Howner' as <-; intro Heq; apply Hnone; left; exact Heq.
  - intro Hin; apply Hnone; right; exact Hin.
Qed.

Lemma task_creation_preserves_mutex_idle_excluded : forall idle action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  mutex_idle_excluded idle before.(EventState) -> mutex_idle_excluded idle after.(EventState).
Proof. intros idle action sg before after [_ [_ ->]] Huse; destruct action; exact Huse. Qed.

Lemma task_stack_publication_preserves_mutex_idle_excluded : forall idle sg publication before after,
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  mutex_idle_excluded idle before.(EventState) -> mutex_idle_excluded idle after.(EventState).
Proof. intros idle sg publication before after [_ ->] Huse; exact Huse. Qed.

Lemma mutex_create_publication_preserves_idle_excluded : forall idle sg pcp before result after,
  MutexCreatePublication.critical_operation sg pcp before result after ->
  mutex_idle_excluded idle before.(EventState) -> mutex_idle_excluded idle after.(EventState).
Proof.
  intros idle sg pcp before result after.
  unfold MutexCreatePublication.critical_operation.
  destruct (MutexCreateCall.priority_slot_busy sg pcp before).
  - intros [_ ->] Huse; exact Huse.
  - destruct before.(EventState).(unUsedEventStates) as [|created rest].
    + intros [_ ->] Huse; exact Huse.
    + intros [_ ->] Huse eid event Hget Htype.
      unfold mutex_create_state, mutex_create_event_state, event_publish in Hget;
        cbn [replace_EventS replace_TskS EventState inUsedEventStates] in Hget.
      unfold kernel_map_set in Hget; destruct (Z.eq_dec eid created).
      * injection Hget as <-; split.
        -- intros held tid Hfields Howner; injection Hfields as <-; discriminate.
        -- simpl; tauto.
      * exact (Huse eid event Hget Htype).
Qed.

Lemma mutex_del_recycle_preserves_idle_excluded : forall idle sg eid event state,
  mutex_idle_excluded idle state.(EventState) ->
  mutex_idle_excluded idle (mutex_del_recycle_state sg eid event state).(EventState).
Proof.
  intros idle sg eid event state Huse mid found Hget.
  cbn [mutex_del_recycle_state replace_EventS EventState event_recycle inUsedEventStates] in Hget.
  unfold kernel_map_set in Hget; destruct (Z.eq_dec mid eid); [discriminate|eapply Huse; eassumption].
Qed.

Lemma event_allocation_preserves_mutex_idle_excluded : forall idle before result after,
  event_create_allocate_critical before result after -> mutex_idle_excluded idle before.(EventState) ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros idle before result after Hstep Huse; unfold event_create_allocate_critical in Hstep.
  destruct before.(EventState).(unUsedEventStates).
  - destruct Hstep as [_ ->]; exact Huse.
  - destruct Hstep as [image [_ [_ ->]]]; exact Huse.
Qed.

Lemma event_private_stores_preserve_mutex_idle_excluded : forall idle eid writes before result after,
  event_create_private_stores eid writes before result after -> mutex_idle_excluded idle before.(EventState) ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros idle eid writes before result after Hstep Huse.
  destruct (event_create_private_stores_published_frame eid writes before result after Hstep) as [Hevents _].
  eapply mutex_idle_excluded_event_map_eq; eassumption.
Qed.

Lemma mutex_creator_publication_preserves_idle_excluded : forall idle creator state eid allocation,
  mutex_idle_excluded idle state.(EventState) ->
  mutex_idle_excluded idle (mutex_del_creator_published_state creator state eid allocation).(EventState).
Proof.
  intros idle creator state eid allocation Huse mid event Hget Htype.
  unfold mutex_del_creator_published_state in Hget;
    cbn [replace_EventS EventState event_publish inUsedEventStates] in Hget.
  unfold kernel_map_set in Hget; destruct (Z.eq_dec mid eid).
  - injection Hget as <-; destruct creator; discriminate Htype.
  - exact (Huse mid event Hget Htype).
Qed.

Lemma mutex_creator_effect_preserves_idle_excluded : forall idle creator sg cut state next returned,
  mutex_del_creator_publication_effect creator sg cut state next returned ->
  mutex_idle_excluded idle state.(EventState) -> mutex_idle_excluded idle returned.(EventState).
Proof.
  intros idle creator sg cut state next returned Hstep Huse; destruct Hstep.
  - destruct H; eapply event_allocation_preserves_mutex_idle_excluded; eassumption.
  - apply mutex_creator_publication_preserves_idle_excluded.
    eapply event_private_stores_preserve_mutex_idle_excluded; eassumption.
Qed.

Lemma mutex_creator_source_preserves_idle_excluded : forall idle creator sg cut state next returned,
  kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  mutex_idle_excluded idle state.(EventState) -> mutex_idle_excluded idle returned.(EventState).
Proof.
  intros idle creator sg cut state next returned Hstep Huse; destruct Hstep.
  - exact Huse.
  - exact Huse.
  - eapply task_stack_publication_preserves_mutex_idle_excluded; [split; [exact H|reflexivity]|exact Huse].
  - eapply mutex_creator_effect_preserves_idle_excluded; eassumption.
Qed.

(** Add admission to the ACTUAL existing source proof, not to its desired
    poststate. Field-only Event edits may remove/reorder existing waiters;
    insertion is the existing Wait constructor, where the caller is checked.
    Other lifecycle/IRQ/cleanup steps retain their original broad domains. *)
Inductive mutex_idle_source_calls (sg : StableGlobVars) (idle : TaskID) :
  forall before after, mutex_owner_source_step sg before after -> Prop :=
| MutexIdleCallsFrame : forall before after Htasks Hevents,
    after.(TskState).(taskLifecycle).(taskActiveOrder) = before.(TskState).(taskLifecycle).(taskActiveOrder) ->
    mutex_idle_source_calls sg idle before after (MutexOwnerSourceFrame sg before after Htasks Hevents)
| MutexIdleCallsTaskField : forall before after tid old new Hget Hptr Hmulti Htasks Hevents,
    mutex_idle_source_calls sg idle before after
      (MutexOwnerSourceTaskField sg before after tid old new Hget Hptr Hmulti Htasks Hevents)
| MutexIdleCallsEventField : forall before after eid old new Hget Htype Hfields Hevents Htasks,
    (forall tid, In tid new.(waitList) -> In tid old.(waitList)) ->
    mutex_idle_source_calls sg idle before after
      (MutexOwnerSourceEventField sg before after eid old new Hget Htype Hfields Hevents Htasks)
| MutexIdleCallsTaskLifecycle : forall before after action Hstep,
    mutex_idle_source_calls sg idle before after (MutexOwnerSourceTaskLifecycle sg before after action Hstep)
| MutexIdleCallsTaskPublication : forall before after publication Hstep,
    mutex_idle_source_calls sg idle before after
      (MutexOwnerSourceTaskPublication sg before after publication Hstep)
| MutexIdleCallsCreate : forall before after pcp result Hstep,
    mutex_idle_source_calls sg idle before after (MutexOwnerSourceCreate sg before after pcp result Hstep)
| MutexIdleCallsAcquire : forall before after eid tid priority Hcall Hstep,
    tid <> idle -> mutex_idle_source_calls sg idle before after
      (MutexOwnerSourceAcquire sg before after eid tid priority Hcall Hstep)
| MutexIdleCallsWait : forall before eid event tid old kind timeout Hget Hnoowner,
    (event.(eventType) = OS_EVENT_TYPE_MUTEX -> tid <> idle) ->
    mutex_idle_source_calls sg idle before (event_pend_state sg before eid event tid old kind timeout)
      (MutexOwnerSourceWait sg before eid event tid old kind timeout Hget Hnoowner)
| MutexIdleCallsWake : forall before eid event tid old kind message result Hget Hnode,
    mutex_idle_source_calls sg idle before (event_wake_state sg before eid event tid old kind message result)
      (MutexOwnerSourceWake sg before eid event tid old kind message result Hget Hnode)
| MutexIdleCallsCleanup : forall before tid old multi clear_message Hget,
    mutex_idle_source_calls sg idle before
      (replace_TskS (glob_task_set_usedtask before.(TskState) tid
        (task_event_pend_cleanup multi clear_message old)) before)
      (MutexOwnerSourceCleanup sg before tid old multi clear_message Hget)
| MutexIdleCallsRelease : forall before after eid Hstep,
    mutex_idle_source_calls sg idle before after (MutexOwnerSourceRelease sg before after eid Hstep)
| MutexIdleCallsHandover : forall before after eid tid Hvalid Hstep,
    mutex_idle_source_calls sg idle before after (MutexOwnerSourceHandover sg before after eid tid Hvalid Hstep)
| MutexIdleCallsPrepare : forall before after mutex Hstep,
    mutex_idle_source_calls sg idle before after (MutexOwnerSourcePrepare sg before after mutex Hstep)
| MutexIdleCallsRecycle : forall before eid event,
    mutex_idle_source_calls sg idle before (mutex_del_recycle_state sg eid event before)
      (MutexOwnerSourceRecycle sg before eid event)
| MutexIdleCallsCreator : forall creator cut before next after Hstep,
    mutex_idle_source_calls sg idle before after (MutexOwnerSourceCreator sg creator cut before next after Hstep)
| MutexIdleCallsNonMutexPublication : forall before eid event Htype,
    mutex_idle_source_calls sg idle before (replace_EventS (event_publish before.(EventState) eid event) before)
      (MutexOwnerSourceNonMutexPublication sg before eid event Htype).

Arguments mutex_idle_source_calls {sg} idle {before after} _.

Lemma mutex_owner_source_preserves_idle_excluded : forall sg idle before after
  (source : mutex_owner_source_step sg before after),
  mutex_idle_source_calls idle source -> mutex_idle_excluded idle before.(EventState) ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros sg idle before after source Hcalls Huse.
  destruct Hcalls as
    [before after Htasks Hevents Horder
    |before after tid old new Hget Hptr Hmulti Htasks Hevents
    |before after eid old new Hget Htype Hfields Hevents Htasks Hsubset
    |before after action Hstep|before after publication Hstep|before after pcp result Hstep
    |before after eid tid priority Hcall Hstep Hnonidle
    |before eid event tid old kind timeout Hget Hnoowner Hnonidle
    |before eid event tid old kind message result Hget Hnode
    |before tid old multi clear_message Hget
    |before after eid Hstep|before after eid tid Hvalid Hstep|before after mutex Hstep
    |before eid event|creator cut before next after Hstep|before eid event Htype].
  - eapply mutex_idle_excluded_event_map_eq; eassumption.
  - rewrite Hevents; exact Huse.
  - rewrite Hevents; apply mutex_idle_excluded_update_event; [exact Huse|].
    eapply mutex_event_fields_preserve_idle_excluded; [exact Htype|exact Hfields|exact Hsubset|eapply Huse; exact Hget].
  - eapply task_creation_preserves_mutex_idle_excluded; eassumption.
  - eapply task_stack_publication_preserves_mutex_idle_excluded; eassumption.
  - eapply mutex_create_publication_preserves_idle_excluded; eassumption.
  - eapply atomic_mutex_acquire_preserves_idle_excluded; eassumption.
  - eapply event_pend_preserves_idle_excluded; eassumption.
  - eapply event_wake_preserves_idle_excluded; eassumption.
  - exact Huse.
  - eapply atomic_mutex_release_preserves_idle_excluded; eassumption.
  - eapply atomic_mutex_handover_preserves_idle_excluded; eassumption.
  - rewrite (mutex_del_prepare_event_state_eq sg mutex before after Hstep); exact Huse.
  - apply mutex_del_recycle_preserves_idle_excluded; exact Huse.
  - eapply mutex_creator_source_preserves_idle_excluded; eassumption.
  - intros mid found Hget Hfound_type.
    cbn [replace_EventS EventState event_publish inUsedEventStates] in Hget.
    unfold kernel_map_set in Hget; destruct (Z.eq_dec mid eid).
    + injection Hget as <-; contradiction.
    + exact (Huse mid found Hget Hfound_type).
Qed.

Lemma task_creation_preserves_mutex_idle_slot : forall idle action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_slot after.(TskState) idle.
Proof.
  intros idle action sg before after [_ [_ ->]] Hslot; destruct action; try exact Hslot.
  apply task_commit_preserves_mutex_idle_slot; exact Hslot.
Qed.

Lemma task_stack_publication_preserves_mutex_idle_slot : forall idle sg publication before after,
  kernel_client_step (task_create_stack_publication_client publication) sg before after ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_slot after.(TskState) idle.
Proof.
  intros idle sg publication before after [_ ->] Hslot.
  apply task_tcb_init_publication_preserves_mutex_idle_slot; exact Hslot.
Qed.

Lemma mutex_create_publication_preserves_idle_slot : forall idle sg pcp before result after,
  MutexCreatePublication.critical_operation sg pcp before result after ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_slot after.(TskState) idle.
Proof.
  intros idle sg pcp before result after Hstep Hslot.
  unfold MutexCreatePublication.critical_operation in Hstep.
  destruct (MutexCreateCall.priority_slot_busy sg pcp before).
  - destruct Hstep as [_ ->]; exact Hslot.
  - destruct before.(EventState).(unUsedEventStates) as [|created rest];
      destruct Hstep as [_ ->]; exact Hslot.
Qed.

Lemma mutex_del_prepare_preserves_idle_slot : forall idle sg mutex before after,
  mutex_del_prepare sg mutex before after ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_slot after.(TskState) idle.
Proof.
  intros idle sg mutex before after Hstep Hslot; unfold mutex_del_prepare in Hstep.
  destruct (Z.eq_dec mutex.(mfPCP) sg.(osPrioMutexCeilDis)); [subst; exact Hslot|].
  destruct mutex.(mfOwner) as [owner|]; [|subst; exact Hslot].
  destruct Hstep as [node [priority [_ [_ ->]]]].
  unfold mutex_del_owner_priority_state; destruct (Z.eq_dec node.(curPrio) priority); exact Hslot.
Qed.

Lemma mutex_creator_effect_preserves_idle_slot : forall idle creator sg cut state next returned,
  mutex_del_creator_publication_effect creator sg cut state next returned ->
  mutex_idle_slot state.(TskState) idle -> mutex_idle_slot returned.(TskState) idle.
Proof.
  intros idle creator sg cut state next returned Hstep Hslot; destruct Hstep.
  - assert (Hallocate : forall before result after,
        event_create_allocate_critical before result after ->
        mutex_idle_slot before.(TskState) idle -> mutex_idle_slot after.(TskState) idle).
    { intros before result after Hallocate Hbefore.
      unfold event_create_allocate_critical in Hallocate.
      destruct before.(EventState).(unUsedEventStates).
      - destruct Hallocate as [_ ->]; exact Hbefore.
      - destruct Hallocate as [image [_ [_ ->]]]; exact Hbefore. }
    destruct H; eapply Hallocate; eassumption.
  - change (mutex_idle_slot initialized.(TskState) idle).
    destruct (event_create_private_stores_published_frame _ _ _ _ _ H1) as [_ [_ [Htasks _]]].
    unfold mutex_idle_slot in *; rewrite Htasks; exact Hslot.
Qed.

Lemma mutex_creator_source_preserves_idle_slot : forall idle creator sg cut state next returned,
  kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  mutex_idle_slot state.(TskState) idle -> mutex_idle_slot returned.(TskState) idle.
Proof.
  intros idle creator sg cut state next returned Hstep Hslot; destruct Hstep; try exact Hslot.
  - eapply task_stack_publication_preserves_mutex_idle_slot; [split; [exact H|reflexivity]|exact Hslot].
  - eapply mutex_creator_effect_preserves_idle_slot; eassumption.
Qed.

Lemma mutex_owner_source_preserves_idle_slot : forall sg idle before after
  (source : mutex_owner_source_step sg before after),
  mutex_idle_source_calls idle source -> mutex_idle_slot before.(TskState) idle ->
  mutex_idle_slot after.(TskState) idle.
Proof.
  intros sg idle before after source Hcalls Hslot.
  destruct Hcalls as
    [before after Htasks Hevents Horder
    |before after tid old new Hget Hptr Hmulti Htasks Hevents
    |before after eid old new Hget Htype Hfields Hevents Htasks Hsubset
    |before after action Hstep|before after publication Hstep|before after pcp result Hstep
    |before after eid tid priority Hcall Hstep Hnonidle
    |before eid event tid old kind timeout Hget Hnoowner Hnonidle
    |before eid event tid old kind message result Hget Hnode
    |before tid old multi clear_message Hget
    |before after eid Hstep|before after eid tid Hvalid Hstep|before after mutex Hstep
    |before eid event|creator cut before next after Hstep|before eid event Htype].
  - eapply mutex_idle_slot_active_order_frame; eassumption.
  - rewrite Htasks; exact Hslot.
  - rewrite Htasks; exact Hslot.
  - eapply task_creation_preserves_mutex_idle_slot; eassumption.
  - eapply task_stack_publication_preserves_mutex_idle_slot; eassumption.
  - eapply mutex_create_publication_preserves_idle_slot; eassumption.
  - destruct Hstep as (event & acquired & mutex & owned & node & He & Htype & Hfields & Hfree &
      Hcur & Hnode & Hpriority & Hready & -> & -> & ->); exact Hslot.
  - exact Hslot.
  - exact Hslot.
  - exact Hslot.
  - destruct Hstep as (event & released & mutex & empty & owner & events & tasks &
      He & Htype & Hfields & Hwait & Howner & -> & -> & -> & -> & ->); exact Hslot.
  - destruct Hstep as (event & handed & mutex & owned & owner & old & awakened & events & tasks &
      scheduler & scheduled & ready & rest & He & Htype & Hfields & Howner & Hwait & Hold &
      Hawakened & Howned & Hhanded & Hevents & Hscheduler & Hready & Hscheduled & Htasks & Hafter).
    subst after tasks scheduled ready scheduler events handed owned awakened; exact Hslot.
  - eapply mutex_del_prepare_preserves_idle_slot; eassumption.
  - exact Hslot.
  - eapply mutex_creator_source_preserves_idle_slot; eassumption.
  - exact Hslot.
Qed.

(** Accept has a broader native input domain than atomic_mutex_acquire:
    it does not test ready/nonwaiting bits. Its adapter below uses its
    already checked exact Event-only transformer, without those guards. *)
Inductive mutex_idle_source_step (sg : StableGlobVars) (idle : TaskID) :
  UCOS2_Verify_State -> UCOS2_Verify_State -> Prop :=
| MutexIdleExistingSource : forall before after (source : mutex_owner_source_step sg before after),
    mutex_idle_source_calls idle source -> mutex_idle_source_step sg idle before after
| MutexIdleAcceptAcquire : forall before eid event mutex tid priority,
    mutex_accept_lookup before eid event -> tid <> idle ->
    mutex_idle_source_step sg idle before (mutex_accept_owned_state before eid event mutex tid priority)
| MutexIdlePendWait : forall before eid event tid node kind timeout,
    before.(EventState).(inUsedEventStates) eid = Some event ->
    (event.(eventType) = OS_EVENT_TYPE_MUTEX -> tid <> idle) ->
    mutex_idle_source_step sg idle before (event_pend_state sg before eid event tid node kind timeout).

Definition mutex_idle_source_history sg idle :=
  clos_refl_trans UCOS2_Verify_State (mutex_idle_source_step sg idle).

Lemma mutex_idle_source_step_preserves_exclusion : forall sg idle before after,
  mutex_idle_source_step sg idle before after -> mutex_idle_excluded idle before.(EventState) ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros sg idle before after Hsource Huse; destruct Hsource.
  - eapply mutex_owner_source_preserves_idle_excluded; eassumption.
  - eapply mutex_accept_acquire_preserves_idle_excluded; eassumption.
  - eapply event_pend_preserves_idle_excluded; eassumption.
Qed.

Lemma mutex_idle_source_history_preserves_exclusion : forall sg idle before after,
  mutex_idle_source_history sg idle before after -> mutex_idle_excluded idle before.(EventState) ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros sg idle before after Hhistory; induction Hhistory; intros Huse.
  - eapply mutex_idle_source_step_preserves_exclusion; eassumption.
  - exact Huse.
  - apply IHHhistory2; apply IHHhistory1; exact Huse.
Qed.

Lemma mutex_idle_source_history_preserves_slot : forall sg idle before after,
  mutex_idle_source_history sg idle before after -> mutex_idle_slot before.(TskState) idle ->
  mutex_idle_slot after.(TskState) idle.
Proof.
  intros sg idle before after Hhistory; induction Hhistory; intros Hslot.
  - destruct H; try exact Hslot; eapply mutex_owner_source_preserves_idle_slot; eassumption.
  - exact Hslot.
  - apply IHHhistory2; apply IHHhistory1; exact Hslot.
Qed.

Lemma mutex_idle_source_history_establishes_exclusion : forall sg idle task_name flag_name memory_name names state,
  mutex_idle_source_history sg idle (UCOS2_boot_state sg task_name flag_name memory_name names) state ->
  mutex_idle_excluded idle state.(EventState).
Proof. intros; eapply mutex_idle_source_history_preserves_exclusion; [eassumption|apply mutex_boot_idle_excluded]. Qed.

Definition mutex_idle_region_source_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (idle : TaskID) : Prop :=
  forall action before after,
    critical.(critical_region_clients) action -> UCOS2_state_inv sg before ->
    kernel_client_step action sg before after -> mutex_idle_source_history sg idle before after.

Lemma mutex_idle_region_interval_history : forall critical sg idle invocation before after,
  mutex_idle_region_source_protocol critical sg idle -> UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before after ->
  mutex_idle_source_history sg idle before after.
Proof.
  intros critical sg idle invocation before after Hprotocol Hvalid Hinterval.
  pose proof (critical_region_interval_raw_trace critical sg invocation before after Hinterval) as Htrace.
  clear Hinterval; revert Hvalid; induction Htrace; intros Hvalid.
  - apply rt_refl.
  - eapply rt_trans; [eapply Hprotocol; eassumption|].
    apply IHHtrace; exact (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action H) sg before middle Hvalid H2).
Qed.

Lemma mutex_idle_region_interval_preserves_exclusion : forall critical sg idle invocation before after,
  mutex_idle_region_source_protocol critical sg idle -> UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before after ->
  mutex_idle_excluded idle before.(EventState) -> mutex_idle_excluded idle after.(EventState).
Proof. intros; eapply mutex_idle_source_history_preserves_exclusion; [eapply mutex_idle_region_interval_history; eassumption|eassumption]. Qed.

Lemma mutex_idle_region_interval_preserves_slot : forall critical sg idle invocation before after,
  mutex_idle_region_source_protocol critical sg idle -> UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before after ->
  mutex_idle_slot before.(TskState) idle -> mutex_idle_slot after.(TskState) idle.
Proof. intros; eapply mutex_idle_source_history_preserves_slot; [eapply mutex_idle_region_interval_history; eassumption|eassumption]. Qed.

Lemma mutex_accept_source_result_idle_consequence :
  forall idle external port critical sg original returned mask saved before entry eid event code value after,
  mutex_idle_region_source_protocol critical sg idle ->
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  mutex_call_non_idle idle original.(os_sched_call_origin) -> mutex_idle_excluded idle before.(EventState) ->
  kernel_call_save_source external port critical sg original returned mask saved before entry ->
  mutex_accept_lookup entry eid event ->
  mutex_accept_protected_result sg eid entry event code value after ->
  mutex_idle_excluded idle after.(EventState).
Proof.
  intros; eapply mutex_accept_source_result_preserves_idle_excluded; try eassumption.
  eapply mutex_idle_region_interval_preserves_exclusion; try eassumption.
  eapply kernel_call_save_source_region_interval; eassumption.
Qed.

(** The extra public calling obligation is ordered by the actual guards.
    NULL/type/free-slot/ISR errors remain in the original C domain. *)
Definition mutex_accept_idle_admission (idle : TaskID) (call : OsSchedCallContext)
  (pe : Z) (before : UCOS2_Verify_State) (eid : EventID) : Prop :=
  pe <> 0 -> event_slot_type_value before.(EventState) eid = 4 ->
  before.(IntrState).(intNesting) <= 0 -> mutex_call_non_idle idle call.(os_sched_call_origin).

(** Source-connected heap consequence at the SAME Save return used by the
    complete checked API. The platform contract is unchanged: registered
    source identity and the admitted source history supply the new facts. *)
Lemma mutex_accept_modular_save_post_idle : forall idle environment platform critical saved_local sg
  original call invocation origin eid mask saved before observed,
  mutex_accept_call_binding environment platform original invocation origin ->
  task_tcb_init_stack_same_call call original ->
  valid_stable_glob_vars sg -> UCOS2_state_inv sg before ->
  kernel_call_task_source original before -> mutex_call_non_idle idle original.(os_sched_call_origin) ->
  mutex_idle_region_source_protocol critical sg idle -> mutex_idle_excluded idle before.(EventState) ->
  mutex_accept_handle_protocol critical sg invocation eid ->
  mutex_accept_lookup before eid observed -> observed.(eventType) = OS_EVENT_TYPE_MUTEX ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    UCOS2_inv (task_create_continuation_local saved_local) critical
    (fun _ _ _ => True) sg call mask saved before |--
  EX acquired current,
    coq_prop (mutex_accept_call_acquire_facts critical sg invocation eid mask saved
      before acquired observed current /\ mutex_idle_excluded idle acquired.(EventState) /\
      (forall tid, acquired.(SchedState).(curTaskID) = Some tid -> tid <> idle)) &&
    (critical_region_masked platform critical sg invocation origin saved acquired **
     UCOS2_inv sg acquired ** mutex_accept_call_support environment saved_local sg original acquired).
Proof.
  intros idle environment platform critical saved_local sg original call invocation origin eid mask saved
    before observed Hbinding Hsame Hsg Hvalid Hsource Hnonidle Hidle_protocol Hidle Hprotocol Hlookup Htype.
  destruct Hbinding as [Hplatform [Hi Ho]]; subst platform.
  assert (Hcallsource : kernel_call_task_source call before).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff call original before Hsame)); exact Hsource. }
  unfold kernel_call_modular_save_post; Intros returned acquired.
  destruct H as [Hsave [Hnormal Hrely]].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  pose proof (kernel_call_save_source_preserves_task_source _ _ _ _ _ _ _ _ _ _
    Hvalid Hcallsource Hsave) as Hreturnedsource.
  pose proof Hsame as [Hci [Hco Hcs]].
  assert (Hcurrent_nonidle : forall tid, acquired.(SchedState).(curTaskID) = Some tid -> tid <> idle).
  { eapply mutex_save_source_non_idle; [exact Hvalid|exact Hcallsource| |exact Hsave].
    rewrite Hco; exact Hnonidle. }
  rewrite Hci, Hi in Hinterval.
  assert (Hacquired_idle : mutex_idle_excluded idle acquired.(EventState)).
  { eapply mutex_idle_region_interval_preserves_exclusion; eassumption. }
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
    - unfold mutex_accept_acquire_facts; destruct Hsave as [_ [_ [_ [_ Hsaved]]]].
      split; [exact Hinterval|]; split; [exact Hacquired|]; split; [exact Hsaved|].
      split; [exact Hlookup|]; split; [exact Hcurrent|]; split; [exact Htype|].
      split; [congruence|exact Hgeneration].
    - eapply mutex_accept_source_current_exists; eassumption. }
  Exists acquired current.
  unfold kernel_continuation_call_masked, kernel_continuation_inv; Intros_p Hcoverage.
  unfold mutex_accept_call_support; Exists returned.
  destruct Hreturned as [Hri [Hro Hrs]]; rewrite Hri, Hro, Hi, Ho.
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.
