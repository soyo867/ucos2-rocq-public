Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.sched Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.task.spec.task_suspend_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source variant task-idle-protection: the additional comparison follows
    SELF resolution and precedes the priority-table lookup. On that branch
    the source executes Restore and returns TASK_SUSPEND_IDLE without a
    Scheduler call. This relation ends BEFORE Restore, as does the original
    critical relation. It does not frame an entire interrupted Restore.
    The original pre-Save argument checks and original model are unchanged. *)
Definition task_suspend_idle_guard_critical (sg : StableGlobVars) (prio : Priority)
  : program UCOS2_Verify_State (OSErrCode * bool) :=
  fun entry result post => exists current_id current,
    entry.(SchedState).(curTaskID) = Some current_id /\
    entry.(TskState).(inUsedTaskStates) current_id = Some current /\
    if Z.eqb (fst (task_suspend_selection sg prio current)) sg.(osTaskIdlePrio)
    then result = (OS_ERR_TASK_SUSPEND_IDLE, false) /\ post = entry
    else task_suspend_critical sg prio entry result post.

Lemma task_suspend_idle_guard_idle_result : forall sg prio entry current_id current result post,
  entry.(SchedState).(curTaskID) = Some current_id ->
  entry.(TskState).(inUsedTaskStates) current_id = Some current ->
  fst (task_suspend_selection sg prio current) = sg.(osTaskIdlePrio) ->
  (task_suspend_idle_guard_critical sg prio entry result post <->
   result = (OS_ERR_TASK_SUSPEND_IDLE, false) /\ post = entry).
Proof.
  intros sg prio entry current_id current result post Hcurrent Hnode Hidle; split.
  - intros [other_id [other [Hother [Hlookup Hstep]]]].
    assert (other_id = current_id) by congruence; subst other_id.
    assert (other = current) by congruence; subst other.
    rewrite Hidle, Z.eqb_refl in Hstep; exact Hstep.
  - intro Hpost; exists current_id, current; split; [exact Hcurrent|].
    split; [exact Hnode|]. rewrite Hidle, Z.eqb_refl; exact Hpost.
Qed.

Lemma task_suspend_idle_guard_non_idle_iff : forall sg prio entry current_id current result post,
  entry.(SchedState).(curTaskID) = Some current_id ->
  entry.(TskState).(inUsedTaskStates) current_id = Some current ->
  fst (task_suspend_selection sg prio current) <> sg.(osTaskIdlePrio) ->
  (task_suspend_idle_guard_critical sg prio entry result post <->
   task_suspend_critical sg prio entry result post).
Proof.
  intros sg prio entry current_id current result post Hcurrent Hnode Hidle; split.
  - intros [other_id [other [Hother [Hlookup Hstep]]]].
    assert (other_id = current_id) by congruence; subst other_id.
    assert (other = current) by congruence; subst other.
    rewrite (proj2 (Z.eqb_neq _ _) Hidle) in Hstep; exact Hstep.
  - intro Hpost; exists current_id, current; split; [exact Hcurrent|].
    split; [exact Hnode|]. rewrite (proj2 (Z.eqb_neq _ _) Hidle); exact Hpost.
Qed.

Lemma task_suspend_idle_guard_self_idle : forall sg entry current_id current,
  entry.(SchedState).(curTaskID) = Some current_id ->
  entry.(TskState).(inUsedTaskStates) current_id = Some current ->
  current.(curPrio) = sg.(osTaskIdlePrio) ->
  task_suspend_idle_guard_critical sg sg.(osPrioSelf) entry
    (OS_ERR_TASK_SUSPEND_IDLE, false) entry.
Proof.
  intros; eapply task_suspend_idle_guard_idle_result; try eassumption.
  - rewrite task_suspend_selection_self; exact H1.
  - split; reflexivity.
Qed.

Lemma task_suspend_idle_guard_original_or_unchanged : forall sg prio entry result post,
  task_suspend_idle_guard_critical sg prio entry result post ->
  post = entry \/ task_suspend_critical sg prio entry result post.
Proof.
  intros sg prio entry result post [cid [current [_ [_ Hstep]]]].
  destruct (Z.eqb (fst (task_suspend_selection sg prio current)) sg.(osTaskIdlePrio));
    [left; exact (proj2 Hstep)|right; exact Hstep].
Qed.

(** A table alias cannot bypass the new guard. The current effective
    priority is the minimum of the real aliases; thus an index below Idle
    cannot name an Idle-priority TCB. No no-mutex-owner premise is added. *)
Lemma task_suspend_table_target_non_idle : forall sg entry selected tid node,
  UCOS2_state_inv sg entry -> task_priority_in_range sg selected ->
  selected <> sg.(osTaskIdlePrio) ->
  entry.(TskState).(prioTbl) selected = PTTask tid ->
  entry.(TskState).(inUsedTaskStates) tid = Some node ->
  node.(curPrio) <> sg.(osLowestPrio).
Proof.
  intros sg entry selected tid node Hvalid Hrange Hnonidle Htable Hnode.
  assert (Hsg : valid_stable_glob_vars sg) by (exact (proj1 (proj1 Hvalid))).
  assert (Hidle : sg.(osTaskIdlePrio) = sg.(osLowestPrio)).
  { unfold valid_stable_glob_vars in Hsg; tauto. }
  assert (Haliases : mutex_priority_alias_consistency sg entry.(TskState) entry.(EventState)).
  { destruct Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
    unfold cross_module_consistency, task_mutex_priotbl_consistency in Hcross; tauto. }
  destruct (Haliases tid node Hnode) as [base [_ [[_ Hminimum] _]]].
  pose proof (Hminimum selected (conj Hrange Htable)) as Hle.
  unfold task_priority_in_range in Hrange; rewrite Hidle in Hnonidle; lia.
Qed.

Lemma task_suspend_idle_guard_preserves_idle_ready : forall sg prio entry result post,
  UCOS2_state_inv sg entry -> task_idle_ready sg entry.(TskState) ->
  task_suspend_idle_guard_critical sg prio entry result post ->
  task_idle_ready sg post.(TskState).
Proof.
  intros sg prio entry result post Hvalid Hidle
    [cid [current [Hcurrent [Hnode Hguard]]]].
  destruct (Z.eqb (fst (task_suspend_selection sg prio current)) sg.(osTaskIdlePrio)) eqn:Htest.
  - destruct Hguard as [_ ->]; exact Hidle.
  - apply Z.eqb_neq in Htest.
    destruct Hguard as [other_id [other [Hother [Hlookup [Hrange Hstep]]]]].
    assert (other_id = cid) by congruence; subst other_id.
    assert (other = current) by congruence; subst other.
    destruct (entry.(TskState).(prioTbl) (fst (task_suspend_selection sg prio current)))
      as [| |tid] eqn:Htable.
    + destruct Hstep as [_ ->]; exact Hidle.
    + destruct Hstep as [_ ->]; exact Hidle.
    + destruct Hstep as [node [Htarget [_ ->]]].
      eapply task_update_non_idle_preserves_idle_ready; [exact Htarget| |exact Hidle].
      eapply task_suspend_table_target_non_idle; eassumption.
Qed.

Lemma task_suspend_idle_guard_preserves_validity : forall sg prio entry result post,
  UCOS2_state_inv sg entry -> task_suspend_idle_guard_critical sg prio entry result post ->
  UCOS2_state_inv sg post.
Proof.
  intros; destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ H0) as [->|Hstep];
    [exact H|eapply task_suspend_critical_preserves_validity; eassumption].
Qed.

Definition task_suspend_idle_guard_client (actor : option nat) (prio : Priority)
  : KernelClientAction :=
  {| kernel_client_actor := actor; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       task_suspend_argument_error sg prio = None /\
       exists result, task_suspend_idle_guard_critical sg prio before result after |}.

Lemma task_suspend_idle_guard_client_certificate : forall actor prio,
  KernelClientCertificate (task_suspend_idle_guard_client actor prio).
Proof.
  intros actor prio; constructor.
  - intros sg before after Hvalid [_ [result Hstep]].
    eapply task_suspend_idle_guard_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hstep) as [->|Horiginal];
      [reflexivity|].
    unfold task_creation_frame, task_creation_view.
    rewrite (proj1 (task_suspend_critical_lifecycle_frame _ _ _ _ _ Horiginal)); reflexivity.
  - intros sg before after observer origin Hvalid [_ [result Hstep]] Hnormal Hactive.
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hstep) as [->|Horiginal];
      [exact Hactive|].
    exact (proj2 (task_suspend_critical_lifecycle_frame _ _ _ _ _ Horiginal) observer origin Hactive).
  - intros sg before after observer Hvalid [_ [result Hstep]] Hforeign.
    destruct (task_suspend_idle_guard_original_or_unchanged _ _ _ _ _ Hstep) as [->|Horiginal];
      [reflexivity|].
    rewrite (task_suspend_critical_event_frame _ _ _ _ _ Horiginal); reflexivity.
Qed.

(** A concrete source-client instance for the existing generic transport
    theorem. Other APIs still require their OWN Idle-preservation proof;
    registering this action does not alter the public allowed environment. *)
Lemma task_suspend_idle_guard_client_preserves_resources : forall actor prio,
  kernel_client_preserves_resources
    (fun sg state => UCOS2_state_inv sg state /\ task_idle_ready sg state.(TskState))
    (task_suspend_idle_guard_client actor prio).
Proof.
  intros actor prio sg before after [Hvalid Hidle] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources _
    (task_suspend_idle_guard_client_certificate actor prio) sg before after Hvalid Hstep)
    as [Hafter Hframes].
  split; [split; [exact Hafter|]|exact Hframes].
  destruct Hstep as [_ [result Hcritical]].
  exact (task_suspend_idle_guard_preserves_idle_ready sg prio before result after
    Hvalid Hidle Hcritical).
Qed.
