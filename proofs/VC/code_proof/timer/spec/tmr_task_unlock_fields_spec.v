Require Export Ucos2Verify.VC.code.sched.spec.sched_fields_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fields_callback_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Export Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.lib.kernel_client_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Ucos2Verify.lib.sched.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** This is the current OSTmr_Task call domain. It is a specialization of
    the unchanged Unlock body, not a replacement for the generic public
    API contract. The caller owns all six observations at the same actual
    call/state before Save. No restored endpoint or future acquisition is
    assumed. The clear observation includes the caller's non-Idle field. *)
Definition tmr_task_unlock_entry sg call state : Prop :=
  kernel_call_task_source call state /\ kernel_call_stack_available call state /\
  state.(SchedState).(isRunning) = true /\
  sched_current_consistency state.(TskState) state.(SchedState) /\
  task_idle_ready sg state.(TskState) /\ tmr_task_fields_caller_clear sg call state.

(** These are source certificates already proved for the selected Task
    region. The adapter does not import that route: it consumes the three
    reusable Scheduler interfaces, avoiding a dependency through the Task
    call adapter. The existing ready certificate and fixed TCB layout are
    retained in os_sched_unlock_fields_pre. *)
Definition tmr_task_unlock_registered_clients critical call : Prop :=
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_current_inv action) /\
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_running_idle_non_idle_inv call) action) /\
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_clear_inv call) action).

Definition tmr_task_unlock_fields_pre environment critical local sg call mask before X : Assertion :=
  coq_prop (tmr_task_unlock_entry sg call before /\ tmr_task_unlock_registered_clients critical call) &&
  os_sched_unlock_fields_pre environment critical local sg call mask before X.

(** A pure record of this input observation, retained while the actual
    Save/checkpoint/Restore states change. Validity comes from the original
    fields owner; the arbitrary continuation X remains unchanged. *)
Definition tmr_task_unlock_call_facts environment critical sg call mask before X : Prop :=
  tmr_task_unlock_entry sg call before /\ tmr_task_unlock_registered_clients critical call /\
  os_sched_unlock_continuation_safe environment critical sg call mask before X /\
  kernel_sched_ready_clients critical /\ kernel_tcb_stack_field_layout sg /\ UCOS2_state_inv sg before.

Lemma tmr_task_unlock_fields_pre_ordinary : forall environment critical local sg call mask before X,
  tmr_task_unlock_fields_pre environment critical local sg call mask before X |--
  os_sched_unlock_fields_pre environment critical local sg call mask before X.
Proof. intros environment critical local sg call mask before X heap [_ Hpre]; exact Hpre. Qed.

Lemma tmr_task_unlock_fields_pre_open : forall environment critical local sg call mask before X,
  tmr_task_unlock_fields_pre environment critical local sg call mask before X |--
  coq_prop (tmr_task_unlock_call_facts environment critical sg call mask before X) &&
  (sg.(g_OSRunning) # UChar |-> os_sched_unlock_running before **
    os_sched_fields_observation_frame environment local sg call mask before).
Proof.
  intros environment critical local sg call mask before X heap [[Hentry Hclients] Hpre].
  destruct (os_sched_unlock_fields_pre_open environment critical local sg call mask before X heap Hpre)
    as [[Hsafe [Hready [Hlayout Hvalid]]] Howned].
  split.
  - exact (conj Hentry (conj Hclients (conj Hsafe (conj Hready (conj Hlayout Hvalid))))).
  - exact Howned.
Qed.

Lemma tmr_task_unlock_entry_invariants : forall sg call before,
  UCOS2_state_inv sg before -> tmr_task_unlock_entry sg call before ->
  os_sched_fields_current_inv sg before /\
  os_sched_fields_running_idle_non_idle_inv call sg before /\
  os_sched_fields_clear_inv call sg before /\ before.(SchedState).(readyList) <> [].
Proof.
  intros sg call before Hvalid [Hsource [Havailable [Hrunning [Hcurrent [Hidle Hfields]]]]].
  destruct (kernel_call_task_source_current_at call before Hsource) as [_ [node [Hnode Hgeneration]]].
  destruct (Hfields node Hnode) as [Hnonidle [Hclear Hflag]].
  assert (Hnonidle_at : flag_pend_non_idle_at sg call before).
  { exists node; split; [exact Hnode|]. split; assumption. }
  assert (Hcurrent_inv : os_sched_fields_current_inv sg before) by (split; assumption).
  assert (Hidle_inv : os_sched_fields_running_idle_non_idle_inv call sg before).
  { split; [exact Hvalid|]. split; [exact Hrunning|]. split; assumption. }
  assert (Hclear_inv : os_sched_fields_clear_inv call sg before).
  { split; [exact Hvalid|]. exists node; split; [exact Hnode|]. split; assumption. }
  split; [exact Hcurrent_inv|]. split; [exact Hidle_inv|]. split; [exact Hclear_inv|].
  eapply sched_idle_ready_nonempty; [exact (proj1 (proj1 (proj2 (proj2 Hvalid))))|exact Hidle].
Qed.

(** The protected C decision is fixed before Restore. Every admission
    atom at restored/unlocked is produced by the two recorded source
    intervals, starting from the current input observations above. The
    caller never supplies these future endpoint facts as a precondition. *)
Lemma tmr_task_unlock_fields_fresh_scheduler_pre : forall environment critical local sg original mask
  before acquired restored unlocked X,
  tmr_task_unlock_call_facts environment critical sg original mask before X ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_unlock_requests acquired = true ->
  os_sched_fields_closed environment local sg restored mask unlocked |--
  os_sched_unlock_task_scheduler_pre environment critical local
    (PendPhaseCandidate.flag_pend_fresh_observation restored) sg restored mask unlocked.
Proof.
  intros environment critical local sg original mask before acquired restored unlocked X
    [Hentry [Hclients [Hsafe [Hready_clients [Hlayout Hvalid]]]]] Hfacts Hrequest.
  destruct (tmr_task_unlock_entry_invariants sg original before Hvalid Hentry)
    as [Hcurrent_inv [Hidle_inv [Hclear_inv Hready]]].
  destruct Hclients as [Hcurrent_clients [Hidle_clients Hclear_clients]].
  pose proof (os_sched_unlock_fields_prefix_registered_current environment critical sg original mask
    before acquired restored unlocked Hcurrent_clients Hfacts Hvalid (proj2 Hcurrent_inv)) as Hcurrent.
  destruct (os_sched_unlock_fields_prefix_idle_non_idle environment critical sg original mask
    before acquired restored unlocked Hidle_clients Hfacts Hvalid
    (proj1 (proj2 (proj2 Hidle_inv))) (proj2 (proj2 (proj2 Hidle_inv)))) as [Hidle Hnonidle].
  pose proof (os_sched_unlock_fields_prefix_registered_clear environment critical sg original mask
    before acquired restored unlocked Hclear_clients Hfacts Hclear_inv) as Hclear.
  destruct Hentry as [Hsource [Havailable Hrest]].
  eapply os_sched_unlock_fields_fresh_scheduler_pre;
    [exact Hfacts|exact Hrequest|exact Hready_clients|exact Hlayout|exact Hsource|exact Havailable|
     exact Hready|exact Hcurrent|exact Hidle|exact Hclear].
Qed.

(** The specialized C instance returns the ordinary fields post verbatim:
    native paths keep their actual local, scheduled paths retain the actual
    next_local/Fresh/current-ready owner, and both retain their exact
    history and the original arbitrary X. Existing return lemmas are
    consumed directly in the annotation. *)
