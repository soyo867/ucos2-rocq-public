Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_runtime_inv.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_phase_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_acquire_observation_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The actual final Restore consumer. It accepts the common platform
    normal-return contract and its registered C source trace. No IRQ or
    instruction-level history must be reconstructed to use the C API. *)
Lemma sem_pend_modular_restore_return_output : forall environment critical saved_local rely
  sg call mask released,
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical rely
    sg call mask released |--
  sem_pend_continuation_phase_restore_output SemPendReturnPhase
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask released ** unmap_table_rep sg.
Proof.
  intros; unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg
    call released returned current) by (unfold sem_pend_modular_call_history; tauto).
  pose proof Hhistory as [Htrace [Hsame Havailable]].
  assert (Hsource : UCOS2_state_inv sg released -> kernel_call_task_source call released ->
    kernel_call_task_source returned current).
  { intros Hvalid Hcall.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hkey : task_stack_call_active_key returned = task_stack_call_active_key call).
  { unfold task_stack_call_active_key; rewrite (proj1 (proj2 Hsame)); reflexivity. }
  rewrite Hkey.
  sep_apply_l_atomic (sem_pend_continuation_restore_source_output_current
    environment critical saved_local sg call returned mask released current
    (or_intror Hhistory) Hsource).
  rewrite sem_pend_continuation_phase_restore_return_output; entailer!.
Qed.

(** The no-capsule Restore arm retains the actual source trace and the
    returned execution/context owner. No Task environment or readiness
    fact is introduced to interpret this normal return. *)
Lemma sem_pend_modular_restore_unowned_output : forall external platform port critical
  saved_local sg call returned mask released current,
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) released false
    returned.(os_sched_call_origin) current ->
  kernel_call_normal_return call released returned current ->
  mutex_query_closed platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) mask current ** os_sched_context_resources external returned |--
  sem_pend_continuation_phase_restore_output SemPendReturnPhase external platform None
    critical saved_local sg call mask released.
Proof.
  intros * Htrace [Hsame Havailable].
  assert (Hhistory : sem_pend_unowned_return_history external platform critical sg
    call released returned current).
  { right; exists port; split; [exact Htrace|]. split; assumption. }
  assert (Hsource : UCOS2_state_inv sg released -> kernel_call_task_source call released ->
    kernel_call_task_source returned current).
  { intros Hvalid Hcall.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    exact (task_tcb_init_stack_registered_source_preserved external port critical sg
      call returned released current Hvalid Hsame Htrace Hcall). }
  unfold sem_pend_continuation_phase_restore_output; Exists returned current.
  unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
    sem_pend_restore_phase_pre, sem_pend_optional_continuation_resources; entailer!.
Qed.

(** The type-independent handle protocol gives the actual acquired
    semaphore incarnation for either resource domain. *)
Lemma sem_pend_save_source_acquire_facts : forall external port critical sg call returned
  pevent eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  sem_pend_call_input critical sg call.(os_sched_call_invocation) pevent before eid observed ->
  pevent <> 0 ->
  sem_pend_context_error (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None ->
  kernel_call_save_source external port critical sg call returned mask saved before acquired ->
  exists current, sem_query_acquire_facts critical sg call.(os_sched_call_invocation)
    eid mask saved before acquired observed current.
Proof.
  intros * Hvalid Hinput Hnonnull Hclear Hsave.
  destruct Hinput as [Hzero|[_ [Haddr [Hid [Hslot Hprotocol]]]]]; [contradiction|].
  assert (Hguards : event_slot_type_value before.(EventState) eid = 3 /\
    before.(IntrState).(intNesting) <= 0 /\ before.(IntrState).(lockNesting) <= 0).
  { unfold sem_pend_context_error in Hclear; cbn [encode_event_type] in Hclear.
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3) eqn:Htype;
      cbn [negb] in Hclear; [|discriminate].
    destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint; [discriminate|].
    destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock; [discriminate|].
    apply Z.eqb_eq in Htype; apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; auto. }
  destruct Hguards as [Htype [Hint Hlock]].
  specialize (Hprotocol Htype Hint Hlock).
  destruct (sem_query_public_slot_is_sem before eid observed Hslot Htype) as [Hlookup Hsem].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid' _].
  destruct (mutex_query_handle_interval_preserves_identity critical sg
    call.(os_sched_call_invocation) eid before acquired observed Hprotocol Hinterval Hvalid Hlookup)
    as [current [Hcurrent [Hgen Htype']]].
  destruct Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  exists current; unfold sem_query_acquire_facts; repeat first [assumption | split | congruence].
Qed.

Lemma sem_pend_modular_acquire_observation : forall environment critical sg call returned
  pevent eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  exists current, sem_pend_acquire_observation environment critical sg call returned
    mask saved before acquired eid observed current.
Proof.
  intros * Hvalid [Hinput [Hnonnull [Hclear Hadmit]]] Hsave Hnormal.
  destruct (sem_pend_save_source_acquire_facts _ _ _ _ _ _ _ _ _ _ _ _ _
    Hvalid Hinput Hnonnull Hclear Hsave) as [current [Hinterval [Hvalid' [Hsaved Hfields]]]].
  exists current; split.
  - right; split; [exact (proj1 Hsave)|exact Hnormal].
  - split; [exact (proj1 Hnormal)|]. split; [exact Hsaved|]. split; assumption.
Qed.

Lemma sem_pend_modular_save_preserves_call_stage : forall environment critical sg call returned
  mask saved before acquired,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  UCOS2_state_inv sg before -> sem_pend_task_call_stage sg call before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_task_call_stage sg call acquired.
Proof.
  intros * Hclients Hvalid Hstage Hsave [Hcontrol [Hruntime [Hcache_rely Hready_rely]]].
  pose proof Hstage as [Hsource [Hrunning [old [Hready [Hg [Hnonidle Hnone]]]]]].
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid' _].
  destruct (sem_pend_resumption_trace_preserves_call_fields critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None before false acquired
    call.(os_sched_call_stack).(stackLeaseSlot) old Hclients Hinterval Hvalid Hvalid'
    Hrunning (proj1 Hready) Hnonidle Hnone) as [Hrunning' [node [Hnode [Hnonidle' Hnone']]]].
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned call) by (repeat split; assumption).
  assert (Hsource' : kernel_call_task_source call acquired).
  { exact (task_tcb_init_stack_registered_source_preserved
      environment.(task_stack_call_external) environment.(task_stack_call_port) critical sg
      call returned before acquired Hvalid Hsame Htrace Hsource). }
  destruct (kernel_call_task_source_current_at call acquired Hsource') as [Hcurrent [found [Hfound Hgen]]].
  assert (found = node) by congruence; subst found.
  assert (Hmember : In call.(os_sched_call_stack).(stackLeaseSlot) acquired.(SchedState).(readyList)).
  { apply Hready_rely; [exact (proj1 (proj2 Hready))|exact (proj1 (proj2 (proj2 (proj2 Hready))))]. }
  pose proof (Hcache_rely (sched_current_ready_at_implies_current_consistency _ _ _ _ Hready)) as Hcache.
  unfold sched_current_consistency in Hcache; rewrite Hcurrent in Hcache.
  destruct Hcache as [cached [Hcached Hpriority]].
  assert (cached = node) by congruence; subst cached.
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid')))) _ Hmember)
    as [ready_node [Hready_node [_ Heffective]]].
  assert (ready_node = node) by congruence; subst ready_node.
  assert (Hready' : sched_current_ready_at acquired.(TskState) acquired.(SchedState)
    call.(os_sched_call_stack).(stackLeaseSlot) node) by (repeat split; assumption).
  split; [exact Hsource'|]. split; [exact Hrunning'|]. exists node; auto.
Qed.

(** The stronger zero-count fact is consumed only after the actual C
    guards and acquisition. It follows the newly explicit initialized
    Task protocol and its C rely, not an unconditional strengthened Save. *)
Lemma sem_pend_modular_acquire_phase_observation : forall environment critical sg call returned
  pevent eid observed mask saved before acquired,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  UCOS2_state_inv sg before -> interrupt_in_range acquired.(IntrState) ->
  sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_save_phase_observation (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call returned mask saved before acquired.
Proof.
  intros * Hclients Hvalid Hrange Hpre Hsave Hnormal Hrely.
  destruct (sem_pend_modular_acquire_observation environment critical sg call returned
    pevent eid observed mask saved before acquired Hvalid Hpre Hsave Hnormal)
    as [current Hacquire].
  exists current; split; [exact Hacquire|]. intro Hzero.
  pose proof Hpre as [_ [Hnonnull [Hclear [Hadmit Hnonblocking]]]].
  assert (Hpreclear : sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); exact Hclear. }
  destruct (Hadmit Hpreclear) as [[Hstage [Hruntime Havailable]]|Hpositive].
  2: { specialize (Hpositive returned mask saved acquired observed current Hacquire); lia. }
  pose proof (sem_pend_modular_save_preserves_call_stage environment critical sg call returned
    mask saved before acquired Hclients Hvalid Hstage Hsave Hrely) as Hstage'.
  split; [exact Hstage'|].
  destruct Hrely as [[Hrunning Hcounters] [Hruntime_rely [Hcache Hready]]].
  assert (Hidle : task_idle_ready sg acquired.(TskState)).
  { apply (Hruntime_rely Hruntime); exact (proj1 (proj2 Hstage')). }
  assert (Havailable' : kernel_call_stack_available call acquired).
  { pose proof (proj2 Hnormal Havailable) as Hreturned.
    unfold kernel_call_stack_available in *; rewrite (proj1 (proj2 (proj1 Hnormal))) in Hreturned;
      exact Hreturned. }
  unfold sem_pend_optional_blocking_call_stage, sem_pend_blocking_call_stage.
  split; [exact Hidle|]. split; [exact Havailable'|].
  unfold interrupt_in_range in Hrange; rewrite Hcounters in Hrange.
  unfold sem_pend_context_error in Hclear.
  destruct (negb (Z.eqb _ _)); [discriminate|].
  destruct (Z.ltb 0 before.(IntrState).(intNesting)) eqn:Hint; [discriminate|].
  destruct (Z.ltb 0 before.(IntrState).(lockNesting)) eqn:Hlock; [discriminate|].
  apply Z.ltb_ge in Hint; apply Z.ltb_ge in Hlock; rewrite Hcounters; lia.
Qed.

(** Append the real registered C interval to the same wait. The existing
    client projection proves preservation of the waiter, object generation,
    pending result and registration; the platform part supplies same-call
    identity only. This is the existing history's Clients constructor. *)
Lemma sem_pend_wait_at_modular_return : forall environment critical sg original mask before
  observed eid timeout waiting call checkpoint returned current,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_wait_at (Some environment) critical sg original mask before observed eid timeout
    waiting call checkpoint ->
  sem_pend_modular_call_history environment critical sg call checkpoint returned current ->
  sem_pend_wait_at (Some environment) critical sg original mask before observed eid timeout
    waiting returned current.
Proof.
  intros * Hclients [owned [Howned [Hsame [Hwait Hpath]]]] [Htrace [Hreturned Havailable]].
  inversion Howned; subst owned.
  exists environment; split; [reflexivity|]. split.
  - unfold kernel_stack_call_same_call, task_tcb_init_stack_same_call in *; intuition congruence.
  - split; [exact Hwait|]. eapply SemPendWaitSourceTrans; [exact Hpath|].
    pose proof Hsame as [Hi [Ho Hs]].
    rewrite Hi, Ho in Htrace.
    eapply SemPendWaitSourceClients; [exact Htrace|].
    intros node Hnode Hcontinuation.
    destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
      as [Hresources _].
    eapply sem_pend_resumption_trace_preserves_continuation; eassumption.
Qed.

Lemma sem_pend_wait_sched_entry_modular_return : forall environment critical sg call checkpoint returned current,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg checkpoint ->
  kernel_call_task_source call checkpoint -> sem_pend_wait_sched_entry sg call checkpoint ->
  sem_pend_modular_call_history environment critical sg call checkpoint returned current ->
  sem_pend_blocking_rely sg checkpoint current ->
  sem_pend_wait_sched_entry sg returned current.
Proof.
  intros environment critical sg call checkpoint returned current Hlayout Hvalid Hsource
    [_ [_ [_ [[Hidle [Havailable [Hint Hlock]]] Hcache]]]]
    [Htrace [Hsame Hnormal]] [Hidle_rely [Hcontrol Hcache_rely]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources Hcontrol_trace].
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) checkpoint current Hresources Hvalid) as [Hvalid' _].
  assert (Hsource' : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    exact (task_tcb_init_stack_registered_source_preserved
      environment.(task_stack_call_external) environment.(task_stack_call_port) critical
      sg call returned checkpoint current Hvalid Hsame Htrace Hsource). }
  specialize (Hidle_rely Hidle).
  destruct (Hcontrol (conj Hint Hlock)) as [Hint' Hlock'].
  specialize (Hnormal Havailable).
  assert (Hready : current.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty;
      [exact (proj1 (proj1 (proj2 (proj2 Hvalid'))))|exact Hidle_rely]. }
  split.
  - apply os_sched_call_cut_from_source; try assumption.
    eapply kernel_call_task_source_stack_field_address; eassumption.
  - split; [apply os_sched_selection_enabled_iff; auto|].
    split; [exact Hsource'|]. split; [unfold sem_pend_blocking_call_stage; auto|auto].
Qed.

(** The Restore at the end of OS_EventTaskWait's critical section returns
    the exact canonical Wait-phase post. Its C rely carries Idle and the
    balanced interrupt/lock counters; the actual registered client trace
    carries the waiter relation. Normal-return carries only the platform
    same-call/execution boundary. *)
Lemma sem_pend_modular_restore_wait_output : forall environment critical saved_local sg
  original initial_mask initial observed eid timeout waiting call mask checkpoint,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg checkpoint ->
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_restore_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask checkpoint ->
  kernel_call_modular_restore_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_blocking_rely
    sg call mask checkpoint |--
  sem_pend_continuation_phase_restore_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask checkpoint ** unmap_table_rep sg.
Proof.
  intros * Hlayout Hvalid Hclients [Hmask [Hwait Hentry]].
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call checkpoint returned current)
    by (unfold sem_pend_modular_call_history; tauto).
  assert (Hrely : sem_pend_blocking_rely sg checkpoint current) by tauto.
  pose proof (sem_pend_wait_at_modular_return environment critical sg original initial_mask initial observed
    eid timeout waiting call checkpoint returned current Hclients Hwait Hhistory) as Hwait'.
  pose proof (proj1 (proj2 (proj2 Hentry))) as Hcall.
  pose proof (sem_pend_wait_sched_entry_modular_return environment critical sg call checkpoint returned
    current Hlayout Hvalid Hcall Hentry Hhistory Hrely) as Hentry'.
  assert (Hphase : sem_pend_restore_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg returned mask current) by (split; [exact Hmask|auto]).
  pose proof Hhistory as [Htrace [Hsame Havailable]].
  assert (Hsource : UCOS2_state_inv sg checkpoint -> kernel_call_task_source call checkpoint ->
    kernel_call_task_source returned current).
  { intros Hvalid0 Hcall0.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff returned call current Hsame)).
    exact (task_tcb_init_stack_registered_source_preserved
      environment.(task_stack_call_external) environment.(task_stack_call_port) critical
      sg call returned checkpoint current Hvalid0 Hsame Htrace Hcall0). }
  assert (Hrestore : sem_pend_restore_call_history environment critical sg call checkpoint returned current)
    by (right; exact Hhistory).
  pose proof Hsame as [Hi [Ho Hs]].
  unfold kernel_continuation_call_closed, kernel_continuation_inv.
  rewrite kernel_program_inv_split_unmap; Intros.
  unfold sem_pend_continuation_phase_restore_output; Exists returned current.
  rewrite mutex_query_closed_equiv.
  unfold sem_pend_optional_restore_history, sem_pend_stack_restore_observation,
    sem_pend_optional_continuation_resources, task_tcb_init_continuation_capsules,
    kernel_call_execution_owned, task_stack_call_active_key.
  rewrite Hi, Ho; entailer!; try discriminate; try tauto.
  unfold task_stack_call_active_key in *; rewrite Ho in *; assumption.
Qed.

Lemma sem_pend_inv_interrupt_range : forall sg state,
  UCOS2_inv sg state |-- coq_prop (interrupt_in_range state.(IntrState)).
Proof.
  intros; rewrite UCOS2_inv_split_interrupt; unfold interrupt_inv; entailer!.
Qed.

(** Exact first-Save post consumed by the canonical C annotation. The
    input's established calling protocol, registered C projection/rely
    and actual returned bytes supply the phase facts. *)
Lemma sem_pend_modular_save_acquire_output : forall environment critical saved_local sg call
  pevent eid observed mask saved before,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  UCOS2_state_inv sg before ->
  sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call mask saved before |--
  sem_pend_continuation_phase_save_output (SemPendAcquirePhase pevent eid observed)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask saved before ** unmap_table_rep sg.
Proof.
  intros * Hclients Hvalid Hpre.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return call before returned acquired) by tauto.
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  unfold kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_inv_split_unmap; Intros.
  prop_apply_p (sem_pend_inv_interrupt_range sg acquired).
  Intros.
  assert (Hrange : interrupt_in_range acquired.(IntrState)) by tauto.
  pose proof (sem_pend_modular_acquire_phase_observation environment critical sg call returned
    pevent eid observed mask saved before acquired Hclients Hvalid Hrange Hpre Hsave Hnormal Hrely)
    as Hobservation.
  pose proof Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  unfold sem_pend_continuation_phase_save_output; Exists returned acquired.
  unfold sem_pend_stack_save_observation, kernel_stack_call_same_call,
    sem_pend_optional_continuation_resources, task_tcb_init_continuation_capsules,
    task_stack_call_active_key.
  rewrite Hi, Ho; entailer!; try discriminate; try tauto.
  unfold task_stack_call_active_key in *; rewrite Ho in *; assumption.
Qed.

(** Preserve this wait across the second Save. Source control preserves
    the current task, the C normal-boundary rely preserves its already
    established readiness, and the real wait trace identifies the result.
    Ready plus the existing waiter relation excludes still-pending paths. *)
Lemma sem_pend_wait_selected_modular_return : forall environment critical sg original initial_mask
  initial observed eid timeout waiting call before returned acquired,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting call before ->
  sem_pend_modular_call_history environment critical sg call before returned acquired ->
  sem_pend_save_rely sg before acquired ->
  sem_pend_wait_selected_at (Some environment) critical sg original initial_mask initial observed
    eid timeout waiting returned acquired.
Proof.
  intros * Hclients [Hwait [old [Hvalid [Hcurrent [Hold [Hregistration Hready]]]]]]
    Hhistory [_ [_ [_ Hready_rely]]].
  pose proof (sem_pend_wait_at_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call before returned acquired Hclients Hwait Hhistory) as Hwait'.
  split; [exact Hwait'|].
  pose proof Hwait as [owned [Howned [Hsame [Hinitial Hpath]]]].
  pose proof Hinitial as [_ [[Horigin _] _]].
  pose proof Hhistory as [Htrace [Hreturned Havailable]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources Hcontrol].
  destruct (critical_region_interval_transports_resources critical sg
    call.(os_sched_call_invocation) before acquired Hresources Hvalid) as [Hvalid' _].
  assert (Hcaller_origin : call.(os_sched_call_origin) = RunningInvocation
    original.(os_sched_call_stack).(stackLeaseSlot) original.(os_sched_call_stack).(stackLeaseGeneration)).
  { rewrite (proj1 (proj2 Hsame)); exact Horigin. }
  assert (Hcurrent' : acquired.(SchedState).(curTaskID) =
    Some original.(os_sched_call_stack).(stackLeaseSlot)).
  { assert (Hbefore : task_execution_current call.(os_sched_call_origin) before).
    { rewrite Hcaller_origin; exact Hcurrent. }
    pose proof (task_execution_source_trace_preserves_current _ _ _ _ _ _ _ Hcontrol Hbefore) as Hafter.
    rewrite (proj1 (proj2 Hreturned)), Hcaller_origin in Hafter; exact Hafter. }
  assert (Hready' : In original.(os_sched_call_stack).(stackLeaseSlot) acquired.(SchedState).(readyList))
    by (apply Hready_rely; assumption).
  destruct (proj1 (proj1 (proj1 (proj2 (proj2 Hvalid')))) _ Hready')
    as [node [Hnode [_ Heffective]]].
  pose proof Hwait' as [owned' [Howned' [Hsame' [Hinitial' Hpath']]]].
  destruct (sem_pend_observed_wait_history_waiter _ _ _ _ _ _ _ _ _ _ Hinitial')
    as [first [Hfirst Hcontinuation]].
  destruct (sem_pend_wait_source_history_preserves_waiter _ _ _ _ _ _ _ _ Hpath'
    first Hfirst Hcontinuation) as [last [Hlast Hcontinuation']].
  assert (last = node) by congruence; subst last.
  destruct (sem_pend_wait_ready_resume_registration eid
    original.(os_sched_call_stack).(stackLeaseGeneration) node Hcontinuation'
    Heffective) as [Hregistration' Hgen].
  exists node; unfold sem_pend_resume_entry; repeat first [assumption | split].
Qed.

Lemma sem_pend_modular_save_wait_output : forall environment critical saved_local sg original
  initial_mask initial observed eid timeout waiting call mask saved before,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  sem_pend_save_phase_pre
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    (Some environment) critical sg call mask before ->
  kernel_call_modular_save_post environment.(task_stack_call_continuations)
    kernel_program_inv (task_create_continuation_local saved_local) critical sem_pend_save_rely
    sg call mask saved before |--
  sem_pend_continuation_phase_save_output
    (SemPendWaitPhase original initial_mask initial observed eid timeout waiting)
    environment.(task_stack_call_external) environment.(task_stack_call_platform)
    (Some environment) critical saved_local sg call mask saved before ** unmap_table_rep sg.
Proof.
  intros * Hclients [Hmask Hselected].
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg call returned mask saved before acquired) by tauto.
  assert (Hhistory : sem_pend_modular_call_history environment critical sg call before returned acquired)
    by (split; [exact (proj1 Hsave)|tauto]).
  assert (Hrely : sem_pend_save_rely sg before acquired) by tauto.
  pose proof (sem_pend_wait_selected_modular_return environment critical sg original initial_mask
    initial observed eid timeout waiting call before returned acquired Hclients Hselected Hhistory Hrely)
    as Hobservation.
  pose proof Hsave as [_ [Hi [Ho [Hs Hsaved]]]].
  unfold kernel_continuation_call_masked, kernel_continuation_inv.
  rewrite kernel_program_inv_split_unmap; Intros.
  unfold sem_pend_continuation_phase_save_output; Exists returned acquired.
  unfold sem_pend_stack_save_observation, kernel_stack_call_same_call,
    sem_pend_optional_continuation_resources, task_tcb_init_continuation_capsules,
    task_stack_call_active_key; cbn [sem_pend_save_phase_observation].
  rewrite Hi, Ho; entailer!; try discriminate; try tauto.
  unfold task_stack_call_active_key in *; rewrite Ho in *; assumption.
Qed.

(** The existing no-capsule nonblocking admission is now explicitly
    carried to the first Save cut. Its actual interval rules out zero
    count; no ready/Idle/current premise or Task capsule is needed. *)
Lemma sem_pend_modular_save_unowned_acquire_output : forall external platform port critical
  saved_local sg call returned pevent eid observed mask saved before acquired,
  UCOS2_state_inv sg before ->
  sem_pend_save_phase_pre (SemPendAcquirePhase pevent eid observed)
    None critical sg call mask before ->
  kernel_call_save_source external port critical sg call returned mask saved before acquired ->
  kernel_call_normal_return call before returned acquired ->
  critical_region_masked platform critical sg call.(os_sched_call_invocation)
    call.(os_sched_call_origin) saved acquired ** os_sched_context_resources external returned **
    UCOS2_inv sg acquired |--
  sem_pend_continuation_phase_save_output (SemPendAcquirePhase pevent eid observed)
    external platform None critical saved_local sg call mask saved before.
Proof.
  intros * Hvalid [Hinput [Hnonnull [Hclear [Hadmit Hnonblocking]]]] Hsave Hnormal.
  destruct (sem_pend_save_source_acquire_facts external port critical sg call returned pevent
    eid observed mask saved before acquired Hvalid Hinput Hnonnull Hclear Hsave) as [current Hfacts].
  pose proof Hfacts as [Hinterval [Hvalid' [Hsaved [Hlookup [Hcurrent [Htype [Htype' Hgen]]]]]]].
  assert (Hpreclear : sem_pend_precritical_error pevent (event_slot_type_value before.(EventState) eid)
    before.(IntrState).(intNesting) before.(IntrState).(lockNesting) = None).
  { unfold sem_pend_precritical_error; rewrite (proj2 (Z.eqb_neq _ _) Hnonnull); exact Hclear. }
  pose proof (Hnonblocking eq_refl Hpreclear acquired current Hinterval Hcurrent Htype') as Hpositive.
  assert (Hphase : sem_pend_save_phase_observation (SemPendAcquirePhase pevent eid observed)
    None critical sg call returned mask saved before acquired).
  { exists current; split.
    - split; [exact (proj1 Hnormal)|exact Hfacts].
    - intro Hzero; lia. }
  assert (Hsavefacts : sem_pend_save_facts critical sg call.(os_sched_call_invocation)
    mask saved before acquired) by (repeat first [assumption | split]).
  pose proof (proj1 Hnormal) as Hsame.
  unfold sem_pend_continuation_phase_save_output; Exists returned acquired.
  unfold sem_pend_stack_save_observation, sem_pend_optional_continuation_resources; entailer!.
Qed.
