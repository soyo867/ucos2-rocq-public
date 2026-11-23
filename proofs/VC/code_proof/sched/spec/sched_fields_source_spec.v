Require Export Ucos2Verify.VC.code.sched.spec.sched_unlock_fields_resource_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_fresh_fields_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_task_return_registry_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_active_phase_source_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.lib.kernel_client_invariants Ucos2Verify.lib.task_idle_ready.
Require Import Coq.Lists.List.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.

(** A composition over the two RECORDED modular traces. Registration must
    prove the requested invariant for each real source action; membership
    or a selected-profile certificate alone is not that proof. *)
Lemma os_sched_fields_checkpoint_registered_invariant :
  forall checkpoint environment critical invariant sg original mask before acquired returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources invariant action) ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  (invariant sg acquired -> invariant sg (checkpoint acquired)) ->
  invariant sg before -> invariant sg current.
Proof.
  intros checkpoint environment critical invariant sg original mask before acquired returned current
    Hclients [entered [saved [Hsave [Hrestore Hsame]]]] Hcheckpoint Hbefore.
  pose proof Hsave as [Hsave_trace Hsave_rest].
  eapply (kernel_call_registered_rely_preserves_invariant
    environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical invariant sg entered returned (checkpoint acquired) current);
    [exact Hclients|exact Hrestore|].
  apply Hcheckpoint.
  eapply (kernel_call_registered_rely_preserves_invariant
    environment.(task_stack_call_external) environment.(task_stack_call_port)
    critical invariant sg original entered before acquired);
    [exact Hclients|exact Hsave_trace|exact Hbefore].
Qed.

Definition os_sched_fields_current_inv sg state : Prop :=
  UCOS2_state_inv sg state /\ sched_current_consistency state.(TskState) state.(SchedState).

Lemma os_sched_fields_source_client_current_inv : forall external action,
  KernelClientCertificate action -> sched_task_source_client external action ->
  kernel_client_preserves_resources os_sched_fields_current_inv action.
Proof.
  intros external action Hcert Hsource sg before after [Hvalid Hcurrent] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcert sg before after Hvalid Hstep)
    as [Hvalid' Hframes].
  split; [|exact Hframes]. split; [exact Hvalid'|].
  exact (sched_task_source_client_preserves_current_consistency external action
    sg before after Hvalid Hcurrent Hsource Hstep).
Qed.

(** This form consumes a proved source invariant, so a caller can use a
    larger real registry without pretending that every action belongs to
    the older seven-constructor Scheduler family. Both modular traces are
    the ones retained in this call's actual return receipt. *)
Lemma os_sched_fields_checkpoint_current_consistency :
  forall checkpoint environment critical sg original mask before acquired returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_current_inv action) ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  (UCOS2_state_inv sg acquired -> UCOS2_state_inv sg (checkpoint acquired)) ->
  (checkpoint acquired).(TskState) = acquired.(TskState) ->
  (checkpoint acquired).(SchedState) = acquired.(SchedState) ->
  UCOS2_state_inv sg before -> sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros checkpoint environment critical sg original mask before acquired returned current
    Hclients Hsources Hvalid_checkpoint Htasks Hsched Hvalid Hcurrent.
  assert (Hafter : os_sched_fields_current_inv sg current).
  { eapply (os_sched_fields_checkpoint_registered_invariant checkpoint environment critical
      os_sched_fields_current_inv sg original mask before acquired returned current);
      [exact Hclients|exact Hsources| |split; assumption].
    intros [Hvalid' Hcurrent']; split; [apply Hvalid_checkpoint; exact Hvalid'|].
    rewrite Htasks, Hsched; exact Hcurrent'. }
  exact (proj2 Hafter).
Qed.

Lemma os_sched_unlock_fields_prefix_registered_current :
  forall environment critical sg original mask before acquired restored unlocked,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_current_inv action) ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  UCOS2_state_inv sg before -> sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency unlocked.(TskState) unlocked.(SchedState).
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hclients
    [Hfacts Hsources] Hvalid Hcurrent.
  eapply (os_sched_fields_checkpoint_current_consistency (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked);
    [exact Hclients|exact Hsources| |reflexivity|reflexivity|exact Hvalid|exact Hcurrent].
  apply os_sched_unlock_checkpoint_preserves_validity.
Qed.

Lemma os_sched_unlock_fields_prefix_ready :
  forall environment critical sg original mask before acquired restored unlocked,
  kernel_sched_ready_clients critical ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  UCOS2_state_inv sg before -> before.(SchedState).(readyList) <> [] ->
  unlocked.(SchedState).(readyList) <> [].
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hclients
    [Hfacts Hsources] Hvalid Hready.
  assert (Hafter : kernel_sched_ready_inv sg unlocked).
  { eapply (os_sched_fields_checkpoint_registered_invariant (os_sched_unlock_checkpoint true)
      environment critical kernel_sched_ready_inv sg original mask before acquired restored unlocked);
      [exact Hclients|exact Hsources| |split; assumption].
    intros [Hvalid' Hready']; split.
    - apply os_sched_unlock_checkpoint_preserves_validity; exact Hvalid'.
    - exact Hready'. }
  exact (proj2 Hafter).
Qed.

Lemma os_sched_unlock_fields_prefix_current_consistency :
  forall environment critical sg original mask before acquired restored unlocked,
  (forall action, critical.(critical_region_clients) action ->
    sched_task_source_client environment.(task_stack_call_external) action) ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  UCOS2_state_inv sg before -> sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency unlocked.(TskState) unlocked.(SchedState).
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hclients [Hfacts Hsources] Hvalid Hcurrent.
  assert (Hregistered : forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_current_inv action).
  { intros action Hin; eapply os_sched_fields_source_client_current_inv.
    - apply (critical_region_client_certificates critical action Hin).
    - apply Hclients; exact Hin. }
  assert (Hafter : os_sched_fields_current_inv sg unlocked).
  { eapply (os_sched_fields_checkpoint_registered_invariant (os_sched_unlock_checkpoint true)
      environment critical os_sched_fields_current_inv sg original mask before acquired restored unlocked);
      [exact Hregistered|exact Hsources| |split; assumption].
    intros [Hvalid' Hcurrent']; split.
    - exact (os_sched_unlock_checkpoint_preserves_validity sg true acquired Hvalid').
    - exact Hcurrent'. }
  exact (proj2 Hafter).
Qed.

Definition os_sched_fields_idle_inv sg state : Prop :=
  UCOS2_state_inv sg state /\ task_idle_ready sg state.(TskState).

Definition os_sched_fields_running_idle_non_idle_inv call sg state : Prop :=
  UCOS2_state_inv sg state /\ state.(SchedState).(isRunning) = true /\
  task_idle_ready sg state.(TskState) /\ flag_pend_non_idle_at sg call state.

Definition os_sched_fields_clear_inv call sg state : Prop :=
  UCOS2_state_inv sg state /\
  exists node, state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    flag_active_event_clear node /\ node.(tcbFlagNode) = 0.

Lemma os_sched_fields_checkpoint_same_call :
  forall checkpoint environment critical sg original mask before acquired returned current,
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  task_tcb_init_stack_same_call returned original.
Proof.
  intros checkpoint environment critical sg original mask before acquired returned current
    [entered [saved [Hsave [Hrestore [Hinv [Horigin Hstack]]]]]].
  destruct Hsave as [Htrace [Hinv' [Horigin' [Hstack' Hmask]]]].
  repeat split; congruence.
Qed.

Lemma os_sched_fields_checkpoint_registered_clear :
  forall checkpoint environment critical sg original mask before acquired returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_clear_inv original) action) ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  (UCOS2_state_inv sg acquired -> UCOS2_state_inv sg (checkpoint acquired)) ->
  (checkpoint acquired).(TskState) = acquired.(TskState) ->
  os_sched_fields_clear_inv original sg before ->
  exists node, current.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    flag_active_event_clear node /\ node.(tcbFlagNode) = 0.
Proof.
  intros checkpoint environment critical sg original mask before acquired returned current
    Hclients Hsources Hvalid_checkpoint Htasks Hbefore.
  assert (Hafter : os_sched_fields_clear_inv original sg current).
  { eapply (os_sched_fields_checkpoint_registered_invariant checkpoint environment critical
      (os_sched_fields_clear_inv original) sg original mask before acquired returned current);
      [exact Hclients|exact Hsources| |exact Hbefore].
    intros [Hvalid [node [Hnode [Hclear Hflag]]]]. split; [apply Hvalid_checkpoint; exact Hvalid|].
    exists node; rewrite Htasks; auto. }
  pose proof (os_sched_fields_checkpoint_same_call checkpoint environment critical sg original
    mask before acquired returned current Hsources) as Hsame.
  rewrite (proj2 (proj2 Hsame)); exact (proj2 Hafter).
Qed.

Lemma os_sched_unlock_fields_prefix_registered_clear :
  forall environment critical sg original mask before acquired restored unlocked,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_clear_inv original) action) ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  os_sched_fields_clear_inv original sg before ->
  forall node, unlocked.(TskState).(inUsedTaskStates) restored.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
    flag_active_event_clear node /\ node.(tcbFlagNode) = 0.
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hclients [Hfacts Hsources]
    Hbefore node Hnode.
  destruct (os_sched_fields_checkpoint_registered_clear (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked Hclients Hsources
    (os_sched_unlock_checkpoint_preserves_validity sg true acquired) eq_refl Hbefore)
    as [actual [Hactual Hclear]].
  assert (node = actual) by congruence; subst node; exact Hclear.
Qed.

Lemma os_sched_lock_fields_return_registered_clear :
  forall environment critical sg original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_clear_inv original) action) ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  os_sched_fields_clear_inv original sg before ->
  exists node, current.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    flag_active_event_clear node /\ node.(tcbFlagNode) = 0.
Proof.
  intros environment critical sg original mask before returned current Hclients Hsources Hbefore.
  unfold os_sched_lock_fields_return_sources in Hsources; destruct before.(SchedState).(isRunning).
  - destruct Hsources as [acquired Hsources].
    eapply (os_sched_fields_checkpoint_registered_clear (os_sched_lock_checkpoint true)
      environment critical sg original mask before acquired returned current);
      [exact Hclients|exact Hsources| |reflexivity|exact Hbefore].
    apply os_sched_lock_checkpoint_preserves_validity.
  - destruct Hsources as [-> ->]; exact (proj2 Hbefore).
Qed.

Lemma os_sched_fields_checkpoint_idle_non_idle :
  forall checkpoint environment critical sg original mask before acquired returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_running_idle_non_idle_inv original) action) ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  (UCOS2_state_inv sg acquired -> UCOS2_state_inv sg (checkpoint acquired)) ->
  (checkpoint acquired).(TskState) = acquired.(TskState) ->
  (checkpoint acquired).(SchedState).(isRunning) = acquired.(SchedState).(isRunning) ->
  os_sched_fields_running_idle_non_idle_inv original sg before ->
  task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg returned current.
Proof.
  intros checkpoint environment critical sg original mask before acquired returned current
    Hclients Hsources Hvalid_checkpoint Htasks Hrunning Hbefore.
  assert (Hafter : os_sched_fields_running_idle_non_idle_inv original sg current).
  { eapply (os_sched_fields_checkpoint_registered_invariant checkpoint environment critical
      (os_sched_fields_running_idle_non_idle_inv original) sg original mask before acquired returned current);
      [exact Hclients|exact Hsources| |exact Hbefore].
    intros [Hvalid [Hrun [Hidle Hnonidle]]]. split; [apply Hvalid_checkpoint; exact Hvalid|].
    split; [rewrite Hrunning; exact Hrun|]. split; [rewrite Htasks; exact Hidle|].
    unfold flag_pend_non_idle_at in *; rewrite Htasks; exact Hnonidle. }
  destruct Hafter as [_ [_ [Hidle Hnonidle]]]; split; [exact Hidle|].
  pose proof (os_sched_fields_checkpoint_same_call checkpoint environment critical sg original
    mask before acquired returned current Hsources) as Hsame.
  unfold flag_pend_non_idle_at in *; rewrite (proj2 (proj2 Hsame)); exact Hnonidle.
Qed.

Lemma os_sched_unlock_fields_prefix_idle_non_idle :
  forall environment critical sg original mask before acquired restored unlocked,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_running_idle_non_idle_inv original) action) ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  UCOS2_state_inv sg before -> task_idle_ready sg before.(TskState) ->
  flag_pend_non_idle_at sg original before ->
  task_idle_ready sg unlocked.(TskState) /\ flag_pend_non_idle_at sg restored unlocked.
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hclients
    [Hfacts Hsources] Hvalid Hidle Hnonidle.
  eapply (os_sched_fields_checkpoint_idle_non_idle (os_sched_unlock_checkpoint true)
    environment critical sg original mask before acquired restored unlocked);
    [exact Hclients|exact Hsources| |reflexivity|reflexivity|].
  - apply os_sched_unlock_checkpoint_preserves_validity.
  - split; [exact Hvalid|]. split; [exact (proj1 (proj1 Hfacts))|]. split; assumption.
Qed.

Lemma os_sched_lock_fields_return_idle_non_idle :
  forall environment critical sg original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources (os_sched_fields_running_idle_non_idle_inv original) action) ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  os_sched_fields_running_idle_non_idle_inv original sg before ->
  task_idle_ready sg current.(TskState) /\ flag_pend_non_idle_at sg returned current.
Proof.
  intros environment critical sg original mask before returned current Hclients Hsources Hbefore.
  unfold os_sched_lock_fields_return_sources in Hsources; rewrite (proj1 (proj2 Hbefore)) in Hsources.
  destruct Hsources as [acquired Hsources].
  eapply (os_sched_fields_checkpoint_idle_non_idle (os_sched_lock_checkpoint true)
    environment critical sg original mask before acquired returned current);
    [exact Hclients|exact Hsources| |reflexivity|reflexivity|exact Hbefore].
  apply os_sched_lock_checkpoint_preserves_validity.
Qed.

(** This is the one-atom C environment obligation for Idle. Actual wake,
    status, creation and selected-return modules provide source-specific
    preservation lemmas; this interface does not classify an arbitrary
    registered action as one of those source programs. *)
Lemma os_sched_unlock_fields_prefix_idle :
  forall environment critical sg original mask before acquired restored unlocked,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_idle_inv action) ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  UCOS2_state_inv sg before -> task_idle_ready sg before.(TskState) ->
  task_idle_ready sg unlocked.(TskState).
Proof.
  intros environment critical sg original mask before acquired restored unlocked Hclients [Hfacts Hsources] Hvalid Hidle.
  assert (Hafter : os_sched_fields_idle_inv sg unlocked).
  { eapply (os_sched_fields_checkpoint_registered_invariant (os_sched_unlock_checkpoint true)
      environment critical os_sched_fields_idle_inv sg original mask before acquired restored unlocked);
      [exact Hclients|exact Hsources| |split; assumption].
    intros [Hvalid' Hidle']; split.
    - exact (os_sched_unlock_checkpoint_preserves_validity sg true acquired Hvalid').
    - exact Hidle'. }
  exact (proj2 Hafter).
Qed.

(** The existing projected SOURCE family supplies clear registration;
    the additional source theorem retains the multi pointer omitted by
    its older wait-field projection. Both use the same actual trace. *)
Lemma os_sched_fields_resumption_clear :
  forall external port critical sg original returned before after node,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after ->
  task_tcb_init_stack_same_call returned original ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  flag_active_event_clear node -> node.(tcbFlagNode) = 0 ->
  exists current,
    after.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some current /\
    flag_active_event_clear current /\ current.(tcbFlagNode) = 0.
Proof.
  intros external port critical sg original returned before after node Hclients Htrace Hsame Hnode
    [Hevent [Hmulti Hptr]] Hflag.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace) as [Hresources Hcontrol].
  assert (Hnone : sem_pend_task_unregistered node) by (repeat split; assumption).
  destruct (sem_pend_resumption_trace_preserves_unregistered critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None before false after
    original.(os_sched_call_stack).(stackLeaseSlot) node Hclients Hresources Hnode Hnone)
    as [current [Hcurrent [Hevent' [Hmulti' Hflag']]]].
  pose proof (tmr_task_resumption_trace_multi_pointer critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None before false after Hclients Hresources
    original.(os_sched_call_stack).(stackLeaseSlot)) as Hpointer.
  rewrite Hcurrent, Hnode in Hpointer; cbn in Hpointer.
  exists current; split.
  - rewrite (proj2 (proj2 Hsame)); exact Hcurrent.
  - split; [|exact Hflag']. split; [exact Hevent'|]. split; [exact Hmulti'|congruence].
Qed.

Lemma os_sched_fields_checkpoint_clear :
  forall checkpoint environment critical sg original mask before acquired returned current node,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  os_sched_fields_checkpoint_sources checkpoint environment critical sg original mask before acquired returned current ->
  (checkpoint acquired).(TskState) = acquired.(TskState) ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  flag_active_event_clear node -> node.(tcbFlagNode) = 0 ->
  exists next,
    current.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some next /\
    flag_active_event_clear next /\ next.(tcbFlagNode) = 0.
Proof.
  intros checkpoint environment critical sg original mask before acquired returned current node Hclients
    [entered [saved [Hsave [Hrestore Hsame]]]] Htasks Hnode Hclear Hflag.
  destruct Hsave as [Hsave_trace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsave_same : task_tcb_init_stack_same_call entered original) by (repeat split; assumption).
  destruct (os_sched_fields_resumption_clear environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original entered before acquired node
    Hclients Hsave_trace Hsave_same Hnode Hclear Hflag) as [middle [Hmiddle [Hclear' Hflag']]].
  eapply (os_sched_fields_resumption_clear environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg entered returned
    (checkpoint acquired) current middle);
    [exact Hclients|exact Hrestore|exact Hsame| |exact Hclear'|exact Hflag'].
  rewrite Htasks; exact Hmiddle.
Qed.

Lemma os_sched_unlock_fields_prefix_clear :
  forall environment critical sg original mask before acquired restored unlocked node,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  os_sched_unlock_fields_restored_facts environment critical sg original mask before acquired restored unlocked ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  flag_active_event_clear node -> node.(tcbFlagNode) = 0 ->
  forall current, unlocked.(TskState).(inUsedTaskStates)
    restored.(os_sched_call_stack).(stackLeaseSlot) = Some current ->
    flag_active_event_clear current /\ current.(tcbFlagNode) = 0.
Proof.
  intros environment critical sg original mask before acquired restored unlocked node Hclients [Hfacts Hsources]
    Hnode Hclear Hflag current Hcurrent.
  destruct (os_sched_fields_checkpoint_clear (os_sched_unlock_checkpoint true) environment critical sg
    original mask before acquired restored unlocked node Hclients Hsources eq_refl Hnode Hclear Hflag)
    as [next [Hnext Hfields]].
  assert (current = next) by congruence; subst current; exact Hfields.
Qed.

Lemma os_sched_lock_fields_return_clear :
  forall environment critical sg original mask before returned current node,
  (forall action, critical.(critical_region_clients) action -> sem_pend_projected_source_client action) ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  before.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  flag_active_event_clear node -> node.(tcbFlagNode) = 0 ->
  exists next, current.(TskState).(inUsedTaskStates) returned.(os_sched_call_stack).(stackLeaseSlot) = Some next /\
    flag_active_event_clear next /\ next.(tcbFlagNode) = 0.
Proof.
  intros environment critical sg original mask before returned current node Hclients Hsources Hnode Hclear Hflag.
  unfold os_sched_lock_fields_return_sources in Hsources; destruct before.(SchedState).(isRunning).
  - destruct Hsources as [acquired Hsources].
    eapply (os_sched_fields_checkpoint_clear (os_sched_lock_checkpoint true)
      environment critical sg original mask before acquired returned current node);
      [exact Hclients|exact Hsources|reflexivity|exact Hnode|exact Hclear|exact Hflag].
  - destruct Hsources as [-> ->]; exists node; split; [exact Hnode|]. split; assumption.
Qed.

Lemma os_sched_lock_fields_return_current_consistency :
  forall environment critical sg original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    sched_task_source_client environment.(task_stack_call_external) action) ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  UCOS2_state_inv sg before -> sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical sg original mask before returned current Hclients Hsources Hvalid Hcurrent.
  unfold os_sched_lock_fields_return_sources in Hsources; destruct before.(SchedState).(isRunning).
  - destruct Hsources as [acquired Hsources].
    assert (Hafter : os_sched_fields_current_inv sg current).
    { eapply (os_sched_fields_checkpoint_registered_invariant (os_sched_lock_checkpoint true)
        environment critical os_sched_fields_current_inv sg original mask before acquired returned current);
        [|exact Hsources| |split; assumption].
      - intros action Hin; eapply os_sched_fields_source_client_current_inv.
        + exact (critical_region_client_certificates critical action Hin).
        + apply Hclients; exact Hin.
      - intros [Hvalid' Hcurrent']; split.
        + exact (os_sched_lock_checkpoint_preserves_validity sg true acquired Hvalid').
        + exact Hcurrent'. }
    exact (proj2 Hafter).
  - destruct Hsources as [-> ->]; exact Hcurrent.
Qed.

Lemma os_sched_lock_fields_return_registered_current :
  forall environment critical sg original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_current_inv action) ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  UCOS2_state_inv sg before -> sched_current_consistency before.(TskState) before.(SchedState) ->
  sched_current_consistency current.(TskState) current.(SchedState).
Proof.
  intros environment critical sg original mask before returned current Hclients Hsources Hvalid Hcurrent.
  unfold os_sched_lock_fields_return_sources in Hsources; destruct before.(SchedState).(isRunning).
  - destruct Hsources as [acquired Hsources].
    eapply (os_sched_fields_checkpoint_current_consistency (os_sched_lock_checkpoint true)
      environment critical sg original mask before acquired returned current);
      [exact Hclients|exact Hsources| |reflexivity|reflexivity|exact Hvalid|exact Hcurrent].
    apply os_sched_lock_checkpoint_preserves_validity.
  - destruct Hsources as [-> ->]; exact Hcurrent.
Qed.

Lemma os_sched_lock_fields_return_idle :
  forall environment critical sg original mask before returned current,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources os_sched_fields_idle_inv action) ->
  os_sched_lock_fields_return_sources environment critical sg original mask before returned current ->
  UCOS2_state_inv sg before -> task_idle_ready sg before.(TskState) ->
  task_idle_ready sg current.(TskState).
Proof.
  intros environment critical sg original mask before returned current Hclients Hsources Hvalid Hidle.
  unfold os_sched_lock_fields_return_sources in Hsources; destruct before.(SchedState).(isRunning).
  - destruct Hsources as [acquired Hsources].
    assert (Hafter : os_sched_fields_idle_inv sg current).
    { eapply (os_sched_fields_checkpoint_registered_invariant (os_sched_lock_checkpoint true)
        environment critical os_sched_fields_idle_inv sg original mask before acquired returned current);
        [exact Hclients|exact Hsources| |split; assumption].
      intros [Hvalid' Hidle']; split.
      - exact (os_sched_lock_checkpoint_preserves_validity sg true acquired Hvalid').
      - exact Hidle'. }
    exact (proj2 Hafter).
  - destruct Hsources as [-> ->]; exact Hidle.
Qed.
