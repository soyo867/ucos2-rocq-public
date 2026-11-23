Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The C client trace already records the actual registered actions.
    Their existing certificates supply intermediate validity, while the
    existing Mutex configuration supplies the owner-use projection. No
    new history relation, platform law, or eventual-return premise is
    introduced. *)
Lemma mutex_del_registered_trace_owner_history : forall configuration sg observer
  event_observer before stopped after,
  UCOS2_state_inv sg before ->
  kernel_client_resource_trace (mutex_program_region configuration).(critical_region_clients)
    sg observer event_observer before stopped after ->
  mutex_owner_source_history sg before after /\ UCOS2_state_inv sg after.
Proof.
  intros configuration sg observer event_observer before stopped after Hvalid Htrace.
  revert Hvalid.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent
    Hstep Htail IH]; intro Hvalid.
  - split; [constructor|exact Hvalid].
  - pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates (mutex_program_region configuration) action Hin)
      sg before middle Hvalid Hstep) as Hmiddle.
    destruct (IH Hmiddle) as [Hhistory Hafter].
    split; [|exact Hafter].
    eapply mutex_owner_source_history_trans; [|exact Hhistory].
    eapply (mutex_program_region_protocol configuration sg); eassumption.
Qed.

(** Projection of one actual switching prefix. The current-storage and
    absent-key facts belong to THIS source cut. The saved binding and
    destination are for THIS hook result, not for all future callbacks.
    The raw C-return relation does not supply these safety facts by itself;
    the corresponding C/port producer obtains them from its owned world. *)
Lemma mutex_del_sched_switch_owner_history : forall external sg entry call sp saved
  hooked incoming resumed,
  UCOS2_state_inv sg entry ->
  os_sched_current_storage_binding sg call entry ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  mutex_program_source_client external.(os_sched_hook_action) ->
  kernel_client_step external.(os_sched_hook_action) sg
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      call.(os_sched_call_stack).(stackLeaseSlot) sp) hooked ->
  os_sched_saved_stack_binding call saved hooked ->
  os_sched_destination_binding external call saved hooked incoming resumed ->
  mutex_owner_source_history sg entry (os_sched_install_context call saved incoming hooked) /\
  UCOS2_state_inv sg (os_sched_install_context call saved incoming hooked).
Proof.
  intros external sg entry call sp saved hooked incoming resumed Hvalid Hbinding Hnone
    Hhook Hstep Hsaved_binding Hdestination.
  assert (Hprefix : UCOS2_state_inv sg (os_sched_prefix_state entry)).
  { apply os_sched_ready_checkpoint_preserves_validity; exact Hvalid. }
  assert (Hsaved : UCOS2_state_inv sg
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      call.(os_sched_call_stack).(stackLeaseSlot) sp)).
  { destruct Hbinding as [Horigin [Hcurrent [Hslot [Haddress [Hlive|Hfree]]]]].
    - destruct Hlive as [node [Hnode [Hid Hgeneration]]].
      unfold os_sched_save_current_sp; cbn [os_sched_prefix_state replace_SchedS TskState].
      rewrite Hnode.
      exact (os_sched_save_live_sp_preserves_validity sg (os_sched_prefix_state entry)
        node sp call.(os_sched_call_stack) Hprefix Hnode Hid Hgeneration Hnone).
    - destruct Hfree as [Hnode Himage].
      unfold os_sched_save_current_sp; cbn [os_sched_prefix_state replace_SchedS TskState].
      rewrite Hnode.
      exact (os_sched_save_free_sp_preserves_validity sg (os_sched_prefix_state entry)
        call.(os_sched_call_stack).(stackLeaseSlot) sp Hprefix). }
  pose proof (os_sched_hook_preserves_validity external sg _ hooked Hsaved Hstep) as Hhooked.
  split.
  - eapply mutex_owner_source_history_trans with (middle := os_sched_prefix_state entry).
    + apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
    + eapply mutex_owner_source_history_trans with
        (middle := os_sched_save_current_sp (os_sched_prefix_state entry)
          call.(os_sched_call_stack).(stackLeaseSlot) sp).
      * apply (mutex_program_saved_sp_source call.(os_sched_call_invocation) call.(os_sched_call_stack).(stackLeaseSlot)
          sp sg (os_sched_prefix_state entry)); reflexivity.
      * eapply mutex_owner_source_history_trans with (middle := hooked).
        -- eapply mutex_program_source_client_history; eassumption.
        -- apply mutex_owner_source_step_history; apply MutexOwnerSourceFrame; reflexivity.
  - apply os_sched_install_context_preserves_validity.
    + exact Hhooked.
    + exact Hsaved_binding.
    + destruct Hdestination as [_ [[node [Hnode [_ [Hpriority _]]]] _]].
      intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
      pose proof (proj1 (proj2 Hhooked)) as Htasks.
      assert (Hpriorities : forall tid t,
        hooked.(TskState).(inUsedTaskStates) tid = Some t -> task_priority_in_range sg t.(curPrio))
        by (unfold task_in_range in Htasks; tauto).
      eapply Hpriorities; exact Hnode.
Qed.

(** Del's actual OS_Sched annotation consumes [mutex_del_runtime_return].
    The modular Scheduler supplies the current physical world on the left;
    its owner-history component is reconstructed below from the unchanged
    Task/Event maps of the executed no-switch C prefix. The private pool is
    the actual current owner, never a private frame carried through an
    interruptible call. No current-ready assumption is needed for this
    consequence: C branch safety remains with the Scheduler producer. *)
Lemma mutex_del_sched_nonswitch_runtime_output : forall environment critical sg
  original returned mask entry current (frame : Assertion),
  mutex_program_selected_reachable sg entry ->
  mutex_del_private_types_non_mutex entry.(EventState) ->
  os_sched_requests_switch entry = false ->
  os_sched_c_return environment.(mutex_del_call_external) critical sg
    entry original returned current ->
  kernel_stack_call_closed environment.(mutex_del_call_continuations)
    (fun sg state => kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState))
    sg (task_stack_call_active_key original) returned mask current ** frame |--
  mutex_del_runtime_return environment environment.(mutex_del_call_external)
    environment.(mutex_del_call_platform) sg original mask ** frame.
Proof.
  intros environment critical sg original returned mask entry current frame Hreachable Htypes
    Hnoswitch Hreturn.
  unfold os_sched_c_return in Hreturn; rewrite Hnoswitch in Hreturn.
  destruct Hreturn as [-> ->].
  assert (Hreachable_after : mutex_program_selected_reachable sg (os_sched_prefix_state entry)).
  { eapply mutex_program_source_step_reachable; [exact Hreachable|].
    apply MutexOwnerSourceFrame; reflexivity. }
  unfold mutex_del_runtime_return, mutex_del_runtime_return_at.
  Exists original (os_sched_prefix_state entry) environment.
  unfold mutex_del_callsite_environment, kernel_stack_call_same_call,
    kernel_stack_call_closed, kernel_stack_inv, mutex_del_stack_resources.
  change (mutex_del_private_types_non_mutex (os_sched_prefix_state entry).(EventState)) in Htypes.
  entailer!.
Qed.

(** A switched return consumes the SAME explicit C/port/registered-client
    witnesses and the same current heap. The actual saved-binding and
    destination observations are not universal future-safety assumptions.

    The exposed private-Type fact is deliberately separate: the existing
    MutexProgramConfiguration only classifies used Task/Event maps. Its
    OtherFields case does not constrain eventPrivate. A concrete creator
    or registry producer must supply [Htypes] for this current cut using
    the existing private-source proofs; owner history alone cannot do so.
    Consequently this lemma is a consumer, not a complete public Scheduler
    implementation theorem or a new guarantee for arbitrary clients. *)
Lemma mutex_del_sched_switched_runtime_output : forall environment configuration sg
  original returned mask before entry sp saved hooked incoming resumed stopped scheduled current
  (frame : Assertion),
  let critical := mutex_program_region configuration in
  let external := environment.(mutex_del_call_external) in
  let installed := os_sched_install_context original saved incoming hooked in
  UCOS2_state_inv sg before ->
  mutex_program_selected_reachable sg before ->
  critical_region_interval critical sg original.(os_sched_call_invocation) before entry ->
  os_sched_requests_switch entry = true ->
  os_sched_current_storage_binding sg original entry ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  external.(os_sched_arch_save_source) original sp saved ->
  mutex_program_source_client external.(os_sched_hook_action) ->
  kernel_client_step external.(os_sched_hook_action) sg
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      original.(os_sched_call_stack).(stackLeaseSlot) sp) hooked ->
  os_sched_saved_stack_binding original saved hooked ->
  os_sched_destination_binding external original saved hooked incoming resumed ->
  kernel_client_trace critical.(critical_region_clients) sg original.(os_sched_call_invocation)
    installed stopped scheduled ->
  orb (kernel_client_stops external.(os_sched_hook_action) original.(os_sched_call_invocation))
    stopped = false ->
  external.(os_sched_arch_resume_source) original returned ->
  kernel_stack_call_same_call returned original ->
  task_invocation_active scheduled.(TskState) original.(os_sched_call_invocation)
    original.(os_sched_call_origin) ->
  scheduled.(SchedState).(curTaskID) = Some original.(os_sched_call_stack).(stackLeaseSlot) ->
  scheduled.(TskState).(parkedTaskStacks) (task_stack_key original.(os_sched_call_stack)) = None ->
  critical_region_interval critical sg original.(os_sched_call_invocation) scheduled current ->
  mutex_del_private_types_non_mutex current.(EventState) ->
  kernel_stack_call_closed environment.(mutex_del_call_continuations)
    (fun sg state => kernel_program_inv sg state ** event_private_pool_rep sg state.(EventState))
    sg (task_stack_call_active_key original) returned mask current ** frame |--
  (coq_prop (os_sched_c_return external critical sg entry original returned scheduled /\
      mutex_owner_source_history sg before current) &&
    mutex_del_runtime_return environment external environment.(mutex_del_call_platform)
      sg original mask) ** frame.
Proof.
  intros environment configuration sg original returned mask before entry sp saved hooked incoming resumed
    stopped scheduled current frame critical external installed Hvalid Hreachable Hentry Hswitch Hbinding
    Hnone Hsave Hhook Hhook_step Hsaved_binding Hdestination Htrace Hnormal Hresume Hsame Hactive
    Hcurrent Htaken Hafter Htypes.
  pose proof (proj1 (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before entry Hentry Hvalid)) as Hentry_valid.
  assert (Hentry_history : mutex_owner_source_history sg before entry).
  { eapply mutex_owner_region_interval_history.
    - apply mutex_program_region_protocol.
    - constructor.
    - exact Hvalid.
    - exact Hentry. }
  destruct (mutex_del_sched_switch_owner_history external sg entry original sp saved hooked incoming
    resumed Hentry_valid Hbinding Hnone Hhook Hhook_step Hsaved_binding Hdestination)
    as [Hinstalled_history Hinstalled_valid].
  fold installed in Hinstalled_history, Hinstalled_valid.
  destruct (mutex_del_registered_trace_owner_history configuration sg
    original.(os_sched_call_invocation) None installed stopped scheduled Hinstalled_valid Htrace)
    as [Hscheduled_history Hscheduled_valid].
  assert (Hhistory : mutex_owner_source_history sg before current).
  { eapply mutex_owner_region_interval_history.
    - apply mutex_program_region_protocol.
    - eapply mutex_owner_source_history_trans; [exact Hentry_history|].
      eapply mutex_owner_source_history_trans; eassumption.
    - exact Hscheduled_valid.
    - exact Hafter. }
  assert (Hreachable_current : mutex_program_selected_reachable sg current).
  { eapply mutex_program_source_history_reachable; eassumption. }
  assert (Hreturn : os_sched_c_return external critical sg entry original returned scheduled).
  { unfold os_sched_c_return; rewrite Hswitch.
    exists installed; split.
    - split; [exact Hswitch|].
      exists sp, saved, hooked, incoming, resumed.
      split; [exact Hsave|]. split; [exact Hhook_step|].
      split; [exact Hdestination|reflexivity].
    - split; [exists stopped; split; assumption|].
      destruct Hsame as [Hi [Ho Hstack]].
      exact (conj Hresume (conj Hi (conj Ho (conj Hstack
        (conj Hactive (conj Hcurrent Htaken)))))). }
  unfold mutex_del_runtime_return, mutex_del_runtime_return_at.
  Exists returned current environment.
  unfold mutex_del_callsite_environment, kernel_stack_call_closed, kernel_stack_inv,
    mutex_del_stack_resources.
  unfold external; entailer!.
Qed.
