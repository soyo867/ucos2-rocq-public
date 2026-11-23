Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait Ucos2Verify.lib.tick.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wake_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_post_call_spec.
Import TaskStateDef EventStateDef ListNotations.
Local Open Scope Z_scope.

(** Only the three ordinary call-point fields. This predicate says
    nothing about ready/running, priority, ownership or the Idle task.
    Its initial occurrence is conditional on the actual busy/wait arm;
    immediate acquisition and the earlier error arms do not consume it. *)
Definition mutex_pend_entry_fields (tid : TaskID) (state : UCOS2_Verify_State) : Prop :=
  exists node, state.(TskState).(inUsedTaskStates) tid = Some node /\
    sem_pend_task_unregistered node.

Lemma mutex_pend_entry_fields_task_frame : forall tid before after,
  after.(TskState).(inUsedTaskStates) = before.(TskState).(inUsedTaskStates) ->
  mutex_pend_entry_fields tid before -> mutex_pend_entry_fields tid after.
Proof. intros tid before after Hmap [node [Hnode Hfields]]; exists node; rewrite Hmap; auto. Qed.

Lemma mutex_pend_entry_fields_task_update : forall tid before selected old new,
  before.(TskState).(inUsedTaskStates) selected = Some old ->
  (sem_pend_task_unregistered old -> sem_pend_task_unregistered new) ->
  mutex_pend_entry_fields tid before ->
  mutex_pend_entry_fields tid
    (replace_TskS (glob_task_set_usedtask before.(TskState) selected new) before).
Proof.
  intros tid before selected old new Hselected Hupdate [node [Hnode Hfields]].
  unfold mutex_pend_entry_fields; cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
  destruct (Z.eqb tid selected) eqn:E.
  - apply Z.eqb_eq in E; subst tid; assert (node = old) by congruence; subst node.
    exists new; split; [reflexivity|apply Hupdate; exact Hfields].
  - exists node; auto.
Qed.

Lemma mutex_pend_equal_fields_preserve_unregistered : forall old new,
  new.(eventPtr) = old.(eventPtr) ->
  new.(eventMultiWaitEvents) = old.(eventMultiWaitEvents) ->
  new.(tcbFlagNode) = old.(tcbFlagNode) ->
  sem_pend_task_unregistered old -> sem_pend_task_unregistered new.
Proof.
  unfold sem_pend_task_unregistered; intros old new He Hm Hf [He0 [Hm0 Hf0]];
    repeat split; congruence.
Qed.

(** EventTaskRdy is polymorphic in the pending bit. In particular the
    real Mutex Post/Del wake clears registration without being a PendSem
    source operation. No claim is made about their readiness effects. *)
Lemma mutex_pend_wake_preserves_entry_fields : forall sg tid state eid event selected old kind message result,
  state.(TskState).(inUsedTaskStates) selected = Some old ->
  mutex_pend_entry_fields tid state ->
  mutex_pend_entry_fields tid (event_wake_state sg state eid event selected old kind message result).
Proof.
  intros; eapply mutex_pend_entry_fields_task_update; try eassumption.
  intros [He [Hm Hf]]; unfold sem_pend_task_unregistered; repeat split; assumption || reflexivity.
Qed.

Lemma mutex_pend_event_task_rdy_preserves_entry_fields : forall sg tid state eid kind message result priority after,
  event_task_rdy sg state eid kind message result = Some (priority, after) ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid after.
Proof.
  intros sg tid state eid kind message result priority after Hstep Hfields.
  unfold event_task_rdy in Hstep.
  destruct (state.(EventState).(inUsedEventStates) eid) as [event|]; [|discriminate].
  destruct (state.(TskState).(prioTbl) (event_wait_priority state.(TskState) event))
    as [| |selected]; try discriminate.
  destruct (state.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hselected; [|discriminate].
  injection Hstep as Hpriority Hafter; subst after.
  eapply mutex_pend_wake_preserves_entry_fields; eassumption.
Qed.

Lemma mutex_pend_broadcast_preserves_entry_fields : forall sg tid eid kind message result state priorities after,
  event_broadcast sg eid kind message result state priorities after ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid after.
Proof.
  intros sg tid eid kind message result state priorities after Hloop; induction Hloop; intro Hfields.
  - exact Hfields.
  - apply IHHloop; eapply mutex_pend_event_task_rdy_preserves_entry_fields; eassumption.
Qed.

Lemma mutex_del_priority_preserves_pend_entry_fields : forall sg tid state ceiling owner old priority,
  state.(TskState).(inUsedTaskStates) owner = Some old ->
  mutex_pend_entry_fields tid state ->
  mutex_pend_entry_fields tid (mutex_del_owner_priority_state sg state ceiling owner old priority).
Proof.
  intros sg tid state ceiling owner old priority Hold Hfields.
  unfold mutex_del_owner_priority_state; destruct Z.eq_dec; [exact Hfields|].
  eapply mutex_pend_entry_fields_task_update; [exact Hold| |exact Hfields].
  apply mutex_pend_equal_fields_preserve_unregistered; reflexivity.
Qed.

Lemma mutex_del_prepare_preserves_pend_entry_fields : forall sg tid mutex state after,
  mutex_del_prepare sg mutex state after ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid after.
Proof.
  intros sg tid mutex state after Hprepare Hfields; unfold mutex_del_prepare in Hprepare.
  destruct Z.eq_dec; [subst; exact Hfields|].
  destruct mutex.(mfOwner); [|subst; exact Hfields].
  destruct Hprepare as [old [priority [Hold [_ ->]]]].
  eapply mutex_del_priority_preserves_pend_entry_fields; eassumption.
Qed.

Lemma mutex_post_prepare_preserves_pend_entry_fields : forall sg tid mutex owner state after,
  mutex_post_prepare sg mutex owner state after ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid after.
Proof.
  intros sg tid mutex owner state after Hprepare Hfields; unfold mutex_post_prepare in Hprepare.
  destruct Z.eq_dec; [subst; exact Hfields|].
  destruct Hprepare as [old [priority [Hold [_ ->]]]].
  rewrite mutex_post_owner_priority_state_ceiling_view_eq.
  eapply mutex_del_priority_preserves_pend_entry_fields; eassumption.
Qed.

Lemma mutex_post_critical_preserves_pend_entry_fields : forall sg tid eid caller state code schedule after,
  mutex_post_critical sg eid caller state code schedule after ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid after.
Proof.
  intros sg tid eid caller state code schedule after Hstep Hfields; destruct Hstep.
  - exact Hfields.
  - change (mutex_pend_entry_fields tid prepared).
    eapply mutex_post_prepare_preserves_pend_entry_fields; eassumption.
  - change (mutex_pend_entry_fields tid woken).
    eapply mutex_pend_event_task_rdy_preserves_entry_fields; [eassumption|].
    eapply mutex_post_prepare_preserves_pend_entry_fields; eassumption.
Qed.

Lemma mutex_del_critical_preserves_pend_entry_fields : forall sg tid eid opt state result after,
  mutex_del_critical sg eid opt state result after ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid after.
Proof.
  intros sg tid eid opt state result after [event [mutex [He [Htype [Hm Hstep]]]]] Hfields.
  destruct Z.eq_dec.
  - destruct Z.eq_dec.
    + destruct Hstep as [prepared [Hprepare [-> Hresult]]].
      change (mutex_pend_entry_fields tid prepared).
      eapply mutex_del_prepare_preserves_pend_entry_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
  - destruct Z.eq_dec.
    + destruct Hstep as [prepared [priorities [drained [Hprepare [Hloop [-> Hresult]]]]]].
      change (mutex_pend_entry_fields tid drained).
      eapply mutex_pend_broadcast_preserves_entry_fields; [exact Hloop|].
      eapply mutex_del_prepare_preserves_pend_entry_fields; eassumption.
    + destruct Hstep as [-> Hresult]; exact Hfields.
Qed.

Lemma mutex_pend_publication_preserves_entry_fields : forall sg tid publication state,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  mutex_pend_entry_fields tid state ->
  mutex_pend_entry_fields tid (task_create_stack_publication_state sg publication state).
Proof.
  intros sg tid publication state Hvalid Hinput [old [Hold Hfields]].
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) node.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node tid old Hfresh Hold)
    as [current [Hcurrent Heq]].
  exists current; split; [exact Hcurrent|].
  eapply mutex_pend_equal_fields_preserve_unregistered; [exact (f_equal eventPtr Heq)|
    exact (f_equal eventMultiWaitEvents Heq)|exact (f_equal tcbFlagNode Heq)|exact Hfields].
Qed.

Lemma mutex_pend_tick_preserves_entry_fields : forall sg tid state selected old,
  state.(TskState).(inUsedTaskStates) selected = Some old ->
  mutex_pend_entry_fields tid state -> mutex_pend_entry_fields tid (tick_task_step sg selected old state).
Proof.
  intros; unfold mutex_pend_entry_fields in *; rewrite tick_task_step_task_state_eq by assumption.
  change (mutex_pend_entry_fields tid
    (replace_TskS (glob_task_set_usedtask state.(TskState) selected (tick_task_update old)) state)).
  eapply mutex_pend_entry_fields_task_update; try eassumption.
  intros [He [Hm Hf]]; unfold tick_task_update; destruct (old.(dly) =? 0);
    [repeat split; assumption|].
  destruct (old.(dly) - 1 =? 0); repeat split; assumption.
Qed.

Lemma mutex_pend_save_sp_preserves_entry_fields : forall tid state selected sp,
  mutex_pend_entry_fields tid state ->
  mutex_pend_entry_fields tid (os_sched_save_current_sp state selected sp).
Proof.
  intros tid state selected sp Hfields; unfold os_sched_save_current_sp.
  destruct (state.(TskState).(inUsedTaskStates) selected) as [old|] eqn:Hold; [|exact Hfields].
  eapply mutex_pend_entry_fields_task_update; [exact Hold| |exact Hfields].
  apply mutex_pend_equal_fields_preserve_unregistered; reflexivity.
Qed.

(** This is an obligation on each ACTUAL registered C client, not a new
    registry, history, state field, or platform promise. Foreign/stopping
    guards and the live invocation are from the same source trace. They
    permit actual lifecycle clients to use continuation non-retirement;
    an arbitrary action is not admitted merely because it is registered. *)
Definition mutex_pend_entry_source_client observer tid generation (action : KernelClientAction) : Prop :=
  forall sg before after,
    kernel_client_actor action <> Some observer -> kernel_client_stops action observer = false ->
    UCOS2_state_inv sg before ->
    task_invocation_active before.(TskState) observer (RunningInvocation tid generation) ->
    kernel_client_step action sg before after ->
    mutex_pend_entry_fields tid before -> mutex_pend_entry_fields tid after.

Lemma mutex_pend_sem_source_preserves_entry_fields : forall observer tid generation action,
  sem_pend_projected_source_client action -> mutex_pend_entry_source_client observer tid generation action.
Proof.
  intros observer tid generation action Hsource sg before after Hforeign Hstop Hvalid Hactive Hstep
    [old [Hold Hfields]].
  destruct (sem_pend_source_client_projection action sg before after tid old Hsource Hstep Hold)
    as [current [Hcurrent Heffects]].
  exists current; split; [exact Hcurrent|].
  eapply sem_pend_wait_trace_preserves_unregistered; eassumption.
Qed.

Lemma mutex_pend_client_trace_preserves_entry_fields : forall clients sg observer event_observer
  before stopped after tid generation,
  (forall action, clients action -> KernelClientCertificate action) ->
  (forall action, clients action -> mutex_pend_entry_source_client observer tid generation action) ->
  kernel_client_resource_trace clients sg observer event_observer before stopped after ->
  stopped = false -> UCOS2_state_inv sg before ->
  task_invocation_active before.(TskState) observer (RunningInvocation tid generation) ->
  mutex_pend_entry_fields tid before -> mutex_pend_entry_fields tid after.
Proof.
  intros clients sg observer event_observer before stopped after tid generation Hcert Hclients Htrace.
  induction Htrace as [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hnormal Hvalid Hactive Hfields; [exact Hfields|].
  apply orb_false_iff in Hnormal; destruct Hnormal as [Hstop Hnormal].
  apply IH; [exact Hnormal| | |].
  - exact (kernel_client_preserves_validity action (Hcert action Hin) sg before middle Hvalid Hstep).
  - exact (kernel_client_preserves_continuation action (Hcert action Hin) sg before middle
      observer (RunningInvocation tid generation) Hvalid Hstep Hstop Hactive).
  - exact (Hclients action Hin sg before middle Hforeign Hstop Hvalid Hactive Hstep Hfields).
Qed.

Lemma mutex_pend_return_source_preserves_entry_fields : forall external port critical sg
  original returned before after,
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client original.(os_sched_call_invocation)
      original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) action) ->
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin) before false
    returned.(os_sched_call_origin) after ->
  kernel_call_normal_return original before returned after ->
  mutex_pend_entry_fields original.(os_sched_call_stack).(stackLeaseSlot) before ->
  exists node, after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_task_unregistered node.
Proof.
  intros external port critical sg original returned before after Hclients Hvalid Hsource Htrace
    Hnormal Hfields.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources Hcontrol].
  pose proof (kernel_resumption_resource_trace_erases _ _ _ _ _ _ _ Hresources) as Hraw.
  assert (Hactive : task_invocation_active before.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration))).
  { destruct Hsource as [Horigin [Hactive Hcurrent]]; rewrite <- Horigin; exact Hactive. }
  destruct (mutex_pend_client_trace_preserves_entry_fields _ _ _ _ _ _ _ _ _
    critical.(critical_region_client_certificates) Hclients Hraw eq_refl Hvalid Hactive Hfields)
    as [node [Hnode Hnone]].
  assert (Hsource_after : kernel_call_task_source original after).
  { eapply task_tcb_init_stack_registered_source_preserved;
      [exact Hvalid|exact (proj1 Hnormal)|exact Htrace|exact Hsource]. }
  destruct (kernel_call_task_source_current_at original after Hsource_after)
    as [Hcurrent [found [Hfound Hgeneration]]].
  assert (found = node) by congruence; subst found; exists node; auto.
Qed.

Lemma mutex_pend_save_source_preserves_entry_fields : forall external port critical sg
  original returned mask saved before after,
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client original.(os_sched_call_invocation)
      original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) action) ->
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_call_save_source external port critical sg original returned mask saved before after ->
  mutex_pend_entry_fields original.(os_sched_call_stack).(stackLeaseSlot) before ->
  exists node, after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_task_unregistered node.
Proof.
  intros external port critical sg original returned mask saved before after Hclients Hvalid Hsource
    Hsave Hfields.
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources Hcontrol].
  pose proof (kernel_resumption_resource_trace_erases _ _ _ _ _ _ _ Hresources) as Hraw.
  assert (Hactive : task_invocation_active before.(TskState) original.(os_sched_call_invocation)
    (RunningInvocation original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration))).
  { destruct Hsource as [Horigin [Hactive Hcurrent]]; rewrite <- Horigin; exact Hactive. }
  destruct (mutex_pend_client_trace_preserves_entry_fields _ _ _ _ _ _ _ _ _
    critical.(critical_region_client_certificates) Hclients Hraw eq_refl Hvalid Hactive Hfields)
    as [node [Hnode Hnone]].
  pose proof (kernel_call_save_source_preserves_task_source _ _ _ _ _ _ _ _ _ _
    Hvalid Hsource Hsave) as Hreturned.
  destruct (kernel_call_task_source_current_at returned after Hreturned)
    as [Hcurrent [found [Hfound Hgeneration]]].
  rewrite Hs in Hfound, Hgeneration.
  assert (found = node) by congruence; subst found; exists node; auto.
Qed.

(** Exposes the branch-conditioned use explicitly. [wait_required] is
    the API owner's actual acquired busy observation, not an assumption
    that all valid/early/immediate calls were ready and unlinked. *)
Lemma mutex_pend_save_source_preserves_entry_fields_when : forall external port critical sg
  original returned mask saved before after (wait_required : UCOS2_Verify_State -> Prop),
  (forall action, critical.(critical_region_clients) action ->
    mutex_pend_entry_source_client original.(os_sched_call_invocation)
      original.(os_sched_call_stack).(stackLeaseSlot)
      original.(os_sched_call_stack).(stackLeaseGeneration) action) ->
  UCOS2_state_inv sg before -> kernel_call_task_source original before ->
  kernel_call_save_source external port critical sg original returned mask saved before after ->
  (wait_required after -> mutex_pend_entry_fields original.(os_sched_call_stack).(stackLeaseSlot) before) ->
  wait_required after ->
  exists node, after.(TskState).(inUsedTaskStates) original.(os_sched_call_stack).(stackLeaseSlot) = Some node /\
    node.(taskGeneration) = original.(os_sched_call_stack).(stackLeaseGeneration) /\
    sem_pend_task_unregistered node.
Proof. intros; eapply mutex_pend_save_source_preserves_entry_fields; eauto. Qed.
