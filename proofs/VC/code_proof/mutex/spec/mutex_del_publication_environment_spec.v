Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The selected source already adopted in main keeps allocation, payload
    initialization, wait-list initialization and Type-last within ONE
    masked operation. Reuse its checked endpoint instead of registering
    its historical Allocate/private-Store cuts as independently exposed
    MutexCreate environment steps. This is one source client, not an
    all-kernel registration or a whole public Save/Restore producer. *)
Definition mutex_del_publication_client (actor : option nat) (pcp : Priority)
  : KernelClientAction :=
  {| kernel_client_actor := actor;
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       valid_mutex_pcp sg pcp /\
       exists result, MutexCreatePublication.critical_operation sg pcp before result after |}.

(** The client's range condition comes from the existing source guard,
    with nonnegativity supplied by the C unsigned parameter. Early
    rejected calls remain represented; they are not filtered out. *)
Lemma mutex_del_publication_call_client_cut :
  forall critical sg invocation pcp before result after,
  0 <= pcp ->
  MutexCreatePublication.call_relation critical sg invocation pcp before result after ->
  ((result = (OS_ERR_PRIO_INVALID, None) \/ result = (OS_ERR_CREATE_ISR, None)) /\
   after = before) \/
  exists entry checkpoint,
    critical_region_interval critical sg invocation before entry /\
    MutexCreatePublication.critical_operation sg pcp entry result checkpoint /\
    kernel_client_step (mutex_del_publication_client (Some invocation) pcp) sg entry checkpoint /\
    critical_region_interval critical sg invocation checkpoint after.
Proof.
  intros critical sg invocation pcp before result after Hnonnegative Hcall.
  unfold MutexCreatePublication.call_relation in Hcall.
  destruct (MutexCreateCall.priority_rejected sg pcp) eqn:Haccepted.
  - left; tauto.
  - destruct (0 <? before.(IntrState).(intNesting)).
    + left; tauto.
    + destruct Hcall as [entry [checkpoint [Hacquire [Hoperation Hrestore]]]].
      right; exists entry, checkpoint; split; [exact Hacquire|].
      split; [exact Hoperation|]. split; [|exact Hrestore].
      split; [eapply MutexCreateCall.priority_accepted_in_range; eassumption|].
      exists result; exact Hoperation.
Qed.

Lemma mutex_del_publication_private_map_eq : forall sg pcp before result after,
  UCOS2_state_inv sg before ->
  MutexCreatePublication.critical_operation sg pcp before result after ->
  after.(EventState).(eventLifecycle).(eventPrivate) =
    before.(EventState).(eventLifecycle).(eventPrivate).
Proof.
  intros sg pcp before result after Hvalid.
  unfold MutexCreatePublication.critical_operation.
  destruct (MutexCreateCall.priority_slot_busy sg pcp before).
  - intros [_ ->]; reflexivity.
  - destruct before.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
    + intros [_ ->]; reflexivity.
    + intros [_ ->].
      pose proof Hvalid as [_ [_ [_ [[Hpool _] _]]]].
      pose proof (proj2 (event_pool_free_unallocated sg before.(EventState) eid Hpool
        ltac:(rewrite Hhead; left; reflexivity))) as Hnone.
      apply functional_extensionality; intro slot.
      unfold mutex_create_state, mutex_create_event_state, event_publish, event_detach_head;
        cbn [replace_EventS replace_TskS EventState eventLifecycle eventPrivate].
      unfold kernel_map_set; destruct (Z.eq_dec slot eid); subst; auto.
Qed.

Lemma mutex_del_publication_client_certificate : forall actor pcp,
  KernelClientCertificate (mutex_del_publication_client actor pcp).
Proof.
  intros actor pcp; constructor.
  - intros sg before after Hvalid [Hpcp [result Hstep]].
    eapply MutexCreatePublication.critical_operation_preserves_validity; eassumption.
  - intros sg before after observer Hvalid [Hpcp [result Hstep]] Hforeign.
    unfold MutexCreatePublication.critical_operation in Hstep.
    destruct (MutexCreateCall.priority_slot_busy sg pcp before).
    + destruct Hstep as [_ ->]; reflexivity.
    + destruct before.(EventState).(unUsedEventStates); destruct Hstep as [_ ->]; reflexivity.
  - intros sg before after observer origin Hvalid [Hpcp [result Hstep]] Hnormal Hactive.
    unfold MutexCreatePublication.critical_operation in Hstep.
    destruct (MutexCreateCall.priority_slot_busy sg pcp before).
    + destruct Hstep as [_ ->]; exact Hactive.
    + destruct before.(EventState).(unUsedEventStates); destruct Hstep as [_ ->]; exact Hactive.
  - intros sg before after observer Hvalid [Hpcp [result Hstep]] Hforeign.
    apply event_creation_frame_map_eq.
    eapply mutex_del_publication_private_map_eq; eassumption.
Qed.

(** Publication preserves a public SLOT, not the old instance. In the
    free-head case the witness deliberately changes to the newly created
    node/generation. No raw-pointer ABA exclusion is hidden in this fact. *)
Lemma mutex_del_publication_preserves_public_slot : forall sg pcp before result after eid observed,
  MutexCreatePublication.critical_operation sg pcp before result after ->
  sem_query_public_slot before eid observed ->
  exists current, sem_query_public_slot after eid current.
Proof.
  intros sg pcp before result after eid observed.
  unfold MutexCreatePublication.critical_operation.
  destruct (MutexCreateCall.priority_slot_busy sg pcp before).
  - intros [_ ->] Hslot; exists observed; exact Hslot.
  - destruct before.(EventState).(unUsedEventStates) as [|created rest] eqn:Hhead.
    + intros [_ ->] Hslot; exists observed; exact Hslot.
    + intros [_ ->] Hslot.
      destruct (Z.eq_dec eid created) as [->|Hdifferent].
      * exists (mutex_create_node pcp before.(EventState).(eventLifecycle).(eventNextGeneration)
          (mutex_create_storage before.(EventState) created)); left.
        unfold mutex_query_lookup, mutex_create_state, mutex_create_event_state, event_publish;
          cbn [replace_EventS replace_TskS EventState inUsedEventStates].
        apply kernel_map_set_same.
      * exists observed; destruct Hslot as [Hused|[Hnone Hfree]].
        -- left; unfold mutex_query_lookup in *.
           unfold mutex_create_state, mutex_create_event_state, event_publish;
             cbn [replace_EventS replace_TskS EventState inUsedEventStates].
           rewrite kernel_map_set_other by exact Hdifferent; exact Hused.
        -- right; split.
           ++ unfold mutex_create_state, mutex_create_event_state, event_publish;
                cbn [replace_EventS replace_TskS EventState inUsedEventStates].
              rewrite kernel_map_set_other by exact Hdifferent; exact Hnone.
           ++ change (In eid rest); rewrite Hhead in Hfree; simpl in Hfree.
              destruct Hfree as [Hequal|Hin]; [congruence|exact Hin].
Qed.

Lemma mutex_del_publication_preserves_owner_use : forall sg pcp before result after,
  MutexCreatePublication.critical_operation sg pcp before result after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros sg pcp before result after.
  unfold MutexCreatePublication.critical_operation.
  destruct (MutexCreateCall.priority_slot_busy sg pcp before).
  - intros [_ ->] Huse; exact Huse.
  - destruct before.(EventState).(unUsedEventStates) as [|created rest].
    + intros [_ ->] Huse; exact Huse.
    + intros [_ ->] Huse eid event mutex owner node Hget Htype Hmutex Howner Hnode.
      unfold mutex_create_state, mutex_create_event_state, event_publish in Hget;
        cbn [replace_EventS replace_TskS EventState inUsedEventStates] in Hget.
      unfold kernel_map_set in Hget; destruct (Z.eq_dec eid created).
      * injection Hget as <-; cbn in Hmutex; injection Hmutex as <-; discriminate Howner.
      * eapply Huse; eassumption.
Qed.

Definition mutex_del_publication_clients (action : KernelClientAction) : Prop :=
  exists actor pcp, action = mutex_del_publication_client actor pcp.

Lemma mutex_del_publication_trace_preserves_public_slot :
  forall sg observer event_observer before stopped after eid observed,
  kernel_client_resource_trace mutex_del_publication_clients sg observer event_observer
    before stopped after ->
  sem_query_public_slot before eid observed ->
  exists current, sem_query_public_slot after eid current.
Proof.
  intros sg observer event_observer before stopped after eid observed Htrace.
  revert observed; induction Htrace as
    [state|action initial middle final stopped Hin Hforeign Hevent Hstep Htail IH]; intros observed Hslot.
  - exists observed; exact Hslot.
  - destruct Hin as [actor [pcp ->]]; destruct Hstep as [_ [result Hstep]].
    destruct (mutex_del_publication_preserves_public_slot sg pcp initial result middle eid observed
      Hstep Hslot) as [current Hcurrent].
    exact (IH current Hcurrent).
Qed.

(** Concrete consumer for Del's protected type acquisition. It uses the
    ACTUAL acquired program heap and returns the one table plus the exact
    type residual; the pure trace does not generate those resources.
    Endpoint validity is derived from this client's checked certificate
    and initial validity, not supplied as a desired final-state premise.
    The trace family is exactly this adopted publication operation only,
    not an assumption that arbitrary kernel clients preserve a slot. *)
Lemma mutex_del_publication_trace_type_load :
  forall sg observer event_observer before stopped entry eid observed (frame : Assertion) heap,
  kernel_client_resource_trace mutex_del_publication_clients sg observer event_observer
    before stopped entry ->
  UCOS2_state_inv sg before ->
  sem_query_public_slot before eid observed ->
  (kernel_program_rep sg entry ** frame) heap ->
  exists current,
    UCOS2_state_inv sg entry /\ sem_query_public_slot entry eid current /\
    uchar_load (event_addr sg eid + OSEventType_off)
      (event_slot_type_value entry.(EventState) eid) heap /\
    ((event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value entry.(EventState) eid **
      sem_query_type_frame sg entry eid ** unmap_table_rep sg ** frame) heap.
Proof.
  intros sg observer event_observer before stopped entry eid observed frame heap Htrace Hvalid Hslot Hheap.
  assert (Hcert : forall action, mutex_del_publication_clients action -> KernelClientCertificate action).
  { intros action [actor [pcp ->]]; apply mutex_del_publication_client_certificate. }
  pose proof (proj1 (kernel_client_resource_trace_transports_resources
    mutex_del_publication_clients sg observer event_observer before stopped entry Hcert Htrace Hvalid))
    as Hentry.
  destruct (mutex_del_publication_trace_preserves_public_slot sg observer event_observer
    before stopped entry eid observed Htrace Hslot) as [current Hcurrent].
  assert (Hclose : kernel_program_rep sg entry ** frame |-- kernel_program_inv sg entry ** frame).
  { unfold kernel_program_inv; entailer!. }
  assert (Hopen : kernel_program_inv sg entry ** frame |--
    (event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value entry.(EventState) eid **
      sem_query_type_frame sg entry eid ** unmap_table_rep sg ** frame).
  { rewrite kernel_program_inv_split_unmap.
    sep_apply_l_atomic (sem_query_type_split_full sg entry eid current Hcurrent); entailer!. }
  pose proof (Hopen heap (Hclose heap Hheap)) as Howned.
  exists current; split; [exact Hentry|]. split; [exact Hcurrent|]. split; [|exact Howned].
  apply framed_uchar_store_load with
    (frame := sem_query_type_frame sg entry eid ** unmap_table_rep sg ** frame).
  assert (Hreorder : (event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value entry.(EventState) eid **
      sem_query_type_frame sg entry eid ** unmap_table_rep sg ** frame |--
    (event_addr sg eid + OSEventType_off) # UChar |->
      event_slot_type_value entry.(EventState) eid **
      (sem_query_type_frame sg entry eid ** unmap_table_rep sg ** frame)) by entailer!.
  exact (Hreorder heap Howned).
Qed.
