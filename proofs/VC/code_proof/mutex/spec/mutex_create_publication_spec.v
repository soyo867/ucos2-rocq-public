Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.micromega.Lia Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Import UCOS2_C_Rules ListNotations TaskStateDef EventStateDef EventFieldStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected-profile source semantics of the publication variant.  The
    protected operation ends with the initialized live ECB.  Restore may
    run the environment: its returned state is not frozen at publication.
    Raw-pointer reuse is deliberately not excluded by this relation. *)
Module MutexCreatePublication.

Definition critical_operation (sg : StableGlobVars) (pcp : Priority)
  : program UCOS2_Verify_State (OSErrCode * option EventID) :=
  fun entry result checkpoint =>
    if MutexCreateCall.priority_slot_busy sg pcp entry then
      result = (OS_ERR_PRIO_EXIST, None) /\ checkpoint = entry
    else match entry.(EventState).(unUsedEventStates) with
    | [] => result = (OS_ERR_PEVENT_NULL, None) /\ checkpoint = entry
    | eid :: rest => result = (OS_ERR_NONE, Some eid) /\
        checkpoint = mutex_create_state sg pcp eid rest entry
    end.

Definition call_relation (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (before : UCOS2_Verify_State)
  (result : OSErrCode * option EventID) (after : UCOS2_Verify_State) : Prop :=
  if MutexCreateCall.priority_rejected sg pcp then
    result = (OS_ERR_PRIO_INVALID, None) /\ after = before
  else if 0 <? before.(IntrState).(intNesting) then
    result = (OS_ERR_CREATE_ISR, None) /\ after = before
  else exists entry checkpoint,
    critical_region_interval critical sg invocation before entry /\
    critical_operation sg pcp entry result checkpoint /\
    critical_region_interval critical sg invocation checkpoint after.

Definition publication_call_program (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) : program UCOS2_Verify_State addr :=
  fun before pointer after => exists result,
    call_relation critical sg invocation pcp before result after /\
    pointer = event_encode_pool_link sg (snd result).

Definition publication_result_prop (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (before after : UCOS2_Verify_State)
  (pointer error : Z) : Prop := exists result,
    call_relation critical sg invocation pcp before result after /\
    pointer = event_encode_pool_link sg (snd result) /\
    error = encode_os_err_code (fst result).

Lemma publication_result_prop_call_program : forall critical sg invocation pcp before after pointer error,
  publication_result_prop critical sg invocation pcp before after pointer error ->
  publication_call_program critical sg invocation pcp before pointer after.
Proof. intros * [result [Hcall [Hpointer _]]]; exists result; auto. Qed.

Lemma critical_operation_preserves_validity : forall sg pcp entry result checkpoint,
  UCOS2_state_inv sg entry -> valid_mutex_pcp sg pcp ->
  critical_operation sg pcp entry result checkpoint -> UCOS2_state_inv sg checkpoint.
Proof.
  intros sg pcp entry result checkpoint Hvalid Hpcp.
  unfold critical_operation.
  destruct (MutexCreateCall.priority_slot_busy sg pcp entry) eqn:Hbusy.
  - intros [_ ->]; exact Hvalid.
  - destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
    + intros [_ ->]; exact Hvalid.
    + intros [_ ->]; apply MutexCreateFull.state_preserves_validity;
        [exact Hvalid|exact Hhead|exact Hpcp|].
      apply MutexCreateCall.priority_slot_available_iff; exact Hbusy.
Qed.

(** These are the actual selected C stores, including the real helper's
    bitmap effect; Type is last.  This equation is only a byte-image fact,
    not an assertion that the statements or platform have been verified. *)
Definition initialization_writes (pcp : Priority) : list (EventField * Z) :=
  [(EventCntField, pcp * 256 + 255); (EventPtrField, 0)] ++
  MutexCreatePrivateContext.wait_list_stores ++ [(EventTypeField, 4)].

Lemma initialization_image_eq : forall pcp image,
  event_create_stores_image image (initialization_writes pcp) =
    event_create_image false 4 (pcp * 256 + 255) 0 0 image.
Proof.
  intros; apply functional_extensionality; intro field; destruct field; reflexivity.
Qed.

Lemma initialized_storage_merge : forall sg entry pcp eid rest image,
  UCOS2_state_inv sg entry ->
  MutexCreateSpatial.free_head_facts sg entry eid rest image ->
  valid_mutex_pcp sg pcp -> MutexCreateSpatial.slot_available sg entry pcp ->
  MutexCreateSpatial.reserved_priority_table sg entry pcp **
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
  event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 4 (pcp * 256 + 255) 0 0 image) **
  MutexCreateFull.node_residual sg entry eid |--
    UCOS2_inv sg (mutex_create_state sg pcp eid rest entry).
Proof.
  intros sg entry pcp eid rest image Hvalid [Hhead [Himage Hrest]] Hpcp Hslot.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hstorage : image = mutex_create_storage entry.(EventState) eid).
  { unfold mutex_create_storage; rewrite Himage; reflexivity. }
  subst image.
  assert (Hrepr : event_storage_rep false (event_pool_addr sg eid)
      (event_create_image false 4 (pcp * 256 + 255) 0 0
        (mutex_create_storage entry.(EventState) eid)) =
    used_event_rep sg (mutex_create_priority_state sg pcp entry.(TskState)) eid
      (mutex_create_node pcp entry.(EventState).(eventLifecycle).(eventNextGeneration)
        (mutex_create_storage entry.(EventState) eid))).
  { unfold used_event_rep; rewrite Hnames.
    apply event_storage_rep_ext; intros field Hin; destruct field;
      try reflexivity; simpl in Hin; intuition discriminate. }
  rewrite Hrepr.
  unfold MutexCreateSpatial.reserved_priority_table.
  change (event_encode_pool_link sg (hd_error rest)) with
    (event_encode_pool_link sg (hd_error
      (mutex_create_event_state pcp eid rest entry.(EventState)).(unUsedEventStates))).
  eapply derivable1_trans; [|apply MutexCreateFull.node_merge_updated_inv;
    [exact Hvalid|exact Hhead|exact Hpcp|exact Hslot]].
  unfold event_free_root_rep; entailer!.
Qed.

End MutexCreatePublication.
