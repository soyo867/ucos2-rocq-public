Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_owner_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_publication_environment_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Import UCOS2_C_Rules ListNotations TaskStateDef EventStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** These proofs concern the actual allocation/initialization/publication
    registry, not arbitrary valid Event publications. In particular the
    latter can manufacture an owner from a waiting task and does not
    preserve the approved application protocol. *)
Lemma event_allocate_preserves_mutex_owner_event_unlinked : forall before result after,
  event_create_allocate_critical before result after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros before result after Hstep Huse.
  unfold event_create_allocate_critical in Hstep.
  destruct before.(EventState).(unUsedEventStates).
  - destruct Hstep as [_ ->]; exact Huse.
  - destruct Hstep as [image [_ [_ ->]]]; exact Huse.
Qed.

Lemma event_private_stores_preserve_mutex_owner_event_unlinked :
  forall eid writes before result after,
  event_create_private_stores eid writes before result after ->
  mutex_owner_event_unlinked before.(TskState) before.(EventState) ->
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros eid writes before result after Hstores Huse.
  destruct (event_create_private_stores_published_frame eid writes before result after Hstores)
    as [Hevents [_ [Htasks _]]].
  unfold mutex_owner_event_unlinked in *; rewrite Hevents, Htasks; exact Huse.
Qed.

Lemma mutex_del_creator_publication_preserves_owner_use :
  forall creator state eid allocation,
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  let after := mutex_del_creator_published_state creator state eid allocation in
  mutex_owner_event_unlinked after.(TskState) after.(EventState).
Proof.
  intros creator state eid allocation Huse; cbn zeta.
  intros mid event mutex owner node He Htype Hmutex Howner Hnode.
  unfold mutex_del_creator_published_state in He;
    cbn [replace_EventS EventState event_publish inUsedEventStates] in He.
  unfold kernel_map_set in He; destruct (Z.eq_dec mid eid).
  - injection He as <-; destruct creator; discriminate Htype.
  - eapply Huse; eassumption.
Qed.

Lemma mutex_del_creator_effect_preserves_owner_use : forall creator sg cut state next returned,
  mutex_del_creator_publication_effect creator sg cut state next returned ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  mutex_owner_event_unlinked returned.(TskState) returned.(EventState).
Proof.
  intros creator sg cut state next returned Hstep Huse; destruct Hstep.
  - destruct H; eapply event_allocate_preserves_mutex_owner_event_unlinked; eassumption.
  - apply mutex_del_creator_publication_preserves_owner_use.
    eapply event_private_stores_preserve_mutex_owner_event_unlinked; eassumption.
Qed.

Lemma mutex_del_creator_state_step_preserves_owner_use : forall creator sg cut state next returned,
  kernel_client_heap_state_step (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  mutex_owner_event_unlinked returned.(TskState) returned.(EventState).
Proof.
  intros creator sg cut state next returned Hstep Huse; destruct Hstep.
  - exact Huse.
  - exact Huse.
  - eapply mutex_del_stack_publication_preserves_owner_use; [split; [exact H|reflexivity]|exact Huse].
  - eapply mutex_del_creator_effect_preserves_owner_use; eassumption.
Qed.

Lemma mutex_del_creator_state_trace_preserves_owner_use : forall creator sg cut state next returned,
  kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  mutex_owner_event_unlinked returned.(TskState) returned.(EventState).
Proof.
  intros creator sg cut state next returned Htrace; induction Htrace; intro Huse.
  - exact Huse.
  - apply IHHtrace; eapply mutex_del_creator_state_step_preserves_owner_use; eassumption.
Qed.

(** Consume the SAME heap trace as the registered source owner. Its
    state projection is produced by that execution, never guessed from
    the desired owner-use endpoint. This supplies the missing preservation
    component for concrete Sem/Mbox creators, IRQ counters and actual TCB
    publication. It does not classify arbitrary IRQ handlers or callbacks. *)
Lemma mutex_del_creator_heap_trace_owner_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) creator sg cut state before next after
  (frame : Assertion),
  mutex_del_creator_arguments creator ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState) ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned /\
    mutex_owner_event_unlinked returned.(TskState) returned.(EventState) /\
    (kernel_client_heap_resources abi (mutex_del_creator_pending abi) sg next returned ** frame) after.
Proof.
  intros external platform port abi creator sg cut state before next after frame Hargs Huse Hsource Hpre.
  destruct (kernel_client_heap_trace_resources external platform port Z abi
    (mutex_del_creator_pending abi) (mutex_del_creator_publication_step creator)
    (mutex_del_creator_publication_effect creator)
    (mutex_del_creator_publication_extension_valid external platform port abi creator Hargs)
    sg cut before next after frame Hsource state Hpre) as [returned [Hlogical Hafter]].
  exists returned; split; [exact Hlogical|]. split; [|exact Hafter].
  eapply mutex_del_creator_state_trace_preserves_owner_use; eassumption.
Qed.

