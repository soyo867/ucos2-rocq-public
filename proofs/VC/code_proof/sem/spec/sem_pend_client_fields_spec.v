Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_cycle_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_trace_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The first-Save caller has not published a wait. These observations do
    not claim it remains current or ready while another task is executing.
    No extra ghost state or strengthened public calling domain is added. *)
Definition sem_pend_call_fields sg tid (state : UCOS2_Verify_State) : Prop :=
  state.(SchedState).(isRunning) = true /\
  exists node, state.(TskState).(inUsedTaskStates) tid = Some node /\
    node.(curPrio) <> sg.(osLowestPrio) /\ sem_pend_task_unregistered node.

Lemma sem_pend_call_stage_fields : forall sg context state,
  sem_pend_task_call_stage sg context state ->
  sem_pend_call_fields sg context.(os_sched_call_stack).(stackLeaseSlot) state.
Proof.
  intros sg context state [_ [Hrunning [node [Hready [Hgen Hfields]]]]].
  split; [exact Hrunning|]. exists node; split; [exact (proj1 Hready)|exact Hfields].
Qed.

(** The new TCB is private before publication; the old calling TCB cannot
    be that allocation. Its Prev link may change, so do not assume the
    complete TCB, or the active-list order, is unchanged. *)
Lemma sem_pend_task_publication_preserves_call_fields : forall sg publication state tid,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  sem_pend_call_fields sg tid state ->
  sem_pend_call_fields sg tid (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state tid Hvalid Hinput [Hrunning [old [Hold [Hnonidle Hnone]]]].
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) node.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid)))
      (task_commit_identity_private _ _ _ _ Hidentity))). }
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node tid old Hfresh Hold)
    as [current [Hcurrent Hfields]].
  split; [exact Hrunning|]. exists current; split; [exact Hcurrent|].
  split.
  - change (curPrio current <> osLowestPrio sg).
    pose proof (f_equal curPrio Hfields) as Hpriority.
    change (curPrio current = curPrio old) in Hpriority.
    rewrite Hpriority; exact Hnonidle.
  - destruct Hnone as [Hevent [Hmulti Hflag]].
    unfold sem_pend_task_unregistered.
    pose proof (f_equal eventPtr Hfields) as HeventEq.
    pose proof (f_equal eventMultiWaitEvents Hfields) as HmultiEq.
    pose proof (f_equal tcbFlagNode Hfields) as HflagEq.
    change (eventPtr current = eventPtr old) in HeventEq.
    change (eventMultiWaitEvents current = eventMultiWaitEvents old) in HmultiEq.
    change (tcbFlagNode current = tcbFlagNode old) in HflagEq.
    rewrite HeventEq, HmultiEq, HflagEq; repeat split; assumption.
Qed.

(** The previously proved source family supplies the other concrete field
    effects. Validity of that real client comes from its ordinary proved
    certificate, not from an operation defined to assume its own poststate. *)
Lemma sem_pend_source_client_preserves_call_fields : forall action sg before after tid,
  sem_pend_projected_source_client action -> KernelClientCertificate action ->
  kernel_client_step action sg before after -> UCOS2_state_inv sg before ->
  sem_pend_call_fields sg tid before -> sem_pend_call_fields sg tid after.
Proof.
  intros action sg before after tid Hsource Hcertificate Hstep Hvalid
    [Hrunning [old [Hold [Hnonidle Hnone]]]].
  pose proof (kernel_client_preserves_validity action Hcertificate sg before after Hvalid Hstep) as Hafter.
  destruct (sem_pend_source_client_call_frame action sg before after Hsource Hstep)
    as [Horder Hr].
  assert (HrunningAfter : after.(SchedState).(isRunning) = true) by congruence.
  destruct (sem_pend_source_client_projection action sg before after tid old Hsource Hstep Hold)
    as [current [Hcurrent Heffects]].
  split; [exact HrunningAfter|]. exists current; split; [exact Hcurrent|]. split.
  - exact (sem_pend_call_frame_preserves_nonidle sg before after tid old current
      Hvalid Hafter Hrunning HrunningAfter Horder Hold Hcurrent Hnonidle).
  - exact (sem_pend_wait_trace_preserves_unregistered old current Heffects Hnone).
Qed.

(** This is the actual built-in client registry, including publication.
    Extra source fragments must prove their own field and validity laws.
    No claim is made that these built-ins cover all enabled kernel calls. *)
Lemma sem_pend_client_step_preserves_call_fields : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg tid,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_call_fields sg tid state ->
    UCOS2_state_inv sg returned /\ sem_pend_call_fields sg tid returned) ->
  forall cut state next returned,
  kernel_client_heap_state_step extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> sem_pend_call_fields sg tid state ->
  UCOS2_state_inv sg returned /\ sem_pend_call_fields sg tid returned.
Proof.
  intros Extra extra_effect sg tid Hextra cut state next returned Hstep Hvalid Hfields.
  destruct Hstep.
  - split; [apply os_int_enter_preserves_validity; exact Hvalid|exact Hfields].
  - split; [exact Hvalid|exact Hfields].
  - split.
    + eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
      split; [exact H|reflexivity].
    + eapply sem_pend_task_publication_preserves_call_fields; eassumption.
  - eapply Hextra; eassumption.
Qed.

Lemma sem_pend_client_trace_preserves_call_fields : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg tid,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_call_fields sg tid state ->
    UCOS2_state_inv sg returned /\ sem_pend_call_fields sg tid returned) ->
  forall cut state next returned,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> sem_pend_call_fields sg tid state ->
  UCOS2_state_inv sg returned /\ sem_pend_call_fields sg tid returned.
Proof.
  intros Extra extra_effect sg tid Hextra cut state next returned Htrace.
  induction Htrace; intros Hvalid Hfields; [split; assumption|].
  destruct (sem_pend_client_step_preserves_call_fields Extra extra_effect sg tid Hextra
    cut state middle_cut middle H Hvalid Hfields) as [Hmiddle Hmiddle_fields].
  exact (IHHtrace Hmiddle Hmiddle_fields).
Qed.

(** Join observations with the SAME concrete heap trace that transports
    the pending call. This does not combine unrelated existential paths. *)
Lemma sem_pend_client_trace_source_fields : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload
  extra_step extra_effect clients sg observer event_observer context,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state ->
    sem_pend_call_fields sg context.(os_sched_call_stack).(stackLeaseSlot) state ->
    UCOS2_state_inv sg returned /\
    sem_pend_call_fields sg context.(os_sched_call_stack).(stackLeaseSlot) returned) ->
  forall cut before next after state origin (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    UCOS2_state_inv sg returned /\
    sem_pend_call_fields sg context.(os_sched_call_stack).(stackLeaseSlot) returned /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect
    clients sg observer event_observer context Hspatial Henter Hexit Hpublish Hsource Hfields
    cut before next after state origin frame Htrace Hcompatible Hvalid Hstage Hpre.
  pose proof (sem_pend_call_stage_fields sg context state Hstage) as Hobserved.
  destruct (kernel_client_call_stack_trace_source_resources external platform port Extra abi
    extra_resources focus payload extra_step extra_effect clients sg observer event_observer
    Hspatial Henter Hexit Hpublish Hsource cut before next after frame Htrace state origin
    Hcompatible Hpre) as [returned [stopped [returned_origin [Hstates [Hrun [Hcut Hpost]]]]]].
  destruct (sem_pend_client_trace_preserves_call_fields Extra extra_effect sg
    context.(os_sched_call_stack).(stackLeaseSlot) Hfields
    cut state next returned Hstates Hvalid Hobserved) as [Hreturned Hobserved_returned].
  exists returned, stopped, returned_origin; split; [exact Hrun|].
  split; [exact Hcut|]. split; [exact Hreturned|].
  split; [exact Hobserved_returned|exact Hpost].
Qed.

(** Publication may change the waiting task's list links, but not its
    wait registration. Freshness comes from the real private allocation;
    it is not a restriction placed on an arbitrary environment action. *)
Lemma sem_pend_task_publication_wait_projection : forall sg publication state tid old,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_task_projection state.(TskState)
    (task_create_stack_publication_state sg publication state).(TskState) tid old.
Proof.
  intros sg publication state tid old Hvalid Hinput Hold.
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node).
  { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
  assert (Hfresh : state.(TskState).(inUsedTaskStates) node.(taskID) = None).
  { exact (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid)))
      (task_commit_identity_private _ _ _ _ Hidentity))). }
  destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node tid old Hfresh Hold)
    as [current [Hcurrent Hfields]].
  exists current; split; [exact Hcurrent|].
  apply rt_step; apply SemPendWaitOtherFields; unfold sem_pend_wait_fields_equal.
  repeat split; first [exact (f_equal taskID Hfields) | exact (f_equal taskGeneration Hfields) |
    exact (f_equal stat Hfields) | exact (f_equal statPend Hfields) |
    exact (f_equal dly Hfields) | exact (f_equal eventPtr Hfields) |
    exact (f_equal eventMultiWaitEvents Hfields) | exact (f_equal tcbFlagNode Hfields)].
Qed.

(** Preserve the wait observation along the SAME registry state trace.
    In particular this does not assert that a still-pending or suspended
    task is ready. Extra operations supply their proved source projection,
    including Post/Abort/Tick; no all-kernel preservation law is assumed. *)
Lemma sem_pend_client_trace_wait_continuation : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg tid,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> UCOS2_state_inv sg returned /\
    forall old, state.(TskState).(inUsedTaskStates) tid = Some old ->
      sem_pend_task_projection state.(TskState) returned.(TskState) tid old) ->
  forall cut state next returned old eid generation,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  UCOS2_state_inv sg returned /\ exists current,
    returned.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current.
Proof.
  intros Extra extra_effect sg tid Hextra.
  assert (Hstep : forall cut state next returned,
    kernel_client_heap_state_step extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> UCOS2_state_inv sg returned /\
    forall old, state.(TskState).(inUsedTaskStates) tid = Some old ->
      sem_pend_task_projection state.(TskState) returned.(TskState) tid old).
  { intros cut state next returned Hrun Hvalid; destruct Hrun.
    - split; [apply os_int_enter_preserves_validity; exact Hvalid|].
      intros old Hold; apply sem_pend_task_projection_refl; exact Hold.
    - split; [exact Hvalid|].
      intros old Hold; apply sem_pend_task_projection_refl; exact Hold.
    - split.
      + eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
        split; [exact H|reflexivity].
      + intros old Hold; eapply sem_pend_task_publication_wait_projection; eassumption.
    - eapply Hextra; eassumption. }
  intros cut state next returned old eid generation Htrace.
  revert old; induction Htrace; intros old Hvalid Hold Hwait.
  - split; [exact Hvalid|]. exists old; split; assumption.
  - destruct (Hstep cut state middle_cut middle H Hvalid) as [Hmiddle Hprojection].
    destruct (Hprojection old Hold) as [current [Hcurrent Heffects]].
    eapply IHHtrace; [exact Hmiddle|exact Hcurrent|].
    eapply sem_pend_wait_trace_preserves_continuation; eassumption.
Qed.

(** Concrete registry execution jointly yields the current stack owner,
    source history, and the pending-call observation. They are not taken
    from three unrelated existential executions. This source cut is for
    returning live instances; retirement is not recast as a normal return. *)
Lemma sem_pend_client_trace_wait_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload
  extra_step extra_effect clients sg observer event_observer tid eid generation,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> UCOS2_state_inv sg returned /\
    forall old, state.(TskState).(inUsedTaskStates) tid = Some old ->
      sem_pend_task_projection state.(TskState) returned.(TskState) tid old) ->
  forall cut before next after state origin old (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  UCOS2_state_inv sg state -> state.(TskState).(inUsedTaskStates) tid = Some old ->
  sem_pend_wait_continuation eid generation old ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin current,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\ UCOS2_state_inv sg returned /\
    returned.(TskState).(inUsedTaskStates) tid = Some current /\
    sem_pend_wait_continuation eid generation current /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect
    clients sg observer event_observer tid eid generation Hspatial Henter Hexit Hpublish Hsource
    Hfields cut before next after state origin old frame Htrace Hcompatible Hvalid Hold Hwait Hpre.
  destruct (kernel_client_call_stack_trace_source_resources external platform port Extra abi
    extra_resources focus payload extra_step extra_effect clients sg observer event_observer
    Hspatial Henter Hexit Hpublish Hsource cut before next after frame Htrace state origin
    Hcompatible Hpre) as [returned [stopped [returned_origin [Hstates [Hrun [Hcut Hpost]]]]]].
  destruct (sem_pend_client_trace_wait_continuation Extra extra_effect sg tid Hfields
    cut state next returned old eid generation Hstates Hvalid Hold Hwait)
    as [Hreturned [current [Hcurrent Hcontinuation]]].
  exists returned, stopped, returned_origin, current.
  exact (conj Hrun (conj Hcut (conj Hreturned (conj Hcurrent (conj Hcontinuation Hpost))))).
Qed.
