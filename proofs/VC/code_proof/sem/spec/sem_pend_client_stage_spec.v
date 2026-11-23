Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_client_fields_spec.
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

(** No-switch segments must retain actual readiness, not infer it from a
    current-task pointer. Publication can change list links and introduce
    a higher-priority child, but does not block the interrupted caller.
    The global ready invariant and the old caller's unchanged status/delay
    establish membership in the new ready list. *)
Lemma sem_pend_task_publication_preserves_call_stage : forall sg publication state context,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  sem_pend_task_call_stage sg context state ->
  sem_pend_task_call_stage sg context (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state context Hvalid Hinput
    [[Horigin [Hactive Hexecuting]] [Hrunning [old [Hready [Hgeneration Hfields]]]]].
  destruct Hready as [Hold [Hcurrent [Hpriority [Hin Heffective]]]].
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
    publication.(stack_publication_invocation) node context.(os_sched_call_stack).(stackLeaseSlot)
    old Hfresh Hold) as [updated [Hupdated Hsame]].
  pose proof (f_equal curPrio Hsame) as Hprio.
  pose proof (f_equal stat Hsame) as Hstat.
  pose proof (f_equal dly Hsame) as Hdly.
  pose proof (f_equal taskGeneration Hsame) as Hgen.
  change (updated.(curPrio) = old.(curPrio)) in Hprio.
  change (updated.(stat) = old.(stat)) in Hstat.
  change (updated.(dly) = old.(dly)) in Hdly.
  change (updated.(taskGeneration) = old.(taskGeneration)) in Hgen.
  set (published := task_create_stack_publication_state sg publication state).
  assert (Hpost : UCOS2_state_inv sg published).
  { eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
    split; [exact Hinput|reflexivity]. }
  assert (Hlookup : published.(TskState).(inUsedTaskStates)
    context.(os_sched_call_stack).(stackLeaseSlot) = Some updated) by exact Hupdated.
  assert (Hready_updated : is_effectively_ready updated.(stat) updated.(dly) = true).
  { rewrite Hstat, Hdly; exact Heffective. }
  assert (Hmember : In context.(os_sched_call_stack).(stackLeaseSlot) published.(SchedState).(readyList)).
  { exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hpost))))))
      _ _ Hlookup Hready_updated). }
  assert (Hcall_fields : sem_pend_call_fields sg context.(os_sched_call_stack).(stackLeaseSlot) published).
  { eapply sem_pend_task_publication_preserves_call_fields; [exact Hvalid|exact Hinput|].
    split; [exact Hrunning|]. exists old; split; [exact Hold|exact Hfields]. }
  destruct Hcall_fields as [_ [observed [Hobserved Hobserved_fields]]].
  assert (observed = updated) by congruence; subst observed.
  unfold sem_pend_task_call_stage, kernel_call_task_source.
  split.
  - split; [exact Horigin|]. split.
    + change (task_invocation_active (task_commit state.(TskState) args.(initPrio)
        publication.(stack_publication_invocation) node)
        context.(os_sched_call_invocation) context.(os_sched_call_origin)).
      eapply task_commit_preserves_invocation_active; [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hactive].
    + unfold task_execution_current; rewrite Horigin; exact Hcurrent.
  - split; [exact Hrunning|]. exists updated; split.
    + unfold sched_current_ready_at; split; [exact Hlookup|]. split; [exact Hcurrent|].
      split; [change (state.(SchedState).(curSchedPrio) = Some updated.(curPrio)); rewrite Hprio; exact Hpriority|].
      split; assumption.
    + split; [rewrite Hgen; exact Hgeneration|exact Hobserved_fields].
Qed.

(** Only source extensions with an independently proved no-switch stage
    law can use this transport. Suspending the focused task or switching
    to another one does not meet that law: those paths instead need the
    actual selector/restore producer, and remain outside this lemma. *)
Lemma sem_pend_client_step_preserves_call_stage : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg context,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
    UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg context returned) ->
  forall cut state next returned,
  kernel_client_heap_state_step extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
  UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg context returned.
Proof.
  intros Extra extra_effect sg context Hextra cut state next returned Hstep Hvalid Hstage.
  destruct Hstep.
  - split; [apply os_int_enter_preserves_validity; exact Hvalid|exact Hstage].
  - split; [exact Hvalid|exact Hstage].
  - split.
    + eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
      split; [exact H|reflexivity].
    + eapply sem_pend_task_publication_preserves_call_stage; eassumption.
  - eapply Hextra; eassumption.
Qed.

Lemma sem_pend_client_trace_preserves_call_stage : forall Extra
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) sg context,
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
    UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg context returned) ->
  forall cut state next returned,
  kernel_client_heap_state_trace extra_effect sg cut state next returned ->
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
  UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg context returned.
Proof.
  intros Extra extra_effect sg context Hextra cut state next returned Htrace.
  induction Htrace; intros Hvalid Hstage; [split; assumption|].
  destruct (sem_pend_client_step_preserves_call_stage Extra extra_effect sg context Hextra
    cut state middle_cut middle H Hvalid Hstage) as [Hmiddle Hmiddle_stage].
  exact (IHHtrace Hmiddle Hmiddle_stage).
Qed.

(** The state-stage proof is consumed on the SAME concrete heap/source
    trace that carries the pending invocation. This is an internal source
    result, not a guarantee inserted into the old generic Save Ensure. *)
Lemma sem_pend_client_trace_source_stage : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload
  extra_step extra_effect clients sg observer event_observer context,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  (forall cut state next returned, extra_effect sg cut state next returned ->
    UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
    UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg context returned) ->
  forall cut before next after state origin (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  UCOS2_state_inv sg state -> sem_pend_task_call_stage sg context state ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    UCOS2_state_inv sg returned /\ sem_pend_task_call_stage sg context returned /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect
    clients sg observer event_observer context Hspatial Henter Hexit Hpublish Hsource Hstage_step
    cut before next after state origin frame Htrace Hcompatible Hvalid Hstage Hpre.
  destruct (kernel_client_call_stack_trace_source_resources external platform port Extra abi
    extra_resources focus payload extra_step extra_effect clients sg observer event_observer
    Hspatial Henter Hexit Hpublish Hsource cut before next after frame Htrace state origin
    Hcompatible Hpre) as [returned [stopped [returned_origin [Hstates [Hrun [Hcut Hpost]]]]]].
  destruct (sem_pend_client_trace_preserves_call_stage Extra extra_effect sg context Hstage_step
    cut state next returned Hstates Hvalid Hstage) as [Hreturned Hreturned_stage].
  exists returned, stopped, returned_origin; split; [exact Hrun|].
  split; [exact Hcut|]. split; [exact Hreturned|].
  split; [exact Hreturned_stage|exact Hpost].
Qed.
