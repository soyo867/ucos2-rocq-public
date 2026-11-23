Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_preparation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_allocation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_call_stack_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_publication_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_creator_interrupt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_c_source_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_task_event_ready_caller_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_dispatch_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_publication_receipt_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_sched_task_prepare_receipt_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_entry_call_source_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Freshness is observed at the actual registration cut. It is not a new
    condition on a generic Create call or on the old open Extra family. *)
Lemma sem_pend_task_registration_foreign : forall sg state call observer origin,
  UCOS2_state_inv sg state ->
  state.(TskState).(taskLifecycle).(taskInvocations) observer = Some origin ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  call.(os_sched_call_invocation) <> observer.
Proof.
  intros sg state call observer origin Hvalid Hobserver Hcall.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 Htasks))))) as Hgeneration.
  destruct Hgeneration as [_ [_ [Hbound _]]].
  specialize (Hbound _ _ Hobserver); lia.
Qed.

Lemma sem_pend_task_register_entry_foreign :
  forall environment critical saved_local sg args name call mask state
    region task_return lower old_frame upper observer origin,
  task_create_call_stage call state ->
  call.(os_sched_call_invocation) = state.(TskState).(taskLifecycle).(taskNextInvocation) ->
  state.(TskState).(taskLifecycle).(taskInvocations) observer = Some origin ->
  task_tcb_init_name_valid sg (task_tcb_init_stack_call_args args name) state ->
  task_create_stack_buffer_domain region args task_return lower old_frame upper ->
  kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg (task_stack_call_active_key call)
    call mask state ** task_stack_storage region (lower ++ old_frame ++ upper) |--
  let registered := replace_TskS
    (task_begin_invocation call.(os_sched_call_origin) state.(TskState)) state in
  coq_prop (task_create_source_entry sg args name call registered /\
    call.(os_sched_call_invocation) <> observer) &&
  task_create_continuation_pre environment critical saved_local sg region args task_return
    lower old_frame upper name call mask registered.
Proof.
  intros environment critical saved_local sg args name call mask state
    region task_return lower old_frame upper observer origin Hstage Hcall Hobserver Hname Hbuffer.
  assert (Hvalidity :
    kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key call) call mask state **
      task_stack_storage region (lower ++ old_frame ++ upper) |--
    coq_prop (UCOS2_state_inv sg state) &&
    (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) sg (task_stack_call_active_key call) call mask state **
      task_stack_storage region (lower ++ old_frame ++ upper))).
  { unfold kernel_continuation_call_closed, kernel_continuation_inv, kernel_program_inv; entailer!. }
  sep_apply_l_atomic Hvalidity; Intros.
  assert (Hvalid : UCOS2_state_inv sg state) by assumption.
  pose proof (sem_pend_task_registration_foreign sg state call observer origin Hvalid Hobserver Hcall) as Hforeign.
  sep_apply_l_atomic (task_create_continuation_register_entry_pre environment critical saved_local sg args name
    call mask state region task_return lower old_frame upper Hstage Hcall Hname Hbuffer).
  cbv zeta; Intros; entailer!.
Qed.

Lemma sem_pend_task_normalized_entry_foreign :
  forall environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial slot generation observer,
  task_create_source_entry sg args name original initial ->
  original.(os_sched_call_origin) = RunningInvocation slot generation ->
  original.(os_sched_call_invocation) <> observer ->
  task_create_continuation_pre environment critical saved_local sg region args task_return
    lower old_frame upper name original mask initial |--
  EX normalized,
    coq_prop (os_sched_execution_view normalized = os_sched_execution_view original /\
      task_stack_call_active_key normalized = task_stack_call_active_key original /\
      task_create_stack_entry sg args name normalized initial /\
      kernel_call_task_source normalized initial /\
      task_create_source_entry sg args name normalized initial /\
      kernel_call_stack_available normalized initial /\
      normalized.(os_sched_call_invocation) <> observer) &&
    task_create_continuation_pre environment critical saved_local sg region args task_return
      lower old_frame upper name normalized mask initial.
Proof.
  intros * Hentry Horigin Hforeign.
  sep_apply_l_atomic (task_create_source_entry_normalized_pre environment critical saved_local sg region args
    task_return lower old_frame upper name original mask initial slot generation Hentry Horigin).
  Intros normalized.
  assert (Hview : os_sched_execution_view normalized = os_sched_execution_view original) by tauto.
  pose proof (f_equal os_execution_invocation Hview) as Hinvocation.
  change (normalized.(os_sched_call_invocation) = original.(os_sched_call_invocation)) in Hinvocation.
  Exists normalized; entailer!.
Qed.

(** Each private cut records the real component that owns it. Closed and
    publication cuts remain shared. The original Extra parameter elsewhere
    is unchanged; this is one finite, concrete module instantiation. *)
Inductive SemPendSchedModuleCut : Type :=
| SemPendAllocationCut (pointer : Z)
| SemPendCreatorCut (creator : MutexDelSimpleCreator) (pointer : Z)
| SemPendTaskPrepareCut (input : TaskCreateStackInput).

Definition sem_pend_sched_module_cut {Extra} (inject : Extra -> SemPendSchedModuleCut)
  (cut : KernelClientHeapCut Extra) : KernelClientHeapCut SemPendSchedModuleCut :=
  match cut with
  | KernelClientHeapClosed => KernelClientHeapClosed
  | KernelClientHeapTaskPublication publication => KernelClientHeapTaskPublication publication
  | KernelClientHeapExtra input => KernelClientHeapExtra (inject input)
  end.

Definition sem_pend_sched_module_resources {external platform port}
  (abi : Armv7aContinuationABI external platform port) saved_local sg
  (cut : KernelClientHeapCut SemPendSchedModuleCut) state : Assertion :=
  let local := task_create_continuation_local saved_local in
  match cut with
  | KernelClientHeapClosed => kernel_client_continuation_fields_world abi local sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_fields_publication abi local sg publication state
  | KernelClientHeapExtra (SemPendAllocationCut pointer) =>
      sem_pend_allocation_fields_resources abi local sg (KernelClientHeapExtra pointer) state
  | KernelClientHeapExtra (SemPendCreatorCut _ pointer) =>
      sem_pend_creator_fields_resources abi local sg (KernelClientHeapExtra pointer) state
  | KernelClientHeapExtra (SemPendTaskPrepareCut input) =>
      sem_pend_task_prepare_fields_input abi saved_local sg input state
  end.

Lemma sem_pend_sched_module_allocation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg cut state,
  sem_pend_sched_module_resources abi saved_local sg
    (sem_pend_sched_module_cut SemPendAllocationCut cut) state =
  sem_pend_allocation_fields_resources abi (task_create_continuation_local saved_local) sg cut state.
Proof. intros; destruct cut; reflexivity. Qed.

Lemma sem_pend_sched_module_creator_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg creator cut state,
  sem_pend_sched_module_resources abi saved_local sg
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) state =
  sem_pend_creator_fields_resources abi (task_create_continuation_local saved_local) sg cut state.
Proof. intros; destruct cut; reflexivity. Qed.

Lemma sem_pend_sched_module_prepare_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local sg cut state,
  sem_pend_sched_module_resources abi saved_local sg
    (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state =
  sem_pend_task_prepare_fields_resources abi saved_local sg cut state.
Proof. intros; destruct cut; reflexivity. Qed.

Inductive sem_pend_sched_module_step sg :
  KernelClientHeapCut SemPendSchedModuleCut -> model -> KernelClientHeapCut SemPendSchedModuleCut -> model -> Prop :=
| SemPendSchedModuleAllocation : forall cut before next after,
    mutex_del_creator_heap_step sg cut before next after ->
    sem_pend_sched_module_step sg (sem_pend_sched_module_cut SemPendAllocationCut cut) before
      (sem_pend_sched_module_cut SemPendAllocationCut next) after
| SemPendSchedModuleCreator : forall creator cut before next after,
    mutex_del_creator_interrupt_step creator sg cut before next after ->
    sem_pend_sched_module_step sg (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) before
      (sem_pend_sched_module_cut (SemPendCreatorCut creator) next) after
| SemPendSchedModulePrepare : forall cut before next after,
    task_create_stack_heap_step sg cut before next after ->
    sem_pend_sched_module_step sg (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) before
      (sem_pend_sched_module_cut SemPendTaskPrepareCut next) after.

Inductive sem_pend_sched_module_effect sg :
  KernelClientHeapCut SemPendSchedModuleCut -> UCOS2_Verify_State ->
  KernelClientHeapCut SemPendSchedModuleCut -> UCOS2_Verify_State -> Prop :=
| SemPendSchedModuleAllocationEffect : forall cut state next returned,
    mutex_del_creator_heap_effect sg cut state next returned ->
    sem_pend_sched_module_effect sg (sem_pend_sched_module_cut SemPendAllocationCut cut) state
      (sem_pend_sched_module_cut SemPendAllocationCut next) returned
| SemPendSchedModuleCreatorEffect : forall creator cut state next returned,
    mutex_del_creator_interrupt_effect creator sg cut state next returned ->
    sem_pend_sched_module_effect sg (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) state
      (sem_pend_sched_module_cut (SemPendCreatorCut creator) next) returned
| SemPendSchedModulePrepareEffect : forall cut state next returned,
    task_create_stack_heap_effect sg cut state next returned ->
    sem_pend_sched_module_effect sg (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state
      (sem_pend_sched_module_cut SemPendTaskPrepareCut next) returned.

Inductive sem_pend_sched_module_client actor : KernelClientAction -> Prop :=
| SemPendSchedModuleAllocationClient : forall action,
    mutex_del_allocation_source_client actor action -> sem_pend_sched_module_client actor action
| SemPendSchedModuleCreatorClient : forall creator action,
    mutex_del_creator_source_client actor creator action -> sem_pend_sched_module_client actor action
| SemPendSchedModulePrepareClient : forall action,
    sem_pend_task_prepare_source_client action -> sem_pend_sched_module_client actor action.

(** These are the real call's finite actor/argument facts. They decorate
    the supplied heap proof; the raw sum above admits every original step.
    No validity, next owner or preservation conclusion is a binding field. *)
Inductive sem_pend_sched_module_step_binding actor observer sg :
  forall cut before next after,
  kernel_client_heap_step sem_pend_sched_module_step sg cut before next after -> Prop :=
| SemPendSchedModuleEnterBinding : forall before after run,
    sem_pend_sched_module_step_binding actor observer sg _ _ _ _
      (@KernelClientHeapEnter SemPendSchedModuleCut sem_pend_sched_module_step sg before after run)
| SemPendSchedModuleExitBinding : forall before after run,
    sem_pend_sched_module_step_binding actor observer sg _ _ _ _
      (@KernelClientHeapExit SemPendSchedModuleCut sem_pend_sched_module_step sg before after run)
| SemPendSchedModulePublishBinding : forall publication before after run,
    publication.(stack_publication_invocation) <> observer ->
    sem_pend_sched_module_step_binding actor observer sg _ _ _ _
      (@KernelClientHeapPublish SemPendSchedModuleCut sem_pend_sched_module_step sg publication before after run)
| SemPendSchedModuleAllocationBinding : forall cut before next after
    (run : mutex_del_creator_heap_step sg cut before next after),
    actor <> Some observer ->
    sem_pend_sched_module_step_binding actor observer sg _ _ _ _
      (@KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg
        (sem_pend_sched_module_cut SemPendAllocationCut cut) before
        (sem_pend_sched_module_cut SemPendAllocationCut next) after
        (SemPendSchedModuleAllocation sg cut before next after run))
| SemPendSchedModuleCreatorBinding : forall creator cut before next after
    (run : mutex_del_creator_interrupt_step creator sg cut before next after),
    mutex_del_creator_arguments creator -> actor <> Some observer ->
    sem_pend_sched_module_step_binding actor observer sg _ _ _ _
      (@KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg
        (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) before
        (sem_pend_sched_module_cut (SemPendCreatorCut creator) next) after
        (SemPendSchedModuleCreator sg creator cut before next after run))
| SemPendSchedModulePrepareBinding : forall cut before next after
    (run : task_create_stack_heap_step sg cut before next after),
    sem_pend_task_prepare_observer_cut observer cut ->
    sem_pend_sched_module_step_binding actor observer sg _ _ _ _
      (@KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg
        (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) before
        (sem_pend_sched_module_cut SemPendTaskPrepareCut next) after
        (SemPendSchedModulePrepare sg cut before next after run)).

Inductive sem_pend_sched_module_trace_binding actor observer sg :
  forall cut before next after,
  kernel_client_heap_trace sem_pend_sched_module_step sg cut before next after -> Prop :=
| SemPendSchedModuleTraceNilBinding : forall cut heap,
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _
      (@KernelClientHeapTraceNil SemPendSchedModuleCut sem_pend_sched_module_step sg cut heap)
| SemPendSchedModuleTraceConsBinding : forall cut before middle_cut middle next after step tail,
    sem_pend_sched_module_step_binding actor observer sg cut before middle_cut middle step ->
    sem_pend_sched_module_trace_binding actor observer sg middle_cut middle next after tail ->
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _
      (@KernelClientHeapTraceCons SemPendSchedModuleCut sem_pend_sched_module_step sg
        cut before middle_cut middle next after step tail).

Lemma sem_pend_sched_module_prepare_state_step : forall sg cut state next returned,
  kernel_client_heap_state_step task_create_stack_heap_effect sg cut state next returned ->
  kernel_client_heap_state_step sem_pend_sched_module_effect sg
    (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state
    (sem_pend_sched_module_cut SemPendTaskPrepareCut next) returned.
Proof.
  intros * Hstep; destruct Hstep; cbn [sem_pend_sched_module_cut].
  - constructor.
  - constructor.
  - constructor; assumption.
  - apply KernelClientHeapExtraState; apply SemPendSchedModulePrepareEffect; assumption.
Qed.

Lemma sem_pend_sched_module_prepare_step_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local actor sg observer
  cut before next after state origin (frame : Assertion),
  sem_pend_task_prepare_observer_cut observer cut ->
  kernel_client_heap_step task_create_stack_heap_step sg cut before next after ->
  (sem_pend_sched_module_resources abi saved_local sg
    (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state ** frame) before ->
  exists returned,
    kernel_client_heap_state_step sem_pend_sched_module_effect sg
      (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) state
      (sem_pend_sched_module_cut SemPendTaskPrepareCut next) returned /\
    (exists trace : kernel_client_task_source_trace external port (sem_pend_sched_module_client actor)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (sem_pend_sched_module_client actor)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_sched_module_resources abi saved_local sg
      (sem_pend_sched_module_cut SemPendTaskPrepareCut next) returned ** frame) after.
Proof.
  intros * Hobserver Hstep Hpre.
  rewrite sem_pend_sched_module_prepare_resources in Hpre.
  destruct (sem_pend_task_prepare_fields_step_receipt external platform port abi saved_local sg observer
    cut before next after state origin frame Hobserver Hstep Hpre)
    as [returned [Heffect [[trace Hreceipt] [Hnext Hpost]]]].
  exists returned; split; [apply sem_pend_sched_module_prepare_state_step; exact Heffect|].
  split.
  - eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
    intros action Hmember; apply SemPendSchedModulePrepareClient; exact Hmember.
  - rewrite sem_pend_sched_module_prepare_resources; exact Hpost.
Qed.

(** The selected component is invoked while both its actual Hpre and its
    returned Hstep/Hmiddle are available. The resulting source uses that
    very state edge and retains that exact next owner. *)
Lemma sem_pend_sched_module_step_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local actor sg observer cut before next after
  (step : kernel_client_heap_step sem_pend_sched_module_step sg cut before next after),
  sem_pend_sched_module_step_binding actor observer sg cut before next after step ->
  forall state origin (frame : Assertion),
  (sem_pend_sched_module_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_step sem_pend_sched_module_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (sem_pend_sched_module_client actor)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (sem_pend_sched_module_client actor)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_sched_module_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer cut before next after step Hbinding.
  destruct Hbinding; intros state origin frame Hpre.
  - eapply (sem_pend_sched_module_prepare_step_receipt external platform port abi saved_local actor sg observer
      KernelClientHeapClosed before KernelClientHeapClosed after state origin frame);
      [exact I|constructor; exact run|exact Hpre].
  - eapply (sem_pend_sched_module_prepare_step_receipt external platform port abi saved_local actor sg observer
      KernelClientHeapClosed before KernelClientHeapClosed after state origin frame);
      [exact I|constructor; exact run|exact Hpre].
  - eapply (sem_pend_sched_module_prepare_step_receipt external platform port abi saved_local actor sg observer
      (KernelClientHeapTaskPublication publication) before KernelClientHeapClosed after state origin frame);
      [exact H|constructor; exact run|exact Hpre].
  - rewrite sem_pend_sched_module_allocation_resources in Hpre.
    pose proof (sem_pend_allocation_fields_source_facts external platform port abi
      (task_create_continuation_local saved_local) sg cut state before frame Hpre) as Hfacts.
    destruct (sem_pend_allocation_fields_extra_resources external platform port abi
      (task_create_continuation_local saved_local) sg cut before next after state frame run Hpre)
      as [returned [Heffect Hpost]].
    assert (Hobserver : kernel_client_heap_observer_cut observer cut) by (destruct run; exact I).
    destruct (sem_pend_allocation_heap_state_step_receipt external port actor sg observer cut state next returned origin
      H Hobserver (KernelClientHeapExtraState mutex_del_creator_heap_effect sg cut state next returned Heffect) Hfacts)
      as [Hnext [trace Hreceipt]].
    exists returned; split.
    + apply KernelClientHeapExtraState; apply SemPendSchedModuleAllocationEffect; exact Heffect.
    + split.
      * eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
        intros action Hmember; apply SemPendSchedModuleAllocationClient; exact Hmember.
      * rewrite sem_pend_sched_module_allocation_resources; exact Hpost.
  - rewrite sem_pend_sched_module_creator_resources in Hpre.
    pose proof (sem_pend_creator_fields_resources_valid external platform port abi
      (task_create_continuation_local saved_local) sg cut state before frame Hpre) as Hvalid.
    destruct (sem_pend_creator_interrupt_fields_extra external platform port abi
      (task_create_continuation_local saved_local) creator H sg cut before next after state frame run Hpre)
      as [returned [Heffect Hpost]].
    assert (Hobserver : kernel_client_heap_observer_cut observer cut).
    { destruct run; try exact I; destruct H1; exact I. }
    destruct (sem_pend_creator_interrupt_state_step_receipt external port actor creator sg observer cut state next returned origin
      H0 Hobserver (KernelClientHeapExtraState (mutex_del_creator_interrupt_effect creator) sg cut state next returned Heffect) Hvalid)
      as [Hnext [trace Hreceipt]].
    exists returned; split.
    + apply KernelClientHeapExtraState; apply SemPendSchedModuleCreatorEffect; exact Heffect.
    + split.
      * eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
        intros action Hmember; eapply SemPendSchedModuleCreatorClient; exact Hmember.
      * rewrite sem_pend_sched_module_creator_resources; exact Hpost.
  - eapply sem_pend_sched_module_prepare_step_receipt;
      [exact H|constructor; exact run|exact Hpre].
Qed.

Lemma sem_pend_sched_module_trace_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) saved_local actor sg observer cut before next after
  (run : kernel_client_heap_trace sem_pend_sched_module_step sg cut before next after),
  sem_pend_sched_module_trace_binding actor observer sg cut before next after run ->
  forall state origin (frame : Assertion),
  (sem_pend_sched_module_resources abi saved_local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace sem_pend_sched_module_effect sg cut state next returned /\
    (exists trace : kernel_client_task_source_trace external port (sem_pend_sched_module_client actor)
        sg observer None origin state false origin returned,
      sem_pend_client_source_local_receipt external port (sem_pend_sched_module_client actor)
        sg observer None origin state false origin returned trace) /\
    (sem_pend_sched_module_resources abi saved_local sg next returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer cut before next after run Hbinding.
  induction Hbinding as [cut heap|cut before middle_cut middle next after step tail Hstep Htail IH];
    intros state origin frame Hpre.
  - exists state; split; [constructor|]. split; [|exact Hpre].
    exists (@KernelClientTaskSourceNil external port (sem_pend_sched_module_client actor) sg observer None origin state).
    constructor.
  - destruct (sem_pend_sched_module_step_receipt external platform port abi saved_local actor sg observer
      cut before middle_cut middle step Hstep state origin frame Hpre)
      as [middle_state [Heffect [[head Hhead] Hmiddle]]].
    destruct (IH middle_state origin frame Hmiddle) as [returned [Hstate [[last Hlast] Hpost]]].
    exists returned; split; [econstructor; eassumption|]. split; [|exact Hpost].
    exact (sem_pend_dispatch_client_receipt_append external port (sem_pend_sched_module_client actor)
      sg observer None origin state false origin middle_state head Hhead false origin returned last Hlast).
Qed.

(** Every original component trace is embedded before resource
    interpretation, retaining all four heap constructors and endpoints. *)
Lemma sem_pend_sched_module_allocation_trace_binding : forall actor sg observer cut before next after,
  actor <> Some observer ->
  kernel_client_heap_trace mutex_del_creator_heap_step sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  exists run : kernel_client_heap_trace sem_pend_sched_module_step sg
    (sem_pend_sched_module_cut SemPendAllocationCut cut) before
    (sem_pend_sched_module_cut SemPendAllocationCut next) after,
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    kernel_client_heap_observer_cut observer next.
Proof.
  intros actor sg observer cut before next after Hforeign Htrace.
  induction Htrace as [cut heap|cut before middle_cut middle next after step tail IH]; intros Hobserver.
  - exists (@KernelClientHeapTraceNil SemPendSchedModuleCut sem_pend_sched_module_step sg _ heap).
    split; [constructor|exact Hobserver].
  - assert (Hhead : exists lifted : kernel_client_heap_step sem_pend_sched_module_step sg
        (sem_pend_sched_module_cut SemPendAllocationCut cut) before
        (sem_pend_sched_module_cut SemPendAllocationCut middle_cut) middle,
        sem_pend_sched_module_step_binding actor observer sg _ _ _ _ lifted /\
        kernel_client_heap_observer_cut observer middle_cut).
    { destruct step as [b0 a0 Hrun|b0 a0 Hrun|publication b0 a0 Hrun|cut0 b0 next0 a0 Hrun].
      - exists (@KernelClientHeapEnter SemPendSchedModuleCut sem_pend_sched_module_step sg b0 a0 Hrun).
        split; [constructor|exact I].
      - exists (@KernelClientHeapExit SemPendSchedModuleCut sem_pend_sched_module_step sg b0 a0 Hrun).
        split; [constructor|exact I].
      - exists (@KernelClientHeapPublish SemPendSchedModuleCut sem_pend_sched_module_step sg publication b0 a0 Hrun).
        split; [constructor; exact Hobserver|exact I].
      - exists (@KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg _ b0 _ a0
          (SemPendSchedModuleAllocation sg cut0 b0 next0 a0 Hrun)).
        split; [constructor; exact Hforeign|]. destruct Hrun; exact I. }
    destruct Hhead as [head [Hbinding Hmiddle]].
    destruct (IH Hmiddle) as [last [Htail Hnext]].
    exists (@KernelClientHeapTraceCons SemPendSchedModuleCut sem_pend_sched_module_step sg
      _ before _ middle _ after head last); split; [constructor; assumption|exact Hnext].
Qed.

(** A private creator cut can also be the final cut of its trace. *)
Lemma sem_pend_sched_module_creator_trace_binding : forall actor creator sg observer cut before next after,
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  exists run : kernel_client_heap_trace sem_pend_sched_module_step sg
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) before
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) next) after,
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    kernel_client_heap_observer_cut observer next.
Proof.
  intros actor creator sg observer cut before next after Hforeign Hargs Htrace.
  induction Htrace as [cut heap|cut before middle_cut middle next after step tail IH]; intros Hobserver.
  - exists (@KernelClientHeapTraceNil SemPendSchedModuleCut sem_pend_sched_module_step sg _ heap).
    split; [constructor|exact Hobserver].
  - assert (Hhead : exists lifted : kernel_client_heap_step sem_pend_sched_module_step sg
        (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) before
        (sem_pend_sched_module_cut (SemPendCreatorCut creator) middle_cut) middle,
        sem_pend_sched_module_step_binding actor observer sg _ _ _ _ lifted /\
        kernel_client_heap_observer_cut observer middle_cut).
    { destruct step as [b0 a0 Hrun|b0 a0 Hrun|publication b0 a0 Hrun|cut0 b0 next0 a0 Hrun].
      - exists (@KernelClientHeapEnter SemPendSchedModuleCut sem_pend_sched_module_step sg b0 a0 Hrun).
        split; [constructor|exact I].
      - exists (@KernelClientHeapExit SemPendSchedModuleCut sem_pend_sched_module_step sg b0 a0 Hrun).
        split; [constructor|exact I].
      - exists (@KernelClientHeapPublish SemPendSchedModuleCut sem_pend_sched_module_step sg publication b0 a0 Hrun).
        split; [constructor; exact Hobserver|exact I].
      - exists (@KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg _ b0 _ a0
          (SemPendSchedModuleCreator sg creator cut0 b0 next0 a0 Hrun)).
        split; [constructor; assumption|].
        destruct Hrun; try exact I. destruct H; try exact I. destruct H; exact I. }
    destruct Hhead as [head [Hbinding Hmiddle]].
    destruct (IH Hmiddle) as [last [Htail Hnext]].
    exists (@KernelClientHeapTraceCons SemPendSchedModuleCut sem_pend_sched_module_step sg
      _ before _ middle _ after head last); split; [constructor; assumption|exact Hnext].
Qed.

Lemma sem_pend_sched_module_publication_trace_binding : forall actor creator sg observer cut before next after,
  actor <> Some observer -> mutex_del_creator_arguments creator ->
  kernel_client_heap_trace (mutex_del_creator_publication_step creator) sg cut before next after ->
  kernel_client_heap_observer_cut observer cut ->
  exists run : kernel_client_heap_trace sem_pend_sched_module_step sg
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) before
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) next) after,
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    kernel_client_heap_observer_cut observer next.
Proof.
  intros actor creator sg observer cut before next after Hforeign Hargs Htrace Hobserver.
  assert (Hinterrupt : kernel_client_heap_trace (mutex_del_creator_interrupt_step creator) sg cut before next after).
  { clear Hobserver. induction Htrace as [cut heap|cut before middle_cut middle next after step tail IH].
    - constructor.
    - eapply KernelClientHeapTraceCons; [|exact IH].
      destruct step; try (constructor; assumption).
      apply KernelClientHeapRegistered; apply MutexDelCreatorInterruptBase; assumption. }
  exact (sem_pend_sched_module_creator_trace_binding actor creator sg observer cut before next after
    Hforeign Hargs Hinterrupt Hobserver).
Qed.

Lemma sem_pend_sched_module_prepare_trace_binding : forall actor sg observer cut before next after,
  kernel_client_heap_trace task_create_stack_heap_step sg cut before next after ->
  sem_pend_task_prepare_observer_cut observer cut ->
  exists run : kernel_client_heap_trace sem_pend_sched_module_step sg
    (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) before
    (sem_pend_sched_module_cut SemPendTaskPrepareCut next) after,
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    sem_pend_task_prepare_observer_cut observer next.
Proof.
  intros actor sg observer cut before next after Htrace.
  induction Htrace as [cut heap|cut before middle_cut middle next after step tail IH]; intros Hobserver.
  - exists (@KernelClientHeapTraceNil SemPendSchedModuleCut sem_pend_sched_module_step sg _ heap).
    split; [constructor|exact Hobserver].
  - assert (Hhead : exists lifted : kernel_client_heap_step sem_pend_sched_module_step sg
        (sem_pend_sched_module_cut SemPendTaskPrepareCut cut) before
        (sem_pend_sched_module_cut SemPendTaskPrepareCut middle_cut) middle,
        sem_pend_sched_module_step_binding actor observer sg _ _ _ _ lifted /\
        sem_pend_task_prepare_observer_cut observer middle_cut).
    { destruct step as [b0 a0 Hrun|b0 a0 Hrun|publication b0 a0 Hrun|cut0 b0 next0 a0 Hrun].
      - exists (@KernelClientHeapEnter SemPendSchedModuleCut sem_pend_sched_module_step sg b0 a0 Hrun).
        split; [constructor|exact I].
      - exists (@KernelClientHeapExit SemPendSchedModuleCut sem_pend_sched_module_step sg b0 a0 Hrun).
        split; [constructor|exact I].
      - exists (@KernelClientHeapPublish SemPendSchedModuleCut sem_pend_sched_module_step sg publication b0 a0 Hrun).
        split; [constructor; exact Hobserver|exact I].
      - exists (@KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg _ b0 _ a0
          (SemPendSchedModulePrepare sg cut0 b0 next0 a0 Hrun)).
        split; [constructor; exact Hobserver|].
        destruct Hrun; exact Hobserver. }
    destruct Hhead as [head [Hbinding Hmiddle]].
    destruct (IH Hmiddle) as [last [Htail Hnext]].
    exists (@KernelClientHeapTraceCons SemPendSchedModuleCut sem_pend_sched_module_step sg
      _ before _ middle _ after head last); split; [constructor; assumption|exact Hnext].
Qed.

Lemma sem_pend_sched_module_publication_state_trace : forall creator sg cut state next returned,
  kernel_client_heap_state_trace (mutex_del_creator_publication_effect creator) sg cut state next returned ->
  kernel_client_heap_state_trace sem_pend_sched_module_effect sg
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) cut) state
    (sem_pend_sched_module_cut (SemPendCreatorCut creator) next) returned.
Proof.
  intros creator sg cut state next returned Htrace; induction Htrace.
  - constructor.
  - eapply KernelClientHeapStateTraceCons; [|exact IHHtrace].
    destruct H; cbn [sem_pend_sched_module_cut]; try (constructor; assumption); try constructor.
    apply SemPendSchedModuleCreatorEffect; apply MutexDelCreatorInterruptBaseState; assumption.
Qed.

(** These factories put their actual heap run in the common dispatcher.
    They retain the original returned state and owner, without interpreting
    the supplied run a second time to select another state witness. *)
Lemma sem_pend_sched_module_allocation_produces :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    saved_local actor sg observer state origin before (frame : Assertion),
  actor <> Some observer -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg state ** frame) before ->
  exists cut after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      KernelClientHeapClosed before (sem_pend_sched_module_cut SemPendAllocationCut cut) after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg KernelClientHeapClosed state
        (sem_pend_sched_module_cut SemPendAllocationCut cut) returned /\
      (exists trace : kernel_client_task_source_trace external port (sem_pend_sched_module_client actor)
          sg observer None origin state false origin returned,
        sem_pend_client_source_local_receipt external port (sem_pend_sched_module_client actor)
          sg observer None origin state false origin returned trace) /\
      (sem_pend_sched_module_resources abi saved_local sg
        (sem_pend_sched_module_cut SemPendAllocationCut cut) returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer state origin before frame Hforeign Hbinding Hpre.
  destruct (sem_pend_allocation_fields_produces_receipt external platform port abi
    (task_create_continuation_local saved_local) actor sg observer origin state before frame Hforeign Hbinding Hpre)
    as [cut [after [allocated [Hallocate [Hstate [Hcalls Hpost]]]]]].
  pose (step := @KernelClientHeapRegistered SemPendSchedModuleCut sem_pend_sched_module_step sg
    KernelClientHeapClosed before (sem_pend_sched_module_cut SemPendAllocationCut cut) after
    (SemPendSchedModuleAllocation sg KernelClientHeapClosed before cut after Hallocate)).
  pose (run := @KernelClientHeapTraceCons SemPendSchedModuleCut sem_pend_sched_module_step sg
    KernelClientHeapClosed before _ after _ after step
    (@KernelClientHeapTraceNil SemPendSchedModuleCut sem_pend_sched_module_step sg _ after)).
  assert (Hrun : sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run).
  { unfold run; constructor; [|constructor]. unfold step.
    exact (SemPendSchedModuleAllocationBinding actor observer sg KernelClientHeapClosed before cut after Hallocate Hforeign). }
  exists cut, after, run; split; [exact Hrun|].
  exists allocated; split.
  - eapply KernelClientHeapStateTraceCons; [|constructor].
    apply KernelClientHeapExtraState.
    exact (SemPendSchedModuleAllocationEffect sg KernelClientHeapClosed state cut allocated Hstate).
  - split.
    + destruct Hcalls as [trace Hreceipt].
      eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
      intros action Hmember; apply SemPendSchedModuleAllocationClient; exact Hmember.
    + rewrite sem_pend_sched_module_allocation_resources; exact Hpost.
Qed.

Lemma sem_pend_sched_module_creator_produces :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    saved_local actor creator sg observer state origin before (frame : Assertion),
  actor <> Some observer -> mutex_del_creator_arguments creator -> sem_create_source_binding sg ->
  (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg state ** frame) before ->
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      KernelClientHeapClosed before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg KernelClientHeapClosed state KernelClientHeapClosed returned /\
      (exists trace : kernel_client_task_source_trace external port (sem_pend_sched_module_client actor)
          sg observer None origin state false origin returned,
        sem_pend_client_source_local_receipt external port (sem_pend_sched_module_client actor)
          sg observer None origin state false origin returned trace) /\
      (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor creator sg observer state origin before frame Hforeign Hargs Hbinding Hpre.
  destruct (sem_pend_creator_publication_fields_produces_closed external platform port abi
    (task_create_continuation_local saved_local) actor creator sg observer state origin before frame
    Hforeign Hargs Hbinding Hpre) as [old_returned [after [oldrun [Hstate [Hcalls Hpost]]]]].
  destruct (sem_pend_sched_module_publication_trace_binding actor creator sg observer
    KernelClientHeapClosed before KernelClientHeapClosed after Hforeign Hargs oldrun I) as [run [Hrun Hnext]].
  exists after, run; split; [exact Hrun|].
  exists old_returned; split.
  - exact (sem_pend_sched_module_publication_state_trace creator sg _ _ _ _ Hstate).
  - split; [|exact Hpost]. destruct Hcalls as [trace Hreceipt].
    eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
    intros action Hmember; apply (SemPendSchedModuleCreatorClient actor creator); exact Hmember.
Qed.

Lemma sem_pend_sched_module_prepare_produces :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    saved_local actor sg observer origin input slot rest (frame : Assertion) before,
  input.(stack_input_call).(os_sched_call_invocation) <> observer ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (sem_pend_task_prepare_fields_input abi saved_local sg input input.(stack_input_state) ** frame) before ->
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      (KernelClientHeapExtra (SemPendTaskPrepareCut input)) before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg
        (KernelClientHeapExtra (SemPendTaskPrepareCut input)) input.(stack_input_state) KernelClientHeapClosed returned /\
      (exists trace : kernel_client_task_source_trace external port (sem_pend_sched_module_client actor)
          sg observer None origin input.(stack_input_state) false origin returned,
        sem_pend_client_source_local_receipt external port (sem_pend_sched_module_client actor)
          sg observer None origin input.(stack_input_state) false origin returned trace) /\
      (kernel_client_continuation_fields_world abi (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros external platform port abi saved_local actor sg observer origin input slot rest frame before
    Hforeign Hnest Hfree Hhead Hpre.
  assert (Hfacts : task_create_stack_input_facts sg input).
  { destruct Hpre as [owned [rest_heap [Hjoin [[[Hsame Hfacts] Howned] Hframe]]]]; exact Hfacts. }
  destruct (sem_pend_task_prepare_fields_produces_calls external platform port abi saved_local sg input slot rest
    frame before Hnest Hfree Hhead Hpre) as [image [prepared [Hprepare [Hdetach [Hreserve [Hcall Howned]]]]]].
  assert (Himage : input.(stack_input_state).(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image)
    by exact (proj2 (proj2 (proj2 Hdetach))).
  pose proof (sem_pend_task_prepare_fields_valid external platform port abi saved_local sg
    (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
    (task_create_stack_input_detached input slot rest image) prepared frame Howned) as Hvalid.
  destruct (sem_pend_task_publication_fields_produces external platform port abi
    (task_create_continuation_local saved_local) sg (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image) frame prepared Howned)
    as [after [Hpublish [Hpublication Hpost]]].
  pose proof (tmr_task_source_call_receipt_step _ _ _ _ _ Hpublication) as Hpublication_step.
  assert (oldrun : kernel_client_heap_trace task_create_stack_heap_step sg
    (KernelClientHeapExtra input) before KernelClientHeapClosed after).
  { eapply KernelClientHeapTraceCons; [apply KernelClientHeapRegistered; exact Hprepare|].
    eapply KernelClientHeapTraceCons; [apply KernelClientHeapPublish; exact Hpublish|constructor]. }
  destruct (sem_pend_sched_module_prepare_trace_binding actor sg observer
    (KernelClientHeapExtra input) before KernelClientHeapClosed after oldrun Hforeign) as [run [Hrun Hnext]].
  exists after, run; split; [exact Hrun|].
  exists (task_create_stack_publication_state sg (task_create_stack_prepared_publication input slot image)
    (task_create_stack_input_detached input slot rest image)); split.
  - eapply KernelClientHeapStateTraceCons.
    + apply KernelClientHeapExtraState.
      eapply (SemPendSchedModulePrepareEffect sg (KernelClientHeapExtra input) input.(stack_input_state)
        (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
        (task_create_stack_input_detached input slot rest image)); constructor.
    + eapply KernelClientHeapStateTraceCons; [apply KernelClientHeapPublishState; exact (proj1 Hpublication_step)|constructor].
  - split; [|exact Hpost].
    destruct (sem_pend_task_prepare_client_receipt external port sg observer origin input slot rest image
      Hforeign Hfacts Hfree Hhead Himage) as [head Hhead_receipt].
    destruct (sem_pend_task_prepare_builtin_receipt external port sg observer
      (KernelClientHeapTaskPublication (task_create_stack_prepared_publication input slot image))
      (task_create_stack_input_detached input slot rest image) KernelClientHeapClosed
      (task_create_stack_publication_state sg (task_create_stack_prepared_publication input slot image)
        (task_create_stack_input_detached input slot rest image)) origin Hforeign Hvalid
      ltac:(constructor; exact (proj1 Hpublication_step))) as [_ [tail Htail_receipt]].
    destruct (sem_pend_dispatch_client_receipt_append external port sem_pend_task_prepare_source_client
      sg observer None origin input.(stack_input_state) false origin (task_create_stack_input_detached input slot rest image)
      head Hhead_receipt false origin _ tail Htail_receipt) as [trace Hreceipt].
    eapply sem_pend_dispatch_client_receipt_inclusion; [|exact Hreceipt].
    intros action Hmember; apply SemPendSchedModulePrepareClient; exact Hmember.
Qed.

(** The registration and Prepare premises are observations at their real
    C cuts. Registration keeps the active call owner; Prepare consumes
    its actual fields input. No conversion between these owners is used.
    The execution view is the one retained by the normalization producer
    above, so freshness is transported along this same invocation. *)
Lemma sem_pend_sched_module_registered_prepare_produces :
  forall environment critical saved_local sg call mask initial observer observer_origin
    input slot rest actor origin entry_heap before (frame : Assertion),
  task_create_call_stage call initial ->
  call.(os_sched_call_invocation) = initial.(TskState).(taskLifecycle).(taskNextInvocation) ->
  initial.(TskState).(taskLifecycle).(taskInvocations) observer = Some observer_origin ->
  task_tcb_init_name_valid sg (task_create_stack_input_args input) initial ->
  task_create_stack_buffer_domain input.(stack_input_region) input.(stack_input_args)
    input.(stack_input_return) input.(stack_input_lower) input.(stack_input_old_frame) input.(stack_input_upper) ->
  os_sched_execution_view input.(stack_input_call) = os_sched_execution_view call ->
  input.(stack_input_state).(IntrState).(intNesting) = 0 ->
  input.(stack_input_state).(TskState).(prioTbl) input.(stack_input_args).(createPriority) = PTFree ->
  input.(stack_input_state).(TskState).(unUsedTaskStates) = slot :: rest ->
  (kernel_continuation_call_closed environment.(task_stack_call_continuations) kernel_program_inv
    (task_create_continuation_local saved_local) sg (task_stack_call_active_key call) call mask initial **
    task_stack_storage input.(stack_input_region)
      (input.(stack_input_lower) ++ input.(stack_input_old_frame) ++ input.(stack_input_upper))) entry_heap ->
  (sem_pend_task_prepare_fields_input environment.(task_stack_call_continuations) saved_local sg input
    input.(stack_input_state) ** frame) before ->
  let registered := replace_TskS (task_begin_invocation call.(os_sched_call_origin) initial.(TskState)) initial in
  task_create_source_entry sg input.(stack_input_args) input.(stack_input_name) call registered /\
  task_create_continuation_pre environment critical saved_local sg input.(stack_input_region) input.(stack_input_args)
    input.(stack_input_return) input.(stack_input_lower) input.(stack_input_old_frame) input.(stack_input_upper)
    input.(stack_input_name) call mask registered entry_heap /\
  exists after (run : kernel_client_heap_trace sem_pend_sched_module_step sg
      (KernelClientHeapExtra (SemPendTaskPrepareCut input)) before KernelClientHeapClosed after),
    sem_pend_sched_module_trace_binding actor observer sg _ _ _ _ run /\
    exists returned,
      kernel_client_heap_state_trace sem_pend_sched_module_effect sg
        (KernelClientHeapExtra (SemPendTaskPrepareCut input)) input.(stack_input_state) KernelClientHeapClosed returned /\
      (exists trace : kernel_client_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) (sem_pend_sched_module_client actor)
          sg observer None origin input.(stack_input_state) false origin returned,
        sem_pend_client_source_local_receipt environment.(task_stack_call_external)
          environment.(task_stack_call_port) (sem_pend_sched_module_client actor)
          sg observer None origin input.(stack_input_state) false origin returned trace) /\
      (kernel_client_continuation_fields_world environment.(task_stack_call_continuations)
        (task_create_continuation_local saved_local) sg returned ** frame) after.
Proof.
  intros environment critical saved_local sg call mask initial observer observer_origin
    input slot rest actor origin entry_heap before frame Hstage Hfresh Hobserver Hname Hbuffer Hview
    Hnest Hfree Hhead Hentry_heap Hpre; cbv zeta.
  destruct (sem_pend_task_register_entry_foreign environment critical saved_local sg input.(stack_input_args)
    input.(stack_input_name) call mask initial input.(stack_input_region) input.(stack_input_return)
    input.(stack_input_lower) input.(stack_input_old_frame) input.(stack_input_upper) observer observer_origin
    Hstage Hfresh Hobserver Hname Hbuffer entry_heap Hentry_heap) as [[Hentry Hforeign] Hregistered].
  pose proof (f_equal os_execution_invocation Hview) as Hinvocation.
  change (input.(stack_input_call).(os_sched_call_invocation) = call.(os_sched_call_invocation)) in Hinvocation.
  split; [exact Hentry|]. split; [exact Hregistered|].
  eapply sem_pend_sched_module_prepare_produces; [congruence|exact Hnest|exact Hfree|exact Hhead|exact Hpre].
Qed.
