Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_fields_disabled_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendTaskViewResources.
Import PrimitiveComponent ViewPrimitiveComponent FlagPendBootViewResources.

Lemma flag_pend_call_with_view_fragments_active_key : forall original returned,
  task_stack_call_active_key (flag_pend_call_with_view_fragments original returned) =
    task_stack_call_active_key original.
Proof. intros; reflexivity. Qed.

(** A resource view uses the real active key. These equivalences assert no
    task liveness, scheduler consistency, normal return, or counter frame. *)
Lemma flag_pend_task_view_save_input_equiv :
  forall environment critical local sg original mask state,
  flag_pend_caller_save_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask state --||--
  flag_pend_caller_save_input environment critical local (fun _ _ => emp) sg
    (FlagPendInterruptCaller (os_sched_execution_view original) (task_stack_call_active_key original))
    original mask state.
Proof.
  intros environment critical local sg original mask state.
  unfold flag_pend_caller_save_input, flag_pend_active_save_input, os_sched_fields_save_input.
  rewrite kernel_call_execution_owned_view_eq.
  split; entailer!.
Qed.

Lemma flag_pend_task_view_restore_input_equiv :
  forall environment critical local sg original saved acquired state,
  flag_pend_caller_restore_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired state --||--
  flag_pend_caller_restore_input environment critical local (fun _ _ => emp) sg
    (FlagPendInterruptCaller (os_sched_execution_view original) (task_stack_call_active_key original))
    original saved acquired state.
Proof.
  intros environment critical local sg original saved acquired state.
  unfold flag_pend_caller_restore_input, flag_pend_active_restore_input,
    os_sched_fields_restore_input, os_execution_view_resources,
    os_sched_context_resources, os_sched_execution_view.
  cbn [os_execution_invocation os_execution_origin os_execution_stack os_execution_fragments].
  split; entailer!.
Qed.

Lemma flag_pend_task_view_save_resources :
  forall environment critical local next_local sg original mask saved
    before first_heap returned_view acquired last_heap,
  flag_pend_view_save_primitive_post environment critical local next_local (fun _ _ => emp) sg
    (os_sched_execution_view original) (task_stack_call_active_key original) original
    mask saved before first_heap returned_view acquired last_heap ->
  let returned := flag_pend_call_with_view_fragments original returned_view in
  os_sched_execution_view returned = returned_view /\
  task_tcb_init_stack_same_call returned original /\
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_caller_save_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask before first_heap /\
  flag_pend_caller_restore_input environment critical next_local (fun _ _ => emp) sg
    (FlagPendTaskCaller returned) returned saved acquired acquired last_heap.
Proof.
  intros environment critical local next_local sg original mask saved before first_heap
    returned_view acquired last_heap [Hsame [Hinterval [Hsaved [Hinput Houtput]]]].
  cbn zeta.
  assert (Hview : os_sched_execution_view (flag_pend_call_with_view_fragments original returned_view) =
    returned_view) by (apply flag_pend_call_with_view_fragments_view; exact Hsame).
  split; [exact Hview|].
  split; [apply flag_pend_call_with_view_fragments_same_call|].
  split; [exact Hinterval|]. split; [exact Hsaved|]. split.
  - exact (proj2 (flag_pend_task_view_save_input_equiv environment critical local sg
      original mask before) first_heap Hinput).
  - apply (proj2 (flag_pend_task_view_restore_input_equiv environment critical next_local sg
      (flag_pend_call_with_view_fragments original returned_view) saved acquired acquired)).
    rewrite Hview, flag_pend_call_with_view_fragments_active_key.
    exact Houtput.
Qed.

Lemma flag_pend_task_view_restore_resources :
  forall environment critical local next_local sg original saved acquired
    released first_heap returned_view current last_heap,
  flag_pend_view_restore_primitive_post environment critical local next_local (fun _ _ => emp) sg
    (os_sched_execution_view original) (task_stack_call_active_key original) original
    saved acquired released first_heap returned_view current last_heap ->
  let returned := flag_pend_call_with_view_fragments original returned_view in
  os_sched_execution_view returned = returned_view /\
  task_tcb_init_stack_same_call returned original /\
  critical_region_interval critical sg original.(os_sched_call_invocation) released current /\
  flag_pend_caller_restore_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired released first_heap /\
  flag_pend_caller_save_input environment critical next_local (fun _ _ => emp) sg
    (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current last_heap.
Proof.
  intros environment critical local next_local sg original saved acquired released first_heap
    returned_view current last_heap [Hsame [Hinterval [Hinput Houtput]]].
  cbn zeta.
  assert (Hview : os_sched_execution_view (flag_pend_call_with_view_fragments original returned_view) =
    returned_view) by (apply flag_pend_call_with_view_fragments_view; exact Hsame).
  split; [exact Hview|].
  split; [apply flag_pend_call_with_view_fragments_same_call|].
  split; [exact Hinterval|]. split.
  - exact (proj2 (flag_pend_task_view_restore_input_equiv environment critical local sg
      original saved acquired released) first_heap Hinput).
  - apply (proj2 (flag_pend_task_view_save_input_equiv environment critical next_local sg
      (flag_pend_call_with_view_fragments original returned_view) (armv7a_irq_fiq_mask saved) current)).
    rewrite Hview, flag_pend_call_with_view_fragments_active_key.
    exact Houtput.
Qed.

End FlagPendTaskViewResources.

Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_boot_primitive_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendInactiveViewPrimitive.
Import PrimitiveComponent ViewPrimitiveComponent FlagPendBootViewResources FlagPendTaskViewResources.

Inductive flag_pend_inactive_save_completion
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local next_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (original : OsSchedCallContext) (mask saved : Z)
  (before : UCOS2_Verify_State) (first_heap : model) :
  OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| FlagPendInactiveSaveCompletion : forall returned_view acquired last_heap,
    flag_pend_view_save_primitive_post environment critical local next_local
      (fun _ _ => emp) sg (os_sched_execution_view original)
      (task_stack_call_active_key original) original mask saved before first_heap
      returned_view acquired last_heap ->
    flag_pend_inactive_save_completion environment critical local next_local sg
      original mask saved before first_heap
      (flag_pend_call_with_view_fragments original returned_view) acquired last_heap.

Inductive flag_pend_inactive_restore_completion
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local next_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (original : OsSchedCallContext) (saved : Z)
  (acquired released : UCOS2_Verify_State) (first_heap : model) :
  OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| FlagPendInactiveRestoreCompletion : forall returned_view current last_heap,
    flag_pend_view_restore_primitive_post environment critical local next_local
      (fun _ _ => emp) sg (os_sched_execution_view original)
      (task_stack_call_active_key original) original saved acquired released first_heap
      returned_view current last_heap ->
    flag_pend_inactive_restore_completion environment critical local next_local sg
      original saved acquired released first_heap
      (flag_pend_call_with_view_fragments original returned_view) current last_heap.

Definition flag_pend_inactive_save_effect environment critical sg original mask saved
  before returned acquired : Prop :=
  exists local next_local first_heap last_heap,
    flag_pend_inactive_save_completion environment critical local next_local sg
      original mask saved before first_heap returned acquired last_heap.

Definition flag_pend_inactive_restore_effect environment critical sg original
  released returned current : Prop :=
  exists local next_local saved acquired first_heap last_heap,
    flag_pend_inactive_restore_completion environment critical local next_local sg
      original saved acquired released first_heap returned current last_heap.

Lemma flag_pend_inactive_save_completion_from_post :
  forall environment critical local next_local sg original mask saved
    before first_heap returned_view acquired last_heap,
  flag_pend_view_save_primitive_post environment critical local next_local
    (fun _ _ => emp) sg (os_sched_execution_view original)
    (task_stack_call_active_key original) original mask saved before first_heap
    returned_view acquired last_heap ->
  flag_pend_inactive_save_completion environment critical local next_local sg
    original mask saved before first_heap
    (flag_pend_call_with_view_fragments original returned_view) acquired last_heap.
Proof. intros; constructor; assumption. Qed.

Lemma flag_pend_inactive_restore_completion_from_post :
  forall environment critical local next_local sg original saved
    acquired released first_heap returned_view current last_heap,
  flag_pend_view_restore_primitive_post environment critical local next_local
    (fun _ _ => emp) sg (os_sched_execution_view original)
    (task_stack_call_active_key original) original saved acquired released first_heap
    returned_view current last_heap ->
  flag_pend_inactive_restore_completion environment critical local next_local sg
    original saved acquired released first_heap
    (flag_pend_call_with_view_fragments original returned_view) current last_heap.
Proof. intros; constructor; assumption. Qed.

Lemma flag_pend_inactive_save_completion_post :
  forall environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap,
  flag_pend_inactive_save_completion environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap ->
  task_tcb_init_stack_same_call returned original /\
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_caller_save_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original mask before first_heap /\
  flag_pend_caller_restore_input environment critical next_local (fun _ _ => emp) sg
    (FlagPendTaskCaller returned) returned saved acquired acquired last_heap.
Proof.
  intros environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap Hcomplete.
  destruct Hcomplete as [returned_view acquired last_heap Hpost].
  exact (proj2 (flag_pend_task_view_save_resources environment critical local next_local sg
    original mask saved before first_heap returned_view acquired last_heap Hpost)).
Qed.

Lemma flag_pend_inactive_restore_completion_post :
  forall environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap,
  flag_pend_inactive_restore_completion environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap ->
  task_tcb_init_stack_same_call returned original /\
  critical_region_interval critical sg original.(os_sched_call_invocation) released current /\
  flag_pend_caller_restore_input environment critical local (fun _ _ => emp) sg
    (FlagPendTaskCaller original) original saved acquired released first_heap /\
  flag_pend_caller_save_input environment critical next_local (fun _ _ => emp) sg
    (FlagPendTaskCaller returned) returned (armv7a_irq_fiq_mask saved) current last_heap.
Proof.
  intros environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap Hcomplete.
  destruct Hcomplete as [returned_view current last_heap Hpost].
  exact (proj2 (flag_pend_task_view_restore_resources environment critical local next_local sg
    original saved acquired released first_heap returned_view current last_heap Hpost)).
Qed.

Lemma flag_pend_inactive_save_completion_effect :
  forall environment critical local next_local sg original mask saved before first_heap returned acquired last_heap,
  flag_pend_inactive_save_completion environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap ->
  flag_pend_inactive_save_effect environment critical sg original mask saved before returned acquired.
Proof.
  intros environment critical local next_local sg original mask saved before first_heap returned acquired last_heap Hcomplete.
  exists local, next_local, first_heap, last_heap; exact Hcomplete.
Qed.

Lemma flag_pend_inactive_restore_completion_effect :
  forall environment critical local next_local sg original saved acquired released first_heap returned current last_heap,
  flag_pend_inactive_restore_completion environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap ->
  flag_pend_inactive_restore_effect environment critical sg original released returned current.
Proof.
  intros environment critical local next_local sg original saved acquired released first_heap returned current last_heap Hcomplete.
  exists local, next_local, saved, acquired, first_heap, last_heap; exact Hcomplete.
Qed.

Lemma flag_pend_inactive_save_effect_observations :
  forall environment critical sg original mask saved before returned acquired,
  flag_pend_inactive_save_effect environment critical sg original mask saved before returned acquired ->
  task_tcb_init_stack_same_call returned original /\
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
  interrupt_saved_value mask saved.
Proof.
  intros environment critical sg original mask saved before returned acquired
    [local [next_local [first_heap [last_heap Hcomplete]]]].
  destruct (flag_pend_inactive_save_completion_post environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap Hcomplete)
    as [Hsame [Hinterval [Hsaved Hresources]]].
  exact (conj Hsame (conj Hinterval Hsaved)).
Qed.

Lemma flag_pend_inactive_restore_effect_observations :
  forall environment critical sg original released returned current,
  flag_pend_inactive_restore_effect environment critical sg original released returned current ->
  task_tcb_init_stack_same_call returned original /\
  critical_region_interval critical sg original.(os_sched_call_invocation) released current.
Proof.
  intros environment critical sg original released returned current
    [local [next_local [saved [acquired [first_heap [last_heap Hcomplete]]]]]].
  destruct (flag_pend_inactive_restore_completion_post environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap Hcomplete)
    as [Hsame [Hinterval Hresources]].
  exact (conj Hsame Hinterval).
Qed.

End FlagPendInactiveViewPrimitive.
