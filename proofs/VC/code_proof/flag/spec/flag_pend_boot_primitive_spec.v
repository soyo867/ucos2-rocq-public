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
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module FlagPendBootViewResources.
Import ViewPrimitiveComponent.

(** Only the observed byte fragments change. The original invocation,
    Boot origin, and complete lease remain those of the outer TaskCaller. *)
Definition flag_pend_call_with_view_fragments (original : OsSchedCallContext)
  (returned : OsExecutionView) : OsSchedCallContext :=
  {| os_sched_call_invocation := original.(os_sched_call_invocation);
     os_sched_call_origin := original.(os_sched_call_origin);
     os_sched_call_stack := original.(os_sched_call_stack);
     os_sched_call_fragments := returned.(os_execution_fragments) |}.

Lemma flag_pend_call_with_view_fragments_view : forall original returned,
  sched_fields_same_view returned (os_sched_execution_view original) ->
  os_sched_execution_view (flag_pend_call_with_view_fragments original returned) = returned.
Proof.
  intros original returned [Hi [Ho [Hcontext Hstack]]].
  destruct returned; cbn in Hi, Ho, Hcontext, Hstack.
  subst; reflexivity.
Qed.

Lemma flag_pend_call_with_view_fragments_same_call : forall original returned,
  task_tcb_init_stack_same_call (flag_pend_call_with_view_fragments original returned) original.
Proof. intros; unfold task_tcb_init_stack_same_call; repeat split; reflexivity. Qed.

Lemma flag_pend_boot_view_normal_return : forall original returned before after,
  original.(os_sched_call_origin) = BootInvocation ->
  kernel_call_normal_return original before
    (flag_pend_call_with_view_fragments original returned) after.
Proof.
  intros original returned before after Hboot.
  split; [apply flag_pend_call_with_view_fragments_same_call|].
  unfold kernel_call_stack_available; cbn [flag_pend_call_with_view_fragments os_sched_call_origin].
  rewrite Hboot; auto.
Qed.

(** These are same-heap resource equivalences, not a change of the outer
    caller or an exception-return rule. None is the real Boot coverage key. *)
Lemma flag_pend_boot_task_view_save_input_equiv :
  forall environment critical local sg original mask state,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical local
    (fun _ _ => emp) sg (FlagPendTaskCaller original) original mask state --||--
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical local
    (fun _ _ => emp) sg (FlagPendInterruptCaller (os_sched_execution_view original) None)
    original mask state.
Proof.
  intros environment critical local sg original mask state Hboot.
  unfold flag_pend_call_protocol.flag_pend_caller_save_input,
    flag_pend_active_save_input, os_sched_fields_save_input, task_stack_call_active_key.
  rewrite Hboot, kernel_call_execution_owned_view_eq.
  split; entailer!.
Qed.

Lemma flag_pend_boot_task_view_restore_input_equiv :
  forall environment critical local sg original saved acquired state,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local
    (fun _ _ => emp) sg (FlagPendTaskCaller original) original saved acquired state --||--
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local
    (fun _ _ => emp) sg (FlagPendInterruptCaller (os_sched_execution_view original) None)
    original saved acquired state.
Proof.
  intros environment critical local sg original saved acquired state Hboot.
  unfold flag_pend_call_protocol.flag_pend_caller_restore_input,
    flag_pend_active_restore_input, os_sched_fields_restore_input, task_stack_call_active_key.
  rewrite Hboot.
  unfold os_execution_view_resources, os_sched_context_resources, os_sched_execution_view.
  cbn [os_execution_invocation os_execution_origin os_execution_stack os_execution_fragments].
  rewrite Hboot.
  split; entailer!.
Qed.

(** The sole completion premise is the original, unchanged view primitive
    post. Its actual first/last heaps and next_local are retained verbatim.
    This theorem does not claim that exception entry alone produces it. *)
Lemma flag_pend_boot_view_save_resources :
  forall environment critical local next_local sg original mask saved
    before first_heap returned_view acquired last_heap,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_view_save_primitive_post environment critical local next_local (fun _ _ => emp) sg
    (os_sched_execution_view original) None original mask saved before first_heap
    returned_view acquired last_heap ->
  let returned := flag_pend_call_with_view_fragments original returned_view in
  os_sched_execution_view returned = returned_view /\
  kernel_call_normal_return original before returned acquired /\
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical local
    (fun _ _ => emp) sg (FlagPendTaskCaller original) original mask before first_heap /\
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical next_local
    (fun _ _ => emp) sg (FlagPendTaskCaller returned) returned saved acquired acquired last_heap.
Proof.
  intros environment critical local next_local sg original mask saved before first_heap
    returned_view acquired last_heap Hboot [Hsame [Hinterval [Hsaved [Hinput Houtput]]]].
  cbn zeta.
  assert (Hview : os_sched_execution_view (flag_pend_call_with_view_fragments original returned_view) =
    returned_view) by (apply flag_pend_call_with_view_fragments_view; exact Hsame).
  split; [exact Hview|].
  split; [apply flag_pend_boot_view_normal_return; exact Hboot|].
  split; [exact Hinterval|].
  split; [exact Hsaved|].
  split.
  - exact (proj2 (flag_pend_boot_task_view_save_input_equiv environment critical local sg
      original mask before Hboot) first_heap Hinput).
  - apply (proj2 (flag_pend_boot_task_view_restore_input_equiv environment critical next_local sg
      (flag_pend_call_with_view_fragments original returned_view) saved acquired acquired Hboot)).
    rewrite Hview.
    exact Houtput.
Qed.

Lemma flag_pend_boot_view_restore_resources :
  forall environment critical local next_local sg original saved acquired
    released first_heap returned_view current last_heap,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_view_restore_primitive_post environment critical local next_local (fun _ _ => emp) sg
    (os_sched_execution_view original) None original saved acquired released first_heap
    returned_view current last_heap ->
  let returned := flag_pend_call_with_view_fragments original returned_view in
  os_sched_execution_view returned = returned_view /\
  kernel_call_normal_return original released returned current /\
  critical_region_interval critical sg original.(os_sched_call_invocation) released current /\
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local
    (fun _ _ => emp) sg (FlagPendTaskCaller original) original saved acquired released first_heap /\
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical next_local
    (fun _ _ => emp) sg (FlagPendTaskCaller returned) returned
      (armv7a_irq_fiq_mask saved) current last_heap.
Proof.
  intros environment critical local next_local sg original saved acquired released first_heap
    returned_view current last_heap Hboot [Hsame [Hinterval [Hinput Houtput]]].
  cbn zeta.
  assert (Hview : os_sched_execution_view (flag_pend_call_with_view_fragments original returned_view) =
    returned_view) by (apply flag_pend_call_with_view_fragments_view; exact Hsame).
  split; [exact Hview|].
  split; [apply flag_pend_boot_view_normal_return; exact Hboot|].
  split; [exact Hinterval|].
  split.
  - exact (proj2 (flag_pend_boot_task_view_restore_input_equiv environment critical local sg
      original saved acquired released Hboot) first_heap Hinput).
  - apply (proj2 (flag_pend_boot_task_view_save_input_equiv environment critical next_local sg
      (flag_pend_call_with_view_fragments original returned_view)
      (armv7a_irq_fiq_mask saved) current Hboot)).
    rewrite Hview.
    exact Houtput.
Qed.

End FlagPendBootViewResources.

Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_call_protocol.
Require Import Ucos2Verify.VC.code.interrupt.spec.interrupt_call_c_primitive_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The preceding frozen FlagPendBootViewResources module supplies the
    same-heap Task/view equivalences. Caller and execution types remain the
    ordinary shared types. No First/mode or environment-body premise occurs. *)
Module FlagPendBootPrimitive.
Import ViewPrimitiveComponent FlagPendBootViewResources.

Inductive flag_pend_boot_save_completion
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local next_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (original : OsSchedCallContext) (mask saved : Z)
  (before : UCOS2_Verify_State) (first_heap : model) :
  OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| FlagPendBootSaveCompletion : forall returned_view acquired last_heap,
    original.(os_sched_call_origin) = BootInvocation ->
    flag_pend_view_save_primitive_post environment critical local next_local
      (fun _ _ => emp) sg (os_sched_execution_view original) None original
      mask saved before first_heap returned_view acquired last_heap ->
    flag_pend_boot_save_completion environment critical local next_local sg
      original mask saved before first_heap
      (flag_pend_call_with_view_fragments original returned_view) acquired last_heap.

Inductive flag_pend_boot_restore_completion
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (local next_local : Armv7aContinuation -> Assertion) (sg : StableGlobVars)
  (original : OsSchedCallContext) (saved : Z)
  (acquired released : UCOS2_Verify_State) (first_heap : model) :
  OsSchedCallContext -> UCOS2_Verify_State -> model -> Prop :=
| FlagPendBootRestoreCompletion : forall returned_view current last_heap,
    original.(os_sched_call_origin) = BootInvocation ->
    flag_pend_view_restore_primitive_post environment critical local next_local
      (fun _ _ => emp) sg (os_sched_execution_view original) None original
      saved acquired released first_heap returned_view current last_heap ->
    flag_pend_boot_restore_completion environment critical local next_local sg
      original saved acquired released first_heap
      (flag_pend_call_with_view_fragments original returned_view) current last_heap.

(** The pure effects forget only the actual resource parameters and heaps.
    Every witness still contains the original primitive post at those heaps. *)
Definition flag_pend_boot_save_effect environment critical sg original mask saved
  before returned acquired : Prop :=
  exists local next_local first_heap last_heap,
    flag_pend_boot_save_completion environment critical local next_local sg
      original mask saved before first_heap returned acquired last_heap.

Definition flag_pend_boot_restore_effect environment critical sg original
  released returned current : Prop :=
  exists local next_local saved acquired first_heap last_heap,
    flag_pend_boot_restore_completion environment critical local next_local sg
      original saved acquired released first_heap returned current last_heap.

Lemma flag_pend_boot_save_completion_from_post :
  forall environment critical local next_local sg original mask saved
    before first_heap returned_view acquired last_heap,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_view_save_primitive_post environment critical local next_local
    (fun _ _ => emp) sg (os_sched_execution_view original) None original
    mask saved before first_heap returned_view acquired last_heap ->
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap
    (flag_pend_call_with_view_fragments original returned_view) acquired last_heap.
Proof. intros; constructor; assumption. Qed.

Lemma flag_pend_boot_restore_completion_from_post :
  forall environment critical local next_local sg original saved
    acquired released first_heap returned_view current last_heap,
  original.(os_sched_call_origin) = BootInvocation ->
  flag_pend_view_restore_primitive_post environment critical local next_local
    (fun _ _ => emp) sg (os_sched_execution_view original) None original
    saved acquired released first_heap returned_view current last_heap ->
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired released first_heap
    (flag_pend_call_with_view_fragments original returned_view) current last_heap.
Proof. intros; constructor; assumption. Qed.

Lemma flag_pend_boot_save_completion_post :
  forall environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap,
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap ->
  original.(os_sched_call_origin) = BootInvocation /\
  task_tcb_init_stack_same_call returned original /\
  kernel_call_normal_return original before returned acquired /\
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
  interrupt_saved_value mask saved /\
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical local
    (fun _ _ => emp) sg (FlagPendTaskCaller original) original mask before first_heap /\
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical next_local
    (fun _ _ => emp) sg (FlagPendTaskCaller returned) returned saved acquired acquired last_heap.
Proof.
  intros environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap Hcomplete.
  destruct Hcomplete as [returned_view acquired last_heap Hboot Hpost].
  destruct (flag_pend_boot_view_save_resources environment critical local next_local sg
    original mask saved before first_heap returned_view acquired last_heap Hboot Hpost)
    as [Hview [Hnormal [Hinterval [Hsaved [Hinput Houtput]]]]].
  split; [exact Hboot|].
  split; [apply flag_pend_call_with_view_fragments_same_call|].
  exact (conj Hnormal (conj Hinterval (conj Hsaved (conj Hinput Houtput)))).
Qed.

Lemma flag_pend_boot_restore_completion_post :
  forall environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap,
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap ->
  original.(os_sched_call_origin) = BootInvocation /\
  task_tcb_init_stack_same_call returned original /\
  kernel_call_normal_return original released returned current /\
  critical_region_interval critical sg original.(os_sched_call_invocation) released current /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current /\
  flag_pend_call_protocol.flag_pend_caller_restore_input environment critical local
    (fun _ _ => emp) sg (FlagPendTaskCaller original) original saved acquired released first_heap /\
  flag_pend_call_protocol.flag_pend_caller_save_input environment critical next_local
    (fun _ _ => emp) sg (FlagPendTaskCaller returned) returned
      (armv7a_irq_fiq_mask saved) current last_heap.
Proof.
  intros environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap Hcomplete.
  destruct Hcomplete as [returned_view current last_heap Hboot Hpost].
  destruct (flag_pend_boot_view_restore_resources environment critical local next_local sg
    original saved acquired released first_heap returned_view current last_heap Hboot Hpost)
    as [Hview [Hnormal [Hinterval [Hinput Houtput]]]].
  assert (Hcall : task_tcb_init_call_preserved sg original.(os_sched_call_invocation)
    released current).
  { intros Hvalid.
    destruct (critical_region_interval_transports_resources critical sg
      original.(os_sched_call_invocation) released current Hinterval Hvalid)
      as [Hcurrent [Hcreation Hactive]].
    refine (conj Hcurrent (conj Hcreation (conj Hactive _))).
    exact (critical_region_interval_preserves_name_state critical sg
      original.(os_sched_call_invocation) released current Hinterval). }
  split; [exact Hboot|].
  split; [apply flag_pend_call_with_view_fragments_same_call|].
  exact (conj Hnormal (conj Hinterval (conj Hcall (conj Hinput Houtput)))).
Qed.

Lemma flag_pend_boot_save_completion_effect :
  forall environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap,
  flag_pend_boot_save_completion environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap ->
  flag_pend_boot_save_effect environment critical sg original mask saved before returned acquired.
Proof.
  intros environment critical local next_local sg original mask saved
    before first_heap returned acquired last_heap Hcomplete.
  exists local, next_local, first_heap, last_heap; exact Hcomplete.
Qed.

Lemma flag_pend_boot_restore_completion_effect :
  forall environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap,
  flag_pend_boot_restore_completion environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap ->
  flag_pend_boot_restore_effect environment critical sg original released returned current.
Proof.
  intros environment critical local next_local sg original saved
    acquired released first_heap returned current last_heap Hcomplete.
  exists local, next_local, saved, acquired, first_heap, last_heap; exact Hcomplete.
Qed.

Lemma flag_pend_boot_save_effect_observations :
  forall environment critical sg original mask saved before returned acquired,
  flag_pend_boot_save_effect environment critical sg original mask saved before returned acquired ->
  original.(os_sched_call_origin) = BootInvocation /\
  task_tcb_init_stack_same_call returned original /\
  kernel_call_normal_return original before returned acquired /\
  critical_region_interval critical sg original.(os_sched_call_invocation) before acquired /\
  interrupt_saved_value mask saved.
Proof.
  intros environment critical sg original mask saved before returned acquired
    [local [next_local [first_heap [last_heap Hcomplete]]]].
  destruct (flag_pend_boot_save_completion_post environment critical local next_local sg
    original mask saved before first_heap returned acquired last_heap Hcomplete)
    as [Hboot [Hsame [Hnormal [Hinterval [Hsaved Hresources]]]]].
  exact (conj Hboot (conj Hsame (conj Hnormal (conj Hinterval Hsaved)))).
Qed.

Lemma flag_pend_boot_restore_effect_observations :
  forall environment critical sg original released returned current,
  flag_pend_boot_restore_effect environment critical sg original released returned current ->
  original.(os_sched_call_origin) = BootInvocation /\
  task_tcb_init_stack_same_call returned original /\
  kernel_call_normal_return original released returned current /\
  critical_region_interval critical sg original.(os_sched_call_invocation) released current /\
  task_tcb_init_call_preserved sg original.(os_sched_call_invocation) released current.
Proof.
  intros environment critical sg original released returned current
    [local [next_local [saved [acquired [first_heap [last_heap Hcomplete]]]]]].
  destruct (flag_pend_boot_restore_completion_post environment critical local next_local sg
    original saved acquired released first_heap returned current last_heap Hcomplete)
    as [Hboot [Hsame [Hnormal [Hinterval [Hcall Hresources]]]]].
  exact (conj Hboot (conj Hsame (conj Hnormal (conj Hinterval Hcall)))).
Qed.

End FlagPendBootPrimitive.

