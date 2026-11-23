Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task_stack Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The common normal-return observation at the C call boundary. A call
    that returns has its original invocation, origin and stack lease; its
    execution resource is no longer parked on behalf of that same call.
    Availability is conditional, so a caller cannot manufacture it from
    an arbitrary old world. The returned stack fragments may have changed.

    This is part of the explicitly selected abstract platform contract,
    not a consequence of the older opaque execution predicates. Detailed
    save/take/restore implementations can refine it separately. It says
    nothing about readiness, Idle, C counters or eventual return. *)
Definition kernel_call_normal_return original before returned after : Prop :=
  task_tcb_init_stack_same_call returned original /\
  (kernel_call_stack_available original before ->
   kernel_call_stack_available returned after).

(** The C environment's completed-call control relation, for a caller
    which has not itself executed Start/Enter/Exit/Lock/Unlock. Intermediate
    interrupt nesting and execution by other tasks are allowed. Matching
    interrupt entry/exit and balanced foreign locking must establish these
    endpoint equalities; same invocation alone cannot establish them.
    This relation is not an ARM/BSP guarantee and is not asserted of each
    elementary R/G step. A consumer selects it only for the relevant
    normal-call interval, retaining early-error and disabled branches. *)
Definition kernel_call_control_rely (_ : StableGlobVars)
  (before after : UCOS2_Verify_State) : Prop :=
  after.(SchedState).(isRunning) = before.(SchedState).(isRunning) /\
  after.(IntrState) = before.(IntrState).

(** Static binding of the selected C layout to the port's first-word SP
    access. In the original ucos_ii.h, OSTCBStkPtr is the first member of
    struct os_tcb, before the optional fields. QCP's named field_addr is
    opaque in Coq, so this is an explicit layout interpretation parameter,
    not a theorem derived from an arbitrary field_addr or a new axiom.
    It is fixed for the program, not a task-specific run-time restriction. *)
Definition kernel_tcb_stack_field_layout (sg : StableGlobVars) : Prop :=
  forall slot, task_slot_in_range sg slot ->
    tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot.

Lemma kernel_call_task_source_stack_field_address : forall sg call state,
  kernel_tcb_stack_field_layout sg -> UCOS2_state_inv sg state ->
  kernel_call_task_source call state ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot).
Proof.
  intros sg call state Hlayout Hvalid Hsource.
  destruct (kernel_call_task_source_current_at call state Hsource)
    as [_ [node [Hnode _]]].
  apply Hlayout.
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  destruct Htasks as [Hpool _].
  apply (proj2 (proj1 Hpool call.(os_sched_call_stack).(stackLeaseSlot))).
  left; exists node; exact Hnode.
Qed.

(** The C modules supply [rely] for their admitted environmental interval.
    It is separate from the normal-return platform observation: Idle,
    scheduler counters, object lifetimes and other kernel invariants must
    be justified by the C environment's R/G guarantees. No theorem below
    derives an arbitrary [rely] merely from registry membership.

    Both posts retain the existing registered source trace and the real
    returned world. [resources] includes any private pool owned by that
    world; it is not treated as an unchanged frame across a switch. *)
Definition kernel_call_modular_save_post {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  resources local critical
  (rely : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop)
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (kernel_call_save_source external port critical sg
      original returned mask saved before acquired /\
      kernel_call_normal_return original before returned acquired /\
      rely sg before acquired) &&
    kernel_continuation_call_masked abi resources local critical sg
      (task_stack_call_active_key returned) returned saved acquired acquired.

Definition kernel_call_modular_restore_post {external platform port}
  (abi : Armv7aContinuationABI external platform port)
  resources local critical
  (rely : StableGlobVars -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop)
  sg original mask released : Assertion :=
  EX returned current,
    coq_prop (kernel_resumption_task_source_trace external port
      critical.(critical_region_clients) sg original.(os_sched_call_invocation)
      None original.(os_sched_call_origin) released false
      returned.(os_sched_call_origin) current /\
      kernel_call_normal_return original released returned current /\
      rely sg released current) &&
    kernel_continuation_call_closed abi resources local sg
      (task_stack_call_active_key returned) returned mask current.

Lemma kernel_call_normal_return_refl : forall call state,
  kernel_call_normal_return call state call state.
Proof.
  intros; unfold kernel_call_normal_return, task_tcb_init_stack_same_call; auto.
Qed.

Lemma kernel_call_normal_return_trans : forall first initial middle current last final,
  kernel_call_normal_return first initial middle current ->
  kernel_call_normal_return middle current last final ->
  kernel_call_normal_return first initial last final.
Proof.
  intros first initial middle current last final [[Hi [Ho Hs]] Hfirst]
    [[Hi' [Ho' Hs']] Hlast].
  split; [unfold task_tcb_init_stack_same_call; repeat split; congruence|auto].
Qed.

(** Actual Scheduler consumer of the shared Save interface. The incoming
    ready fact is transported by the supplied C rely guarantee; current
    binding follows the existing registered source theorem. The platform
    part supplies only same-call execution availability. *)
Lemma kernel_call_modular_save_post_sched_cut :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    resources local critical rely sg original mask saved before,
  UCOS2_state_inv sg before ->
  kernel_call_task_source original before ->
  kernel_call_stack_available original before ->
  before.(SchedState).(readyList) <> [] ->
  (forall after, rely sg before after -> before.(SchedState).(readyList) <> [] ->
    after.(SchedState).(readyList) <> []) ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  kernel_call_modular_save_post abi resources local critical rely
    sg original mask saved before |--
  EX returned acquired,
    coq_prop (kernel_call_save_source external port critical sg original returned mask saved before acquired /\
      kernel_call_normal_return original before returned acquired /\
      rely sg before acquired /\ os_sched_call_cut sg returned acquired) &&
    kernel_continuation_call_masked abi resources local critical sg
      (task_stack_call_active_key returned) returned saved acquired acquired.
Proof.
  intros external platform port abi resources local critical rely sg original mask saved before
    Hvalid Hsource Havailable Hready Hrely Haddress.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source external port critical sg
    original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  assert (Henv : rely sg before acquired) by tauto.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid' _].
  assert (Hcut : os_sched_call_cut sg returned acquired).
  { apply os_sched_call_cut_from_source.
    - exact Hvalid'.
    - exact (kernel_call_save_source_preserves_task_source external port critical sg
        original returned mask saved before acquired Hvalid Hsource Hsave).
    - apply Hrely; assumption.
    - apply (proj2 Hnormal); exact Havailable.
    - rewrite (proj2 (proj2 (proj1 Hnormal))); exact Haddress. }
  Exists returned acquired; entailer!.
Qed.

(** Boot/ISR/locked entries do not need an unconditional ready or current
    task premise. These two C rely obligations are guarded by the ACTUAL
    acquired decision. In particular a normal control-frame relation can
    carry a disabled entry to the disabled acquired branch. *)
Lemma kernel_call_modular_save_post_guarded_cut :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    resources local critical rely sg original mask saved before,
  UCOS2_state_inv sg before -> kernel_tcb_stack_field_layout sg ->
  (forall after, rely sg before after -> os_sched_selection_enabled after = true ->
    after.(SchedState).(readyList) <> []) ->
  (forall after, rely sg before after -> os_sched_requests_switch after = true ->
    kernel_call_task_source original before /\ kernel_call_stack_available original before) ->
  kernel_call_modular_save_post abi resources local critical rely
    sg original mask saved before |--
  EX returned acquired,
    coq_prop (kernel_call_save_source external port critical sg original returned mask saved before acquired /\
      kernel_call_normal_return original before returned acquired /\
      rely sg before acquired /\ os_sched_call_cut sg returned acquired) &&
    kernel_continuation_call_masked abi resources local critical sg
      (task_stack_call_active_key returned) returned saved acquired acquired.
Proof.
  intros external platform port abi resources local critical rely sg original mask saved before
    Hvalid Hlayout Hready Hsource.
  unfold kernel_call_modular_save_post; Intros returned acquired.
  assert (Hsave : kernel_call_save_source external port critical sg
    original returned mask saved before acquired) by tauto.
  assert (Hnormal : kernel_call_normal_return original before returned acquired) by tauto.
  assert (Henv : rely sg before acquired) by tauto.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid' _].
  assert (Hcut : os_sched_call_cut sg returned acquired).
  { split; [apply Hready; exact Henv|].
    intro Hswitch; destruct (Hsource acquired Henv Hswitch) as [Horiginal Havailable].
    assert (Hcurrent : kernel_call_task_source returned acquired).
    { exact (kernel_call_save_source_preserves_task_source external port critical sg
        original returned mask saved before acquired Hvalid Horiginal Hsave). }
    split.
    - apply kernel_call_task_source_current_storage; try assumption.
      eapply kernel_call_task_source_stack_field_address; eassumption.
    - pose proof (proj2 Hnormal Havailable) as Hnone.
      unfold kernel_call_stack_available in Hnone; rewrite (proj1 Hcurrent) in Hnone.
      exact Hnone. }
  Exists returned acquired; entailer!.
Qed.

(** Reuse the existing resource-trace invariant theorem for the C rely
    component. This has no platform premise, new trace or new registry. *)
Lemma kernel_call_registered_rely_preserves_invariant :
  forall external port critical invariant sg original returned before after,
  (forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources invariant action) ->
  kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    before false returned.(os_sched_call_origin) after ->
  invariant sg before -> invariant sg after.
Proof.
  intros external port critical invariant sg original returned before after Hclients Htrace Hbefore.
  destruct (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)
    as [Hresources _].
  exact (proj1 (kernel_resumption_resource_trace_transports_invariant invariant
    critical.(critical_region_clients) sg original.(os_sched_call_invocation)
    None before false after Hclients Hresources Hbefore)).
Qed.

Lemma kernel_call_modular_restore_post_source :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    resources local critical rely sg original mask released,
  UCOS2_state_inv sg released -> kernel_call_task_source original released ->
  kernel_call_stack_available original released ->
  kernel_call_modular_restore_post abi resources local critical rely
    sg original mask released |--
  EX returned current,
    coq_prop (kernel_call_normal_return original released returned current /\
      kernel_call_task_source returned current /\ kernel_call_stack_available returned current /\
      rely sg released current) &&
    kernel_continuation_call_closed abi resources local sg
      (task_stack_call_active_key returned) returned mask current.
Proof.
  intros external platform port abi resources local critical rely sg original mask released
    Hvalid Hsource Havailable.
  unfold kernel_call_modular_restore_post; Intros returned current.
  assert (Hnormal : kernel_call_normal_return original released returned current) by tauto.
  assert (Htrace : kernel_resumption_task_source_trace external port critical.(critical_region_clients)
    sg original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current) by tauto.
  assert (Hpreserved : task_tcb_init_stack_source_preserved original released current).
  { eapply task_tcb_init_stack_registered_source_preserved;
      [exact Hvalid|exact (proj1 Hnormal)|exact Htrace]. }
  assert (Hcurrent : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original current (proj1 Hnormal))).
    apply Hpreserved; exact Hsource. }
  assert (Havailable' : kernel_call_stack_available returned current)
    by (apply (proj2 Hnormal); exact Havailable).
  Exists returned current; entailer!.
Qed.
