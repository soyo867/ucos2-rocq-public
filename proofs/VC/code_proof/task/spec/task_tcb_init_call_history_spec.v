Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Observations transported by this call's actual interference segment.
    The public state, current TCB SP and parked map may change. Validity is
    conditional on the actual entry world, so legacy registered traces have
    a direct consequence without inventing an initial-world premise.
    Actual source producers also return the CURRENT spatial owner. *)
Definition task_tcb_init_call_preserved sg invocation before after : Prop :=
  UCOS2_state_inv sg before ->
  UCOS2_state_inv sg after /\
  task_creation_frame invocation before.(TskState) after.(TskState) /\
  (forall origin, task_invocation_active before.(TskState) invocation origin ->
    task_invocation_active after.(TskState) invocation origin) /\
  before.(NameState) = after.(NameState).

Lemma task_tcb_init_call_preserved_refl : forall sg invocation state,
  task_tcb_init_call_preserved sg invocation state state.
Proof.
  intros sg invocation state Hvalid; split; [exact Hvalid|].
  split; [unfold task_creation_frame; reflexivity|].
  split; [auto|reflexivity].
Qed.

Lemma task_tcb_init_call_preserved_trans : forall sg invocation before middle after,
  task_tcb_init_call_preserved sg invocation before middle ->
  task_tcb_init_call_preserved sg invocation middle after ->
  task_tcb_init_call_preserved sg invocation before after.
Proof.
  intros sg invocation before middle after Hfirst Hlast Hvalid.
  destruct (Hfirst Hvalid) as [Hmiddle [Hframe1 [Hactive1 Hname1]]].
  destruct (Hlast Hmiddle) as [Hafter [Hframe2 [Hactive2 Hname2]]].
  split; [exact Hafter|]. split.
  - unfold task_creation_frame in *; congruence.
  - split; [intros origin Hactive; apply Hactive2, Hactive1; exact Hactive|congruence].
Qed.

Lemma task_tcb_init_interval_preserves_call : forall critical sg invocation before after,
  critical_region_interval critical sg invocation before after ->
  task_tcb_init_call_preserved sg invocation before after.
Proof.
  intros critical sg invocation before after Hinterval Hvalid.
  destruct (critical_region_interval_transports_resources critical sg invocation
    before after Hinterval Hvalid) as [Hafter [Hframe Hactive]].
  split; [exact Hafter|]. split; [exact Hframe|]. split; [exact Hactive|].
  eapply critical_region_interval_preserves_name_state; exact Hinterval.
Qed.

Lemma task_tcb_init_call_preserves_entry : forall sg args invocation origin before after,
  task_tcb_init_entry sg args invocation origin before ->
  task_tcb_init_call_preserved sg invocation before after ->
  task_tcb_init_entry sg args invocation origin after.
Proof.
  intros sg args invocation origin before after
    [Hvalid [Hpriority [Hactive [Hpending Hname]]]] Hpreserved.
  destruct (Hpreserved Hvalid) as [Hpost [Hframe [Hresume Hname_frame]]].
  split; [exact Hpost|]. split; [exact Hpriority|].
  split; [apply Hresume; exact Hactive|]. split.
  - unfold task_tcb_init_pending in *.
    eapply task_creation_frame_lookup; [exact Hframe|exact Hpending|reflexivity].
  - unfold task_tcb_init_name_valid in *; intros Htasknames.
    destruct (Hname Htasknames) as [chars Hread].
    exists chars; rewrite <- Hname_frame; exact Hread.
Qed.

Lemma task_tcb_init_call_preserves_allocation :
  forall sg args invocation origin acquired slot rest image current,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  task_tcb_init_call_preserved sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest image) current ->
  UCOS2_state_inv sg current /\
  task_tcb_init_commit_binding args invocation origin acquired current slot /\
  task_invocation_active current.(TskState) invocation origin.
Proof.
  intros sg args invocation origin acquired slot rest image current Hentry Hdetach Hpreserved.
  pose proof (task_tcb_init_detach_preserves_validity sg args invocation origin acquired
    slot rest image Hentry Hdetach) as Hvalid.
  destruct (Hpreserved Hvalid) as [Hpost [Hframe [Hresume Hname]]].
  split; [exact Hpost|]. split.
  - unfold task_tcb_init_commit_binding.
    exists {| creationInvocation := invocation; creationOrigin := origin;
      creationAllocation := Some {| privateSlot := slot;
        privateGeneration := acquired.(TskState).(taskLifecycle).(taskNextGeneration);
        privateStorage := image |} |}.
    exists {| privateSlot := slot;
      privateGeneration := acquired.(TskState).(taskLifecycle).(taskNextGeneration);
      privateStorage := image |}; split.
    + eapply task_creation_frame_lookup; [exact Hframe| |reflexivity].
      simpl; destruct (Z.eq_dec args.(initPrio) args.(initPrio)); [reflexivity|contradiction].
    + repeat split; reflexivity.
  - apply Hresume; exact (proj1 (proj2 (proj2 Hentry))).
Qed.

(** The result keeps the two actual protected mutations, including exact
    allocation slot/generation and every configured published field. Only
    the surrounding interference observations are generalized to admit the
    physical IRQ deposit/take steps. The legacy result implies this one. *)
Inductive task_tcb_init_call_result
  (sg : StableGlobVars) (args : TaskTCBInitArgs)
  (invocation : nat) (origin : TaskInvocationOrigin)
  (initial : UCOS2_Verify_State) : Z -> UCOS2_Verify_State -> Prop :=
| TaskTCBInitCallNoFree : forall acquired,
    task_tcb_init_call_preserved sg invocation initial acquired ->
    acquired.(TskState).(unUsedTaskStates) = [] ->
    task_tcb_init_pending args invocation origin acquired ->
    UCOS2_state_inv sg acquired ->
    task_tcb_init_call_result sg args invocation origin initial 66 acquired
| TaskTCBInitCallPublished : forall acquired slot rest old current entry allocation node,
    task_tcb_init_call_preserved sg invocation initial acquired ->
    task_tcb_init_detach_observation args invocation origin acquired slot rest old ->
    task_tcb_init_call_preserved sg invocation
      (task_tcb_init_detached_state args invocation origin acquired slot rest old) current ->
    current.(TskState).(taskLifecycle).(taskReservations) args.(initPrio) = Some entry ->
    entry.(creationInvocation) = invocation -> entry.(creationOrigin) = origin ->
    entry.(creationAllocation) = Some allocation ->
    allocation.(privateSlot) = slot ->
    allocation.(privateGeneration) = acquired.(TskState).(taskLifecycle).(taskNextGeneration) ->
    task_commit_identity current.(TskState) args.(initPrio) invocation node ->
    (forall field, In field (tcb_configured_fields sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)) ->
      task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
        (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile) args old) field =
      task_layout_image sg
        (task_set_links node current.(TskState).(tcbListHead) None) field) ->
    UCOS2_state_inv sg current ->
    UCOS2_state_inv sg (task_tcb_init_commit_state sg args invocation node current) ->
    task_tcb_init_call_result sg args invocation origin initial 0
      (task_tcb_init_commit_state sg args invocation node current).

Lemma task_tcb_init_call_result_return_codes : forall sg args invocation origin
    initial result released,
  task_tcb_init_call_result sg args invocation origin initial result released ->
  result = 0 \/ result = 66.
Proof. intros; inversion H; auto. Qed.

Lemma task_tcb_init_call_result_success_has_publication :
  forall sg args invocation origin initial released,
  task_tcb_init_call_result sg args invocation origin initial 0 released ->
  exists slot generation, task_publication_happened released.(TskState)
    invocation slot generation.
Proof.
  intros; inversion H; subst.
  eexists; eexists; apply task_tcb_init_commit_records_publication.
Qed.

Lemma task_tcb_init_call_published_result : forall sg args invocation origin initial
    acquired slot rest image current,
  task_tcb_init_entry sg args invocation origin acquired ->
  task_tcb_init_call_preserved sg invocation initial acquired ->
  task_tcb_init_detach_observation args invocation origin acquired slot rest image ->
  task_tcb_init_call_preserved sg invocation
    (task_tcb_init_detached_state args invocation origin acquired slot rest image) current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  UCOS2_state_inv sg current ->
  task_tcb_init_call_result sg args invocation origin initial 0
    (task_tcb_init_published_state sg args invocation acquired current slot image).
Proof.
  intros sg args invocation origin initial acquired slot rest image current
    Hentry Hinter Hdetach Hopen Hbinding Hvalid.
  pose proof (proj2 (proj2 (proj2 Hentry))) as [Hpending Hname].
  destruct (Hopen (task_tcb_init_detach_preserves_validity sg args invocation origin
    acquired slot rest image Hentry Hdetach)) as [_ [_ [_ Hname_frame]]].
  assert (Hname_current : sg.(osKernelConfig).(cfgTaskNames) = true ->
      exists chars, readable_name current.(NameState)
        (task_tcb_init_commit_node args acquired slot image).(tcbTaskName) chars).
  { intros Htasknames.
    destruct (Hname Htasknames) as [chars Hread].
    exists chars; rewrite (task_tcb_init_commit_node_name args acquired slot image).
    rewrite <- Hname_frame; exact Hread. }
  pose proof (task_tcb_init_commit_binding_identity args invocation origin
    acquired current slot image Hbinding) as Hidentity.
  destruct (task_tcb_init_detached_flags_defined sg args invocation origin
    acquired slot rest image Hentry Hdetach) as [flags Hflags].
  destruct Hbinding as [entry [allocation [He [Hi [Ho [Ha [Hs Hg]]]]]]].
  unfold task_tcb_init_published_state.
  eapply TaskTCBInitCallPublished with (acquired := acquired) (slot := slot)
    (rest := rest) (old := image) (entry := entry) (allocation := allocation);
    try eassumption.
  - eapply task_tcb_init_commit_node_layout_field_eq; eassumption.
  - unfold task_tcb_init_commit_state.
    eapply UCOS2_task_commit_preserves_validity.
    + exact Hvalid.
    + exact Hidentity.
    + unfold task_tcb_init_commit_node, task_tcb_init_node_from_free_image,
        is_effectively_ready, task_non_suspension_bits, task_is_suspended.
      cbn; reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact Hname_current.
Qed.


Lemma task_tcb_init_result_implies_call_result :
  forall critical sg args invocation origin initial result released,
  task_tcb_init_result critical sg args invocation origin initial result released ->
  task_tcb_init_call_result sg args invocation origin initial result released.
Proof.
  intros critical sg args invocation origin initial result released Hresult.
  destruct Hresult.
  - apply TaskTCBInitCallNoFree; try assumption.
    eapply task_tcb_init_interval_preserves_call; eassumption.
  - eapply TaskTCBInitCallPublished; try eassumption;
      eapply task_tcb_init_interval_preserves_call; eassumption.
Qed.

Lemma task_tcb_init_call_no_free_pending_agreement :
  forall sg args invocation origin initial released,
  task_tcb_init_call_result sg args invocation origin initial 66 released ->
  task_creation_fragment_agrees released.(TskState)
    (task_creation_singleton args.(initPrio) (task_tcb_init_initial_entry invocation origin)) /\
  task_rollback_guard released.(TskState) args.(initPrio) invocation.
Proof.
  intros sg args invocation origin initial released Hresult; inversion Hresult; subst.
  split.
  - apply task_creation_singleton_agreement; assumption.
  - eexists; split; [eassumption|]; split; reflexivity.
Qed.
