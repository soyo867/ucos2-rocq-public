Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source-call parameters at the protected TCBInit publication cut.
    This record contains values, not a CPU ABI, a ready-coverage law, or a
    second mutable stack ledger.  Its lease is the real allocation chosen
    by TCBInit; the image is the initialized private TCB layout. *)
Record TaskCreateStackPublication : Type := {
  stack_publication_region : TaskStackRegion;
  stack_publication_args : TaskCreateArgs;
  stack_publication_return : Z;
  stack_publication_lower : list (option Z);
  stack_publication_upper : list (option Z);
  stack_publication_name : Z;
  stack_publication_invocation : nat;
  stack_publication_origin : TaskInvocationOrigin;
  stack_publication_acquired : UCOS2_Verify_State;
  stack_publication_slot : TaskID;
  stack_publication_image : TCBLayoutImage;
  stack_publication_lease : TaskStackLease
}.

Definition task_create_stack_publication_args (publication : TaskCreateStackPublication) :=
  task_create_tcb_args publication.(stack_publication_args)
    (task_stack_init_sp TaskStackNoVFP publication.(stack_publication_args).(createStackTop))
    publication.(stack_publication_name).

Definition task_create_stack_publication_words (publication : TaskCreateStackPublication) :=
  task_create_stack_image TaskStackNoVFP publication.(stack_publication_args)
    publication.(stack_publication_return) publication.(stack_publication_lower)
    publication.(stack_publication_upper).

Definition task_create_stack_publication_raw_state sg
  (publication : TaskCreateStackPublication) current :=
  task_tcb_init_published_state sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image).

Definition task_create_stack_publication_state sg
  (publication : TaskCreateStackPublication) current :=
  task_create_stack_published_state sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image)
    publication.(stack_publication_lease) (task_create_stack_publication_words publication).

Definition task_create_stack_publication_input sg
  (publication : TaskCreateStackPublication) current : Prop :=
  let actual := task_create_stack_publication_args publication in
  task_create_stack_layout TaskStackNoVFP publication.(stack_publication_region)
    publication.(stack_publication_args) publication.(stack_publication_lower)
    publication.(stack_publication_upper) /\
  publication.(stack_publication_lease).(stackLeaseRegion) = publication.(stack_publication_region) /\
  task_tcb_init_commit_binding actual publication.(stack_publication_invocation)
    publication.(stack_publication_origin) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) /\
  task_stack_creation_binding current.(TskState) actual.(initPrio)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_lease) /\
  (exists flags, publication.(stack_publication_image) (TCBCommonField TCBFlagsRdy) = Some flags) /\
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node actual publication.(stack_publication_acquired)
        publication.(stack_publication_slot) publication.(stack_publication_image)).(tcbTaskName) chars).

(** The real publication action includes the stack-map outcome.  The old
    TaskPublish remains a useful TCB/lifecycle projection, but is not used
    as if it had already deposited this buffer or its continuation entry. *)
Definition task_create_stack_publication_client (publication : TaskCreateStackPublication)
  : KernelClientAction :=
  {| kernel_client_actor := Some publication.(stack_publication_invocation);
     kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg current after =>
       task_create_stack_publication_input sg publication current /\
       after = task_create_stack_publication_state sg publication current |}.

Lemma task_create_stack_publication_raw_projection : forall sg publication current after,
  kernel_client_step (task_create_stack_publication_client publication) sg current after ->
  let actual := task_create_stack_publication_args publication in
  let node := task_tcb_init_commit_node actual publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image) in
  kernel_client_step (task_creation_client
    (TaskPublish actual.(initPrio) publication.(stack_publication_invocation) node)) sg current
    (task_create_stack_publication_raw_state sg publication current) /\
  after = replace_TskS
    (glob_task_set_parked_stacks
      (task_create_stack_publication_raw_state sg publication current).(TskState)
      (task_stack_park current.(TskState).(parkedTaskStacks)
        publication.(stack_publication_lease) (task_create_stack_publication_words publication)))
    (task_create_stack_publication_raw_state sg publication current).
Proof.
  intros sg publication current after [Hinput ->] actual node.
  destruct Hinput as [Hlayout [Hregion [Hcommit [Hcreation [Hflags Hname]]]]].
  split; [|reflexivity].
  change (task_lifecycle_action_guard sg
      (TaskPublish actual.(initPrio) publication.(stack_publication_invocation) node) current /\
    task_lifecycle_name_protocol sg
      (TaskPublish actual.(initPrio) publication.(stack_publication_invocation) node) current /\
    task_create_stack_publication_raw_state sg publication current =
      task_lifecycle_action_state sg
        (TaskPublish actual.(initPrio) publication.(stack_publication_invocation) node) current).
  split.
  - split.
    + eapply task_tcb_init_commit_binding_identity; exact Hcommit.
    + split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - split; [exact Hname|reflexivity].
Qed.

Lemma task_create_stack_publication_name_frame : forall sg publication current after,
  kernel_client_step (task_create_stack_publication_client publication) sg current after ->
  current.(NameState) = after.(NameState).
Proof.
  intros sg publication current after [Hinput ->]; reflexivity.
Qed.

Lemma task_create_stack_publication_timer_state_eq : forall sg publication current after,
  kernel_client_step (task_create_stack_publication_client publication) sg current after ->
  after.(TimerState) = current.(TimerState).
Proof.
  intros sg publication current after [Hinput ->]; reflexivity.
Qed.

Definition task_create_stack_publication_resources external platform port
  (abi : Armv7aContinuationABI external platform port) sg
  (publication : TaskCreateStackPublication) current : Assertion :=
  task_create_publication_storage sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image) **
  task_stack_storage publication.(stack_publication_region)
    (task_create_stack_publication_words publication) **
  armv7a_task_continuations abi current.(TskState).(parkedTaskStacks).

(** Bind the source action to the very heap cut that publishes the TCB and
    hands over the initialized buffer.  Action certification alone is not a
    resource producer: this theorem consumes the concrete owners and the
    old continuation map, yielding the map stored in the action's outcome. *)
Lemma task_create_stack_publication_source_post :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg publication current,
  UCOS2_state_inv sg current ->
  task_create_stack_publication_input sg publication current ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_stack_publication_resources external platform port abi sg publication current |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current after) &&
  (UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication current Hvalid Hinput after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current after)
    by (split; [exact Hinput|reflexivity]).
  destruct Hinput as [Hlayout [Hregion [Hcommit [Hcreation [[flags Hflags] Hname]]]]].
  unfold task_create_stack_publication_resources.
  pose proof (task_create_publication_stack_merge external platform port abi sg
    publication.(stack_publication_region) publication.(stack_publication_args)
    publication.(stack_publication_return) publication.(stack_publication_lower)
    publication.(stack_publication_upper) publication.(stack_publication_name)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) current publication.(stack_publication_slot)
    publication.(stack_publication_image) publication.(stack_publication_lease) flags
    Hvalid Hlayout Hregion Hcommit Hcreation Hflags Hname) as Hmerge.
  cbv zeta in Hmerge.
  fold (task_create_stack_publication_args publication) in Hmerge.
  fold (task_create_stack_publication_words publication) in Hmerge.
  fold (task_create_stack_publication_state sg publication current) in Hmerge.
  fold after in Hmerge; sep_apply_l_atomic Hmerge.
  apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; exact Hstep.
  - reflexivity.
Qed.

Lemma task_create_stack_publication_preserves_validity : forall sg publication current after,
  UCOS2_state_inv sg current ->
  kernel_client_step (task_create_stack_publication_client publication) sg current after ->
  UCOS2_state_inv sg after.
Proof.
  intros sg publication current after Hvalid Hstep.
  destruct (task_create_stack_publication_raw_projection sg publication current after Hstep)
    as [Hraw Hafter].
  pose proof (kernel_client_preserves_validity _ (task_creation_client_certificate _)
    sg current (task_create_stack_publication_raw_state sg publication current) Hvalid Hraw) as Hraw_valid.
  destruct Hstep as [[Hlayout [Hregion [Hcommit [Hcreation [Hflags Hname]]]]] Hstate].
  set (actual := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node actual publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  pose proof (task_tcb_init_commit_binding_identity actual publication.(stack_publication_invocation)
    publication.(stack_publication_origin) publication.(stack_publication_acquired) current
    publication.(stack_publication_slot) publication.(stack_publication_image) Hcommit) as Hidentity.
  destruct (task_stack_creation_binding_commit_identity current.(TskState) actual.(initPrio)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_lease) node Hcreation Hidentity) as [Hslot Hgeneration].
  rewrite Hafter; apply UCOS2_replace_parked_stacks_preserves_validity; [exact Hraw_valid|].
  apply task_stack_park_preserves_consistency with (invocation := publication.(stack_publication_invocation)).
  - change (parked_stacks_consistent
      (task_create_stack_publication_raw_state sg publication current).(TskState)
      (task_create_stack_publication_raw_state sg publication current).(TskState).(parkedTaskStacks)).
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hraw_valid; tauto.
  - rewrite Hregion; exact (proj1 (proj1 Hlayout)).
  - apply task_commit_establishes_stack_binding.
    split; [exact Hslot|]. split; [exact Hgeneration|].
    rewrite Hregion.
    change (task_stack_saved_pointer_in_range publication.(stack_publication_region)
      actual.(initStkPtr)).
    unfold actual, task_create_stack_publication_args.
    rewrite (proj1 (proj2 (task_create_tcb_args_common_fields publication.(stack_publication_args)
      (task_stack_init_sp TaskStackNoVFP publication.(stack_publication_args).(createStackTop))
      publication.(stack_publication_name)))).
    eapply task_create_stack_pointer_in_range; exact Hlayout.
  - rewrite <- Hslot, <- Hgeneration; apply task_commit_records_history.
Qed.

Lemma task_create_stack_publication_certificate : forall publication,
  KernelClientCertificate (task_create_stack_publication_client publication).
Proof.
  intro publication; constructor.
  - intros; eapply task_create_stack_publication_preserves_validity; eauto.
  - intros sg current after observer Hvalid Hstep Hforeign.
    destruct (task_create_stack_publication_raw_projection sg publication current after Hstep)
      as [Hraw Hafter].
    rewrite Hafter.
    change (task_creation_frame observer current.(TskState)
      (task_create_stack_publication_raw_state sg publication current).(TskState)).
    eapply kernel_client_frames_creation; [apply task_creation_client_certificate|exact Hvalid|exact Hraw|].
    exact Hforeign.
  - intros sg current after observer origin Hvalid Hstep Hresume Hactive.
    destruct (task_create_stack_publication_raw_projection sg publication current after Hstep)
      as [Hraw Hafter].
    rewrite Hafter.
    change (task_invocation_active
      (task_create_stack_publication_raw_state sg publication current).(TskState) observer origin).
    eapply kernel_client_preserves_continuation;
      [apply task_creation_client_certificate|exact Hvalid|exact Hraw|reflexivity|exact Hactive].
  - intros sg current after observer Hvalid Hstep Hforeign.
    destruct (task_create_stack_publication_raw_projection sg publication current after Hstep)
      as [Hraw Hafter].
    rewrite Hafter; reflexivity.
Qed.
