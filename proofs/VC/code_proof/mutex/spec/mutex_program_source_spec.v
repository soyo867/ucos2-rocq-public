Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.core.spec.kernel_program_boot_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Program-level reachability, not another kernel-state Record. The
    initial-state predicate and ordinary invariant stay parameters, so a
    selected64 instance cannot silently supply the full-profile instance.
    No caller-ready/nonwaiting property is imposed at every program cut. *)
Definition mutex_program_reachable
  (initial : StableGlobVars -> UCOS2_Verify_State -> Prop)
  (sg : StableGlobVars) (state : UCOS2_Verify_State) : Prop :=
  exists boot, initial sg boot /\ mutex_owner_source_history sg boot state.

Definition mutex_program_state_inv
  (invariant initial : StableGlobVars -> UCOS2_Verify_State -> Prop)
  (sg : StableGlobVars) (state : UCOS2_Verify_State) : Prop :=
  invariant sg state /\ mutex_program_reachable initial sg state.

Definition mutex_program_resources
  (resources : StableGlobVars -> UCOS2_Verify_State -> Assertion)
  (initial : StableGlobVars -> UCOS2_Verify_State -> Prop)
  (sg : StableGlobVars) (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (mutex_program_reachable initial sg state) && resources sg state.

Lemma mutex_program_initial_reachable : forall initial sg boot,
  initial sg boot -> mutex_program_reachable initial sg boot.
Proof. intros; exists boot; split; [assumption|constructor]. Qed.

Lemma mutex_program_source_step_reachable : forall initial sg before after,
  mutex_program_reachable initial sg before ->
  mutex_owner_source_step sg before after -> mutex_program_reachable initial sg after.
Proof.
  intros initial sg before after [boot [Hinitial Hhistory]] Hstep.
  exists boot; split; [exact Hinitial|econstructor; eassumption].
Qed.

Lemma mutex_program_source_history_reachable : forall initial sg before after,
  mutex_program_reachable initial sg before ->
  mutex_owner_source_history sg before after -> mutex_program_reachable initial sg after.
Proof.
  intros initial sg before after [boot [Hinitial Hhistory]] Hstep.
  exists boot; split; [exact Hinitial|].
  eapply mutex_owner_source_history_trans; eassumption.
Qed.

Lemma mutex_program_reachable_owner_use : forall initial sg state,
  (forall boot eid, initial sg boot -> boot.(EventState).(inUsedEventStates) eid = None) ->
  mutex_program_reachable initial sg state ->
  mutex_owner_event_unlinked state.(TskState) state.(EventState).
Proof.
  intros initial sg state Hboot [boot [Hinitial Hhistory]].
  eapply mutex_owner_source_history_establishes_owner_use; [intros; eapply Hboot; eassumption|exact Hhistory].
Qed.

(** Reuse the existing invariant-parametric client obligation. The source
    classification is about the actual action, not its desired owner-use
    endpoint. Concrete configuration membership will discharge it below. *)
Lemma mutex_program_client_preserves_resources : forall invariant initial action,
  kernel_client_preserves_resources invariant action ->
  (forall sg before after, invariant sg before -> kernel_client_step action sg before after ->
    mutex_owner_source_history sg before after) ->
  kernel_client_preserves_resources (mutex_program_state_inv invariant initial) action.
Proof.
  intros invariant initial action Hresources Hsource sg before after [Hvalid Hreachable] Hstep.
  destruct (Hresources sg before after Hvalid Hstep) as [Hafter [Htask [Hevent Hactive]]].
  split.
  - split; [exact Hafter|].
    eapply mutex_program_source_history_reachable; [exact Hreachable|eapply Hsource; eassumption].
  - split; [exact Htask|]; split; assumption.
Qed.

Definition mutex_program_selected_initial sg state : Prop :=
  exists task_name flag_name memory_name names,
    state = UCOS2_boot_state sg task_name flag_name memory_name names.

Definition mutex_program_selected_reachable sg state : Prop :=
  mutex_program_reachable mutex_program_selected_initial sg state.

Lemma mutex_program_selected_initial_empty : forall sg state eid,
  mutex_program_selected_initial sg state -> state.(EventState).(inUsedEventStates) eid = None.
Proof. intros sg state eid [task_name [flag_name [memory_name [names ->]]]]; reflexivity. Qed.

(** This producer consumes the same existing initializer endpoints and
    the one actual UnMapTbl. It creates neither bytes from a pure history
    nor an OSInit/BSP theorem. Their existing startup boundaries remain. *)
Lemma mutex_program_selected_boot_resources : forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names ** unmap_table_rep sg |--
  mutex_program_resources kernel_program_inv mutex_program_selected_initial sg
    (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory.
  assert (Hreachable : mutex_program_reachable mutex_program_selected_initial sg
      (UCOS2_boot_state sg task_name flag_name memory_name names)).
  { apply mutex_program_initial_reachable.
    exists task_name, flag_name, memory_name, names; reflexivity. }
  unfold mutex_program_resources; apply _derivable1_andp_intros.
  - apply derivable1s_coq_prop_r; exact Hreachable.
  - eapply kernel_boot_initializer_post_establishes_program_inv; eassumption.
Qed.

Lemma mutex_program_selected_reachable_history : forall sg state,
  mutex_program_reachable mutex_program_selected_initial sg state ->
  mutex_owner_program_history sg state.
Proof.
  intros sg state [boot [[task_name [flag_name [memory_name [names ->]]]] Hhistory]].
  exists task_name, flag_name, memory_name, names; exact Hhistory.
Qed.

(** Selecting the reachable-program instance restricts ACTUAL source
    entries, not the desired poststate. The underlying step, actor and
    stop information are unchanged. This is the explicit program-domain
    adapter needed when a kernel operation is valid under the approved
    client protocol but not in every unreachable defensive model state. *)
Definition mutex_program_reachable_client initial (action : KernelClientAction) : KernelClientAction :=
  {| kernel_client_actor := action.(kernel_client_actor);
     kernel_client_event_actor := action.(kernel_client_event_actor);
     kernel_client_stops := action.(kernel_client_stops);
     kernel_client_step := fun sg before after =>
       mutex_program_reachable initial sg before /\ kernel_client_step action sg before after |}.

Lemma mutex_program_reachable_client_source : forall initial action sg before after,
  mutex_program_reachable initial sg before -> kernel_client_step action sg before after ->
  kernel_client_step (mutex_program_reachable_client initial action) sg before after.
Proof. intros; split; assumption. Qed.

Lemma mutex_program_reachable_client_certificate : forall initial action,
  kernel_client_preserves_resources (mutex_program_state_inv UCOS2_state_inv initial) action ->
  KernelClientCertificate (mutex_program_reachable_client initial action).
Proof.
  intros initial action Hresources; constructor;
    intros sg before after; intros; destruct H0 as [Hreachable Hstep];
    destruct (Hresources sg before after (conj H Hreachable) Hstep)
      as [[Hvalid Hafter] [Htask [Hevent Hactive]]].
  - exact Hvalid.
  - apply Htask; assumption.
  - eapply Hactive; eassumption.
  - apply Hevent; assumption.
Qed.
