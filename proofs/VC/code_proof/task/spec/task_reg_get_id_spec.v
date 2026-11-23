Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.

Import ListNotations UCOS2_C_Rules TaskStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** V2.93.01 OSTaskRegGetID, selected one-register profile. The allocator
    effect ends BEFORE Restore. The two region intervals are separate from
    that effect, and the caller error byte is privately owned throughout.
    Invocation/origin below index the existing CPU/CSL resources; neither
    one asserts that a task, rather than boot or an ISR, is executing. *)
Definition task_reg_get_id_next (s : UCOS2_Verify_State) : Z :=
  s.(TskState).(taskRegNextID).

Definition task_reg_get_id_update (s : UCOS2_Verify_State) (next : Z)
  : UCOS2_Verify_State :=
  replace_TskS (task_set_reg_next_id s.(TskState) next) s.

Definition task_reg_get_id_effect (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (id err : Z) (released : UCOS2_Verify_State) : Prop :=
  exists code tasks,
    task_reg_get_id sg entry.(TskState) = (id, code, tasks) /\
    err = encode_os_err_code code /\
    released = replace_TskS tasks entry.

(** The two environment intervals remain distinct. The protected allocator
    returns both the C return value and the privately owned error-byte output.
    Neither interval is replaced by equality or an unconstrained state change. *)
Definition task_reg_get_id_allocate (sg : StableGlobVars)
  : program UCOS2_Verify_State (Z * Z) :=
  fun entry result released =>
    task_reg_get_id_effect sg entry (fst result) (snd result) released.

Definition task_reg_get_id_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat)
  : program UCOS2_Verify_State (Z * Z) :=
  StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (task_reg_get_id_allocate sg)
      (fun result => StateRelMonad.bind
        (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret result))).

Definition task_reg_get_id_safe (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (task_reg_get_id_program critical sg invocation)
    (fun result current => X (fst result) (snd result) current).

Lemma task_reg_get_id_safe_return :
  forall critical sg invocation before entry released current id err X,
  critical_region_interval critical sg invocation before entry ->
  task_reg_get_id_effect sg entry id err released ->
  critical_region_interval critical sg invocation released current ->
  task_reg_get_id_safe critical sg invocation before X ->
  safeExec (eq current) (StateRelMonad.ret (id, err))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation before entry released current id err X
    Hentry Heffect Hreturn Hsafe.
  unfold task_reg_get_id_safe in Hsafe.
  eapply (highstependret_derive
    (task_reg_get_id_program critical sg invocation) (eq before)
    (id, err) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state.
  exists current; split; [|reflexivity].
  unfold task_reg_get_id_program, StateRelMonad.bind,
    task_reg_get_id_allocate, update, StateRelMonad.ret; cbn.
  exists tt, entry; split; [exact Hentry|].
  exists (id, err), released; split; [exact Heffect|].
  exists tt, current; split; [exact Hreturn|].
  split; reflexivity.
Qed.

Definition task_reg_get_id_addresses (sg : StableGlobVars) (next_addr : Z) : Prop :=
  sg.(g_OSTaskRegNextAvailID) = next_addr.

Definition task_reg_get_id_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  : Assertion :=
  task_public_storage_without_reg_allocator sg s.(TskState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) **
  UCOS2_raw_rep_missing_task sg s.

Definition task_reg_get_id_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  critical_region_outside critical sg invocation s.

Definition task_reg_get_id_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (perr : Z) : Assertion :=
  coq_prop (UCOS2_state_inv sg before) &&
  (task_reg_get_id_closed platform critical sg invocation origin mask before **
   perr # UChar |->_).

(** Permissive normal-return observation of the existing Restore contract.
    Registered interference is not replaced by equality to [released].
    The consequence below also embeds its immediate, empty-interval return;
    no new platform resource or invariant-preservation axiom is introduced. *)
Definition task_reg_get_id_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (released : UCOS2_Verify_State) : Assertion :=
  EX current,
    coq_prop (critical_region_interval critical sg invocation released current /\
      UCOS2_state_inv sg current) &&
    task_reg_get_id_closed platform critical sg invocation origin
      (armv7a_irq_fiq_mask saved) current.

Lemma task_reg_get_id_restore_immediate_consequence :
  forall platform critical sg invocation origin saved released,
  UCOS2_state_inv sg released ->
  task_reg_get_id_closed platform critical sg invocation origin
    (armv7a_irq_fiq_mask saved) released |--
  task_reg_get_id_restore_post platform critical sg invocation origin saved released.
Proof.
  intros; unfold task_reg_get_id_restore_post; Exists released.
  assert (critical_region_interval critical sg invocation released released)
    by constructor.
  entailer!.
Qed.

Definition task_reg_get_id_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (perr id : Z)
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX entry released current err,
    coq_prop (critical_region_interval critical sg invocation before entry /\
      task_reg_get_id_effect sg entry id err released /\
      critical_region_interval critical sg invocation released current /\
      UCOS2_state_inv sg current /\
      safeExec (eq current) (StateRelMonad.ret (id, err))
        (fun result state => X (fst result) (snd result) state)) &&
    (task_reg_get_id_closed platform critical sg invocation origin mask current **
     perr # UChar |-> err).

Lemma task_reg_get_id_configuration : forall sg s,
  UCOS2_state_inv sg s -> sg.(osKernelConfig).(cfgTaskRegisters) = 1.
Proof.
  intros sg s H; unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
    selected_kernel_profile, tcb64_configuration in H; tauto.
Qed.

Lemma task_reg_get_id_next_in_range : forall sg s,
  UCOS2_state_inv sg s -> 0 <= task_reg_get_id_next s <= 1.
Proof.
  intros sg s H; pose proof (task_reg_get_id_configuration sg s H) as Hcfg.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, task_in_range,
    valid_task_reg_allocator in H.
  unfold task_reg_get_id_next; rewrite <- Hcfg; tauto.
Qed.

Lemma task_reg_get_id_update_preserves_invariant : forall sg s next,
  UCOS2_state_inv sg s -> 0 <= next <= 1 ->
  UCOS2_state_inv sg (task_reg_get_id_update s next).
Proof.
  intros sg s next Hvalid Hnext.
  pose proof (task_reg_get_id_configuration sg s Hvalid) as Hcfg.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  destruct Hvalid as [Hprofile [Htasks Hrest]].
  split; [exact Hprofile|]. split.
  - apply task_set_reg_next_id_preserves_in_range; [exact Htasks|].
    rewrite Hcfg; exact Hnext.
  - exact Hrest.
Qed.

Lemma task_reg_get_id_other_modules_eq : forall sg s next,
  UCOS2_raw_rep_missing_task sg (task_reg_get_id_update s next) =
  UCOS2_raw_rep_missing_task sg s.
Proof.
  intros sg s next; apply UCOS2_raw_rep_missing_module_frame.
  intros m Hother; destruct m; try contradiction; try reflexivity.
  - apply sched_raw_rep_change_task_index; reflexivity.
  - apply event_raw_rep_change_task_index,
      event_wait_priority_agreement_encodes.
    unfold event_wait_priority_agreement; intros; reflexivity.
Qed.

Lemma task_reg_get_id_frame_update_eq : forall sg s next,
  task_reg_get_id_frame sg (task_reg_get_id_update s next) =
  task_reg_get_id_frame sg s.
Proof.
  intros; unfold task_reg_get_id_frame.
  rewrite task_reg_get_id_other_modules_eq; reflexivity.
Qed.

Lemma task_reg_get_id_split : forall sg s,
  UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s /\ 0 <= task_reg_get_id_next s <= 1) &&
  (sg.(g_OSTaskRegNextAvailID) # UChar |-> task_reg_get_id_next s **
   task_reg_get_id_frame sg s).
Proof.
  intros sg s; rewrite UCOS2_inv_split_task; Intros.
  assert (Hvalid : UCOS2_state_inv sg s) by assumption.
  pose proof (task_reg_get_id_configuration sg s Hvalid) as Hcfg.
  pose proof (task_reg_get_id_next_in_range sg s Hvalid) as Hrange.
  unfold task_shared_rep, task_reg_get_id_frame.
  sep_apply (task_public_storage_split_reg_allocator sg s.(TskState)).
  unfold task_reg_allocator_rep; rewrite Hcfg; simpl.
  unfold task_reg_get_id_next; entailer!.
Qed.

Lemma task_reg_get_id_merge_updated : forall sg s next,
  UCOS2_state_inv sg s -> 0 <= next <= 1 ->
  sg.(g_OSTaskRegNextAvailID) # UChar |-> next **
  task_reg_get_id_frame sg s |--
  UCOS2_inv sg (task_reg_get_id_update s next).
Proof.
  intros sg s next Hvalid Hnext.
  pose proof (task_reg_get_id_configuration sg s Hvalid) as Hcfg.
  pose proof (task_reg_get_id_update_preserves_invariant sg s next Hvalid Hnext) as Hpost.
  unfold task_reg_get_id_frame.
  assert (Hcell : sg.(g_OSTaskRegNextAvailID) # UChar |-> next =
    task_reg_allocator_rep sg (task_set_reg_next_id s.(TskState) next)).
  { unfold task_reg_allocator_rep; rewrite Hcfg; reflexivity. }
  rewrite Hcell.
  sep_apply (task_public_storage_merge_updated_reg_allocator sg s.(TskState) next).
  rewrite <- task_reg_get_id_other_modules_eq with (next := next).
  rewrite UCOS2_inv_split_task.
  unfold task_shared_rep.
  entailer!.
Qed.

Lemma task_reg_get_id_update_put_back : forall s,
  task_reg_get_id_update s (task_reg_get_id_next s) = s.
Proof.
  intros s; unfold task_reg_get_id_update, task_reg_get_id_next.
  rewrite task_set_reg_next_id_put_back; destruct s; reflexivity.
Qed.

Lemma task_reg_get_id_effect_exhausted : forall sg entry,
  UCOS2_state_inv sg entry -> 1 <= task_reg_get_id_next entry ->
  task_reg_get_id_effect sg entry 1 150 entry.
Proof.
  intros sg entry Hvalid Hfull.
  pose proof (task_reg_get_id_configuration sg entry Hvalid) as Hcfg.
  exists OS_ERR_NO_MORE_ID_AVAIL, entry.(TskState); split.
  - rewrite task_reg_get_id_exhausted by
      (rewrite Hcfg; unfold task_reg_get_id_next in Hfull; lia).
    rewrite Hcfg; reflexivity.
  - split; [reflexivity|]. destruct entry; reflexivity.
Qed.

Lemma task_reg_get_id_effect_available : forall sg entry,
  UCOS2_state_inv sg entry -> task_reg_get_id_next entry < 1 ->
  task_reg_get_id_effect sg entry (task_reg_get_id_next entry) 0
    (task_reg_get_id_update entry (task_reg_get_id_next entry + 1)).
Proof.
  intros sg entry Hvalid Havailable.
  pose proof (task_reg_get_id_configuration sg entry Hvalid) as Hcfg.
  exists OS_ERR_NONE,
    (task_set_reg_next_id entry.(TskState) (task_reg_get_id_next entry + 1)).
  split; [|split; reflexivity].
  apply task_reg_get_id_available.
  - unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, task_in_range in Hvalid; tauto.
  - rewrite Hcfg; lia.
  - rewrite Hcfg; exact Havailable.
Qed.
