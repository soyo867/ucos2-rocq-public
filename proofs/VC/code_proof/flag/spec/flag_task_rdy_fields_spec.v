Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_fields_spec.
Require Export Ucos2Verify.lib.flag_node_fields.
Require Export Ucos2Verify.lib.flag_fields_resources.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Six-field footprint companion for the same caller-protected helper.
    Pure domains, TCB stores, bitmap updates and Boolean observation are reused.
    The actual Unlink fields callee clears the retained intermediate backlink.
    Supplemental padding belongs to the caller's real frame. *)
Definition flag_task_rdy_fields_resources (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  flag_fields_raw_rep sg s.(FlagState) **
  task_public_storage sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState).
Definition flag_task_rdy_fields_pre (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : addr) (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z) : Assertion :=
  coq_prop (flag_task_rdy_domain sg s p w old bits) && flag_task_rdy_fields_resources sg s.
Definition flag_task_rdy_fields_post (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : addr) (w : FlagWaiterState) (bits : Z) (result : PendStatus) (returned : Z) : Assertion :=
  EX post, EX schedule,
  coq_prop (flag_task_rdy sg s p bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\ valid_flag_state sg post.(FlagState)) &&
  (flag_task_rdy_fields_resources sg post ** flag_node_fields_return_loan sg.(osKernelConfig) w).

Definition flag_task_rdy_fields_node_frame (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) : Assertion :=
  flag_unlink_fields_node_without_tcb sg p w **
  flag_fields_raw_rep_without_node sg s p.

Lemma flag_task_rdy_fields_node_split_tcb : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  flag_fields_raw_rep sg s |--
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
  flag_task_rdy_fields_node_frame sg s p w.
Proof.
  intros sg s p w [_ [_ [Htcb _]]] Hw; rewrite Htcb.
  rewrite (flag_fields_raw_rep_split_node sg s p w Hw).
  unfold flag_task_rdy_fields_node_frame, flag_node_fields_rep,
    flag_unlink_fields_node_without_tcb, flag_unlink_fields_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_group_addr, flag_unlink_tcb_addr;
    entailer!.
Qed.

Lemma flag_task_rdy_fields_node_merge_tcb : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
  flag_task_rdy_fields_node_frame sg s p w |-- flag_fields_raw_rep sg s.
Proof.
  intros sg s p w [_ [_ [Htcb _]]] Hw; rewrite Htcb.
  rewrite (flag_fields_raw_rep_split_node sg s p w Hw).
  unfold flag_task_rdy_fields_node_frame, flag_node_fields_rep,
    flag_unlink_fields_node_without_tcb, flag_unlink_fields_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_group_addr, flag_unlink_tcb_addr;
    entailer!.
Qed.

Lemma flag_task_rdy_fields_unlink_finish : forall sg s p w old bits result F,
  flag_task_rdy_domain sg s p w old bits ->
  flag_unlink_fields_post sg s.(FlagState) p w (flag_task_rdy_middle old bits result) **
  flag_task_rdy_call_frame sg s w old bits result F |--
  flag_task_rdy_fields_post sg s p w bits result (flag_task_rdy_return old) ** F.
Proof.
  intros sg s p w old bits result F Hdomain.
  destruct Hdomain as [Hlayout [Hdomain [Hlookup [Hprio Hbits]]]].
  pose proof Hdomain as [Hcfg _].
  unfold flag_unlink_fields_post; Intros after.
  rewrite flag_task_rdy_middle_clear_node_eq.
  rewrite <- flag_task_rdy_task_rep_equiv by exact Hcfg.
  unfold flag_task_rdy_call_frame.
  sepcon_right_assoc.
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg s.(TskState)
    w.(flagTask) (task_flag_wake old bits result)).
  unfold flag_task_rdy_fields_post.
  Exists (flag_wake_state sg s w after old bits result) (Z.eqb (flag_task_rdy_status old) 0).
  unfold flag_task_rdy_fields_resources, flag_task_rdy_after_tasks, flag_task_rdy_after_sched,
    flag_wake_state; simpl.
  entailer!.
  - unfold flag_task_rdy; rewrite (proj1 H), Hlookup.
    change (Some (Z.eqb (encode_task_status (task_clear_flag_status old.(stat))) 0,
      flag_wake_state sg s w after old bits result) =
      Some (Z.eqb (flag_task_rdy_status old) 0, flag_wake_state sg s w after old bits result)).
    rewrite task_clear_flag_status_encoding; reflexivity.
Qed.

(** Stable entry and restoration retain the same pure global invariant. *)
Lemma flag_task_rdy_fields_stable_split : forall sg s p w bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_unlink_layout -> 0 <= bits < 65536 ->
  s.(FlagState).(flagWaitNodes) p = Some w ->
  UCOS2_fields_inv sg s |--
  EX old, coq_prop (UCOS2_state_inv sg s) &&
    (flag_task_rdy_fields_pre sg s p w old bits **
     UCOS2_raw_rep_missing_task_storage_sched_flag sg s).
Proof.
  intros sg s p w bits Hcfg Hlayout Hbits Hw.
  rewrite UCOS2_fields_inv_split_task_storage_sched_flag.
  Intros.
  destruct (flag_task_rdy_stable_domain sg s p w bits Hcfg Hlayout Hbits H Hw)
    as [old Hdomain].
  Exists old.
  unfold flag_task_rdy_fields_pre, flag_task_rdy_fields_resources, flag_fields_configured_rep.
  rewrite Hcfg; cbn [selected_kernel_configuration cfgFlagEnabled]; entailer!.
Qed.

Lemma flag_task_rdy_fields_stable_merge : forall sg s p w old bits result returned,
  UCOS2_state_inv sg s ->
  flag_task_rdy_domain sg s p w old bits ->
  flag_task_rdy_fields_post sg s p w bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg s p bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_fields_inv sg post ** flag_node_fields_return_loan sg.(osKernelConfig) w).
Proof.
  intros sg s p w old bits result returned Hvalid Hdomain.
  destruct Hdomain as [_ [Hdomain [Hlookup _]]].
  pose proof Hdomain as [Hcfg [Hflags [Hw _]]].
  unfold flag_task_rdy_fields_post; Intros post schedule.
  destruct (flag_task_rdy_result sg s p bits result schedule post (proj1 H))
    as [selected [after [before [Hunlink [Hbefore [Hpost Hschedule]]]]]].
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hselected.
  assert (selected = w) by congruence; subst selected.
  assert (before = old) by congruence; subst before; subst post.
  Exists (flag_wake_state sg s w after old bits result) schedule.
  unfold flag_task_rdy_fields_resources.
  assert (Hconfigured : flag_fields_configured_rep sg
    (flag_wake_state sg s w after old bits result).(FlagState) =
    flag_fields_raw_rep sg (flag_wake_state sg s w after old bits result).(FlagState)).
  { unfold flag_fields_configured_rep; rewrite Hcfg; reflexivity. }
  rewrite <- Hconfigured.
  sepcon_right_assoc.
  pose proof (UCOS2_fields_inv_merge_flag_wake sg s p w after old bits result Hvalid Hunlink Hlookup) as Hmerge.
  cbv zeta in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.
