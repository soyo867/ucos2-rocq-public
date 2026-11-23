Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task_status.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.flag.
Require Export Ucos2Verify.lib.cross_module_invariants.
Require Export Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Require Export Ucos2Verify.lib.ucos2_verify_inv.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Caller-protected internal helper; no Save/Restore or schedule. *)
Definition flag_task_rdy_status (old : TaskAbstractState) : Z :=
  Z.land (encode_task_status old.(stat)) 223.
Definition flag_task_rdy_return (old : TaskAbstractState) : Z :=
  if Z.eqb (flag_task_rdy_status old) 0 then 1 else 0.

(** The four source stores precede Unlink, so the registered node is
    deliberately retained in this intermediate TCB. *)
Definition flag_task_rdy_middle (old : TaskAbstractState)
  (bits : Z) (result : PendStatus) : TaskAbstractState :=
  task_set_flag_node (task_flag_wake old bits result) old.(tcbFlagNode).
Definition flag_task_rdy_middle_image (sg : StableGlobVars)
  (old : TaskAbstractState) (bits : Z) (result : PendStatus) : TCBCommonImage :=
  tcb_write
    (tcb_write
      (tcb_write (tcb_write (task_tcb64_image sg old) TCBDly (Some 0))
        TCBFlagsRdy (Some bits))
      TCBStat (Some (flag_task_rdy_status old)))
    TCBStatPend (Some (encode_pend_status result)).

Lemma flag_task_rdy_middle_image_eq : forall sg old bits result,
  task_tcb64_image sg (flag_task_rdy_middle old bits result) =
  flag_task_rdy_middle_image sg old bits result.
Proof.
  intros; apply functional_extensionality; intros field; destruct field; try reflexivity.
  change (Some (encode_task_status (task_clear_flag_status old.(stat))) =
    Some (flag_task_rdy_status old)).
  unfold flag_task_rdy_status; rewrite task_clear_flag_status_encoding; reflexivity.
Qed.
Lemma flag_task_rdy_middle_clear_node_eq : forall old bits result,
  task_set_flag_node (flag_task_rdy_middle old bits result) 0 =
  task_flag_wake old bits result.
Proof. intros; reflexivity. Qed.
Lemma flag_task_rdy_ready_test_eq : forall old bits result,
  is_effectively_ready (task_flag_wake old bits result).(stat)
    (task_flag_wake old bits result).(dly) =
  Z.eqb (flag_task_rdy_status old) 0.
Proof.
  intros; change (is_effectively_ready (task_clear_flag_status old.(stat)) 0 =
    Z.eqb (flag_task_rdy_status old) 0).
  rewrite is_effectively_ready_zero_delay_eq, task_clear_flag_status_encoding; reflexivity.
Qed.

Definition flag_task_rdy_domain (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : addr) (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z) : Prop :=
  flag_unlink_layout /\ flag_unlink_domain sg s.(FlagState) p w old /\
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old /\
  0 <= old.(curPrio) < 64 /\ 0 <= bits < 65536.
Definition flag_task_rdy_resources (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  flag_raw_rep sg s.(FlagState) **
  task_public_storage sg s.(TskState) **
  sched_raw_rep sg s.(TskState) s.(SchedState).
Definition flag_task_rdy_pre (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : addr) (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z) : Assertion :=
  coq_prop (flag_task_rdy_domain sg s p w old bits) && flag_task_rdy_resources sg s.
Definition flag_task_rdy_post (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (p : addr) (w : FlagWaiterState) (bits : Z) (result : PendStatus) (returned : Z) : Assertion :=
  EX post, EX schedule,
  coq_prop (flag_task_rdy sg s p bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\ valid_flag_state sg post.(FlagState)) &&
  (flag_task_rdy_resources sg post ** flag_node_return_loan sg.(osKernelConfig) w).

Definition flag_task_rdy_node_frame (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) : Assertion :=
  flag_unlink_node_without_tcb sg p w ** flag_nodes_without sg s p ** flag_groups_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.
Lemma flag_task_rdy_node_split_tcb : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  flag_raw_rep sg s |--
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
  flag_task_rdy_node_frame sg s p w.
Proof.
  intros sg s p w [_ [_ [Htcb _]]] Hw; rewrite Htcb.
  unfold flag_raw_rep, flag_task_rdy_node_frame.
  sep_apply_l_atomic (flag_nodes_split_node sg s p w Hw).
  unfold flag_node_rep, flag_unlink_node_without_tcb, flag_unlink_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_group_addr, flag_unlink_tcb_addr; entailer!.
Qed.
Lemma flag_task_rdy_node_merge_tcb : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
  flag_task_rdy_node_frame sg s p w |-- flag_raw_rep sg s.
Proof.
  intros sg s p w [_ [_ [Htcb _]]] Hw; rewrite Htcb.
  assert (Hnode : (p + 8) # Ptr |-> flag_unlink_tcb_addr w **
    flag_unlink_node_without_tcb sg p w |--
    flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)).
  { unfold flag_node_rep, flag_unlink_node_without_tcb, flag_unlink_node_payload,
      flag_unlink_next, flag_unlink_prev, flag_unlink_group_addr, flag_unlink_tcb_addr; entailer!. }
  unfold flag_task_rdy_node_frame, flag_raw_rep.
  sep_apply_l_atomic Hnode; sep_apply_l_atomic (flag_nodes_merge_node sg s p w Hw); entailer!.
Qed.
Lemma flag_task_rdy_task_rep_equiv : forall sg w old,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  used_task_rep sg w.(flagTask) old --||-- flag_unlink_task_rep sg w old.
Proof.
  intros sg w old Hcfg.
  assert (Hm : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hcfg; reflexivity).
  assert (Hp : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hcfg; reflexivity).
  unfold flag_unlink_task_rep; rewrite task_slot_addr_tcb64 by assumption.
  apply used_task_rep_tcb64; assumption.
Qed.

(** Structural residual: all unaccessed fields and both padding bytes. *)
Definition flag_task_rdy_tcb_frame (base : addr) (image : TCBCommonImage) : Assertion :=
  tcb64_fields_rep base (remove TCBField_eq_dec TCBBitY (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields))))))) image.
Lemma flag_task_rdy_tcb_split : forall base image,
  tcb64_storage_rep base image |--
  tcb_cell base TCBDly (image TCBDly) **
  tcb_cell base TCBFlagsRdy (image TCBFlagsRdy) **
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) ** flag_task_rdy_tcb_frame base image.
Proof.
  intros; unfold tcb64_storage_rep.
  sep_apply_l_atomic (tcb64_fields_rep_split tcb_fields base image TCBDly
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBDly tcb_fields) base image TCBFlagsRdy
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields)) base image TCBStat
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields))) base image TCBStatPend
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields)))) base image TCBY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields))))) base image TCBBitX
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields)))))) base image TCBBitY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  unfold flag_task_rdy_tcb_frame; entailer!.
Qed.
Lemma flag_task_rdy_tcb_merge : forall base image,
  tcb_cell base TCBDly (image TCBDly) **
  tcb_cell base TCBFlagsRdy (image TCBFlagsRdy) **
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) ** flag_task_rdy_tcb_frame base image |--
  tcb64_storage_rep base image.
Proof.
  intros; unfold flag_task_rdy_tcb_frame.
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields)))))) base image TCBBitY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields))))) base image TCBBitX
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields)))) base image TCBY
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBStat (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields))) base image TCBStatPend
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBFlagsRdy (remove TCBField_eq_dec TCBDly tcb_fields)) base image TCBStat
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBDly tcb_fields) base image TCBFlagsRdy
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  sep_apply_l_atomic (tcb64_fields_rep_merge tcb_fields base image TCBDly
    ltac:(vm_compute; repeat constructor; simpl; intuition discriminate)
    ltac:(vm_compute; intuition congruence)).
  unfold tcb64_storage_rep; entailer!.
Qed.
Lemma flag_task_rdy_tcb_frame_middle_eq : forall sg old base bits result,
  flag_task_rdy_tcb_frame base (flag_task_rdy_middle_image sg old bits result) =
  flag_task_rdy_tcb_frame base (task_tcb64_image sg old).
Proof.
  intros; unfold flag_task_rdy_tcb_frame, flag_task_rdy_middle_image.
  repeat rewrite tcb64_fields_rep_off_field by (vm_compute; intuition discriminate).
  reflexivity.
Qed.
Lemma flag_task_rdy_tcb_merge_middle : forall sg old base bits result,
  tcb_cell base TCBDly (Some 0) **
  tcb_cell base TCBFlagsRdy (Some bits) **
  tcb_cell base TCBStat (Some (flag_task_rdy_status old)) **
  tcb_cell base TCBStatPend (Some (encode_pend_status result)) **
  tcb_cell base TCBY (Some (tcb_y_of_prio old.(curPrio))) **
  tcb_cell base TCBBitX (Some (tcb_bit_x_of_prio old.(curPrio))) **
  tcb_cell base TCBBitY (Some (tcb_bit_y_of_prio old.(curPrio))) **
  flag_task_rdy_tcb_frame base (task_tcb64_image sg old) |--
  tcb64_storage_rep base (task_tcb64_image sg (flag_task_rdy_middle old bits result)).
Proof.
  intros; rewrite flag_task_rdy_middle_image_eq.
  rewrite <- (flag_task_rdy_tcb_frame_middle_eq sg old base bits result).
  exact (flag_task_rdy_tcb_merge base (flag_task_rdy_middle_image sg old bits result)).
Qed.

Definition flag_task_rdy_after_tasks (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z) (result : PendStatus) :=
  glob_task_set_usedtask s.(TskState) w.(flagTask) (task_flag_wake old bits result).
Definition flag_task_rdy_after_sched (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z) (result : PendStatus) :=
  sched_wake_task sg s.(TskState) s.(SchedState) w.(flagTask) (task_flag_wake old bits result).
Definition flag_task_rdy_ready_group (s : UCOS2_Verify_State) : Z :=
  encode_ready_grp s.(SchedState).(readyList) s.(TskState).
Definition flag_task_rdy_ready_row (s : UCOS2_Verify_State) (old : TaskAbstractState) : Z :=
  encode_ready_tbl_at_or s.(SchedState).(readyList) s.(TskState) (tcb_y_of_prio old.(curPrio)).
Definition flag_task_rdy_ready_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (old : TaskAbstractState) : Assertion :=
  UCharArray.missing_i sg.(g_OSRdyTbl) (tcb_y_of_prio old.(curPrio)) 0 8
    (sched_row_values s.(TskState) s.(SchedState).(readyList)) **
  sched_physical_rep sg s.(SchedState).
Lemma flag_task_rdy_ready_split : forall sg s old,
  0 <= old.(curPrio) < 64 ->
  sched_raw_rep sg s.(TskState) s.(SchedState) |--
  sg.(g_OSRdyGrp) # UChar |-> flag_task_rdy_ready_group s **
  (sg.(g_OSRdyTbl) + tcb_y_of_prio old.(curPrio) * sizeof(UCHAR)) # UChar |->
    flag_task_rdy_ready_row s old ** flag_task_rdy_ready_frame sg s old.
Proof.
  intros sg s old Hp.
  assert (Hy : 0 <= tcb_y_of_prio old.(curPrio) < 8).
  { unfold tcb_y_of_prio; split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  unfold sched_raw_rep, flag_task_rdy_ready_frame, flag_task_rdy_ready_group, flag_task_rdy_ready_row.
  sep_apply_l_atomic (sched_rows_split_cell sg s.(TskState) s.(SchedState).(readyList)
    (tcb_y_of_prio old.(curPrio)) Hy); entailer!.
Qed.
Lemma flag_task_rdy_ready_merge_written : forall sg s w old bits result,
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  0 <= old.(curPrio) < 64 -> flag_task_rdy_status old = 0 ->
  sg.(g_OSRdyGrp) # UChar |->
    Z.lor (flag_task_rdy_ready_group s) (tcb_bit_y_of_prio old.(curPrio)) **
  (sg.(g_OSRdyTbl) + tcb_y_of_prio old.(curPrio) * sizeof(UCHAR)) # UChar |->
    Z.lor (flag_task_rdy_ready_row s old) (tcb_bit_x_of_prio old.(curPrio)) **
  flag_task_rdy_ready_frame sg s old |--
  sched_raw_rep sg (flag_task_rdy_after_tasks s w old bits result)
    (flag_task_rdy_after_sched sg s w old bits result).
Proof.
  intros sg s w old bits result Hlookup Hp Hz.
  assert (Hy : 0 <= old.(curPrio) / 8 < 8).
  { split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  assert (Hr : is_effectively_ready (task_flag_wake old bits result).(stat)
    (task_flag_wake old bits result).(dly) = true).
  { rewrite flag_task_rdy_ready_test_eq, Hz; reflexivity. }
  destruct (sched_wake_ready_encoding sg s.(TskState) s.(SchedState)
    w.(flagTask) old (task_flag_wake old bits result) Hlookup eq_refl Hr) as [Hgroup _].
  unfold flag_task_rdy_after_tasks, flag_task_rdy_after_sched, sched_raw_rep.
  rewrite Hgroup.
  unfold flag_task_rdy_ready_group, flag_task_rdy_ready_row, flag_task_rdy_ready_frame,
    tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio, tcb_bit_y_of_prio.
  unfold tcb_y_of_prio.
  assert (Hphysical : sched_physical_rep sg
    (sched_wake_task sg s.(TskState) s.(SchedState) w.(flagTask)
      (task_flag_wake old bits result)) = sched_physical_rep sg s.(SchedState))
    by reflexivity.
  rewrite Hphysical.
  entailer!.
  apply (sched_rows_merge_wake sg s.(TskState) s.(SchedState)
    w.(flagTask) old (task_flag_wake old bits result) Hlookup eq_refl Hr Hy).
Qed.
Lemma flag_task_rdy_ready_unchanged_eq : forall sg s w old bits result,
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  flag_task_rdy_status old <> 0 ->
  sched_raw_rep sg (flag_task_rdy_after_tasks s w old bits result)
    (flag_task_rdy_after_sched sg s w old bits result) =
  sched_raw_rep sg s.(TskState) s.(SchedState).
Proof.
  intros sg s w old bits result Hlookup Hz.
  assert (Hr : is_effectively_ready (task_flag_wake old bits result).(stat)
    (task_flag_wake old bits result).(dly) = false).
  { rewrite flag_task_rdy_ready_test_eq; apply Z.eqb_neq; exact Hz. }
  destruct (sched_wake_not_ready_encoding sg s.(TskState) s.(SchedState)
    w.(flagTask) old (task_flag_wake old bits result) Hlookup eq_refl Hr) as [Hgroup Hrows].
  unfold flag_task_rdy_after_tasks, flag_task_rdy_after_sched, sched_raw_rep.
  rewrite Hgroup; cbn [sched_rows_rep]; rewrite !Hrows.
  unfold sched_physical_rep, sched_wake_task, sched_set_ready; simpl; reflexivity.
Qed.

Definition flag_task_rdy_call_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (old : TaskAbstractState) (bits : Z) (result : PendStatus)
  (F : Assertion) : Assertion :=
  task_public_storage_without_task sg s.(TskState) w.(flagTask) **
  sched_raw_rep sg (flag_task_rdy_after_tasks s w old bits result)
    (flag_task_rdy_after_sched sg s w old bits result) ** F.
Lemma flag_task_rdy_middle_unlink_domain : forall sg s p w old bits result,
  flag_task_rdy_domain sg s p w old bits ->
  flag_unlink_domain sg s.(FlagState) p w (flag_task_rdy_middle old bits result).
Proof.
  intros sg s p w old bits result [_ [Hdomain _]].
  unfold flag_unlink_domain in *; unfold flag_task_rdy_middle; simpl; exact Hdomain.
Qed.
Lemma flag_task_rdy_unlink_finish : forall sg s p w old bits result F,
  flag_task_rdy_domain sg s p w old bits ->
  flag_unlink_post sg s.(FlagState) p w (flag_task_rdy_middle old bits result) **
  flag_task_rdy_call_frame sg s w old bits result F |--
  flag_task_rdy_post sg s p w bits result (flag_task_rdy_return old) ** F.
Proof.
  intros sg s p w old bits result F Hdomain.
  destruct Hdomain as [Hlayout [Hdomain [Hlookup [Hprio Hbits]]]].
  pose proof Hdomain as [Hcfg _].
  unfold flag_unlink_post; Intros after.
  rewrite flag_task_rdy_middle_clear_node_eq.
  rewrite <- flag_task_rdy_task_rep_equiv by exact Hcfg.
  unfold flag_task_rdy_call_frame.
  sepcon_right_assoc.
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg s.(TskState)
    w.(flagTask) (task_flag_wake old bits result)).
  unfold flag_task_rdy_post.
  Exists (flag_wake_state sg s w after old bits result) (Z.eqb (flag_task_rdy_status old) 0).
  unfold flag_task_rdy_resources, flag_task_rdy_after_tasks, flag_task_rdy_after_sched,
    flag_wake_state; simpl.
  entailer!.
  - unfold flag_task_rdy; rewrite (proj1 H), Hlookup.
    change (Some (Z.eqb (encode_task_status (task_clear_flag_status old.(stat))) 0,
      flag_wake_state sg s w after old bits result) =
      Some (Z.eqb (flag_task_rdy_status old) 0, flag_wake_state sg s w after old bits result)).
    rewrite task_clear_flag_status_encoding; reflexivity.
Qed.

(** Exact byte normalization and source BOOLEAN observation. *)
Lemma flag_task_rdy_status_in_range : forall old,
  0 <= flag_task_rdy_status old < 256.
Proof.
  intros; unfold flag_task_rdy_status.
  rewrite <- task_clear_flag_status_encoding; apply encode_task_status_in_range.
Qed.
Lemma flag_task_rdy_status_cast_eq : forall old,
  Z.land (encode_task_status old.(stat)) (unsigned_last_nbits (Z.lnot 32) 8) =
  flag_task_rdy_status old.
Proof. intros; unfold flag_task_rdy_status; reflexivity. Qed.
Lemma flag_task_rdy_return_zero_status : forall old,
  flag_task_rdy_status old = 0 -> flag_task_rdy_return old = 1.
Proof. intros old H; unfold flag_task_rdy_return; rewrite H; reflexivity. Qed.
Lemma flag_task_rdy_return_nonzero_status : forall old,
  flag_task_rdy_status old <> 0 -> flag_task_rdy_return old = 0.
Proof.
  intros old H; unfold flag_task_rdy_return.
  apply Z.eqb_neq in H; rewrite H; reflexivity.
Qed.

(** Entry from a stable kernel uses the actual linked-node/task identity,
    never an independently selected TCB. The rest of the kernel remains
    owned by the caller throughout this internal helper. *)
Lemma flag_task_rdy_active_links_task_id : forall ids used previous tid old,
  task_active_links used previous ids ->
  In tid ids -> used tid = Some old -> old.(taskID) = tid.
Proof.
  induction ids as [|head rest IH]; intros used previous tid old Hlinks Hin Hlookup;
    [contradiction|].
  simpl in Hlinks; destruct Hlinks as [t [Ht [Hid [_ [_ Htail]]]]].
  destruct Hin as [Heq|Hin].
  - assert (t = old) by congruence; subst t; congruence.
  - eapply IH; eassumption.
Qed.

Lemma flag_task_rdy_stable_domain : forall sg s p w bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_unlink_layout -> 0 <= bits < 65536 ->
  UCOS2_state_inv sg s -> s.(FlagState).(flagWaitNodes) p = Some w ->
  exists old, flag_task_rdy_domain sg s p w old bits.
Proof.
  intros sg s p w bits Hcfg Hlayout Hbits Hinv Hw.
  pose proof Hinv as [Hprofile [Htasks [_ [_ [Hcross [_ [_ [Hflags _]]]]]]]].
  assert (Hvalid : valid_flag_state sg s.(FlagState)).
  { unfold valid_flag_configuration in Hflags; rewrite Hcfg in Hflags; exact Hflags. }
  assert (Hwait : task_flag_waiter_consistency sg s.(TskState) s.(FlagState)).
  { unfold cross_module_consistency in Hcross; tauto. }
  destruct Hwait as [Hnodes _].
  destruct (Hnodes p w Hw) as [_ [old [Hlookup [Hgeneration [Hnode [Haddr _]]]]]].
  destruct (valid_flag_state_node_position sg s.(FlagState) p w Hvalid Hw)
    as [g [prefix [rest [_ [_ [Hnodeaddr _]]]]]].
  destruct Htasks as [_ [Hactive [_ [_ [_ [_ [_ [Hprios _]]]]]]]].
  pose proof (task_live_has_one_occurrence s.(TskState) w.(flagTask) old Hactive Hlookup)
    as [Hin _].
  pose proof Hactive as [_ [_ [_ [_ Hlinks]]]].
  pose proof (flag_task_rdy_active_links_task_id _ _ _ _ _ Hlinks Hin Hlookup) as Hid.
  pose proof (Hprios _ old Hlookup) as Hprio.
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  exists old; unfold flag_task_rdy_domain.
  split; [exact Hlayout|].
  split.
  - unfold flag_unlink_domain, flag_unlink_tcb_addr.
    repeat (split; [assumption|]); assumption.
  - split; [exact Hlookup|].
    split; [unfold task_priority_in_range in Hprio; lia|exact Hbits].
Qed.

Lemma flag_task_rdy_stable_split : forall sg s p w bits,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_unlink_layout -> 0 <= bits < 65536 ->
  s.(FlagState).(flagWaitNodes) p = Some w ->
  UCOS2_inv sg s |--
  EX old, coq_prop (UCOS2_state_inv sg s) &&
    (flag_task_rdy_pre sg s p w old bits **
     UCOS2_raw_rep_missing_task_storage_sched_flag sg s).
Proof.
  intros sg s p w bits Hcfg Hlayout Hbits Hw.
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched_flag sg s).
  Intros.
  destruct (flag_task_rdy_stable_domain sg s p w bits Hcfg Hlayout Hbits H Hw)
    as [old Hdomain].
  Exists old.
  unfold flag_task_rdy_pre, flag_task_rdy_resources, flag_configured_rep.
  rewrite Hcfg; cbn [selected_kernel_configuration cfgFlagEnabled]; entailer!.
Qed.

Lemma flag_task_rdy_stable_merge : forall sg s p w old bits result returned,
  UCOS2_state_inv sg s ->
  flag_task_rdy_domain sg s p w old bits ->
  flag_task_rdy_post sg s p w bits result returned **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |--
  EX post, EX schedule,
    coq_prop (flag_task_rdy sg s p bits result = Some (schedule, post) /\
      returned = (if schedule then 1 else 0)) &&
    (UCOS2_inv sg post ** flag_node_return_loan sg.(osKernelConfig) w).
Proof.
  intros sg s p w old bits result returned Hvalid Hdomain.
  destruct Hdomain as [_ [Hdomain [Hlookup _]]].
  pose proof Hdomain as [Hcfg [Hflags [Hw _]]].
  unfold flag_task_rdy_post; Intros post schedule.
  destruct (flag_task_rdy_result sg s p bits result schedule post (proj1 H))
    as [selected [after [before [Hunlink [Hbefore [Hpost Hschedule]]]]]].
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hunlink)) as Hselected.
  assert (selected = w) by congruence; subst selected.
  assert (before = old) by congruence; subst before; subst post.
  Exists (flag_wake_state sg s w after old bits result) schedule.
  unfold flag_task_rdy_resources.
  assert (Hconfigured : flag_configured_rep sg
    (flag_wake_state sg s w after old bits result).(FlagState) =
    flag_raw_rep sg (flag_wake_state sg s w after old bits result).(FlagState)).
  { unfold flag_configured_rep; rewrite Hcfg; reflexivity. }
  rewrite <- Hconfigured.
  sepcon_right_assoc.
  pose proof (UCOS2_inv_merge_flag_wake sg s p w after old bits result Hvalid Hunlink Hlookup) as Hmerge.
  cbv zeta in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.


