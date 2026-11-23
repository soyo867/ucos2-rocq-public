Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import ListLib int_auto.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.flag_execution.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.flag_stack Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.VC.code.flag.spec.flag_block_spec.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Source-faithful protected internal call.  OS_FlagBlock does not acquire
    or release exclusion and does not call the scheduler.  Its caller supplies
    the genuine live-current, ready and unregistered-wait protocol below;
    none is inferred merely from readable TCB/current cells. *)
Definition flag_block_call_layout : Prop :=
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeNext") = p) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodePrev") = p + 4) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") = p + 8) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") = p + 12) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeFlags") = p + 16) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeWaitType") = p + 18) /\
  (forall p, &(p # "os_flag_grp" ->ₛ "OSFlagWaitList") = p + 4).

Definition flag_block_call_node (w : FlagWaiterState) : addr := w.(flagNodeAddr).
Definition flag_block_call_group (sg : StableGlobVars) (w : FlagWaiterState) : addr :=
  flag_pool_addr sg w.(flagGroup).
Definition flag_block_call_tcb (sg : StableGlobVars) (w : FlagWaiterState) : addr :=
  task_slot_addr sg w.(flagTask).
Definition flag_block_call_mask (w : FlagWaiterState) : Z := w.(flagMask).
Definition flag_block_call_mode (w : FlagWaiterState) : Z := encode_flag_wait_mode w.(flagWaitMode).
Definition flag_block_call_head (v : FlagGroupImage) : addr := v.(flagImageHead).
Definition flag_block_call_status (t : TaskAbstractState) : Z := encode_task_status t.(stat).
Definition flag_block_call_pend (t : TaskAbstractState) : Z := encode_pend_status t.(statPend).
Definition flag_block_call_delay (t : TaskAbstractState) : Z := t.(dly).
Definition flag_block_call_y (t : TaskAbstractState) : Z := tcb_y_of_prio t.(curPrio).
Definition flag_block_call_bit_x (t : TaskAbstractState) : Z := tcb_bit_x_of_prio t.(curPrio).
Definition flag_block_call_bit_y (t : TaskAbstractState) : Z := tcb_bit_y_of_prio t.(curPrio).
Definition flag_block_call_row (s : UCOS2_Verify_State) (t : TaskAbstractState) : Z :=
  encode_ready_tbl_at_or s.(SchedState).(readyList) s.(TskState) (flag_block_call_y t).
Definition flag_block_call_grp (s : UCOS2_Verify_State) : Z :=
  encode_ready_grp s.(SchedState).(readyList) s.(TskState).
Definition flag_block_call_row_cleared (s : UCOS2_Verify_State) (t : TaskAbstractState) : Z :=
  Z.land (flag_block_call_row s t) (unsigned_last_nbits (Z.lnot (flag_block_call_bit_x t)) 8).
Definition flag_block_call_grp_cleared (s : UCOS2_Verify_State) (t : TaskAbstractState) : Z :=
  if Z.eqb (flag_block_call_row_cleared s t) 0
  then Z.land (flag_block_call_grp s) (unsigned_last_nbits (Z.lnot (flag_block_call_bit_y t)) 8)
  else flag_block_call_grp s.

Definition flag_block_call_ranges (s : UCOS2_Verify_State) (t : TaskAbstractState) : Prop :=
  0 <= flag_block_call_status t < 256 /\
  0 <= flag_block_call_y t < 8 /\
  0 <= flag_block_call_bit_x t < 256 /\
  0 <= flag_block_call_bit_y t < 256 /\
  0 <= flag_block_call_row s t < 256 /\
  0 <= flag_block_call_grp s < 256.

Definition flag_block_call_node_padding (w : FlagWaiterState) : Assertion :=
  store_optional_bytes (w.(flagNodeAddr) + 19) [None].

Definition flag_block_call_protocol (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (g : FlagGroupState)
  (v : FlagGroupImage) (timeout : Z) : Prop :=
  s.(SchedState).(curTaskID) = Some w.(flagTask) /\
  s.(SchedState).(curSchedPrio) = Some t.(curPrio) /\
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some t /\
  In w.(flagTask) s.(SchedState).(readyList) /\
  t.(tcbFlagNode) = 0 /\ t.(eventPtr) = None /\ t.(eventMultiWaitEvents) = [] /\
  w.(flagTaskGeneration) = t.(taskGeneration) /\ w.(flagNodeAddr) <> 0 /\
  s.(FlagState).(flagWaitNodes) w.(flagNodeAddr) = None /\
  s.(FlagState).(flagUsed) w.(flagGroup) = Some g /\
  w.(flagGroupGeneration) = g.(flagGeneration) /\
  s.(FlagState).(flagImages) w.(flagGroup) = Some v /\
  flag_word_in_range sg.(osKernelConfig) w.(flagMask) /\
  w.(flagWaitImage).(flagNodePadding) = [None] /\
  0 <= timeout <= 4294967295.

Definition flag_block_call_context (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (g : FlagGroupState)
  (v : FlagGroupImage) (timeout : Z) : Prop :=
  flag_block_call_layout /\ sg.(osKernelConfig) = selected_kernel_configuration /\
  UCOS2_state_inv sg s /\ flag_block_call_protocol sg s w t g v timeout.

Definition flag_block_call_pre (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (g : FlagGroupState)
  (v : FlagGroupImage) (timeout : Z) : Assertion :=
  coq_prop (flag_block_call_layout /\ sg.(osKernelConfig) = selected_kernel_configuration /\
    flag_block_call_protocol sg s w t g v timeout) &&
  (UCOS2_inv sg s ** flag_node_uninit_rep sg.(osKernelConfig) w.(flagNodeAddr)).

Definition flag_block_call_post (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (timeout : Z) : Assertion :=
  EX flags, coq_prop
    (flag_block_node sg s.(FlagState) w (flag_block_call_tcb sg w) = Some flags /\
     flag_block_spec.flag_block sg s w timeout =
       Some (flag_execution.flag_block_state s w flags t timeout) /\
     sched_current_blocked_before_schedule
       (flag_execution.flag_block_state s w flags t timeout).(TskState)
       (flag_execution.flag_block_state s w flags t timeout).(SchedState)
       w.(flagTask) (task_prepare_flag_wait t w.(flagNodeAddr) timeout)) &&
    UCOS2_inv sg (flag_execution.flag_block_state s w flags t timeout).

(** These are finite field slices of the canonical TCB64 storage, not a
    second TCB/state transformer.  The four written fields and the three
    later-read priority encodings are focused together. *)
Definition flag_block_call_tcb_rest (base : addr) (image : TCBCommonImage) : Assertion :=
  tcb64_fields_rep base (remove TCBField_eq_dec TCBBitY (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))))))) image.

Lemma flag_block_call_tcb_split : forall base image,
  tcb64_storage_rep base image |--
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBDly (image TCBDly) **
  tcb_cell base TCBFlagNode (image TCBFlagNode) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) **
  flag_block_call_tcb_rest base image.
Proof.
  intros base image; unfold tcb64_storage_rep.
  sep_apply_l_atomic (tcb64_fields_rep_split tcb_fields base image TCBStat
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBStat tcb_fields) base image TCBStatPend
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)) base image TCBDly
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))) base image TCBFlagNode
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))) base image TCBY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))))) base image TCBBitX
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_split (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))))) base image TCBBitY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  unfold flag_block_call_tcb_rest; entailer!.
Qed.

Lemma flag_block_call_tcb_merge : forall base image,
  tcb_cell base TCBStat (image TCBStat) **
  tcb_cell base TCBStatPend (image TCBStatPend) **
  tcb_cell base TCBDly (image TCBDly) **
  tcb_cell base TCBFlagNode (image TCBFlagNode) **
  tcb_cell base TCBY (image TCBY) **
  tcb_cell base TCBBitX (image TCBBitX) **
  tcb_cell base TCBBitY (image TCBBitY) **
  flag_block_call_tcb_rest base image |-- tcb64_storage_rep base image.
Proof.
  intros base image; unfold flag_block_call_tcb_rest, tcb64_storage_rep.
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBBitX (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))))) base image TCBBitY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBY (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))))) base image TCBBitX
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBFlagNode (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)))) base image TCBY
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBDly (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields))) base image TCBFlagNode
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBStatPend (remove TCBField_eq_dec TCBStat tcb_fields)) base image TCBDly
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge (remove TCBField_eq_dec TCBStat tcb_fields) base image TCBStatPend
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  sep_apply_l_atomic (tcb64_fields_rep_merge tcb_fields base image TCBStat
    ltac:(cbn; repeat constructor; simpl; intuition discriminate) ltac:(cbn; tauto)).
  entailer!.
Qed.

Lemma flag_block_call_tcb_rest_update : forall sg t node timeout base,
  flag_block_call_tcb_rest base
    (task_tcb64_image sg (task_prepare_flag_wait t node timeout)) =
  flag_block_call_tcb_rest base (task_tcb64_image sg t).
Proof.
  intros; rewrite task_prepare_flag_wait_image_eq.
  unfold tcb_prepare_wait_image, flag_block_call_tcb_rest.
  repeat rewrite tcb64_fields_rep_off_field by (cbn; intuition discriminate).
  reflexivity.
Qed.

Definition flag_block_call_sched_rest (sg : StableGlobVars) (s : SchedAbstractState) : Assertion :=
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(isRunning) then 1 else 0).

Definition flag_block_call_residual (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) : Assertion :=
  flag_block_call_tcb_rest (flag_block_call_tcb sg w) (task_tcb64_image sg t) **
  task_public_storage_without_task sg s.(TskState) w.(flagTask) **
  flag_block_call_sched_rest sg s.(SchedState) **
  UCharArray.missing_i sg.(g_OSRdyTbl) (flag_block_call_y t) 0 8
    (sched_row_values s.(TskState) s.(SchedState).(readyList)) **
  flag_group_rep_without_head sg.(osKernelConfig) (flag_block_call_group sg w) v **
  flag_groups_without sg s.(FlagState) w.(flagGroup) **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
  UCOS2_raw_rep_missing_task_storage_sched_flag sg s.

Definition flag_block_call_nodes (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  flag_wait_nodes_rep sg s.(FlagState).(flagWaitNodes).
Definition flag_block_call_old_nodes (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (v : FlagGroupImage) : Assertion :=
  flag_wait_nodes_rep sg (flag_block_old_nodes s.(FlagState) v.(flagImageHead) w.(flagNodeAddr)).
Definition flag_block_call_head_lookup (s : UCOS2_Verify_State) (v : FlagGroupImage)
  (head : FlagWaiterState) : Prop := s.(FlagState).(flagWaitNodes) v.(flagImageHead) = Some head.
Definition flag_block_call_head_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (v : FlagGroupImage) (head : FlagWaiterState) : Assertion :=
  flag_node_rep_without_prev sg.(osKernelConfig) v.(flagImageHead) head.(flagWaitImage) **
  flag_wait_nodes_without_node sg s.(FlagState).(flagWaitNodes) v.(flagImageHead).

(** The backlink has already made the node reachable when initialization
    begins.  All these resources are a protected transient, never an
    unpublished/private frame across Restore (there is no Restore here). *)
Definition flag_block_call_ready_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) (timeout : Z) : Assertion :=
  tcb_cell (flag_block_call_tcb sg w) TCBStat
    (Some (Z.lor (flag_block_call_status t) 32)) **
  tcb_cell (flag_block_call_tcb sg w) TCBStatPend (Some 0) **
  tcb_cell (flag_block_call_tcb sg w) TCBDly (Some timeout) **
  tcb_cell (flag_block_call_tcb sg w) TCBFlagNode (Some w.(flagNodeAddr)) **
  flag_node_rep sg.(osKernelConfig) w.(flagNodeAddr)
    (flag_block_node_image sg w (flag_block_call_tcb sg w) v.(flagImageHead)) **
  (flag_block_call_group sg w + 4) # Ptr |-> w.(flagNodeAddr) **
  flag_block_call_old_nodes sg s w v **
  flag_block_call_residual sg s w t v.

Definition flag_block_call_ready_stage (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) (timeout : Z) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> flag_block_call_tcb sg w **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  (sg.(g_OSRdyTbl) + flag_block_call_y t * sizeof(UCHAR)) # UChar |-> flag_block_call_row s t **
  sg.(g_OSRdyGrp) # UChar |-> flag_block_call_grp s **
  flag_block_call_ready_frame sg s w t v timeout.

Definition flag_block_call_written (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) (timeout : Z) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> flag_block_call_tcb sg w **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  (sg.(g_OSRdyTbl) + flag_block_call_y t * sizeof(UCHAR)) # UChar |-> flag_block_call_row_cleared s t **
  sg.(g_OSRdyGrp) # UChar |-> flag_block_call_grp_cleared s t **
  flag_block_call_ready_frame sg s w t v timeout.

Lemma flag_block_call_context_facts : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout ->
  valid_stable_glob_vars sg /\ task_in_range sg s.(TskState) /\
  sched_in_range sg s.(TskState) s.(SchedState) /\ valid_flag_state sg s.(FlagState) /\
  0 <= flag_block_call_y t < 8.
Proof.
  intros sg s w t g v timeout [_ [Hconfig [Hvalid Hprotocol]]].
  pose proof Hvalid as [Hprofile [Htasks [Hsched [_ [_ [_ [_ [Hflags _]]]]]]]].
  pose proof Hprofile as [Hsg _].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hconfig; reflexivity).
  unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags.
  destruct Hprotocol as [_ [_ [Ht _]]].
  pose proof Htasks as [_ [_ [_ [_ [_ [_ [_ [Hprios _]]]]]]]].
  pose proof (Hprios _ _ Ht) as Hp.
  pose proof Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
  unfold task_priority_in_range in Hp.
  split; [exact Hsg|]. split; [exact Htasks|]. split; [exact Hsched|].
  split; [exact Hflags|]. split.
  - unfold flag_block_call_y, tcb_y_of_prio; apply Z.div_pos; lia.
  - unfold flag_block_call_y, tcb_y_of_prio; apply Z.div_lt_upper_bound; lia.
Qed.

Lemma flag_block_call_endpoint_eq : forall sg s w t g v timeout flags,
  flag_block_call_context sg s w t g v timeout ->
  flag_block_node sg s.(FlagState) w (flag_block_call_tcb sg w) = Some flags ->
  flag_block_spec.flag_block sg s w timeout =
    Some (flag_execution.flag_block_state s w flags t timeout).
Proof.
  intros sg s w t g v timeout flags [_ [Hconfig [_ Hprotocol]]] Hstep.
  destruct Hprotocol as [Hcurrent [_ [Ht _]]].
  unfold flag_block_call_tcb in Hstep.
  unfold flag_block_spec.flag_block; rewrite Hcurrent, Ht, Hstep.
  unfold flag_block_spec.flag_block_state, flag_block_spec.flag_block_task.
  rewrite Hconfig; reflexivity.
Qed.

Lemma flag_block_call_blocked : forall sg s w t g v timeout flags,
  flag_block_call_context sg s w t g v timeout ->
  sched_current_blocked_before_schedule
    (flag_execution.flag_block_state s w flags t timeout).(TskState)
    (flag_execution.flag_block_state s w flags t timeout).(SchedState)
    w.(flagTask) (task_prepare_flag_wait t w.(flagNodeAddr) timeout).
Proof.
  intros sg s w t g v timeout flags [_ [_ [_ [Hcurrent [Hprio [Ht Hrest]]]]]].
  unfold sched_current_blocked_before_schedule.
  split; [cbn; rewrite Z.eqb_refl; reflexivity|].
  split; [exact Hcurrent|]. split; [exact Hprio|].
  split; [apply remove_Z_eqb_notin|apply task_prepare_event_wait_not_ready].
Qed.

Lemma flag_block_call_context_ranges : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout -> flag_block_call_ranges s t.
Proof.
  intros sg s w t g v timeout Hcontext.
  destruct (flag_block_call_context_facts _ _ _ _ _ _ _ Hcontext)
    as [Hsg [Htasks [Hsched [Hflags Hy]]]].
  unfold flag_block_call_ranges.
  split; [apply encode_task_status_in_range|].
  split; [exact Hy|]. split.
  - unfold flag_block_call_bit_x, tcb_bit_x_of_prio, tcb_x_of_prio.
    change (0 <= Z.shiftl 1 (curPrio t mod 8) < 2 ^ 8).
    apply bitmap_single_bit_in_range; apply Z.mod_pos_bound; lia.
  - split.
    + unfold flag_block_call_bit_y, tcb_bit_y_of_prio.
      change (0 <= Z.shiftl 1 (tcb_y_of_prio (curPrio t)) < 2 ^ 8).
      apply bitmap_single_bit_in_range; exact Hy.
    + split; [apply encode_ready_tbl_or_in_range|].
      unfold flag_block_call_grp.
      change (0 <= encode_ready_grp (readyList (SchedState s)) (TskState s) < 2 ^ 8).
      apply encode_ready_grp_in_range; intros tid found Hin Hfound.
      destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hprios _]]]]]]]].
      pose proof (Hprios _ _ Hfound) as Hp.
      destruct Hsg as [_ [_ [_ [_ [_ [Hlowest _]]]]]].
      unfold task_priority_in_range in Hp.
      split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
Qed.

Lemma flag_block_call_head_exists : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout -> v.(flagImageHead) <> 0 ->
  exists head, flag_block_call_head_lookup s v head.
Proof.
  intros sg s w t g v timeout Hcontext Hnonzero.
  destruct (flag_block_call_context_facts _ _ _ _ _ _ _ Hcontext) as [_ [_ [_ [Hflags _]]]].
  destruct Hcontext as [_ [_ [_ Hprotocol]]].
  destruct Hprotocol as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hg [_ [Hv _]]]]]]]]]]]]].
  destruct Hflags as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ _ Hg) as [_ [_ [Hlist [image [Himage [_ [Hhead _]]]]]]].
  rewrite Hv in Himage; injection Himage as Himage; subst image.
  destruct (flagWaitOrder g) as [|p rest] eqn:E; simpl in Hhead; [contradiction|].
  destruct (Hlist [] p rest E) as [head [Hlookup _]].
  exists head; unfold flag_block_call_head_lookup; now rewrite Hhead.
Qed.

Lemma flag_block_call_head_split : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout -> flag_block_call_head v <> 0 ->
  flag_block_call_nodes sg s |--
  EX head, coq_prop (flag_block_call_head_lookup s v head) &&
    &(((flag_block_call_head v)) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |->_ **
    flag_block_call_head_frame sg s v head.
Proof.
  intros sg s w t g v timeout Hcontext Hnonzero.
  destruct (flag_block_call_head_exists _ _ _ _ _ _ _ Hcontext Hnonzero) as [head Hhead].
  destruct Hcontext as [[_ [Hprev _]] _].
  unfold flag_block_call_nodes, flag_block_call_head_frame, flag_block_call_head.
  rewrite Hprev.
  sep_apply_l_atomic (flag_wait_nodes_rep_split_prev sg s.(FlagState).(flagWaitNodes)
    v.(flagImageHead) head Hhead).
  sep_apply_l_atomic (store_ptr_undef_store_ptr
    (v.(flagImageHead) + 4) head.(flagWaitImage).(flagNodePrev)).
  Exists head; entailer!.
Qed.

Lemma flag_block_call_head_merge : forall sg s w t g v timeout head,
  flag_block_call_context sg s w t g v timeout -> flag_block_call_head v <> 0 ->
  flag_block_call_head_lookup s v head ->
  &(((flag_block_call_head v)) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> w.(flagNodeAddr) **
    flag_block_call_head_frame sg s v head |-- flag_block_call_old_nodes sg s w v.
Proof.
  intros sg s w t g v timeout head [[_ [Hprev _]] _] Hnonzero Hhead.
  unfold flag_block_call_old_nodes, flag_block_old_nodes, flag_block_call_head in *.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonzero), Hprev.
  unfold flag_block_call_head_frame.
  sep_apply_l_atomic (flag_wait_nodes_rep_merge_updated_prev sg
    s.(FlagState).(flagWaitNodes) v.(flagImageHead) head w.(flagNodeAddr) Hhead).
  entailer!.
Qed.

Lemma flag_block_call_node_split : forall sg w,
  flag_block_call_layout -> sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_node_uninit_rep sg.(osKernelConfig) w.(flagNodeAddr) |--
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlags") # UShort |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeWaitType") # UChar |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |->_ **
    flag_block_call_node_padding w.
Proof.
  intros sg w [Hnext [Hprev [Htcb [Hgroup [Hmask [Hmode Hhead]]]]]] Hconfig.
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode, Hconfig.
  unfold flag_node_uninit_rep, flag_block_call_node_padding.
  cbn; entailer!.
  change (store_optional_bytes (w.(flagNodeAddr) + 18 + 1) [None] |--
    (w.(flagNodeAddr) + 19 + 0) # UChar |->_).
  replace (w.(flagNodeAddr) + 18 + 1) with (w.(flagNodeAddr) + 19) by lia.
  unfold store_optional_bytes; cbn; entailer!.
Qed.

Lemma flag_block_call_node_merge : forall sg w v,
  flag_block_call_layout -> sg.(osKernelConfig) = selected_kernel_configuration ->
  w.(flagWaitImage).(flagNodePadding) = [None] ->
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlags") # UShort |-> w.(flagMask) **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeWaitType") # UChar |-> encode_flag_wait_mode w.(flagWaitMode) **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_block_call_tcb sg w **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |-> v.(flagImageHead) **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> 0 **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |-> flag_block_call_group sg w **
  flag_block_call_node_padding w |--
  flag_node_rep sg.(osKernelConfig) w.(flagNodeAddr)
    (flag_block_node_image sg w (flag_block_call_tcb sg w) v.(flagImageHead)).
Proof.
  intros sg w v [Hnext [Hprev [Htcb [Hgroup [Hmask [Hmode Hhead]]]]]] Hconfig Hpadding.
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode.
  unfold flag_node_rep, flag_block_node_image, flag_block_call_node_padding, flag_block_call_group.
  cbn [flagNodeNext flagNodePrev flagNodeTCB flagNodeGroup flagNodeMask flagNodeMode flagNodePadding].
  rewrite Hpadding, Hconfig.
  unfold flag_word_rep, flag_node_mode_offset, flag_word_bytes, selected_kernel_configuration; cbn.
  replace (w.(flagNodeAddr) + 18 + 1) with (w.(flagNodeAddr) + 19) by lia.
  entailer!.
Qed.

Definition flag_block_call_entry (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> flag_block_call_tcb sg w **
  tcb_cell (flag_block_call_tcb sg w) TCBStat (Some (flag_block_call_status t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBStatPend (Some (flag_block_call_pend t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBDly (Some (flag_block_call_delay t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBFlagNode (Some 0) **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  flag_node_uninit_rep sg.(osKernelConfig) w.(flagNodeAddr) **
  (flag_block_call_group sg w + 4) # Ptr |-> v.(flagImageHead) **
  (sg.(g_OSRdyTbl) + flag_block_call_y t * sizeof(UCHAR)) # UChar |-> flag_block_call_row s t **
  sg.(g_OSRdyGrp) # UChar |-> flag_block_call_grp s **
  flag_block_call_nodes sg s ** flag_block_call_residual sg s w t v.

Lemma flag_block_call_pre_split : forall sg s w t g v timeout,
  flag_block_call_pre sg s w t g v timeout |--
  coq_prop (flag_block_call_context sg s w t g v timeout /\ flag_block_call_ranges s t) &&
    flag_block_call_entry sg s w t v.
Proof.
  intros sg s w t g v timeout; unfold flag_block_call_pre.
  apply coq_prop_andp_left; intros Hpre.
  destruct Hpre as [Hlayout [Hconfig Hprotocol]].
  sep_apply_l_atomic (UCOS2_inv_open_task_storage_sched_flag sg s).
  Intros.
  match goal with H : UCOS2_state_inv sg s |- _ => rename H into Hvalid end.
  assert (Hcontext : flag_block_call_context sg s w t g v timeout).
  { unfold flag_block_call_context; tauto. }
  pose proof (flag_block_call_context_ranges _ _ _ _ _ _ _ Hcontext) as Hranges.
  destruct (flag_block_call_context_facts _ _ _ _ _ _ _ Hcontext)
    as [Hsg [Htasks [Hsched [Hflags Hy]]]].
  destruct Hprotocol as [Hcur [Hprio [Ht [Hready [Hnull [Hevent [Hmultiwait
    [Hgen [Hnode [Hfresh [Hg [Hgroupgen [Hv Hrest]]]]]]]]]]]]].
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hconfig; reflexivity).
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hconfig; reflexivity).
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hconfig; reflexivity).
  unfold flag_configured_rep; rewrite Henabled.
  sep_apply_l_atomic (task_public_storage_split_task sg s.(TskState) w.(flagTask) t Ht).
  rewrite used_task_rep_tcb64 by assumption.
  rewrite <- task_slot_addr_tcb64 by assumption.
  sep_apply_l_atomic (flag_block_call_tcb_split (task_slot_addr sg w.(flagTask)) (task_tcb64_image sg t)).
  unfold sched_raw_rep, flag_raw_rep, flag_nodes_rep.
  sep_apply_l_atomic (sched_rows_split_cell sg s.(TskState) s.(SchedState).(readyList)
    (flag_block_call_y t) Hy).
  sep_apply_l_atomic (flag_groups_rep_split_head sg s.(FlagState) w.(flagGroup) v Hv).
  unfold flag_block_call_entry, flag_block_call_residual, flag_block_call_nodes,
    flag_block_call_sched_rest, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link].
  cbn [task_tcb64_image]; rewrite Hnull.
  unfold flag_block_call_tcb, flag_block_call_group, flag_block_call_status,
    flag_block_call_pend, flag_block_call_delay, flag_block_call_row, flag_block_call_grp,
    flag_block_call_y, flag_block_call_bit_x, flag_block_call_bit_y.
  entailer!.
Qed.

Lemma flag_block_call_task_merge : forall sg w t timeout,
  sg.(osKernelConfig) = selected_kernel_configuration ->
  tcb_cell (flag_block_call_tcb sg w) TCBStat (Some (Z.lor (flag_block_call_status t) 32)) **
  tcb_cell (flag_block_call_tcb sg w) TCBStatPend (Some 0) **
  tcb_cell (flag_block_call_tcb sg w) TCBDly (Some timeout) **
  tcb_cell (flag_block_call_tcb sg w) TCBFlagNode (Some w.(flagNodeAddr)) **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  flag_block_call_tcb_rest (flag_block_call_tcb sg w) (task_tcb64_image sg t) |--
  used_task_rep sg w.(flagTask) (task_prepare_flag_wait t w.(flagNodeAddr) timeout).
Proof.
  intros sg w t timeout Hconfig.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false) by (rewrite Hconfig; reflexivity).
  assert (Hprofile : sg.(osKernelConfig).(cfgTaskProfile) = false) by (rewrite Hconfig; reflexivity).
  rewrite used_task_rep_tcb64 by assumption.
  rewrite <- task_slot_addr_tcb64 by assumption.
  pose proof (flag_block_call_tcb_merge (flag_block_call_tcb sg w)
    (task_tcb64_image sg (task_prepare_flag_wait t w.(flagNodeAddr) timeout))) as Hmerge.
  rewrite flag_block_call_tcb_rest_update in Hmerge.
  cbn [task_tcb64_image] in Hmerge.
  unfold task_prepare_flag_wait, task_set_flag_node in Hmerge.
  cbn [stat statPend dly tcbFlagNode curPrio] in Hmerge.
  rewrite task_prepare_event_wait_status_encoding in Hmerge.
  cbn [task_prepare_event_wait encode_pend_status encode_pend_type task_pend_mask
    statPend dly curPrio] in Hmerge.
  exact Hmerge.
Qed.

Lemma flag_block_call_written_merge : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout ->
  flag_block_call_written sg s w t v timeout |-- flag_block_call_post sg s w t timeout.
Proof.
  intros sg s w t g v timeout Hcontext.
  destruct (flag_block_call_context_facts _ _ _ _ _ _ _ Hcontext)
    as [Hsg [Htasks [Hsched [Hflags Hy]]]].
  pose proof Hcontext as [Hlayout [Hconfig [Hvalid Hprotocol]]].
  destruct Hprotocol as [Hcur [Hprio [Ht [Hready [Hnull [Hevent [Hmultiwait
    [Hgen [Hnode [Hfresh [Hg [Hgroupgen [Hv [Hmask [Hpadding Htimeout]]]]]]]]]]]]]]].
  assert (Henabled : sg.(osKernelConfig).(cfgFlagEnabled) = true) by (rewrite Hconfig; reflexivity).
  assert (Hstep_exists : exists after,
    flag_block_node sg s.(FlagState) w (flag_block_call_tcb sg w) = Some after).
  { unfold flag_block_node; rewrite Hg, Hv; eexists; reflexivity. }
  destruct Hstep_exists as [after Hstep].
  pose proof (flag_block_call_endpoint_eq _ _ _ _ _ _ _ _ Hcontext Hstep) as Hendpoint.
  pose proof (flag_block_call_blocked sg s w t g v timeout after Hcontext) as Hblocked.
  unfold flag_block_call_post; Exists after.
  unfold flag_block_call_written, flag_block_call_ready_frame, flag_block_call_residual.
  sepcon_assoc_change.
  sep_apply_l_atomic (flag_block_call_task_merge sg w t timeout Hconfig).
  sep_apply_l_atomic (task_public_storage_merge_updated_task sg s.(TskState) w.(flagTask)
    (task_prepare_flag_wait t w.(flagNodeAddr) timeout)).
  unfold flag_block_call_row_cleared, flag_block_call_row, flag_block_call_bit_x,
    flag_block_call_y, tcb_y_of_prio, tcb_bit_x_of_prio, tcb_x_of_prio.
  sep_apply_l_atomic (sched_rows_merge_removed_ready_member sg s.(TskState) s.(SchedState)
    w.(flagTask) t (task_prepare_flag_wait t w.(flagNodeAddr) timeout)
    Hsg Htasks Hsched Ht Hready Hy).
  destruct (sched_remove_ready_member_encoding sg s.(TskState) s.(SchedState)
    w.(flagTask) t (task_prepare_flag_wait t w.(flagNodeAddr) timeout)
    Hsg Htasks Hsched Ht Hready) as [Hgrp Hrows].
  assert (Hgrp_eq : flag_block_call_grp_cleared s t =
    encode_ready_grp (sched_remove_ready_task s.(SchedState) w.(flagTask)).(readyList)
      (glob_task_set_usedtask s.(TskState) w.(flagTask)
        (task_prepare_flag_wait t w.(flagNodeAddr) timeout))).
  { symmetry; exact Hgrp. }
  rewrite Hgrp_eq.
  assert (Hpadding_length : Z.of_nat (List.length w.(flagWaitImage).(flagNodePadding)) =
    flag_node_size sg.(osKernelConfig) - flag_node_mode_offset sg.(osKernelConfig) - 1).
  { rewrite Hpadding, Hconfig; reflexivity. }
  pose proof (flag_block_merge_global_resources sg s w after t timeout g v Henabled Hvalid
    Ht Hready Hnull Hevent Hmultiwait Hgen Hnode Hfresh Hg Hgroupgen Hv Hmask
    Hpadding_length Hstep) as Hfinish.
  cbn zeta in Hfinish.
  unfold sched_raw_rep, sched_physical_rep, flag_block_written_rep in Hfinish.
  cbn [flag_execution.flag_block_state replace_SchedS replace_FlagS replace_TskS
    TskState SchedState sched_remove_ready_task sched_set_ready curTaskID curSchedPrio
    highRdyTid highRdyPrio ctxSwCtr isRunning readyList] in Hfinish.
  rewrite Hcur in Hfinish; cbn [encode_task_link] in Hfinish.
  unfold flag_block_call_sched_rest, flag_block_call_old_nodes, flag_block_call_tcb,
    flag_block_call_group.
  apply _derivable1_andp_intros.
  - entailer!.
  - sep_apply_r_atomic Hfinish.
    cbn [sched_remove_ready_task sched_set_ready readyList]; entailer!.
Qed.



