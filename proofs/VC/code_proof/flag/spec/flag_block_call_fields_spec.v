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

Require Export Ucos2Verify.VC.code.flag.spec.flag_block_call_spec.
Require Export Ucos2Verify.lib.flag_node_fields.
Require Export Ucos2Verify.lib.flag_fields_resources.

Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Protected OS_FlagBlock contract for the six actual local C fields.
    Pure protocol, canonical transition, Task/Sched/group resources and validity
    are unchanged. Any actual node padding is separately owned by the caller's
    frame. This contract does not derive local addresses from a task-stack ABI. *)

Definition flag_block_call_fields_pre (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (g : FlagGroupState)
  (v : FlagGroupImage) (timeout : Z) : Assertion :=
  coq_prop (flag_block_call_layout /\ sg.(osKernelConfig) = selected_kernel_configuration /\
    flag_block_call_protocol sg s w t g v timeout) &&
  (UCOS2_fields_inv sg s ** flag_node_fields_uninit_rep sg.(osKernelConfig) w.(flagNodeAddr)).

Definition flag_block_call_fields_post (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (timeout : Z) : Assertion :=
  EX flags, coq_prop
    (flag_block_node sg s.(FlagState) w (flag_block_call_tcb sg w) = Some flags /\
     flag_block_spec.flag_block sg s w timeout =
       Some (flag_execution.flag_block_state s w flags t timeout) /\
     sched_current_blocked_before_schedule
       (flag_execution.flag_block_state s w flags t timeout).(TskState)
       (flag_execution.flag_block_state s w flags t timeout).(SchedState)
       w.(flagTask) (task_prepare_flag_wait t w.(flagNodeAddr) timeout)) &&
    UCOS2_fields_inv sg (flag_execution.flag_block_state s w flags t timeout).

Definition flag_block_call_fields_nodes (sg : StableGlobVars) (s : UCOS2_Verify_State) : Assertion :=
  flag_wait_nodes_fields_rep sg s.(FlagState).(flagWaitNodes).

Definition flag_block_call_fields_old_nodes (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (v : FlagGroupImage) : Assertion :=
  flag_wait_nodes_fields_rep sg (flag_block_old_nodes s.(FlagState) v.(flagImageHead) w.(flagNodeAddr)).

Definition flag_block_call_fields_head_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (v : FlagGroupImage) (head : FlagWaiterState) : Assertion :=
  flag_node_fields_rep_without_prev sg.(osKernelConfig) v.(flagImageHead) head.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg s.(FlagState).(flagWaitNodes) v.(flagImageHead).

Definition flag_block_call_fields_ready_frame (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) (timeout : Z) : Assertion :=
  tcb_cell (flag_block_call_tcb sg w) TCBStat
    (Some (Z.lor (flag_block_call_status t) 32)) **
  tcb_cell (flag_block_call_tcb sg w) TCBStatPend (Some 0) **
  tcb_cell (flag_block_call_tcb sg w) TCBDly (Some timeout) **
  tcb_cell (flag_block_call_tcb sg w) TCBFlagNode (Some w.(flagNodeAddr)) **
  flag_node_fields_rep sg.(osKernelConfig) w.(flagNodeAddr)
    (flag_block_node_image sg w (flag_block_call_tcb sg w) v.(flagImageHead)) **
  (flag_block_call_group sg w + 4) # Ptr |-> w.(flagNodeAddr) **
  flag_block_call_fields_old_nodes sg s w v **
  flag_block_call_residual sg s w t v.

Definition flag_block_call_fields_ready_stage (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) (timeout : Z) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> flag_block_call_tcb sg w **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  (sg.(g_OSRdyTbl) + flag_block_call_y t * sizeof(UCHAR)) # UChar |-> flag_block_call_row s t **
  sg.(g_OSRdyGrp) # UChar |-> flag_block_call_grp s **
  flag_block_call_fields_ready_frame sg s w t v timeout.

Definition flag_block_call_fields_written (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) (timeout : Z) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> flag_block_call_tcb sg w **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  (sg.(g_OSRdyTbl) + flag_block_call_y t * sizeof(UCHAR)) # UChar |-> flag_block_call_row_cleared s t **
  sg.(g_OSRdyGrp) # UChar |-> flag_block_call_grp_cleared s t **
  flag_block_call_fields_ready_frame sg s w t v timeout.

Lemma flag_block_call_fields_head_split : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout -> flag_block_call_head v <> 0 ->
  flag_block_call_fields_nodes sg s |--
  EX head, coq_prop (flag_block_call_head_lookup s v head) &&
    &(((flag_block_call_head v)) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |->_ **
    flag_block_call_fields_head_frame sg s v head.
Proof.
  intros sg s w t g v timeout Hcontext Hnonzero.
  destruct (flag_block_call_head_exists _ _ _ _ _ _ _ Hcontext Hnonzero) as [head Hhead].
  destruct Hcontext as [[_ [Hprev _]] _].
  unfold flag_block_call_fields_nodes, flag_block_call_fields_head_frame, flag_block_call_head.
  rewrite Hprev.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_prev sg s.(FlagState).(flagWaitNodes)
    v.(flagImageHead) head Hhead).
  sep_apply_l_atomic (store_ptr_undef_store_ptr
    (v.(flagImageHead) + 4) head.(flagWaitImage).(flagNodePrev)).
  Exists head; entailer!.
Qed.

Lemma flag_block_call_fields_head_merge : forall sg s w t g v timeout head,
  flag_block_call_context sg s w t g v timeout -> flag_block_call_head v <> 0 ->
  flag_block_call_head_lookup s v head ->
  &(((flag_block_call_head v)) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> w.(flagNodeAddr) **
    flag_block_call_fields_head_frame sg s v head |-- flag_block_call_fields_old_nodes sg s w v.
Proof.
  intros sg s w t g v timeout head [[_ [Hprev _]] _] Hnonzero Hhead.
  unfold flag_block_call_fields_old_nodes, flag_block_old_nodes, flag_block_call_head in *.
  rewrite (proj2 (Z.eqb_neq _ _) Hnonzero), Hprev.
  unfold flag_block_call_fields_head_frame.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_merge_updated_prev sg
    s.(FlagState).(flagWaitNodes) v.(flagImageHead) head w.(flagNodeAddr) Hhead).
  entailer!.
Qed.

Lemma flag_block_call_fields_node_split : forall sg w,
  flag_block_call_layout -> sg.(osKernelConfig) = selected_kernel_configuration ->
  flag_node_fields_uninit_rep sg.(osKernelConfig) w.(flagNodeAddr) |--
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlags") # UShort |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeWaitType") # UChar |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |->_ **
    &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |->_.
Proof.
  intros sg w [Hnext [Hprev [Htcb [Hgroup [Hmask [Hmode Hhead]]]]]] Hconfig.
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode, Hconfig.
  unfold flag_node_fields_uninit_rep.
  cbn; entailer!.
Qed.

Lemma flag_block_call_fields_node_merge : forall sg w v,
  flag_block_call_layout -> sg.(osKernelConfig) = selected_kernel_configuration ->
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlags") # UShort |-> w.(flagMask) **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeWaitType") # UChar |-> encode_flag_wait_mode w.(flagWaitMode) **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_block_call_tcb sg w **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |-> v.(flagImageHead) **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> 0 **
  &(((w.(flagNodeAddr))) # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |-> flag_block_call_group sg w |--
  flag_node_fields_rep sg.(osKernelConfig) w.(flagNodeAddr)
    (flag_block_node_image sg w (flag_block_call_tcb sg w) v.(flagImageHead)).
Proof.
  intros sg w v [Hnext [Hprev [Htcb [Hgroup [Hmask [Hmode Hhead]]]]]] Hconfig.
  rewrite Hnext, Hprev, Htcb, Hgroup, Hmask, Hmode.
  unfold flag_node_fields_rep, flag_block_node_image, flag_block_call_group.
  cbn [flagNodeNext flagNodePrev flagNodeTCB flagNodeGroup flagNodeMask flagNodeMode].
  rewrite Hconfig.
  unfold flag_word_rep, flag_node_mode_offset, flag_word_bytes, selected_kernel_configuration; cbn.
  entailer!.
Qed.

Definition flag_block_call_fields_entry (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (w : FlagWaiterState) (t : TaskAbstractState) (v : FlagGroupImage) : Assertion :=
  sg.(g_OSTCBCur) # Ptr |-> flag_block_call_tcb sg w **
  tcb_cell (flag_block_call_tcb sg w) TCBStat (Some (flag_block_call_status t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBStatPend (Some (flag_block_call_pend t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBDly (Some (flag_block_call_delay t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBFlagNode (Some 0) **
  tcb_cell (flag_block_call_tcb sg w) TCBY (Some (flag_block_call_y t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitX (Some (flag_block_call_bit_x t)) **
  tcb_cell (flag_block_call_tcb sg w) TCBBitY (Some (flag_block_call_bit_y t)) **
  flag_node_fields_uninit_rep sg.(osKernelConfig) w.(flagNodeAddr) **
  (flag_block_call_group sg w + 4) # Ptr |-> v.(flagImageHead) **
  (sg.(g_OSRdyTbl) + flag_block_call_y t * sizeof(UCHAR)) # UChar |-> flag_block_call_row s t **
  sg.(g_OSRdyGrp) # UChar |-> flag_block_call_grp s **
  flag_block_call_fields_nodes sg s ** flag_block_call_residual sg s w t v.

Lemma flag_block_call_fields_pre_split : forall sg s w t g v timeout,
  flag_block_call_fields_pre sg s w t g v timeout |--
  coq_prop (flag_block_call_context sg s w t g v timeout /\ flag_block_call_ranges s t) &&
    flag_block_call_fields_entry sg s w t v.
Proof.
  intros sg s w t g v timeout; unfold flag_block_call_fields_pre.
  apply coq_prop_andp_left; intros Hpre.
  destruct Hpre as [Hlayout [Hconfig Hprotocol]].
  sep_apply_l_atomic (proj1 (UCOS2_fields_inv_split_task_storage_sched_flag sg s)).
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
  unfold flag_fields_configured_rep; rewrite Henabled.
  sep_apply_l_atomic (task_public_storage_split_task sg s.(TskState) w.(flagTask) t Ht).
  rewrite used_task_rep_tcb64 by assumption.
  rewrite <- task_slot_addr_tcb64 by assumption.
  sep_apply_l_atomic (flag_block_call_tcb_split (task_slot_addr sg w.(flagTask)) (task_tcb64_image sg t)).
  unfold sched_raw_rep, flag_fields_raw_rep.
  sep_apply_l_atomic (sched_rows_split_cell sg s.(TskState) s.(SchedState).(readyList)
    (flag_block_call_y t) Hy).
  sep_apply_l_atomic (flag_groups_rep_split_head sg s.(FlagState) w.(flagGroup) v Hv).
  unfold flag_block_call_fields_entry, flag_block_call_residual, flag_block_call_fields_nodes,
    flag_block_call_sched_rest, sched_physical_rep.
  rewrite Hcur; cbn [encode_task_link].
  cbn [task_tcb64_image]; rewrite Hnull.
  unfold flag_block_call_tcb, flag_block_call_group, flag_block_call_status,
    flag_block_call_pend, flag_block_call_delay, flag_block_call_row, flag_block_call_grp,
    flag_block_call_y, flag_block_call_bit_x, flag_block_call_bit_y.
  entailer!.
Qed.

(** Reassemble the actual publication stores using the finite-support field map. *)
Definition flag_block_call_fields_publication_rep (sg : StableGlobVars) (flags : GlobFlagState)
  (w : FlagWaiterState) (tcb : addr) (v : FlagGroupImage) : Assertion :=
  (flag_pool_addr sg w.(flagGroup) + 4) # Ptr |-> w.(flagNodeAddr) **
  flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg w.(flagGroup)) v **
  flag_groups_without sg flags w.(flagGroup) **
  flag_node_fields_rep sg.(osKernelConfig) w.(flagNodeAddr) (flag_block_node_image sg w tcb v.(flagImageHead)) **
  flag_wait_nodes_fields_rep sg (flag_block_old_nodes flags v.(flagImageHead) w.(flagNodeAddr)) **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match flags.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end).

Lemma flag_block_call_fields_reconstructs_raw_rep : forall sg flags w tcb post g v,
  valid_flag_state sg flags -> flags.(flagUsed) w.(flagGroup) = Some g ->
  flags.(flagImages) w.(flagGroup) = Some v ->
  flags.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg flags w tcb = Some post ->
  flag_block_call_fields_publication_rep sg flags w tcb v |-- flag_fields_raw_rep sg post.
Proof.
  intros sg flags w tcb post g v Hvalid Hg Hv Hfresh Hstep.
  destruct (flag_block_group_fields sg flags w tcb post g v Hstep Hg Hv) as [_ [Himages [Hfree _]]].
  pose proof (flag_block_nodes_map_eq sg flags w tcb post g v Hvalid Hg Hv Hfresh Hstep) as Hnodes.
  unfold flag_block_call_fields_publication_rep.
  sep_apply_l_atomic (flag_groups_rep_merge_updated_head sg flags post w.(flagGroup) v w.(flagNodeAddr) Himages).
  pose proof (flag_wait_nodes_fields_rep_insert_node sg
    (flag_block_old_nodes flags v.(flagImageHead) w.(flagNodeAddr)) w.(flagNodeAddr)
    (flag_waiter_set_image w (flag_block_node_image sg w tcb v.(flagImageHead)))
    (flag_block_old_nodes_fresh sg flags w g v Hvalid Hg Hv Hfresh)) as Hinsert.
  cbn [flag_waiter_set_image flagWaitImage] in Hinsert.
  sep_apply_l_atomic Hinsert.
  unfold flag_fields_raw_rep; rewrite Hnodes, Hfree; entailer!.
Qed.

Lemma flag_block_call_fields_merge_global_resources : forall sg s w flags old timeout g v,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old -> In w.(flagTask) s.(SchedState).(readyList) ->
  old.(tcbFlagNode) = 0 -> old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] ->
  w.(flagTaskGeneration) = old.(taskGeneration) -> w.(flagNodeAddr) <> 0 ->
  s.(FlagState).(flagWaitNodes) w.(flagNodeAddr) = None ->
  s.(FlagState).(flagUsed) w.(flagGroup) = Some g -> w.(flagGroupGeneration) = g.(flagGeneration) ->
  s.(FlagState).(flagImages) w.(flagGroup) = Some v ->
  flag_word_in_range sg.(osKernelConfig) w.(flagMask) ->
  Z.of_nat (List.length w.(flagWaitImage).(flagNodePadding)) =
    flag_node_size sg.(osKernelConfig) - flag_node_mode_offset sg.(osKernelConfig) - 1 ->
  flag_block_node sg s.(FlagState) w (task_slot_addr sg w.(flagTask)) = Some flags ->
  let post := flag_block_state s w flags old timeout in
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_block_call_fields_publication_rep sg s.(FlagState) w (task_slot_addr sg w.(flagTask)) v **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |-- UCOS2_fields_inv sg post.
Proof.
  intros sg s w flags old timeout g v Henabled Hvalid Hold Hready Hflagnull Hnull Hmulti
    Hgeneration Hp0 Hfresh Hg Hgroupgen Hv Hmask Hpadding Hstep post.
  pose proof (flag_block_preserves_global_validity sg s w flags old timeout g Henabled Hvalid
    Hold Hready Hflagnull Hnull Hmulti Hgeneration Hp0 Hfresh Hg Hgroupgen Hmask Hpadding Hstep) as Hpost.
  assert (Hflags : valid_flag_state sg s.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_flag_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  sep_apply_l_atomic (flag_block_call_fields_reconstructs_raw_rep sg s.(FlagState) w
    (task_slot_addr sg w.(flagTask)) flags g v Hflags Hg Hv Hfresh Hstep).
  assert (Hflag_rep : flag_fields_configured_rep sg post.(FlagState) = flag_fields_raw_rep sg flags).
  { unfold post, flag_block_state; cbn [replace_TskS replace_FlagS replace_SchedS FlagState].
    unfold flag_fields_configured_rep; rewrite Henabled; reflexivity. }
  rewrite <- Hflag_rep.
  sep_apply_r_atomic (UCOS2_fields_inv_merge_updated_task_storage_sched_flag sg s post Hpost
    ltac:(symmetry; apply flag_block_global_residual_eq; exact Hold)); entailer!.
Qed.

Lemma flag_block_call_fields_written_merge : forall sg s w t g v timeout,
  flag_block_call_context sg s w t g v timeout ->
  flag_block_call_fields_written sg s w t v timeout |-- flag_block_call_fields_post sg s w t timeout.
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
  unfold flag_block_call_fields_post; Exists after.
  unfold flag_block_call_fields_written, flag_block_call_fields_ready_frame, flag_block_call_residual.
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
  pose proof (flag_block_call_fields_merge_global_resources sg s w after t timeout g v Henabled Hvalid
    Ht Hready Hnull Hevent Hmultiwait Hgen Hnode Hfresh Hg Hgroupgen Hv Hmask
    Hpadding_length Hstep) as Hfinish.
  cbn zeta in Hfinish.
  unfold sched_raw_rep, sched_physical_rep, flag_block_call_fields_publication_rep in Hfinish.
  cbn [flag_execution.flag_block_state replace_SchedS replace_FlagS replace_TskS
    TskState SchedState sched_remove_ready_task sched_set_ready curTaskID curSchedPrio
    highRdyTid highRdyPrio ctxSwCtr isRunning readyList] in Hfinish.
  rewrite Hcur in Hfinish; cbn [encode_task_link] in Hfinish.
  unfold flag_block_call_sched_rest, flag_block_call_fields_old_nodes, flag_block_call_tcb,
    flag_block_call_group.
  apply _derivable1_andp_intros.
  - entailer!.
  - sep_apply_r_atomic Hfinish.
    cbn [sched_remove_ready_task sched_set_ready readyList]; entailer!.
Qed.
