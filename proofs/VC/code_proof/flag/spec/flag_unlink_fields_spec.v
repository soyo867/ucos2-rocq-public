Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.flag Ucos2Verify.lib.flag_node_fields.
Require Import Ucos2Verify.lib.flag_fields_resources Ucos2Verify.lib.task.
Require Import Ucos2Verify.VC.code.flag.spec.flag_unlink_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Six-field companion for the actual OS_FlagUnlink stores. The original
    layout, domain, unlink transition and TCB resources are reused unchanged.
    Padding, if supplied by a caller, remains a separate frame; no predicate
    in the core contract obtains or discards those bytes. *)

Definition flag_unlink_fields_neighbors_rep (sg : StableGlobVars) (s : GlobFlagState) (w : FlagWaiterState) : Assertion :=
  flag_wait_nodes_fields_rep sg (flag_unlink_neighbor_nodes s.(flagWaitNodes) w).

Lemma flag_unlink_fields_reconstructs_raw_rep : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  flag_groups_rep sg post ** flag_unlink_fields_neighbors_rep sg s w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) |--
    flag_node_fields_return_loan sg.(osKernelConfig) w ** flag_fields_raw_rep sg post.
Proof.
  intros sg s p w post Hvalid Hstep.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as [g [pre [rest [_ [_ [Haddr _]]]]]].
  pose proof (flag_unlink_neighbor_nodes_keep_removed_node _ _ _ _ Hvalid Hw) as Hlookup.
  destruct (flag_unlink_node_map_eq _ _ _ _ Hstep) as [Hnodes Hfree].
  unfold flag_unlink_fields_neighbors_rep, flag_node_fields_return_loan, flag_fields_raw_rep.
  rewrite Hnodes, Hfree, Haddr.
  sep_apply_l_atomic (proj1 (flag_wait_nodes_fields_rep_remove_node sg (flag_unlink_neighbor_nodes (flagWaitNodes s) w) p w Hlookup)).
  unfold flag_wait_nodes_fields_rep; entailer!.
Qed.

Definition flag_unlink_fields_head_store_frame (sg : StableGlobVars) (s : GlobFlagState)
  (w : FlagWaiterState) (v : FlagGroupImage) : Assertion :=
  flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg w.(flagGroup)) v **
  flag_groups_without sg s w.(flagGroup) ** flag_wait_nodes_fields_rep sg s.(flagWaitNodes) **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_unlink_fields_prev_store_frame (sg : StableGlobVars) (s : GlobFlagState)
  (w prevw : FlagWaiterState) : Assertion :=
  flag_node_fields_rep_without_next sg.(osKernelConfig) w.(flagWaitImage).(flagNodePrev) prevw.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) **
  flag_groups_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_unlink_fields_after_first_store_rep (sg : StableGlobVars)
  (s post : GlobFlagState) (w : FlagWaiterState) : Assertion :=
  flag_groups_rep sg post **
  flag_wait_nodes_fields_rep sg (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w) **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Lemma flag_unlink_fields_split_head_store : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodePrev) = 0 ->
  exists v, s.(flagImages) w.(flagGroup) = Some v /\
    flag_fields_raw_rep sg s |--
      (w.(flagWaitImage).(flagNodeGroup) + 4) # Ptr |-> p ** flag_unlink_fields_head_store_frame sg s w v.
Proof.
  intros sg s p w Hvalid Hw Hprev0.
  destruct (flag_linked_node_head_lookup _ _ _ _ Hvalid Hw Hprev0) as [v [Hv [Hhead Hgroup]]].
  exists v; split; [exact Hv|].
  unfold flag_fields_raw_rep, flag_unlink_fields_head_store_frame.
  sep_apply_l_atomic (flag_groups_rep_split_head sg s w.(flagGroup) v Hv).
  rewrite Hhead, Hgroup; entailer!.
Qed.

Lemma flag_unlink_fields_merge_head_store : forall sg s p w post v,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodePrev) = 0 -> s.(flagImages) w.(flagGroup) = Some v ->
  (w.(flagWaitImage).(flagNodeGroup) + 4) # Ptr |-> w.(flagWaitImage).(flagNodeNext) **
    flag_unlink_fields_head_store_frame sg s w v |-- flag_unlink_fields_after_first_store_rep sg s post w.
Proof.
  intros sg s p w post v Hvalid Hstep Hprev0 Hv.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [Hg [_ [_ [_ [Hgroup _]]]]]]]].
  destruct (flag_unlink_group_fields _ _ _ _ _ _ Hstep Hg Hv) as [_ [Himages _]].
  rewrite Hprev0, Z.eqb_refl in Himages.
  unfold flag_unlink_fields_head_store_frame, flag_unlink_fields_after_first_store_rep,
    flag_unlink_first_neighbor_nodes.
  rewrite Hprev0, Z.eqb_refl, Hgroup.
  sep_apply_l_atomic (flag_groups_rep_merge_updated_head sg s post w.(flagGroup) v
    w.(flagWaitImage).(flagNodeNext) Himages); entailer!.
Qed.

Lemma flag_unlink_fields_split_prev_store : forall sg s p w,
  valid_flag_state sg s -> s.(flagWaitNodes) p = Some w ->
  w.(flagWaitImage).(flagNodePrev) <> 0 ->
  exists prevw, s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) = Some prevw /\
    flag_fields_raw_rep sg s |--
      w.(flagWaitImage).(flagNodePrev) # Ptr |-> p ** flag_unlink_fields_prev_store_frame sg s w prevw.
Proof.
  intros sg s p w Hvalid Hw Hprev0.
  destruct (flag_linked_node_prev_lookup _ _ _ _ Hvalid Hw Hprev0) as [prevw [Hprevw Hnext]].
  exists prevw; split; [exact Hprevw|].
  unfold flag_fields_raw_rep, flag_unlink_fields_prev_store_frame.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_next sg s.(flagWaitNodes)
    w.(flagWaitImage).(flagNodePrev) prevw Hprevw).
  rewrite Hnext; entailer!.
Qed.

Lemma flag_unlink_fields_merge_prev_store : forall sg s p w post prevw,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodePrev) <> 0 ->
  s.(flagWaitNodes) w.(flagWaitImage).(flagNodePrev) = Some prevw ->
  w.(flagWaitImage).(flagNodePrev) # Ptr |-> w.(flagWaitImage).(flagNodeNext) **
    flag_unlink_fields_prev_store_frame sg s w prevw |-- flag_unlink_fields_after_first_store_rep sg s post w.
Proof.
  intros sg s p w post prevw Hvalid Hstep Hprev0 Hprevw.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as [g [pre [rest [Hg _]]]].
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [_ [v [Hv _]]]]].
  destruct (flag_unlink_group_fields _ _ _ _ _ _ Hstep Hg Hv) as [_ [Himages _]].
  apply Z.eqb_neq in Hprev0; rewrite Hprev0 in Himages.
  unfold flag_unlink_fields_prev_store_frame, flag_unlink_fields_after_first_store_rep, flag_unlink_first_neighbor_nodes.
  rewrite Hprev0.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_merge_updated_next sg s.(flagWaitNodes)
    w.(flagWaitImage).(flagNodePrev) prevw w.(flagWaitImage).(flagNodeNext) Hprevw).
  unfold flag_groups_rep; rewrite Himages; entailer!.
Qed.

Definition flag_unlink_fields_next_store_frame (sg : StableGlobVars) (s post : GlobFlagState)
  (w nextw : FlagWaiterState) : Assertion :=
  flag_node_fields_rep_without_prev sg.(osKernelConfig) w.(flagWaitImage).(flagNodeNext) nextw.(flagWaitImage) **
  flag_wait_nodes_fields_without_node sg (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w)
    w.(flagWaitImage).(flagNodeNext) ** flag_groups_rep sg post **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Lemma flag_unlink_fields_split_next_store : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodeNext) <> 0 ->
  exists nextw,
    flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w w.(flagWaitImage).(flagNodeNext) = Some nextw /\
    flag_unlink_fields_after_first_store_rep sg s post w |--
      (w.(flagWaitImage).(flagNodeNext) + 4) # Ptr |-> p ** flag_unlink_fields_next_store_frame sg s post w nextw.
Proof.
  intros sg s p w post Hvalid Hstep Hnext0.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (flag_unlink_first_neighbor_next_lookup _ _ _ _ Hvalid Hw Hnext0) as [nextw [Hnextw Hprev]].
  exists nextw; split; [exact Hnextw|].
  unfold flag_unlink_fields_after_first_store_rep, flag_unlink_fields_next_store_frame.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_prev sg (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w)
    w.(flagWaitImage).(flagNodeNext) nextw Hnextw).
  rewrite Hprev; entailer!.
Qed.

Lemma flag_unlink_fields_merge_next_store : forall sg s p w post nextw,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodeNext) <> 0 ->
  flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w w.(flagWaitImage).(flagNodeNext) = Some nextw ->
  (w.(flagWaitImage).(flagNodeNext) + 4) # Ptr |-> w.(flagWaitImage).(flagNodePrev) **
    flag_unlink_fields_next_store_frame sg s post w nextw |--
    flag_node_fields_return_loan sg.(osKernelConfig) w ** flag_fields_raw_rep sg post.
Proof.
  intros sg s p w post nextw Hvalid Hstep Hnext0 Hnextw.
  unfold flag_unlink_fields_next_store_frame.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_merge_updated_prev sg
    (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w)
    w.(flagWaitImage).(flagNodeNext) nextw w.(flagWaitImage).(flagNodePrev) Hnextw).
  pose proof (flag_unlink_fields_reconstructs_raw_rep sg s p w post Hvalid Hstep) as Hclose.
  unfold flag_unlink_fields_neighbors_rep, flag_unlink_neighbor_nodes in Hclose.
  apply Z.eqb_neq in Hnext0; rewrite Hnext0 in Hclose.
  fold (flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w) in Hclose.
  sep_apply_l_atomic Hclose; entailer!.
Qed.

Lemma flag_unlink_fields_without_next_store_reconstructs_raw_rep : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  w.(flagWaitImage).(flagNodeNext) = 0 ->
  flag_unlink_fields_after_first_store_rep sg s post w |--
    flag_node_fields_return_loan sg.(osKernelConfig) w ** flag_fields_raw_rep sg post.
Proof.
  intros sg s p w post Hvalid Hstep Hnext0.
  unfold flag_unlink_fields_after_first_store_rep.
  pose proof (flag_unlink_fields_reconstructs_raw_rep sg s p w post Hvalid Hstep) as Hclose.
  unfold flag_unlink_fields_neighbors_rep, flag_unlink_neighbor_nodes in Hclose.
  rewrite Hnext0, Z.eqb_refl in Hclose.
  unfold flag_unlink_first_neighbor_nodes; rewrite Hnext0.
  sep_apply_l_atomic Hclose; entailer!.
Qed.

Definition flag_unlink_fields_loan (sg : StableGlobVars) (w : FlagWaiterState) : Assertion :=
  flag_node_fields_return_loan sg.(osKernelConfig) w.

Definition flag_unlink_fields_after_next_store_rep (sg : StableGlobVars)
  (s post : GlobFlagState) (w : FlagWaiterState) : Assertion :=
  if Z.eqb (flag_unlink_next w) 0
  then flag_unlink_fields_after_first_store_rep sg s post w
  else flag_unlink_fields_loan sg w ** flag_fields_raw_rep sg post.

Definition flag_unlink_fields_pre (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) (t : TaskAbstractState) : Assertion :=
  coq_prop (flag_unlink_layout /\ flag_unlink_domain sg s p w t) &&
  (flag_fields_raw_rep sg s ** flag_unlink_task_rep sg w t).

Definition flag_unlink_fields_post (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) (t : TaskAbstractState) : Assertion :=
  EX post, coq_prop (flag_unlink_node s p = Some (w, post) /\ valid_flag_state sg post) &&
    (flag_fields_raw_rep sg post ** flag_node_fields_return_loan sg.(osKernelConfig) w **
     flag_unlink_task_rep sg w (task_set_flag_node t 0)).

Definition flag_unlink_fields_node_payload (sg : StableGlobVars) (p : addr)
  (w : FlagWaiterState) : Assertion :=
  flag_word_rep sg.(osKernelConfig) (p + 16) w.(flagWaitImage).(flagNodeMask) **
  (p + flag_node_mode_offset sg.(osKernelConfig)) # UChar |-> w.(flagWaitImage).(flagNodeMode).

Definition flag_unlink_fields_read_frame (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) : Assertion :=
  flag_unlink_fields_node_payload sg p w ** flag_wait_nodes_fields_without_node sg s.(flagWaitNodes) p ** flag_groups_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_unlink_fields_node_without_tcb (sg : StableGlobVars) (p : addr)
  (w : FlagWaiterState) : Assertion :=
  p # Ptr |-> flag_unlink_next w ** (p + 4) # Ptr |-> flag_unlink_prev w **
  (p + 12) # Ptr |-> flag_unlink_group_addr w ** flag_unlink_fields_node_payload sg p w.

Lemma flag_unlink_fields_read_fields_split : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  flag_fields_raw_rep sg s |--
    &(p # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |-> flag_unlink_next w **
    &(p # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> flag_unlink_prev w **
    &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
    &(p # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |-> flag_unlink_group_addr w **
    flag_unlink_fields_read_frame sg s p w.
Proof.
  intros sg s p w [Hnext [Hprev [Htcb [Hgroup Hhead]]]] Hw.
  rewrite Hnext, Hprev, Htcb, Hgroup.
  unfold flag_fields_raw_rep, flag_unlink_fields_read_frame.
  sep_apply_l_atomic (flag_wait_nodes_fields_rep_split_node sg s.(flagWaitNodes) p w Hw).
  unfold flag_node_fields_rep, flag_unlink_fields_node_payload, flag_unlink_next,
    flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!.
Qed.

Lemma flag_unlink_fields_read_fields_merge : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  &(p # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |-> flag_unlink_next w **
  &(p # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> flag_unlink_prev w **
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
  &(p # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |-> flag_unlink_group_addr w **
  flag_unlink_fields_read_frame sg s p w |-- flag_fields_raw_rep sg s.
Proof.
  intros sg s p w [Hnext [Hprev [Htcb [Hgroup Hhead]]]] Hw.
  rewrite Hnext, Hprev, Htcb, Hgroup.
  assert (Hfold : p # Ptr |-> flag_unlink_next w ** (p + 4) # Ptr |-> flag_unlink_prev w **
    (p + 8) # Ptr |-> flag_unlink_tcb_addr w ** (p + 12) # Ptr |-> flag_unlink_group_addr w **
    flag_unlink_fields_node_payload sg p w |-- flag_node_fields_rep sg.(osKernelConfig) p w.(flagWaitImage)).
  { unfold flag_node_fields_rep, flag_unlink_fields_node_payload, flag_unlink_next,
      flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!. }
  unfold flag_unlink_fields_read_frame, flag_fields_raw_rep.
  sep_apply_l_atomic Hfold; sep_apply_l_atomic (flag_wait_nodes_fields_rep_merge_node sg s.(flagWaitNodes) p w Hw); entailer!.
Qed.

Lemma flag_unlink_fields_loan_split_tcb : forall sg p w,
  flag_unlink_layout -> w.(flagNodeAddr) = p ->
  flag_node_fields_return_loan sg.(osKernelConfig) w |--
    &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
    flag_unlink_fields_node_without_tcb sg p w.
Proof.
  intros sg p w [_ [_ [Htcb _]]] Haddr; rewrite Htcb.
  unfold flag_node_fields_return_loan; rewrite Haddr.
  unfold flag_node_fields_rep, flag_unlink_fields_node_without_tcb, flag_unlink_fields_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!.
Qed.

Lemma flag_unlink_fields_loan_merge_tcb : forall sg p w,
  flag_unlink_layout -> w.(flagNodeAddr) = p ->
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
    flag_unlink_fields_node_without_tcb sg p w |-- flag_node_fields_return_loan sg.(osKernelConfig) w.
Proof.
  intros sg p w [_ [_ [Htcb _]]] Haddr; rewrite Htcb.
  unfold flag_node_fields_return_loan; rewrite Haddr.
  unfold flag_node_fields_rep, flag_unlink_fields_node_without_tcb, flag_unlink_fields_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!.
Qed.

Lemma flag_unlink_fields_after_next_store_reconstructs_raw_rep : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  flag_unlink_fields_after_next_store_rep sg s post w |--
    flag_unlink_fields_loan sg w ** flag_fields_raw_rep sg post.
Proof.
  intros sg s p w post Hvalid Hstep.
  unfold flag_unlink_fields_after_next_store_rep; destruct (Z.eqb (flag_unlink_next w) 0) eqn:Hnext.
  - apply Z.eqb_eq in Hnext; unfold flag_unlink_fields_loan.
    eapply flag_unlink_fields_without_next_store_reconstructs_raw_rep; eassumption.
  - entailer!.
Qed.

Lemma flag_unlink_fields_finish_post : forall sg s p w t post,
  flag_unlink_context sg s p w t post ->
  flag_fields_raw_rep sg post ** flag_node_fields_return_loan sg.(osKernelConfig) w **
    flag_unlink_task_rep sg w (task_set_flag_node t 0) |-- flag_unlink_fields_post sg s p w t.
Proof.
  intros sg s p w t post [_ [[_ [Hvalid _]] Hstep]].
  pose proof (flag_unlink_preserves_state_validity sg s p w post Hvalid Hstep) as Hpost.
  unfold flag_unlink_fields_post; Exists post; entailer!.
Qed.

(** A full-byte caller keeps its existing padding as an explicit frame.
    These consequences never manufacture a missing padding owner. *)
Lemma flag_unlink_pre_fields_padding : forall sg s p w t,
  flag_unlink_pre sg s p w t --||--
    flag_unlink_fields_pre sg s p w t ** flag_wait_nodes_padding_rep sg s.(flagWaitNodes).
Proof.
  intros; unfold flag_unlink_pre, flag_unlink_fields_pre.
  rewrite flag_raw_rep_fields_padding; split; entailer!.
Qed.

Lemma flag_unlink_fields_padding_after : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  flag_wait_nodes_padding_rep sg s.(flagWaitNodes) --||--
    flag_node_padding_rep sg.(osKernelConfig) w.(flagNodeAddr) w.(flagWaitImage) **
    flag_wait_nodes_padding_rep sg post.(flagWaitNodes).
Proof.
  intros sg s p w post Hvalid Hstep.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  destruct (valid_flag_state_node_position _ _ _ _ Hvalid Hw) as
    [g [pre [rest [_ [_ [Haddr _]]]]]].
  pose proof (flag_unlink_neighbor_nodes_keep_removed_node _ _ _ _ Hvalid Hw) as Hlookup.
  destruct (flag_unlink_node_map_eq _ _ _ _ Hstep) as [Hnodes Hfree].
  rewrite Hnodes, Haddr.
  change (flag_wait_nodes_padding_policy_rep sg (fun _ => true) s.(flagWaitNodes) --||--
    flag_node_padding_policy_rep sg.(osKernelConfig) (fun _ => true) p w.(flagWaitImage) **
    flag_wait_nodes_padding_policy_rep sg (fun _ => true)
      (kernel_map_set (flag_unlink_neighbor_nodes s.(flagWaitNodes) w) p None)).
  rewrite <- (flag_wait_nodes_padding_policy_rep_unlink_neighbors sg (fun _ => true) s.(flagWaitNodes) w).
  apply flag_wait_nodes_padding_policy_rep_remove_node; exact Hlookup.
Qed.

Lemma flag_unlink_fields_post_padding_implies_full : forall sg s p w t,
  valid_flag_state sg s ->
  flag_unlink_fields_post sg s p w t ** flag_wait_nodes_padding_rep sg s.(flagWaitNodes) |--
    flag_unlink_post sg s p w t.
Proof.
  intros sg s p w t Hvalid.
  unfold flag_unlink_fields_post; Intros post; Intros.
  match goal with
  | H : flag_unlink_node s p = Some (w, post) /\ valid_flag_state sg post |- _ =>
      destruct H as [Hstep Hpost]
  end.
  sep_apply_l_atomic (proj1 (flag_unlink_fields_padding_after sg s p w post Hvalid Hstep)).
  sep_apply_l_atomic (proj2 (flag_raw_rep_fields_padding sg post)).
  sep_apply_l_atomic (proj2 (flag_node_return_loan_fields_padding sg.(osKernelConfig) w)).
  unfold flag_unlink_post; Exists post; entailer!.
Qed.
