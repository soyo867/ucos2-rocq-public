Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.task.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
Local Open Scope string_scope.

(** Initial controller seed only: the annotation owner supplies the actual
    source-faithful OS_FlagUnlink contract and its proved localization and
    update consequences. This file is not an implementation proof. The
    selected source clears OSTCBFlagNode, preserves the removed node image,
    and returns its storage without freeing it. *)

Definition flag_unlink_next (w : FlagWaiterState) : addr := w.(flagWaitImage).(flagNodeNext).
Definition flag_unlink_prev (w : FlagWaiterState) : addr := w.(flagWaitImage).(flagNodePrev).
Definition flag_unlink_group_addr (w : FlagWaiterState) : addr := w.(flagWaitImage).(flagNodeGroup).
Definition flag_unlink_tcb_addr (w : FlagWaiterState) : addr := w.(flagWaitImage).(flagNodeTCB).

(** Static interpretation of exactly the source fields this helper accesses.
    The arithmetic representations are Flag-owned; these equalities bind the
    actual alias-arrow terms emitted by the current QCP frontend. *)
Definition flag_unlink_layout : Prop :=
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeNext") = p) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodePrev") = p + 4) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") = p + 8) /\
  (forall p, &(p # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") = p + 12) /\
  (forall p, &(p # "os_flag_grp" ->ₛ "OSFlagWaitList") = p + 4).

(** A protected internal call receives genuine ownership, not another
    Outside/Inside transition.  In particular the Task may already be in a
    caller's wake/delete intermediate phase.  No status/ready condition is
    required, and the source does not change those fields. *)
Definition flag_unlink_domain (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) (t : TaskAbstractState) : Prop :=
  sg.(osKernelConfig) = selected_kernel_configuration /\
  valid_flag_state sg s /\ s.(flagWaitNodes) p = Some w /\
  w.(flagNodeAddr) = p /\
  t.(taskID) = w.(flagTask) /\ t.(taskGeneration) = w.(flagTaskGeneration) /\
  flag_unlink_tcb_addr w = task_slot_addr sg w.(flagTask) /\
  t.(tcbFlagNode) = p.

Definition flag_unlink_task_rep (sg : StableGlobVars) (w : FlagWaiterState)
  (t : TaskAbstractState) : Assertion :=
  tcb64_storage_rep (task_slot_addr sg w.(flagTask)) (task_tcb64_image sg t).

Definition flag_unlink_loan (sg : StableGlobVars) (w : FlagWaiterState) : Assertion :=
  flag_node_return_loan sg.(osKernelConfig) w.

Definition flag_unlink_after_next_store_rep (sg : StableGlobVars)
  (s post : GlobFlagState) (w : FlagWaiterState) : Assertion :=
  if Z.eqb (flag_unlink_next w) 0
  then flag_unlink_after_first_store_rep sg s post w
  else flag_unlink_loan sg w ** flag_raw_rep sg post.

Definition flag_unlink_pre (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) (t : TaskAbstractState) : Assertion :=
  coq_prop (flag_unlink_layout /\ flag_unlink_domain sg s p w t) &&
  (flag_raw_rep sg s ** flag_unlink_task_rep sg w t).

Definition flag_unlink_context (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) (t : TaskAbstractState)
  (post : GlobFlagState) : Prop :=
  flag_unlink_layout /\ flag_unlink_domain sg s p w t /\
  flag_unlink_node s p = Some (w, post).

Definition flag_unlink_post (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) (t : TaskAbstractState) : Assertion :=
  EX post, coq_prop (flag_unlink_node s p = Some (w, post) /\ valid_flag_state sg post) &&
    (flag_raw_rep sg post ** flag_node_return_loan sg.(osKernelConfig) w **
     flag_unlink_task_rep sg w (task_set_flag_node t 0)).

Definition flag_unlink_node_payload (sg : StableGlobVars) (p : addr)
  (w : FlagWaiterState) : Assertion :=
  flag_word_rep sg.(osKernelConfig) (p + 16) w.(flagWaitImage).(flagNodeMask) **
  (p + flag_node_mode_offset sg.(osKernelConfig)) # UChar |-> w.(flagWaitImage).(flagNodeMode) **
  store_optional_bytes (p + flag_node_mode_offset sg.(osKernelConfig) + 1)
    w.(flagWaitImage).(flagNodePadding).

Definition flag_unlink_read_frame (sg : StableGlobVars) (s : GlobFlagState)
  (p : addr) (w : FlagWaiterState) : Assertion :=
  flag_unlink_node_payload sg p w ** flag_nodes_without sg s p ** flag_groups_rep sg s **
  sg.(g_OSFlagFreeList) # Ptr |->
    match s.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end.

Definition flag_unlink_node_without_tcb (sg : StableGlobVars) (p : addr)
  (w : FlagWaiterState) : Assertion :=
  p # Ptr |-> flag_unlink_next w ** (p + 4) # Ptr |-> flag_unlink_prev w **
  (p + 12) # Ptr |-> flag_unlink_group_addr w ** flag_unlink_node_payload sg p w.

Definition flag_unlink_task_without_node (sg : StableGlobVars) (w : FlagWaiterState)
  (t : TaskAbstractState) : Assertion :=
  tcb64_storage_without (task_slot_addr sg w.(flagTask)) TCBFlagNode (task_tcb64_image sg t).

Definition flag_unlink_group_lookup (s : GlobFlagState) (w : FlagWaiterState)
  (v : FlagGroupImage) : Prop := s.(flagImages) w.(flagGroup) = Some v.
Definition flag_unlink_prev_lookup (s : GlobFlagState) (w previous : FlagWaiterState) : Prop :=
  s.(flagWaitNodes) (flag_unlink_prev w) = Some previous.
Definition flag_unlink_next_lookup (s : GlobFlagState) (w following : FlagWaiterState) : Prop :=
  flag_unlink_first_neighbor_nodes s.(flagWaitNodes) w (flag_unlink_next w) = Some following.

Lemma flag_unlink_domain_post_exists : forall sg s p w t,
  flag_unlink_domain sg s p w t -> exists post, flag_unlink_node s p = Some (w, post).
Proof.
  intros sg s p w t [_ [Hvalid [Hw _]]].
  eapply flag_linked_node_unlink_exists; eassumption.
Qed.

Lemma flag_unlink_read_fields_split : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  flag_raw_rep sg s |--
    &(p # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |-> flag_unlink_next w **
    &(p # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> flag_unlink_prev w **
    &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
    &(p # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |-> flag_unlink_group_addr w **
    flag_unlink_read_frame sg s p w.
Proof.
  intros sg s p w [Hnext [Hprev [Htcb [Hgroup Hhead]]]] Hw.
  rewrite Hnext, Hprev, Htcb, Hgroup.
  unfold flag_raw_rep, flag_unlink_read_frame.
  sep_apply_l_atomic (flag_nodes_split_node sg s p w Hw).
  unfold flag_node_rep, flag_unlink_node_payload, flag_unlink_next,
    flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!.
Qed.

Lemma flag_unlink_read_fields_merge : forall sg s p w,
  flag_unlink_layout -> s.(flagWaitNodes) p = Some w ->
  &(p # "os_flag_node" ->ₛ "OSFlagNodeNext") # Ptr |-> flag_unlink_next w **
  &(p # "os_flag_node" ->ₛ "OSFlagNodePrev") # Ptr |-> flag_unlink_prev w **
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
  &(p # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp") # Ptr |-> flag_unlink_group_addr w **
  flag_unlink_read_frame sg s p w |-- flag_raw_rep sg s.
Proof.
  intros sg s p w [Hnext [Hprev [Htcb [Hgroup Hhead]]]] Hw.
  rewrite Hnext, Hprev, Htcb, Hgroup.
  assert (Hfold : p # Ptr |-> flag_unlink_next w ** (p + 4) # Ptr |-> flag_unlink_prev w **
    (p + 8) # Ptr |-> flag_unlink_tcb_addr w ** (p + 12) # Ptr |-> flag_unlink_group_addr w **
    flag_unlink_node_payload sg p w |-- flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage)).
  { unfold flag_node_rep, flag_unlink_node_payload, flag_unlink_next,
      flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!. }
  unfold flag_unlink_read_frame, flag_raw_rep.
  sep_apply_l_atomic Hfold; sep_apply_l_atomic (flag_nodes_merge_node sg s p w Hw); entailer!.
Qed.

Lemma flag_unlink_loan_split_tcb : forall sg p w,
  flag_unlink_layout -> w.(flagNodeAddr) = p ->
  flag_node_return_loan sg.(osKernelConfig) w |--
    &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
    flag_unlink_node_without_tcb sg p w.
Proof.
  intros sg p w [_ [_ [Htcb _]]] Haddr; rewrite Htcb.
  unfold flag_node_return_loan; rewrite Haddr.
  unfold flag_node_rep, flag_unlink_node_without_tcb, flag_unlink_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!.
Qed.

Lemma flag_unlink_loan_merge_tcb : forall sg p w,
  flag_unlink_layout -> w.(flagNodeAddr) = p ->
  &(p # "os_flag_node" ->ₛ "OSFlagNodeTCB") # Ptr |-> flag_unlink_tcb_addr w **
    flag_unlink_node_without_tcb sg p w |-- flag_node_return_loan sg.(osKernelConfig) w.
Proof.
  intros sg p w [_ [_ [Htcb _]]] Haddr; rewrite Htcb.
  unfold flag_node_return_loan; rewrite Haddr.
  unfold flag_node_rep, flag_unlink_node_without_tcb, flag_unlink_node_payload,
    flag_unlink_next, flag_unlink_prev, flag_unlink_tcb_addr, flag_unlink_group_addr; entailer!.
Qed.

Lemma flag_unlink_task_split_node : forall sg s p w t,
  flag_unlink_domain sg s p w t ->
  flag_unlink_task_rep sg w t |--
    (tcb_field_address (flag_unlink_tcb_addr w) TCBFlagNode) # Ptr |-> p **
    flag_unlink_task_without_node sg w t.
Proof.
  intros sg s p w t [_ [_ [_ [_ [_ [_ [Htcb Hnode]]]]]]].
  rewrite Htcb; unfold flag_unlink_task_rep, flag_unlink_task_without_node.
  sep_apply_l_atomic (tcb64_storage_split (task_slot_addr sg (flagTask w))
    (task_tcb64_image sg t) TCBFlagNode).
  cbn [tcb_cell tcb_field_address task_tcb64_image]; rewrite Hnode; entailer!.
Qed.

Lemma flag_unlink_task_merge_cleared_node : forall sg w t,
  flag_unlink_tcb_addr w = task_slot_addr sg w.(flagTask) ->
  (tcb_field_address (flag_unlink_tcb_addr w) TCBFlagNode) # Ptr |-> 0 **
    flag_unlink_task_without_node sg w t |--
  flag_unlink_task_rep sg w (task_set_flag_node t 0).
Proof.
  intros sg w t Htcb; rewrite Htcb.
  unfold flag_unlink_task_rep, flag_unlink_task_without_node.
  rewrite task_set_flag_node_image_eq.
  apply (tcb64_storage_merge_updated (task_slot_addr sg (flagTask w))
    (task_tcb64_image sg t) TCBFlagNode (Some 0)).
Qed.

Lemma flag_unlink_task_non_target_field_frame : forall sg t field,
  field <> TCBFlagNode ->
  task_tcb64_image sg (task_set_flag_node t 0) field = task_tcb64_image sg t field.
Proof. intros; rewrite task_set_flag_node_image_eq; apply tcb_write_frame; assumption. Qed.

Lemma flag_unlink_after_next_store_reconstructs_raw_rep : forall sg s p w post,
  valid_flag_state sg s -> flag_unlink_node s p = Some (w, post) ->
  flag_unlink_after_next_store_rep sg s post w |--
    flag_unlink_loan sg w ** flag_raw_rep sg post.
Proof.
  intros sg s p w post Hvalid Hstep.
  unfold flag_unlink_after_next_store_rep; destruct (Z.eqb (flag_unlink_next w) 0) eqn:Hnext.
  - apply Z.eqb_eq in Hnext; unfold flag_unlink_loan.
    eapply flag_unlink_without_next_store_reconstructs_raw_rep; eassumption.
  - entailer!.
Qed.

Lemma flag_unlink_finish_post : forall sg s p w t post,
  flag_unlink_context sg s p w t post ->
  flag_raw_rep sg post ** flag_node_return_loan sg.(osKernelConfig) w **
    flag_unlink_task_rep sg w (task_set_flag_node t 0) |-- flag_unlink_post sg s p w t.
Proof.
  intros sg s p w t post [_ [[_ [Hvalid _]] Hstep]].
  pose proof (flag_unlink_preserves_state_validity sg s p w post Hvalid Hstep) as Hpost.
  unfold flag_unlink_post; Exists post; entailer!.
Qed.
