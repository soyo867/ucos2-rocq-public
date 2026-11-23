Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.flag_stack.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_FlagUnlink leaves the removed node's own fields unchanged. The
    direct caller may still read Next; only after that last access may the
    returned node be combined with its original stack fragments. These
    resource cutpoints are not a context-switch or stack-provenance proof. *)

Lemma flag_unlink_returns_stack_resources : forall sg flags p w after region lower upper,
  valid_flag_state sg flags -> flag_unlink_node flags p = Some (w, after) ->
  sg.(osKernelConfig).(cfgFlagBits) = 8 \/
    sg.(osKernelConfig).(cfgFlagBits) = 16 \/ sg.(osKernelConfig).(cfgFlagBits) = 32 ->
  w.(flagNodeAddr) = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  w.(flagNodeAddr) mod 4 = 0 ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count sg.(osKernelConfig) + Zlength upper ->
  flag_groups_rep sg after ** flag_unlink_neighbors_rep sg flags w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match flags.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
    task_stack_fragments_rep region (flag_node_stack_residual_fragments sg.(osKernelConfig) region lower upper) |--
    task_stack_storage region (lower ++ flag_node_stack_words sg.(osKernelConfig) w.(flagWaitImage) ++ upper) **
    flag_raw_rep sg after.
Proof.
  intros sg flags p w after region lower upper Hvalid Hstep Hbits Haddr Halign Hsize.
  pose proof (proj1 (flag_unlink_removes_node_and_keeps_its_image _ _ _ _ Hstep)) as Hw.
  assert (Himage : flag_node_image_valid sg.(osKernelConfig) w.(flagWaitImage)).
  { destruct Hvalid as [_ [_ [_ [_ [_ Hnodes]]]]]; exact (proj1 (proj2 (Hnodes p w Hw))). }
  sep_apply_l_atomic (flag_unlink_reconstructs_raw_rep sg flags p w after Hvalid Hstep).
  sep_apply_l_atomic (flag_node_return_loan_merge_stack_fragments sg.(osKernelConfig)
    region lower upper w Hbits Haddr Halign Hsize Himage); entailer!.
Qed.

(** The post-store Task/ready representations below come from OS_FlagTaskRdy
    and OS_FlagUnlink. Restoring validity is proved from the pre-state and
    their transformer; it is not required as a post-state premise. *)
Lemma flag_wake_returns_stack_and_global_resources : forall sg s p w flags old bits result region lower upper,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> flag_unlink_node s.(FlagState) p = Some (w, flags) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  sg.(osKernelConfig).(cfgFlagBits) = 8 \/
    sg.(osKernelConfig).(cfgFlagBits) = 16 \/ sg.(osKernelConfig).(cfgFlagBits) = 32 ->
  w.(flagNodeAddr) = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  w.(flagNodeAddr) mod 4 = 0 ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count sg.(osKernelConfig) + Zlength upper ->
  let post := flag_wake_state sg s w flags old bits result in
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_groups_rep sg flags ** flag_unlink_neighbors_rep sg s.(FlagState) w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s **
    task_stack_fragments_rep region (flag_node_stack_residual_fragments sg.(osKernelConfig) region lower upper) |--
    task_stack_storage region (lower ++ flag_node_stack_words sg.(osKernelConfig) w.(flagWaitImage) ++ upper) **
    UCOS2_inv sg post.
Proof.
  intros sg s p w flags old bits result region lower upper Henabled Hvalid Hstep Hold Hbits Haddr Halign Hsize post.
  assert (Hflags : valid_flag_state sg s.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_flag_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  eapply derivable1_trans with (y :=
    (flag_groups_rep sg flags ** flag_unlink_neighbors_rep sg s.(FlagState) w **
     sg.(g_OSFlagFreeList) # Ptr |->
       (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
     task_stack_fragments_rep region (flag_node_stack_residual_fragments sg.(osKernelConfig) region lower upper)) **
    (task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
     UCOS2_raw_rep_missing_task_storage_sched_flag sg s)); [entailer!|].
  sep_apply_l_atomic (flag_unlink_returns_stack_resources sg s.(FlagState) p w flags region lower upper
    Hflags Hstep Hbits Haddr Halign Hsize).
  pose proof (UCOS2_inv_merge_flag_wake sg s p w flags old bits result Hvalid Hstep Hold) as Hmerge.
  cbn zeta in Hmerge; fold post in Hmerge.
  assert (Hflag_rep : flag_configured_rep sg post.(FlagState) = flag_raw_rep sg flags).
  { unfold post, flag_wake_state; cbn [replace_TskS replace_FlagS replace_SchedS FlagState].
    unfold flag_configured_rep; rewrite Henabled; reflexivity. }
  rewrite Hflag_rep in Hmerge; sep_apply_r_atomic Hmerge; entailer!.
Qed.

(** The selected profile has OS_TASK_DEL_EN, so OS_FlagBlock writes four
    TCB fields before publishing its stack node. Reuse the Task owner's
    byte-level status OR, PendOK and timeout update; no duplicate TCB model. *)
Definition task_prepare_flag_wait (old : TaskAbstractState) (node : addr)
  (timeout : Z) : TaskAbstractState :=
  task_set_flag_node (task_prepare_event_wait old PendFlag timeout) node.

Lemma task_prepare_flag_wait_image_eq : forall sg old node timeout,
  task_tcb64_image sg (task_prepare_flag_wait old node timeout) =
    tcb_write (tcb_prepare_wait_image (task_tcb64_image sg old)
      (task_status_set_wait (encode_task_status old.(stat)) PendFlag) timeout)
      TCBFlagNode (Some node).
Proof.
  intros; unfold task_prepare_flag_wait.
  rewrite task_set_flag_node_image_eq, task_prepare_event_wait_image_eq; reflexivity.
Qed.

Lemma flag_block_preserves_name_references : forall sg before w tcb post,
  flag_block_node sg before w tcb = Some post ->
  forall name, flag_name_reference post name -> flag_name_reference before name.
Proof.
  intros sg before w tcb post Hstep.
  unfold flag_block_node in Hstep.
  destruct (before.(flagUsed) w.(flagGroup)) as [g|] eqn:Hg;
    destruct (before.(flagImages) w.(flagGroup)) as [v|] eqn:Hv;
    try discriminate.
  inversion Hstep; subst post; clear Hstep.
  intros name [i [found [Hlookup Hname]]].
  cbv beta iota zeta delta [flagUsed] in Hlookup;
    unfold kernel_map_set in Hlookup.
  destruct (Z.eq_dec i (flagGroup w)) as [Heq|Hother].
  - subst i; injection Hlookup as Hfound; subst found.
    exists (flagGroup w), g; split; [exact Hg|].
    cbn [flag_group_set_wait_order] in Hname; exact Hname.
  - exists i, found; split; assumption.
Qed.

Definition flag_block_state (s : UCOS2_Verify_State) (w : FlagWaiterState)
  (flags : GlobFlagState) (old : TaskAbstractState) (timeout : Z) : UCOS2_Verify_State :=
  replace_SchedS (sched_remove_ready_task s.(SchedState) w.(flagTask))
    (replace_FlagS flags (replace_TskS (glob_task_set_usedtask s.(TskState) w.(flagTask)
      (task_prepare_flag_wait old w.(flagNodeAddr) timeout)) s)).

Lemma flag_block_old_node_origin : forall sg flags w tcb post p current,
  flag_block_node sg flags w tcb = Some post -> p <> w.(flagNodeAddr) ->
  post.(flagWaitNodes) p = Some current -> exists previous,
    flags.(flagWaitNodes) p = Some previous /\
    flag_waiter_link_identity current = flag_waiter_link_identity previous.
Proof.
  intros sg flags w tcb post p current Hstep Hne Hcurrent.
  pose proof (flag_block_frames_waiter_identity sg flags w tcb post p Hstep Hne) as Hidentity.
  rewrite Hcurrent in Hidentity; destruct (flags.(flagWaitNodes) p) as [previous|] eqn:Hprevious;
    [|discriminate].
  exists previous; split; [reflexivity|].
  cbn [option_map] in Hidentity; congruence.
Qed.

Lemma flag_block_preserves_task_waiter_consistency : forall sg tasks flags w post old timeout g v,
  valid_flag_state sg flags -> task_flag_waiter_consistency sg tasks flags ->
  tasks.(inUsedTaskStates) w.(flagTask) = Some old ->
  old.(tcbFlagNode) = 0 -> old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] ->
  task_non_suspension_bits old.(stat) = 0 ->
  w.(flagTaskGeneration) = old.(taskGeneration) -> w.(flagNodeAddr) <> 0 ->
  flags.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flags.(flagUsed) w.(flagGroup) = Some g -> flags.(flagImages) w.(flagGroup) = Some v ->
  flag_block_node sg flags w (task_slot_addr sg w.(flagTask)) = Some post ->
  task_flag_waiter_consistency sg
    (glob_task_set_usedtask tasks w.(flagTask) (task_prepare_flag_wait old w.(flagNodeAddr) timeout)) post.
Proof.
  intros sg tasks flags w post old timeout g v Hvalid [Hnodes Htasks]
    Hold Hflagnull Hnull Hmulti Hnone Hgeneration Hp0 Hfresh Hg Hv Hstep.
  pose proof (flag_block_installs_node sg flags w (task_slot_addr sg w.(flagTask))
    post g v Hvalid Hg Hv Hfresh Hstep) as Hnew.
  assert (Hother : forall p previous, flags.(flagWaitNodes) p = Some previous ->
    previous.(flagTask) <> w.(flagTask)).
  { intros p previous Hprevious Heq.
    destruct (Hnodes p previous Hprevious) as [Hnonzero [t [Ht [_ [Hptr _]]]]].
    rewrite Heq, Hold in Ht; injection Ht as Ht; subst t; congruence. }
  split.
  - intros p current Hcurrent; destruct (Z.eq_dec p w.(flagNodeAddr)) as [->|Hne].
    + rewrite Hnew in Hcurrent; injection Hcurrent as Hcurrent; subst current.
      split; [exact Hp0|].
      exists (task_prepare_flag_wait old w.(flagNodeAddr) timeout).
      split; [cbn [glob_task_set_usedtask inUsedTaskStates flag_waiter_set_image flagTask]; rewrite Z.eqb_refl; reflexivity|].
      split; [symmetry; exact Hgeneration|]. split; [reflexivity|]. split; [reflexivity|].
      split; [|split; assumption].
      left; apply task_prepare_event_wait_pending_bits; exact Hnone.
    + destruct (flag_block_old_node_origin sg flags w (task_slot_addr sg w.(flagTask))
        post p current Hstep Hne Hcurrent) as [previous [Hprevious Hidentity]].
      assert (Htask : current.(flagTask) = previous.(flagTask))
        by (unfold flag_waiter_link_identity in Hidentity; congruence).
      assert (Hgen : current.(flagTaskGeneration) = previous.(flagTaskGeneration))
        by (unfold flag_waiter_link_identity in Hidentity; congruence).
      assert (Htcb : current.(flagWaitImage).(flagNodeTCB) = previous.(flagWaitImage).(flagNodeTCB))
        by (unfold flag_waiter_link_identity in Hidentity; congruence).
      destruct (Hnodes p previous Hprevious) as [Hnonzero [t [Ht [Htg [Hptr [Htc [Hphase Hrest]]]]]]].
      split; [exact Hnonzero|]; exists t; split.
      * simpl; rewrite Htask, (proj2 (Z.eqb_neq _ _) (Hother p previous Hprevious)); exact Ht.
      * rewrite Htask, Hgen, Htcb; repeat (split; [assumption|]); exact Hrest.
  - intros tid t Ht Hactive; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
    destruct (Z.eqb tid w.(flagTask)) eqn:E.
    + apply Z.eqb_eq in E; subst tid; injection Ht as Ht; subst t.
      exists (flag_waiter_set_image w (flag_block_node_image sg w
        (task_slot_addr sg w.(flagTask)) v.(flagImageHead))); split; [exact Hnew|reflexivity].
    + destruct (Htasks tid t Ht Hactive) as [previous [Hprevious Htid]].
      assert (Hne : t.(tcbFlagNode) <> w.(flagNodeAddr)) by congruence.
      pose proof (flag_block_frames_waiter_identity sg flags w (task_slot_addr sg w.(flagTask))
        post t.(tcbFlagNode) Hstep Hne) as Hidentity.
      rewrite Hprevious in Hidentity.
      destruct (post.(flagWaitNodes) t.(tcbFlagNode)) as [current|] eqn:Hcurrent; [|discriminate].
      exists current; split; [reflexivity|].
      unfold flag_waiter_link_identity in Hidentity; simpl in Hidentity; congruence.
Qed.

Lemma flag_block_preserves_cross_module_consistency : forall sg s w flags old timeout g v,
  cross_module_consistency sg s -> event_in_range sg s.(TskState) s.(EventState) ->
  valid_flag_state sg s.(FlagState) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  old.(tcbFlagNode) = 0 -> old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] ->
  task_non_suspension_bits old.(stat) = 0 ->
  w.(flagTaskGeneration) = old.(taskGeneration) -> w.(flagNodeAddr) <> 0 ->
  s.(FlagState).(flagWaitNodes) w.(flagNodeAddr) = None ->
  s.(FlagState).(flagUsed) w.(flagGroup) = Some g -> s.(FlagState).(flagImages) w.(flagGroup) = Some v ->
  flag_block_node sg s.(FlagState) w (task_slot_addr sg w.(flagTask)) = Some flags ->
  cross_module_consistency sg (flag_block_state s w flags old timeout).
Proof.
  intros sg s w flags old timeout g v
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]] Hevents Hflags
    Hold Hflagnull Hnull Hmulti Hnone Hgeneration Hp0 Hfresh Hg Hv Hstep.
  assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e ->
    ~ In w.(flagTask) e.(waitList)).
  { intros eid e He Hin.
    destruct (event_waiter_task_fields sg s.(TskState) eid e w.(flagTask)
      (proj1 Hwait eid e He) Hin) as [t [kind [Ht [_ [Hptr _]]]]].
    rewrite Hold in Ht; injection Ht as Ht; subst t; congruence. }
  split.
  - eapply task_mutex_priotbl_consistency_update_task; [exact Hold|reflexivity|exact Htable].
  - split.
    + eapply mutex_owner_snapshot_update_task; eassumption.
    + split.
      * exact (event_wait_object_update_unlisted_task sg s w.(flagTask) old
          (task_prepare_flag_wait old w.(flagNodeAddr) timeout) Hold eq_refl eq_refl Habsent Hwait).
      * split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Htimer].
        eapply flag_block_preserves_task_waiter_consistency; eassumption.
Qed.

Lemma flag_block_preserves_global_validity : forall sg s w flags old timeout g,
  sg.(osKernelConfig).(cfgFlagEnabled) = true -> UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old -> In w.(flagTask) s.(SchedState).(readyList) ->
  old.(tcbFlagNode) = 0 -> old.(eventPtr) = None -> old.(eventMultiWaitEvents) = [] ->
  w.(flagTaskGeneration) = old.(taskGeneration) -> w.(flagNodeAddr) <> 0 ->
  s.(FlagState).(flagWaitNodes) w.(flagNodeAddr) = None ->
  s.(FlagState).(flagUsed) w.(flagGroup) = Some g -> w.(flagGroupGeneration) = g.(flagGeneration) ->
  flag_word_in_range sg.(osKernelConfig) w.(flagMask) ->
  Z.of_nat (List.length w.(flagWaitImage).(flagNodePadding)) =
    flag_node_size sg.(osKernelConfig) - flag_node_mode_offset sg.(osKernelConfig) - 1 ->
  flag_block_node sg s.(FlagState) w (task_slot_addr sg w.(flagTask)) = Some flags ->
  UCOS2_state_inv sg (flag_block_state s w flags old timeout).
Proof.
  intros sg s w flags old timeout g Henabled
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus [Hflags Hmodules]]]]]]]]
    Hold Hready Hflagnull Hnull Hmulti Hgeneration Hp0 Hfresh Hg Hgroupgen Hmask Hpadding Hstep.
  destruct Hmodules as
    [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]].
  unfold valid_flag_configuration in Hflags; rewrite Henabled in Hflags.
  assert (HreferencesAfter : kernel_names_valid sg (flag_block_state s w flags old timeout)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hold|reflexivity].
    - intros; assumption.
    - eapply flag_block_preserves_name_references; exact Hstep.
    - intros; assumption.
    - intros; assumption. }
  assert (Hnone : task_non_suspension_bits old.(stat) = 0).
  { destruct (proj1 (proj1 Hsched) w.(flagTask) Hready) as [found [Hfound [_ Heffective]]].
    assert (found = old) by congruence; subst found.
    apply task_effectively_ready_has_no_pending; exact Heffective. }
  assert (Habsent : forall eid e, s.(EventState).(inUsedEventStates) eid = Some e ->
    ~ In w.(flagTask) e.(waitList)).
  { destruct Hcross as [_ [_ [Hwait _]]]; intros eid e He Hin.
    destruct (event_waiter_task_fields sg s.(TskState) eid e w.(flagTask)
      (proj1 Hwait eid e He) Hin) as [t [kind [Ht [_ [Hptr _]]]]].
    rewrite Hold in Ht; injection Ht as Ht; subst t; congruence. }
  assert (HtasksAfter : task_in_range sg (flag_block_state s w flags old timeout).(TskState)).
  { eapply task_update_preserves_in_range; eauto; reflexivity. }
  assert (HschedAfter : sched_in_range sg (flag_block_state s w flags old timeout).(TskState)
    (flag_block_state s w flags old timeout).(SchedState)).
  { eapply sched_remove_ready_task_preserves_in_range;
      [exact Hsched|exact Hold|reflexivity|apply task_prepare_event_wait_not_ready]. }
  assert (HstacksAfter : parked_stacks_consistent
    (flag_block_state s w flags old timeout).(TskState) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  assert (HbitsAfter : task_reserved_bits_clear sg (flag_block_state s w flags old timeout).(TskState)).
  { apply task_reserved_bits_clear_update_task; [exact Hstatus|].
    apply task_status_set_wait_preserves_reserved_bits; [exact (Hstatus _ old Hold)|].
    left; discriminate. }
  split; [exact Hprofile|]. split; [exact HtasksAfter|]. split; [exact HschedAfter|]. split.
  - apply event_update_unlisted_task_preserves_in_range; [exact Habsent|exact Hevents].
  - split.
    + pose proof Hflags as [_ [_ [_ [Hused _]]]].
      destruct (Hused _ g Hg) as [_ [_ [_ [v [Hv _]]]]].
      eapply flag_block_preserves_cross_module_consistency;
        [exact Hcross|exact Hevents|exact Hflags|exact Hold|exact Hflagnull|exact Hnull|exact Hmulti|
         exact Hnone|exact Hgeneration|exact Hp0|exact Hfresh|exact Hg|exact Hv|exact Hstep].
    + split.
      * intro Hrunning; eapply task_update_preserves_idle_tail;
          [exact Hold|reflexivity|apply Hidle; exact Hrunning].
      * split; [exact HbitsAfter|].
        split.
        -- unfold valid_flag_configuration; rewrite Henabled.
           eapply flag_block_preserves_state_validity; eassumption.
        -- split; [exact Hmemory|].
           split; [exact Htimer|].
           split; [exact Hstats|].
           split; [exact Hcontrol|].
           split; [exact Hnames|].
           split; [exact HreferencesAfter|].
           split.
           ++ change (parked_stacks_consistent
                (flag_block_state s w flags old timeout).(TskState)
                s.(TskState).(parkedTaskStacks)).
              exact HstacksAfter.
           ++ exact Hpending.
Qed.

Lemma flag_block_global_residual_eq : forall sg s w flags old timeout,
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  UCOS2_raw_rep_missing_task_storage_sched_flag sg (flag_block_state s w flags old timeout) =
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s.
Proof.
  intros sg s w flags old timeout Hold.
  assert (Hevents : event_raw_rep sg s.(TskState) s.(EventState) =
    event_raw_rep sg (glob_task_set_usedtask s.(TskState) w.(flagTask)
      (task_prepare_flag_wait old w.(flagNodeAddr) timeout)) s.(EventState)).
  { apply event_raw_rep_change_task_index, event_wait_priority_agreement_encodes.
    eapply glob_task_set_usedtask_preserves_event_priority_agreement; [exact Hold|reflexivity]. }
  unfold UCOS2_raw_rep_missing_task_storage_sched_flag, flag_block_state; simpl.
  rewrite <- Hevents; reflexivity.
Qed.

(** The old chain after its head's Prev store, but without the new node.
    This is a transient map view of actual bytes, not another state field. *)
Definition flag_block_old_nodes (flags : GlobFlagState) (head node : addr) :=
  if Z.eqb head 0 then flags.(flagWaitNodes)
  else flag_nodes_set_prev flags.(flagWaitNodes) head node.

Lemma flag_block_fresh_node_differs_from_head : forall sg flags w g v,
  valid_flag_state sg flags -> flags.(flagUsed) w.(flagGroup) = Some g ->
  flags.(flagImages) w.(flagGroup) = Some v ->
  flags.(flagWaitNodes) w.(flagNodeAddr) = None -> v.(flagImageHead) <> 0 ->
  v.(flagImageHead) <> w.(flagNodeAddr).
Proof.
  intros sg flags w g v Hvalid Hg Hv Hfresh Hhead0 Heq.
  pose proof (flag_fresh_node_absent_from_wait_order _ _ _ _ _ Hvalid Hg Hfresh) as Hnot.
  destruct Hvalid as [_ [_ [_ [Hused _]]]].
  destruct (Hused _ g Hg) as [_ [_ [_ [image [Himage [_ [Hhead _]]]]]]].
  rewrite Hv in Himage; injection Himage as Himage; subst image.
  apply Hnot; destruct g.(flagWaitOrder) as [|p rest]; simpl in Hhead; [contradiction|].
  left; congruence.
Qed.

Lemma flag_block_old_nodes_fresh : forall sg flags w g v,
  valid_flag_state sg flags -> flags.(flagUsed) w.(flagGroup) = Some g ->
  flags.(flagImages) w.(flagGroup) = Some v ->
  flags.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_old_nodes flags v.(flagImageHead) w.(flagNodeAddr) w.(flagNodeAddr) = None.
Proof.
  intros sg flags w g v Hvalid Hg Hv Hfresh; unfold flag_block_old_nodes.
  destruct (Z.eqb v.(flagImageHead) 0) eqn:E; [exact Hfresh|].
  apply Z.eqb_neq in E.
  pose proof (flag_block_fresh_node_differs_from_head sg flags w g v Hvalid Hg Hv Hfresh E) as Hne.
  unfold flag_nodes_set_prev; rewrite kernel_map_set_other by congruence; exact Hfresh.
Qed.

Lemma flag_block_nodes_map_eq : forall sg flags w tcb post g v,
  valid_flag_state sg flags -> flags.(flagUsed) w.(flagGroup) = Some g ->
  flags.(flagImages) w.(flagGroup) = Some v ->
  flags.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg flags w tcb = Some post ->
  post.(flagWaitNodes) = kernel_map_set
    (flag_block_old_nodes flags v.(flagImageHead) w.(flagNodeAddr)) w.(flagNodeAddr)
    (Some (flag_waiter_set_image w (flag_block_node_image sg w tcb v.(flagImageHead)))).
Proof.
  intros sg flags w tcb post g v Hvalid Hg Hv Hfresh Hstep.
  unfold flag_block_node in Hstep; rewrite Hg, Hv in Hstep; injection Hstep as Hstep; subst post.
  cbn [flagWaitNodes]; unfold flag_block_old_nodes; destruct (Z.eqb v.(flagImageHead) 0) eqn:E;
    [reflexivity|].
  apply Z.eqb_neq in E.
  pose proof (flag_block_fresh_node_differs_from_head sg flags w g v Hvalid Hg Hv Hfresh E) as Hne.
  unfold flag_nodes_set_prev; rewrite kernel_map_set_other by exact Hne.
  apply functional_extensionality; intro q; unfold kernel_map_set.
  destruct (Z.eq_dec q v.(flagImageHead)), (Z.eq_dec q w.(flagNodeAddr)); congruence.
Qed.

Lemma flag_wait_nodes_rep_insert_node : forall sg nodes p w,
  nodes p = None ->
  flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) ** flag_wait_nodes_rep sg nodes |--
    flag_wait_nodes_rep sg (kernel_map_set nodes p (Some w)).
Proof.
  intros sg nodes p w Hfresh.
  eapply derivable1_trans with (y := flag_node_rep sg.(osKernelConfig) p w.(flagWaitImage) **
    flag_wait_nodes_without_node sg nodes p).
  - apply derivable1_sepcon_mono; [reflexivity|].
    apply store_map_equiv_store_map_missing; exact Hfresh.
  - apply flag_wait_nodes_rep_merge_updated_node.
Qed.

Definition flag_block_written_rep (sg : StableGlobVars) (flags : GlobFlagState)
  (w : FlagWaiterState) (tcb : addr) (v : FlagGroupImage) : Assertion :=
  (flag_pool_addr sg w.(flagGroup) + 4) # Ptr |-> w.(flagNodeAddr) **
  flag_group_rep_without_head sg.(osKernelConfig) (flag_pool_addr sg w.(flagGroup)) v **
  flag_groups_without sg flags w.(flagGroup) **
  flag_node_rep sg.(osKernelConfig) w.(flagNodeAddr) (flag_block_node_image sg w tcb v.(flagImageHead)) **
  flag_wait_nodes_rep sg (flag_block_old_nodes flags v.(flagImageHead) w.(flagNodeAddr)) **
  sg.(g_OSFlagFreeList) # Ptr |->
    (match flags.(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end).

Lemma flag_block_reconstructs_raw_rep : forall sg flags w tcb post g v,
  valid_flag_state sg flags -> flags.(flagUsed) w.(flagGroup) = Some g ->
  flags.(flagImages) w.(flagGroup) = Some v ->
  flags.(flagWaitNodes) w.(flagNodeAddr) = None ->
  flag_block_node sg flags w tcb = Some post ->
  flag_block_written_rep sg flags w tcb v |-- flag_raw_rep sg post.
Proof.
  intros sg flags w tcb post g v Hvalid Hg Hv Hfresh Hstep.
  destruct (flag_block_group_fields sg flags w tcb post g v Hstep Hg Hv) as [_ [Himages [Hfree _]]].
  pose proof (flag_block_nodes_map_eq sg flags w tcb post g v Hvalid Hg Hv Hfresh Hstep) as Hnodes.
  unfold flag_block_written_rep.
  sep_apply_l_atomic (flag_groups_rep_merge_updated_head sg flags post w.(flagGroup) v w.(flagNodeAddr) Himages).
  pose proof (flag_wait_nodes_rep_insert_node sg
    (flag_block_old_nodes flags v.(flagImageHead) w.(flagNodeAddr)) w.(flagNodeAddr)
    (flag_waiter_set_image w (flag_block_node_image sg w tcb v.(flagImageHead)))
    (flag_block_old_nodes_fresh sg flags w g v Hvalid Hg Hv Hfresh)) as Hinsert.
  cbn [flag_waiter_set_image flagWaitImage] in Hinsert.
  sep_apply_l_atomic Hinsert.
  unfold flag_raw_rep, flag_nodes_rep; rewrite Hnodes, Hfree; entailer!.
Qed.

(** Publication consumes the initialized node, old-head Prev and group-head
    stores together with the new Task/ready bytes. Only the caller's true
    stack residual may be framed around this entailment; keeping a whole
    stack would duplicate the newly published node. *)
Lemma flag_block_merge_global_resources : forall sg s w flags old timeout g v,
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
    flag_block_written_rep sg s.(FlagState) w (task_slot_addr sg w.(flagTask)) v **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s |-- UCOS2_inv sg post.
Proof.
  intros sg s w flags old timeout g v Henabled Hvalid Hold Hready Hflagnull Hnull Hmulti
    Hgeneration Hp0 Hfresh Hg Hgroupgen Hv Hmask Hpadding Hstep post.
  pose proof (flag_block_preserves_global_validity sg s w flags old timeout g Henabled Hvalid
    Hold Hready Hflagnull Hnull Hmulti Hgeneration Hp0 Hfresh Hg Hgroupgen Hmask Hpadding Hstep) as Hpost.
  assert (Hflags : valid_flag_state sg s.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_flag_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  sep_apply_l_atomic (flag_block_reconstructs_raw_rep sg s.(FlagState) w
    (task_slot_addr sg w.(flagTask)) flags g v Hflags Hg Hv Hfresh Hstep).
  assert (Hflag_rep : flag_configured_rep sg post.(FlagState) = flag_raw_rep sg flags).
  { unfold post, flag_block_state; cbn [replace_TskS replace_FlagS replace_SchedS FlagState].
    unfold flag_configured_rep; rewrite Henabled; reflexivity. }
  rewrite <- Hflag_rep.
  sep_apply_r_atomic (UCOS2_inv_merge_updated_task_storage_sched_flag sg s post Hpost
    ltac:(symmetry; apply flag_block_global_residual_eq; exact Hold)); entailer!.
Qed.

Lemma flag_timeout_returns_stack_and_global_resources : forall sg s p w flags old region lower upper,
  sg.(osKernelConfig).(cfgFlagEnabled) = true ->
  UCOS2_state_inv sg s -> flag_unlink_node s.(FlagState) p = Some (w, flags) ->
  s.(TskState).(inUsedTaskStates) w.(flagTask) = Some old ->
  task_non_suspension_bits old.(stat) = 0 ->
  sg.(osKernelConfig).(cfgFlagBits) = 8 \/
    sg.(osKernelConfig).(cfgFlagBits) = 16 \/ sg.(osKernelConfig).(cfgFlagBits) = 32 ->
  w.(flagNodeAddr) = region.(stackRegionBase) + Zlength lower * sizeof(UINT) ->
  w.(flagNodeAddr) mod 4 = 0 ->
  region.(stackRegionWords) = Zlength lower + flag_node_stack_word_count sg.(osKernelConfig) + Zlength upper ->
  let post := flag_timeout_cleanup_state s w flags old in
  task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
    flag_groups_rep sg flags ** flag_unlink_neighbors_rep sg s.(FlagState) w **
    sg.(g_OSFlagFreeList) # Ptr |->
      (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
    UCOS2_raw_rep_missing_task_storage_sched_flag sg s **
    task_stack_fragments_rep region (flag_node_stack_residual_fragments sg.(osKernelConfig) region lower upper) |--
    task_stack_storage region (lower ++ flag_node_stack_words sg.(osKernelConfig) w.(flagWaitImage) ++ upper) **
    UCOS2_inv sg post.
Proof.
  intros sg s p w flags old region lower upper Henabled Hvalid Hstep Hold Hpending Hbits Haddr Halign Hsize post.
  assert (Hflags : valid_flag_state sg s.(FlagState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_flag_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  eapply derivable1_trans with (y :=
    (flag_groups_rep sg flags ** flag_unlink_neighbors_rep sg s.(FlagState) w **
     sg.(g_OSFlagFreeList) # Ptr |->
       (match s.(FlagState).(flagFree) with [] => 0 | i :: _ => flag_pool_addr sg i end) **
     task_stack_fragments_rep region (flag_node_stack_residual_fragments sg.(osKernelConfig) region lower upper)) **
    (task_public_storage sg post.(TskState) ** sched_raw_rep sg post.(TskState) post.(SchedState) **
     UCOS2_raw_rep_missing_task_storage_sched_flag sg s)); [entailer!|].
  sep_apply_l_atomic (flag_unlink_returns_stack_resources sg s.(FlagState) p w flags region lower upper
    Hflags Hstep Hbits Haddr Halign Hsize).
  pose proof (UCOS2_inv_merge_flag_timeout_cleanup sg s p w flags old Hvalid Hstep Hold Hpending) as Hmerge.
  cbn zeta in Hmerge; fold post in Hmerge.
  assert (Hflag_rep : flag_configured_rep sg post.(FlagState) = flag_raw_rep sg flags).
  { unfold post, flag_timeout_cleanup_state; cbn [replace_TskS replace_FlagS FlagState].
    unfold flag_configured_rep; rewrite Henabled; reflexivity. }
  rewrite Hflag_rep in Hmerge; sep_apply_r_atomic Hmerge; entailer!.
Qed.
