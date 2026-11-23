Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_inherit_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_idle_spec.
Import ListNotations SetsNotation Snaive_C_Rules UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Local Open Scope sac_scope.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.

Lemma mutex_pend_count_decode__priority_wait : forall sg entry eid event mutex,
  UCOS2_state_inv sg entry -> mutex_query_lookup entry eid event ->
  event.(eventType) = OS_EVENT_TYPE_MUTEX -> event.(mutexFields) = Some mutex ->
  0 <= mutex.(mfPCP) < 256 /\
  Z.shiftr (encode_event_cnt_value event) 8 = mutex.(mfPCP) /\
  unsigned_last_nbits (Z.shiftr (encode_event_cnt_value event) 8) 8 =
    Z.shiftr (encode_event_cnt_value event) 8.
Proof.
  intros sg entry eid event mutex Hvalid He Htype Hfields.
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
  destruct (Hprotocol eid event mutex He Htype Hfields) as [Hpcp [Hshape Hslot]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hrange : 0 <= mutex.(mfPCP) < 256).
  { unfold valid_mutex_pcp in Hpcp; rewrite Hlowest, Hdisabled in Hpcp; lia. }
  assert (Hdecode : Z.shiftr (encode_event_cnt_value event) 8 = mutex.(mfPCP)).
  { unfold encode_event_cnt_value; rewrite Htype, Hfields.
    destruct mutex.(mfOwner) as [owner|] eqn:Ho;
      destruct mutex.(mfOwnerOrigPrio) as [original|] eqn:Horig;
      simpl in Hshape |- *; try contradiction;
      rewrite Z.shiftr_div_pow2 by lia; cbn;
      rewrite Z.add_comm, Z.div_add by lia;
      rewrite Z.div_small; try lia.
    destruct Hshape as [Horig_range _].
    unfold task_priority_in_range in Horig_range; lia. }
  split; [exact Hrange|]. split; [exact Hdecode|].
  rewrite Hdecode; apply unsigned_last_nbits_eq; exact Hrange.
Qed.

Lemma mutex_pend_owner_ceiling_range__priority_wait : forall sg entry eid event mutex tid caller owner node,
  mutex_pend_owner_snapshot sg entry eid event mutex tid caller owner node ->
  Z.shiftr (encode_event_cnt_value event) 8 <> 255 ->
  0 <= Z.shiftr (encode_event_cnt_value event) 8 < 64.
Proof.
  intros * [Hwait [Hm _]] Hneq.
  destruct Hwait as [Hvalid [_ [_ [He [Htype _]]]]].
  destruct (mutex_pend_count_decode__priority_wait _ _ _ _ _ Hvalid He Htype Hm)
    as [_ [Hdecode _]]. rewrite Hdecode in *.
  destruct Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
  destruct (Hprotocol eid event mutex He Htype Hm) as [Hpcp _].
  unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile.
  assert (Hlowest : sg.(osLowestPrio) = 63) by tauto.
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255) by tauto.
  unfold valid_mutex_pcp in Hpcp; rewrite Hlowest, Hdisabled in Hpcp; lia.
Qed.

Lemma mutex_pend_priority_without_fields_eq__priority_wait : forall pointer image,
  tcb64_storage_without pointer TCBPrio image =
  tcb64_fields_rep pointer (TCBBitY :: TCBBitX :: TCBY :: TCBX :: mutex_priority_unchanged_fields) image.
Proof.
  intros; unfold tcb64_storage_without, tcb64_fields_rep, TaskFieldStorage.store_fields.
  f_equal; apply functional_extensionality; intro field.
  destruct field; simpl; repeat (destruct in_dec; simpl); reflexivity.
Qed.

Lemma mutex_pend_owner_fields_split__priority_wait : forall pointer image,
  image TCBEventPtr = Some 0 ->
  tcb64_storage_without pointer TCBPrio image |--
  mutex_pend_owner_fields_rest pointer image **
  tcb_cell pointer TCBEventPtr (Some 0) **
  tcb_cell pointer TCBX (image TCBX) **
  tcb_cell pointer TCBY (image TCBY) **
  tcb_cell pointer TCBBitX (image TCBBitX) **
  tcb_cell pointer TCBBitY (image TCBBitY).
Proof.
  intros pointer image Hptr.
  rewrite mutex_pend_priority_without_fields_eq__priority_wait.
  sep_apply_l_atomic (tcb64_fields_rep_split
    (TCBBitY :: TCBBitX :: TCBY :: TCBX :: mutex_priority_unchanged_fields) pointer image TCBBitY
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; auto)).
  cbn [remove TCBField_eq_dec].
  sep_apply_l_atomic (tcb64_fields_rep_split
    (TCBBitX :: TCBY :: TCBX :: mutex_priority_unchanged_fields) pointer image TCBBitX
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; auto)).
  cbn [remove TCBField_eq_dec].
  sep_apply_l_atomic (tcb64_fields_rep_split
    (TCBY :: TCBX :: mutex_priority_unchanged_fields) pointer image TCBY
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; auto)).
  cbn [remove TCBField_eq_dec].
  sep_apply_l_atomic (tcb64_fields_rep_split
    (TCBX :: mutex_priority_unchanged_fields) pointer image TCBX
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; auto)).
  cbn [remove TCBField_eq_dec].
  sep_apply_l_atomic (tcb64_fields_rep_split mutex_priority_unchanged_fields pointer image TCBEventPtr
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)).
  unfold mutex_pend_owner_fields_rest; rewrite Hptr; entailer!.
Qed.

Lemma mutex_pend_owner_fields_merge__priority_wait : forall pointer image priority,
  image TCBEventPtr = Some 0 ->
  mutex_pend_owner_fields_rest pointer image **
  tcb_cell pointer TCBEventPtr (Some 0) **
  tcb_cell pointer TCBPrio (Some priority) **
  tcb_cell pointer TCBX (Some (tcb_x_of_prio priority)) **
  tcb_cell pointer TCBY (Some (tcb_y_of_prio priority)) **
  tcb_cell pointer TCBBitX (Some (tcb_bit_x_of_prio priority)) **
  tcb_cell pointer TCBBitY (Some (tcb_bit_y_of_prio priority)) |--
  tcb64_storage_rep pointer (mutex_priority_image image priority).
Proof.
  intros pointer image priority Hptr.
  unfold mutex_pend_owner_fields_rest; rewrite <- Hptr.
  sep_apply_l_atomic (tcb64_fields_rep_merge mutex_priority_unchanged_fields pointer image TCBEventPtr
    ltac:(repeat constructor; simpl; intuition discriminate) ltac:(simpl; tauto)).
  fold (mutex_priority_tcb_rest pointer image).
  rewrite <- (mutex_priority_rest_updated pointer image priority).
  unfold mutex_priority_tcb_rest.
  pose proof (proj2 (TaskFieldStorage.store_fields_cons _ _ TCBField_eq_dec (tcb_cell pointer)
    mutex_priority_unchanged_fields (mutex_priority_image image priority) TCBPrio
    ltac:(repeat constructor; simpl; intuition discriminate))) as Hprio.
  change (tcb_cell pointer TCBPrio (Some (priority)) **
    tcb64_fields_rep pointer mutex_priority_unchanged_fields (mutex_priority_image image priority) |--
    tcb64_fields_rep pointer (TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority)) in Hprio.
  sep_apply_l_atomic Hprio.
  pose proof (proj2 (TaskFieldStorage.store_fields_cons _ _ TCBField_eq_dec (tcb_cell pointer)
    (TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) TCBX
    ltac:(repeat constructor; simpl; intuition discriminate))) as Hx.
  change (tcb_cell pointer TCBX (Some (tcb_x_of_prio priority)) **
    tcb64_fields_rep pointer (TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) |--
    tcb64_fields_rep pointer (TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority)) in Hx.
  sep_apply_l_atomic Hx.
  pose proof (proj2 (TaskFieldStorage.store_fields_cons _ _ TCBField_eq_dec (tcb_cell pointer)
    (TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) TCBY
    ltac:(repeat constructor; simpl; intuition discriminate))) as Hy.
  change (tcb_cell pointer TCBY (Some (tcb_y_of_prio priority)) **
    tcb64_fields_rep pointer (TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) |--
    tcb64_fields_rep pointer (TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority)) in Hy.
  sep_apply_l_atomic Hy.
  pose proof (proj2 (TaskFieldStorage.store_fields_cons _ _ TCBField_eq_dec (tcb_cell pointer)
    (TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) TCBBitX
    ltac:(repeat constructor; simpl; intuition discriminate))) as Hbitx.
  change (tcb_cell pointer TCBBitX (Some (tcb_bit_x_of_prio priority)) **
    tcb64_fields_rep pointer (TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) |--
    tcb64_fields_rep pointer (TCBBitX :: TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority)) in Hbitx.
  sep_apply_l_atomic Hbitx.
  pose proof (proj2 (TaskFieldStorage.store_fields_cons _ _ TCBField_eq_dec (tcb_cell pointer)
    (TCBBitX :: TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) TCBBitY
    mutex_priority_reordered_nodup)) as Hbity.
  change (tcb_cell pointer TCBBitY (Some (tcb_bit_y_of_prio priority)) **
    tcb64_fields_rep pointer (TCBBitX :: TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority) |--
    tcb64_fields_rep pointer (TCBBitY :: TCBBitX :: TCBY :: TCBX :: TCBPrio :: mutex_priority_unchanged_fields) (mutex_priority_image image priority)) in Hbity.
  sep_apply_l_atomic Hbity.
  rewrite mutex_priority_reordered_fields; entailer!.
Qed.

Lemma mutex_pend_task_entry_cache__priority_wait : forall idle call state,
  mutex_pend_task_entry idle call state ->
  sched_current_consistency state.(TskState) state.(SchedState).
Proof.
  intros * [_ [_ [_ [node [[Hnode [Hcurrent [Hprio _]]] _]]]]].
  unfold sched_current_consistency; rewrite Hcurrent; eauto.
Qed.

Lemma mutex_pend_disabled_inherited_snapshot__priority_wait :
  forall sg entry eid current mutex tid caller,
  mutex_pend_wait_entry sg entry eid current tid caller ->
  current.(mutexFields) = Some mutex ->
  unsigned_last_nbits (Z.shiftr (encode_event_cnt_value current) 8) 8 = 255 ->
  mutex_pend_inherited_snapshot sg entry eid current mutex tid caller entry.
Proof.
  intros * Hwait Hfields Hdisabled.
  pose proof Hwait as [Hvalid [_ [_ [He [Htype [[found [owner [Hfound [Howner _]]]] _]]]]]].
  assert (found = mutex) by congruence; subst found.
  destruct (mutex_pend_count_decode__priority_wait _ _ _ _ _ Hvalid He Htype Hfields)
    as [_ [Hdecode Hcast]].
  rewrite Hcast, Hdecode in Hdisabled.
  assert (Hceildis : sg.(osPrioMutexCeilDis) = 255).
  { destruct Hvalid as [Hprofile _].
    unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto. }
  exists owner; split; [exact Howner|]. split; [left; split; congruence|exact Hwait].
Qed.

Lemma mutex_pend_busy_observations__priority_wait :
  forall owned critical sg idle original entered mask saved before entry eid observed current m tid caller pe,
  UCOS2_state_inv sg before -> event_object_layout_prop sg eid ->
  interrupt_in_range entry.(IntrState) ->
  mutex_pend_first_snapshot owned critical sg idle original entered mask saved
    before entry eid observed current m tid caller ->
  mutex_pend_api_scope (Some owned) critical sg idle original pe before eid ->
  mutex_pend_api_prefix pe before eid ->
  Z.land (encode_event_cnt_value current) 255 <> 255 ->
  mutex_pend_wait_entry sg entry eid current tid caller /\
  mutex_pend_task_entry idle entered entry /\
  sem_pend_blocking_call_stage sg entered entry.
Proof.
  intros * Hbefore Hlayout Hintr Hfirst Hscope Hprefix Hbusy.
  destruct Hfirst as [Hhistory [Hsaved [Hrely [Hacquire [Hsource [Hnonidle
    [Huse [Hslot [Hexcluded [Hsnapshot Hcurrent]]]]]]]]]].
  pose proof Hacquire as [_ [Hvalid _]].
  pose proof Hsnapshot as [He [Htype [Hm _]]].
  pose proof Hcurrent as [Hcur [Hcaller Hrange]].
  assert (Howner : m.(mfOwner) <> None).
  { intro Hnone.
    pose proof Hvalid as [_ [_ [_ [_ [Hcross _]]]]].
    destruct Hcross as [_ [_ [_ [Hprotocol _]]]].
    destruct (Hprotocol eid current m He Htype Hm) as [_ [Hshape _]].
    unfold mutex_fields_consistency in Hshape; rewrite Hnone in Hshape.
    destruct m.(mfOwnerOrigPrio) as [orig|] eqn:Horig; [contradiction|].
    apply Hbusy; unfold encode_event_cnt_value; rewrite Htype, Hm, Hnone, Horig.
    apply mutex_accept_low_byte; lia. }
  destruct (Hscope Hprefix) as [Hu [Hs [Hi [Hop [Hip [Hclients [Hproject Hwait]]]]]]].
  destruct (Hwait owned eq_refl entered entry current m Hhistory He Htype Hm Howner)
    as [Hentry_before [Hruntime [Havailable Hholds]]].
  destruct Hentry_before as [Hsource_before [Hrunning_before [Hnonidle_before
    [old [Hready_before [Hg_before [Hptr_before [Hmulti_before Hflag_before]]]]]]]].
  destruct (mutex_pend_modular_history_preserves_ready_entry owned critical sg
    original entered before entry old Hclients Hbefore Hsource_before Hrunning_before
    Hready_before ltac:(repeat split; assumption) Hhistory Hrely)
    as [Hsource_after [Hrunning [node [Hready [Hg Hfields]]]]].
  pose proof (proj1 (proj2 Hready)) as Hcur_after.
  assert (Htid : tid = entered.(os_sched_call_stack).(stackLeaseSlot)) by congruence.
  assert (Hnode : node = caller).
  { pose proof (proj1 Hready); rewrite <- Htid in H; congruence. }
  subst node.
  assert (Hentry : mutex_pend_task_entry idle entered entry).
  { split; [exact Hsource_after|]. split; [exact Hrunning|].
    split; [exact Hnonidle|]. exists caller; tauto. }
  pose proof (mutex_pend_task_entry_sem_stage sg idle entered entry Hvalid Hslot Hentry)
    as [_ [_ [stage_node [Hready_node [Hgen_node [Hprio Hrest]]]]]].
  assert (stage_node = caller) by (pose proof (proj1 Hready_node); pose proof (proj1 Hready); congruence).
  subst stage_node.
  assert (Hwait_entry : mutex_pend_wait_entry sg entry eid current tid caller).
  { split; [exact Hvalid|]. split; [exact Hcur|]. split; [exact Hcaller|].
    split; [exact He|]. split; [exact Htype|]. split.
    - destruct m.(mfOwner) as [owner|] eqn:Ho; [|contradiction].
      exists m, owner; split; [exact Hm|]. split; [exact Ho|].
      intro E; subst owner; apply (Hholds eid current m He Htype Hm).
      rewrite <- Htid; exact Ho.
    - rewrite Htid; unfold sem_pend_task_unregistered in Hfields.
      destruct Hready as [_ [_ [_ [Hmember _]]]]. tauto. }
  split; [exact Hwait_entry|]. split; [exact Hentry|].
  destruct Hhistory as [Htrace Hnormal].
  destruct Hrely as [[Hr Hints] [Hruntime_rely Hrest_rely]].
  split; [exact (Hruntime_rely Hruntime Hrunning)|].
  split; [exact (proj2 Hnormal Havailable)|].
  pose proof (proj1 (mutex_pend_precritical_continues_iff _ _ _ _) Hprefix)
    as [_ [_ [Hint Hlock]]].
  unfold interrupt_in_range in Hintr; rewrite Hints in *; lia.
Qed.

Lemma mutex_pend_tcb_not_reserved__priority_wait : forall sg entry owner node,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  kernel_tcb_stack_field_layout sg ->
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) |--
  coq_prop (task_slot_addr sg owner <> 1) &&
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node).
Proof.
  intros sg entry owner node [Hprofile [Htasks Hrest]] Hnode Hlayout.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hslot : task_slot_in_range sg owner).
  { apply (proj2 (proj1 (proj1 Htasks) owner)); left; exists node; exact Hnode. }
  assert (Hstorage : used_task_rep sg owner node --||--
    tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node)).
  { rewrite used_task_rep_tcb64, <- task_slot_addr_tcb64 by assumption; reflexivity. }
  rewrite <- Hstorage; apply mutex_del_task_storage_pointer_not_reserved; apply Hlayout; exact Hslot.
Qed.

Lemma mutex_pend_inherited_observations__priority_wait :
  forall owned critical sg idle original entered mask saved before entry eid observed current m tid caller
    owner node base inherited,
  mutex_pend_first_snapshot owned critical sg idle original entered mask saved
    before entry eid observed current m tid caller ->
  mutex_pend_owner_snapshot sg entry eid current m tid caller owner node ->
  mutex_pend_task_entry idle entered entry -> sem_pend_blocking_call_stage sg entered entry ->
  task_base_priority sg entry.(TskState).(prioTbl) owner base ->
  m.(mfPCP) <> sg.(osPrioMutexCeilDis) ->
  mutex_pend_inherit_step sg entry owner node base caller.(curPrio) m.(mfPCP) inherited ->
  mutex_pend_inherited_snapshot sg entry eid current m tid caller inherited /\
  kernel_call_task_source entered inherited /\
  sched_current_consistency inherited.(TskState) inherited.(SchedState) /\
  sem_pend_blocking_call_stage sg entered inherited.
Proof.
  intros * Hfirst Howner Hentry Hstage Hbase Henabled Hstep.
  pose proof Hfirst as [_ [_ [_ [_ [Hsource [_ [Huse [Hslot [Hexcluded _]]]]]]]]].
  pose proof Howner as [Hwait [Hm [Ho [Hnode [Hneq [Hptr [Hnotidle _]]]]]]].
  pose proof Hwait as [Hvalid [Hcur [Hcaller [He [Htype [Howners Hrest]]]]]].
  pose proof (mutex_pend_inherit_observations sg entry eid current m owner node base caller.(curPrio)
    inherited Hvalid Huse He Htype Hm Ho Hnode Hstep) as [Hevents [Hcurrent [Hnodes Hready]]].
  assert (Hvalid_after : UCOS2_state_inv sg inherited).
  { eapply mutex_pend_inherit_preserves_validity; eassumption. }
  assert (Hwait_after : mutex_pend_wait_entry sg inherited eid current tid caller).
  { unfold mutex_pend_wait_entry, mutex_query_lookup; split; [exact Hvalid_after|].
    rewrite Hcurrent, (Hnodes tid ltac:(congruence)), Hevents.
    split; [exact Hcur|]. split; [exact Hcaller|]. split; [exact He|].
    split; [exact Htype|]. split; [exact Howners|].
    destruct Hrest as [Hprio [Hevent [Hmulti [Hflag [Hmember Hlayout]]]]].
    split; [exact Hprio|]. split; [exact Hevent|]. split; [exact Hmulti|].
    split; [exact Hflag|]. split; [apply (proj2 (Hready tid)); exact Hmember|exact Hlayout]. }
  split.
  - exists owner; split; [exact Ho|]. split; [right; split; [exact Henabled|]|exact Hwait_after].
    exists node, base; auto.
  - pose proof Hentry as [_ [Hrunning _]].
    pose proof (mutex_pend_task_entry_cache__priority_wait _ _ _ Hentry) as Hcache.
    pose proof (proj1 (kernel_call_task_source_current_at _ _ Hsource)) as Htid.
    assert (Hother : entered.(os_sched_call_stack).(stackLeaseSlot) <> owner) by congruence.
    exact (mutex_pend_inherit_preserves_call_stage sg entered entry idle eid current m owner node base
      caller.(curPrio) inherited Hvalid Hslot Hexcluded Huse He Htype Hm Ho Hnode Hrunning Hother
      Hsource Hcache Hstage Hstep).
Qed.

Lemma mutex_pend_masked_frame_inherit__priority_wait :
  forall owned critical saved_local sg entered saved acquired entry owner node base waiter ceiling inherited,
  entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_inherit_step sg entry owner node base waiter ceiling inherited ->
  mutex_pend_masked_frame owned critical saved_local sg entered saved acquired entry |--
  mutex_pend_masked_frame owned critical saved_local sg entered saved acquired inherited.
Proof.
  intros * Hnode Hstep.
  pose proof (mutex_pend_inherit_coverage_iff sg entry owner node base waiter ceiling inherited
    (task_stack_call_active_key entered) Hnode Hstep) as Hcoverage.
  unfold mutex_pend_masked_frame.
  rewrite (mutex_pend_inherit_continuation_capsules_equiv owned saved_local sg entry owner node
    base waiter ceiling inherited Hnode Hstep).
  entailer!; tauto.
Qed.

Lemma mutex_pend_priority_input_merge__priority_wait : forall sg entry owner node,
  UCOS2_state_inv sg entry -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  mutex_pend_priority_input sg entry owner node ** mutex_del_priority_frame sg entry owner |--
  UCOS2_inv sg entry.
Proof.
  intros sg entry owner node Hvalid Hnode.
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (used_task_rep_tcb64 sg owner node Hmulti Hprofiling) as Htcb.
  rewrite <- task_slot_addr_tcb64 in Htcb by assumption.
  unfold mutex_pend_priority_input, mutex_del_priority_frame; rewrite <- Htcb.
  Intros.
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner node entry.(TskState).(inUsedTaskStates) Hnode).
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv.
  unfold UCOS2_raw_rep_missing_priority_table, task_public_storage_without_prio_tbl,
    store_used_task_map, sched_raw_rep, sched_physical_rep, store_prio_tbl, mutex_del_priority_values.
  rewrite sched_rows_array_equiv; entailer!.
Qed.

Lemma mutex_pend_owner_observations__priority_wait :
  forall owned critical sg idle original entered mask saved before entry eid observed current m tid caller,
  mutex_pend_first_snapshot owned critical sg idle original entered mask saved
    before entry eid observed current m tid caller ->
  mutex_pend_wait_entry sg entry eid current tid caller ->
  exists owner node, mutex_pend_owner_snapshot sg entry eid current m tid caller owner node /\
    encode_event_ptr_value sg current = task_slot_addr sg owner.
Proof.
  intros * Hfirst Hwait.
  pose proof Hfirst as [_ [_ [_ [_ [_ [_ [Huse [Hslot [Hexcluded [Hsnapshot _]]]]]]]]]].
  pose proof Hsnapshot as [He [Htype [Hm _]]].
  pose proof Hwait as [Hvalid [_ [_ [_ [_ [[m' [owner [Hm' [Ho Hneq]]]] _]]]]]].
  assert (m' = m) by congruence; subst m'.
  pose proof Hvalid as [_ [_ [_ [_ [[_ [Howners _]] _]]]]].
  destruct (Howners eid current m owner He Htype Hm Ho) as [node [base [orig [Hnode Hrest]]]].
  exists owner, node; split.
  - split; [exact Hwait|]. split; [exact Hm|]. split; [exact Ho|].
    split; [exact Hnode|]. split; [exact Hneq|].
    split; [exact (proj1 (Huse eid current m owner node He Htype Hm Ho Hnode))|].
    split; [|exact Huse].
    eapply mutex_owner_non_idle_priority_when_running; eassumption.
  - unfold encode_event_ptr_value; rewrite Htype, Hm, Ho; reflexivity.
Qed.

Lemma mutex_pend_owner_base_result__priority_wait :
  forall sg entry eid current m tid caller owner node result,
  mutex_pend_owner_snapshot sg entry eid current m tid caller owner node ->
  task_slot_addr sg owner <> 1 ->
  mutex_base_priority_result (mutex_del_priority_values sg entry.(TskState).(prioTbl))
    (task_slot_addr sg owner) node.(curPrio) result ->
  task_base_priority sg entry.(TskState).(prioTbl) owner result.
Proof.
  intros * [Hwait [Hm [Ho [Hnode Hrest]]]] Hnotreserved Hscan.
  destruct Hwait as [Hvalid [_ [_ [He [Htype _]]]]].
  pose proof Hvalid as [Hprofile [_ [_ [_ [[_ [Howners _]] _]]]]].
  destruct (Howners eid current m owner He Htype Hm Ho) as [found [base [orig [_ [Hbase _]]]]].
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
  assert (Hnonzero : task_slot_addr sg owner <> 0)
    by (eapply mutex_del_live_task_pointer_nonzero; eassumption).
  eapply mutex_base_priority_result_implies_task_base_priority;
    [exact Hlowest| |exact (proj1 Hbase)|exact Hscan].
  intros p Hp; apply mutex_del_table_task_encoding; assumption.
Qed.

Lemma mutex_pend_priority_table_frame_merge__priority_wait : forall sg entry owner node values,
  selected_kernel_profile sg -> entry.(TskState).(inUsedTaskStates) owner = Some node ->
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 values **
  UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio) **
  mutex_del_priority_frame sg entry owner |--
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 values ** UCOS2_raw_rep_missing_priority_table sg entry.
Proof.
  intros sg entry owner node values Hprofile Hnode.
  assert (Hmulti : sg.(osKernelConfig).(cfgEventMultiEnabled) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  assert (Hprofiling : sg.(osKernelConfig).(cfgTaskProfile) = false)
    by (unfold selected_kernel_profile, tcb64_configuration in Hprofile; tauto).
  pose proof (used_task_rep_tcb64 sg owner node Hmulti Hprofiling) as Htcb.
  rewrite <- task_slot_addr_tcb64 in Htcb by assumption.
  unfold mutex_del_priority_frame; rewrite <- Htcb; Intros.
  sep_apply_l_atomic (store_map_merge (used_task_rep sg) owner node entry.(TskState).(inUsedTaskStates) Hnode).
  unfold UCOS2_raw_rep_missing_priority_table, task_public_storage_without_prio_tbl,
    store_used_task_map, sched_raw_rep, sched_physical_rep.
  rewrite sched_rows_array_equiv; entailer!.
Qed.

Lemma mutex_pend_record_array_merge__priority_wait :
  forall sg entry eid current m tid caller owner node base,
  mutex_pend_owner_snapshot sg entry eid current m tid caller owner node ->
  task_base_priority sg entry.(TskState).(prioTbl) owner base ->
  m.(mfPCP) <> sg.(osPrioMutexCeilDis) -> node.(curPrio) <= m.(mfPCP) -> m.(mfPCP) < base ->
  tcb64_storage_rep (task_slot_addr sg owner) (task_tcb64_image sg node) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64
    (replace_Znth m.(mfPCP) (task_slot_addr sg owner) (mutex_del_priority_values sg entry.(TskState).(prioTbl))) **
  UCharArray.full sg.(g_OSRdyTbl) 8 (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) **
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte entry.(SchedState).(curSchedPrio) **
  mutex_del_priority_frame sg entry owner |--
  UCOS2_inv sg (replace_TskS
    (mutex_pend_demand_tasks entry.(TskState) owner node RecordMutexDemand m.(mfPCP)) entry).
Proof.
  intros * Howner Hbase Henabled Hcurrent Hless.
  pose proof Howner as [Hwait [Hm [Ho [Hnode Hrest]]]].
  pose proof Hwait as [Hvalid [_ [_ [He [Htype Hwait_rest]]]]].
  pose proof (mutex_pend_record_preserves_validity sg entry eid current m owner node base
    Hvalid He Htype Hm Ho Henabled Hnode Hbase Hcurrent Hless) as Hpost.
  pose proof (mutex_pend_count_decode__priority_wait sg entry eid current m Hvalid He Htype Hm)
    as [_ [Hdecode Hcast]].
  assert (Hrange : 0 <= m.(mfPCP) < 64).
  { rewrite <- Hdecode; eapply mutex_pend_owner_ceiling_range__priority_wait; [exact Howner|].
    rewrite Hdecode. pose proof (proj1 Hvalid) as Hprofile.
    assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
      by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto).
    congruence. }
  sep_apply_l_atomic (mutex_pend_priority_table_frame_merge__priority_wait sg entry owner node
    (replace_Znth m.(mfPCP) (task_slot_addr sg owner) (mutex_del_priority_values sg entry.(TskState).(prioTbl)))
    (proj1 Hvalid) Hnode).
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv.
  rewrite <- mutex_pend_record_priority_residual_eq.
  unfold store_prio_tbl; cbn [replace_TskS TskState mutex_pend_demand_tasks prioTbl mutex_demand_table].
  rewrite mutex_pend_priority_values_write by exact Hrange.
  unfold mutex_del_priority_values; entailer!.
Qed.

Lemma mutex_pend_priority_coordinates__priority_wait : forall priority,
  0 <= priority < 64 ->
  0 <= tcb_y_of_prio priority < 8 /\
  0 <= tcb_bit_x_of_prio priority < 256 /\
  0 <= tcb_bit_y_of_prio priority < 256 /\
  unsigned_last_nbits (Z.shiftr priority 3) 8 = tcb_y_of_prio priority /\
  unsigned_last_nbits (Z.shiftl 1 (Z.land priority 7)) 8 = tcb_bit_x_of_prio priority /\
  unsigned_last_nbits (Z.shiftl 1 (unsigned_last_nbits (Z.shiftr priority 3) 8)) 8 =
    tcb_bit_y_of_prio priority.
Proof.
  intros priority Hrange.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding priority Hrange)
    as [Hx [Hy [Hland Hshift]]].
  assert (Hcast : unsigned_last_nbits (Z.shiftr priority 3) 8 = tcb_y_of_prio priority).
  { rewrite Z.shiftr_div_pow2 by lia; change (unsigned_last_nbits (priority / 8) 8 = priority / 8).
    apply unsigned_last_nbits_eq; unfold tcb_y_of_prio in Hy; lia. }
  pose proof (single_bit_in_byte_range__ready_bitmap_stages _ Hx) as Hbitx.
  pose proof (single_bit_in_byte_range__ready_bitmap_stages _ Hy) as Hbity.
  split; [exact Hy|]. split; [exact Hbitx|]. split; [exact Hbity|]. split; [exact Hcast|].
  split.
  - rewrite Hland; apply shift_one_unsigned_byte_eq__priority_encoding; exact Hx.
  - rewrite Hcast; apply shift_one_unsigned_byte_eq__priority_encoding; exact Hy.
Qed.

Lemma mutex_pend_ready_bitmap_ranges__priority_wait : forall sg entry,
  UCOS2_state_inv sg entry ->
  Zlength (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) = 8 /\
  (forall y, 0 <= y < 8 ->
    0 <= Znth y (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) 0 < 256) /\
  0 <= encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) < 256.
Proof.
  intros sg entry Hvalid.
  split; [reflexivity|].
  split.
  - intros y Hy; rewrite sched_row_values_Znth by exact Hy.
    apply encode_ready_tbl_or_in_range.
  - apply encode_ready_grp_in_range; intros tid node Hin Hnode.
    pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hnode) as Hprio.
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia.
Qed.

Lemma mutex_pend_replaced_row_range__priority_wait : forall rows old_y old_bitx y,
  Zlength rows = 8 -> 0 <= old_y < 8 ->
  (forall index, 0 <= index < 8 -> 0 <= Znth index rows 0 < 256) -> 0 <= y < 8 ->
  0 <= Znth y (replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bitx) rows) 0 < 256.
Proof.
  intros rows old_y old_bitx y Hlen Hold Hrows Hy.
  destruct (Z.eq_dec old_y y) as [->|Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    apply mutex_priority_cleared_row_in_range__ready_bitmap_stages, Hrows; exact Hy.
  - rewrite Znth_replace_Znth_Diff by lia; apply Hrows; exact Hy.
Qed.

Ltac mutex_pend_no_change__priority_wait sg entry eid current m tid caller owner node base owned entered :=
  let Howner := fresh "Howner" in
  let Hwait := fresh "Hwait" in
  let Hm := fresh "Hm" in
  let Ho := fresh "Ho" in
  let Hnode := fresh "Hnode" in
  let Hneq := fresh "Hneq" in
  let Howner_rest := fresh "Howner_rest" in
  let Hvalid := fresh "Hvalid" in
  let Hcur := fresh "Hcur" in
  let Hcaller := fresh "Hcaller" in
  let He := fresh "He" in
  let Htype := fresh "Htype" in
  let Hwait_rest := fresh "Hwait_rest" in
  let Hpcpbytes := fresh "Hpcpbytes" in
  let Hdecode := fresh "Hdecode" in
  let Hcast := fresh "Hcast" in
  let Hdisabled := fresh "Hdisabled" in
  let Hprofile := fresh "Hprofile" in
  let Henabled := fresh "Henabled" in
  let Haction := fresh "Haction" in
  let Hstep := fresh "Hstep" in
  let Hinherit := fresh "Hinherit" in
  let Hsource := fresh "Hsource" in
  let Hcache := fresh "Hcache" in
  let Haddresses := fresh "Haddresses" in
  let Hi := fresh "Hi" in
  let Hl := fresh "Hl" in
  let Hhigh := fresh "Hhigh" in
  let Hcurrent := fresh "Hcurrent" in
  let Hhightcb := fresh "Hhightcb" in
  let Htable := fresh "Htable" in
  let Hctr := fresh "Hctr" in
  let Hunmap := fresh "Hunmap" in
  let Hgrp := fresh "Hgrp" in
  let Hrows := fresh "Hrows" in
  let Hhigh2 := fresh "Hhigh2" in
  match goal with H : mutex_pend_owner_snapshot sg entry eid current m tid caller owner node |- _ =>
    pose proof H as Howner end;
  pose proof Howner as [Hwait [Hm [Ho [Hnode [Hneq Howner_rest]]]]];
  pose proof Hwait as [Hvalid [Hcur [Hcaller [He [Htype Hwait_rest]]]]];
  destruct (mutex_pend_count_decode__priority_wait sg entry eid current m Hvalid He Htype Hm)
    as [Hpcpbytes [Hdecode Hcast]];
  repeat rewrite Hcast in *; repeat rewrite Hdecode in *;
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
    by (pose proof (proj1 Hvalid) as Hprofile;
      unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto);
  assert (Henabled : m.(mfPCP) <> sg.(osPrioMutexCeilDis)) by lia;
  assert (Haction : mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio)
    caller.(curPrio) m.(mfPCP) = NoMutexDemand)
    by (apply mutex_pend_inherit_none_iff; lia);
  assert (Hstep : mutex_pend_inherit_step sg entry owner node base caller.(curPrio) m.(mfPCP) entry)
    by (unfold mutex_pend_inherit_step; rewrite Haction; reflexivity);
  assert (Hinherit : mutex_pend_inherited_snapshot sg entry eid current m tid caller entry)
    by (exists owner; split; [exact Ho|]; split; [right; split; [exact Henabled|]|exact Hwait];
      exists node, base; split; [exact Hnode|]; split; [assumption|exact Hstep]);
  assert (Hsource : kernel_call_task_source entered entry)
    by (match goal with H : mutex_pend_first_snapshot _ _ _ _ _ entered _ _ _ entry _ _ _ _ _ _ |- _ =>
      unfold mutex_pend_first_snapshot in H; tauto end);
  assert (Hcache : sched_current_consistency entry.(TskState) entry.(SchedState))
    by (eapply mutex_pend_task_entry_cache__priority_wait; eassumption);
  match goal with H : os_sched_global_addresses sg _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses;
    unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses;
    destruct Haddresses as [Hi [Hl [Hhigh [Hcurrent [Hhightcb [Htable [Hctr [Hunmap [Hgrp [Hrows Hhigh2]]]]]]]]]] end;
  rewrite Htable, Hrows, Hgrp, Hcurrent;
  match goal with H : ?p = sg.(g_OSTCBCur) |- _ => rewrite H end;
  let Hmerge := fresh "Hmerge" in
  pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hmerge;
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Hmerge; sep_apply_l_atomic Hmerge;
  let Hcaller_merge := fresh "Hcaller_merge" in
  pose proof (mutex_del_priority_frame_merge_caller_prio sg entry owner tid caller
    (proj1 Hvalid) ltac:(congruence) Hcaller) as Hcaller_merge;
  cbn [tcb_field_address] in Hcaller_merge; sep_apply_l_atomic Hcaller_merge;
  let Hfull := fresh "Hfull" in
  pose proof (mutex_pend_priority_input_merge__priority_wait sg entry owner node Hvalid Hnode) as Hfull;
  unfold mutex_pend_priority_input in Hfull; rewrite Hcur in Hfull; cbn [encode_task_link] in Hfull;
  sep_apply_l_atomic Hfull;
  Exists entry entered entry current m tid caller owned; entailer!;
    try (unfold os_sched_global_addresses, sched_new_global_addresses; tauto).


Ltac mutex_pend_promote__priority_wait sg entry eid current m tid caller owner node base owned entered
  critical saved_local saved wasready cleared :=
  let Howner := fresh "Howner" in
  let Hwait := fresh "Hwait" in
  let Hm := fresh "Hm" in
  let Ho := fresh "Ho" in
  let Hnode := fresh "Hnode" in
  let Hneq := fresh "Hneq" in
  let Hptr := fresh "Hptr" in
  let Hnotidle := fresh "Hnotidle" in
  let Huse := fresh "Huse" in
  let Hvalid := fresh "Hvalid" in
  let Hcur := fresh "Hcur" in
  let Hcaller := fresh "Hcaller" in
  let He := fresh "He" in
  let Htype := fresh "Htype" in
  let Hwait_rest := fresh "Hwait_rest" in
  let Hfirst := fresh "Hfirst" in
  let Hentry := fresh "Hentry" in
  let Hstage := fresh "Hstage" in
  let Hbase := fresh "Hbase" in
  let Hpcpbytes := fresh "Hpcpbytes" in
  let Hdecode := fresh "Hdecode" in
  let Hcast := fresh "Hcast" in
  let Hdisabled := fresh "Hdisabled" in
  let Hprofile := fresh "Hprofile" in
  let Henabled := fresh "Henabled" in
  let Hpcp := fresh "Hpcp" in
  let Hnodeprio := fresh "Hnodeprio" in
  let Haddresses := fresh "Haddresses" in
  let Hi := fresh "Hi" in
  let Hl := fresh "Hl" in
  let Hhigh := fresh "Hhigh" in
  let Hcurrent := fresh "Hcurrent" in
  let Hhightcb := fresh "Hhightcb" in
  let Htable := fresh "Htable" in
  let Hctr := fresh "Hctr" in
  let Hunmap := fresh "Hunmap" in
  let Hgrp := fresh "Hgrp" in
  let Hrows := fresh "Hrows" in
  let Hhigh2 := fresh "Hhigh2" in
  let Haction := fresh "Haction" in
  let Hstep := fresh "Hstep" in
  let Hnewy := fresh "Hnewy" in
  let Hnewbitx := fresh "Hnewbitx" in
  let Hnewbity := fresh "Hnewbity" in
  let Hrowcast := fresh "Hrowcast" in
  let Hbitxcast := fresh "Hbitxcast" in
  let Hbitycast := fresh "Hbitycast" in
  let Holdy := fresh "Holdy" in
  let Holdbitx := fresh "Holdbitx" in
  let Holdbity := fresh "Holdbity" in
  let Holdcasts := fresh "Holdcasts" in
  let Hrowlen := fresh "Hrowlen" in
  let Hrowranges := fresh "Hrowranges" in
  let Hgrouprange := fresh "Hgrouprange" in
  let Hbitx32 := fresh "Hbitx32" in
  let Hwas := fresh "Hwas" in
  let Hcaller_merge := fresh "Hcaller_merge" in
  let Hfull := fresh "Hfull" in
  let Hclearrange := fresh "Hclearrange" in
  let Hclear32 := fresh "Hclear32" in
  let Hclear := fresh "Hclear" in
  let Hnewrowrange := fresh "Hnewrowrange" in
  let Hnewrowcast := fresh "Hnewrowcast" in
  let Hgroupcast := fresh "Hgroupcast" in
  let Hobservations := fresh "Hobservations" in
  let Hinherit := fresh "Hinherit" in
  let Hsource := fresh "Hsource" in
  let Hcache := fresh "Hcache" in
  let Hblocking := fresh "Hblocking" in
  match goal with H : mutex_pend_owner_snapshot sg entry eid current m tid caller owner node |- _ =>
    pose proof H as Howner end;
  pose proof Howner as [Hwait [Hm [Ho [Hnode [Hneq [Hptr [Hnotidle Huse]]]]]]];
  pose proof Hwait as [Hvalid [Hcur [Hcaller [He [Htype Hwait_rest]]]]];
  match goal with H : mutex_pend_first_snapshot owned _ sg _ _ entered _ _ _ entry eid _ current m tid caller |- _ =>
    pose proof H as Hfirst end;
  match goal with H : mutex_pend_task_entry _ entered entry |- _ => pose proof H as Hentry end;
  match goal with H : sem_pend_blocking_call_stage sg entered entry |- _ => pose proof H as Hstage end;
  match goal with H : task_base_priority sg entry.(TskState).(prioTbl) owner base |- _ => pose proof H as Hbase end;
  destruct (mutex_pend_count_decode__priority_wait sg entry eid current m Hvalid He Htype Hm)
    as [Hpcpbytes [Hdecode Hcast]];
  repeat rewrite Hcast in *; repeat rewrite Hdecode in *;
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
    by (pose proof (proj1 Hvalid) as Hprofile;
      unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto);
  assert (Henabled : m.(mfPCP) <> sg.(osPrioMutexCeilDis)) by lia;
  assert (Hpcp : 0 <= m.(mfPCP) < 64) by lia;
  pose proof (sem_pend_task_priority_in_range sg entry owner node Hvalid Hnode) as Hnodeprio;
  match goal with H : os_sched_global_addresses sg _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses;
    unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses;
    destruct Haddresses as [Hi [Hl [Hhigh [Hcurrent [Hhightcb [Htable [Hctr [Hunmap [Hgrp [Hrows Hhigh2]]]]]]]]]] end;
  rewrite Htable, Hrows, Hgrp, Hcurrent;
  match goal with H : ?p = sg.(g_OSTCBCur) |- _ => rewrite H end;
  assert (Haction : mutex_pend_inherit_action sg.(osPrioMutexCeilDis) base node.(curPrio)
    caller.(curPrio) m.(mfPCP) = PromoteMutexOwner)
    by (apply mutex_pend_inherit_promote_iff; lia);
  let after := constr:(mutex_pend_promoted_state sg entry owner node m.(mfPCP)) in
  assert (Hstep : mutex_pend_inherit_step sg entry owner node base caller.(curPrio) m.(mfPCP) after)
    by (apply (proj2 (mutex_pend_promote_branch_eq sg entry owner node base caller.(curPrio)
      m.(mfPCP) after Hptr Haction)); reflexivity);
  destruct (mutex_pend_priority_coordinates__priority_wait m.(mfPCP) Hpcp)
    as [Hnewy [Hnewbitx [Hnewbity [Hrowcast [Hbitxcast Hbitycast]]]]];
  destruct (mutex_pend_priority_coordinates__priority_wait node.(curPrio) ltac:(lia))
    as [Holdy [Holdbitx [Holdbity Holdcasts]]];
  destruct (mutex_pend_ready_bitmap_ranges__priority_wait sg entry Hvalid)
    as [Hrowlen [Hrowranges Hgrouprange]];
  assert (Hbitx32 : unsigned_last_nbits (tcb_bit_x_of_prio node.(curPrio)) 32 = tcb_bit_x_of_prio node.(curPrio))
    by (apply unsigned_last_nbits_eq; change (0 <= tcb_bit_x_of_prio node.(curPrio) < 4294967296); lia);
  repeat rewrite Hbitx32 in *;
  repeat rewrite Hrowcast in *; repeat rewrite Hbitxcast in *; repeat rewrite Hbitycast in *;
  assert (Hwas : mutex_priority_was_ready
    (sched_row_values entry.(TskState) entry.(SchedState).(readyList))
    (tcb_y_of_prio node.(curPrio)) (tcb_bit_x_of_prio node.(curPrio)) = wasready)
    by (unfold mutex_priority_was_ready;
      destruct (Z.eqb (Z.land (Znth (tcb_y_of_prio node.(curPrio))
        (sched_row_values entry.(TskState) entry.(SchedState).(readyList)) 0)
        (tcb_bit_x_of_prio node.(curPrio))) 0) eqn:E;
      [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; cbn; try reflexivity; lia);
  let Hcaller_merge := fresh "Hcaller_merge" in
  pose proof (mutex_del_priority_frame_merge_caller_prio sg entry owner tid caller
    (proj1 Hvalid) ltac:(congruence) Hcaller) as Hcaller_merge;
  cbn [tcb_field_address] in Hcaller_merge; sep_apply_l_atomic Hcaller_merge;
  let Hfull := fresh "Hfull" in
  pose proof (mutex_pend_priority_output_merge sg entry eid current m owner node base Hvalid Huse He Htype Hm Ho
    Henabled Hnode Hbase ltac:(lia) Hnotidle) as Hfull;
  unfold mutex_pend_priority_output, mutex_priority_rows, mutex_priority_group,
    mutex_priority_removed_rows in Hfull;
  rewrite Hwas, Hcur in Hfull; cbn [encode_task_link] in Hfull;
  lazymatch wasready with
  | true =>
      let rows := constr:(sched_row_values entry.(TskState) entry.(SchedState).(readyList)) in
      let old_y := constr:(tcb_y_of_prio node.(curPrio)) in
      let old_bit := constr:(tcb_bit_x_of_prio node.(curPrio)) in
      assert (Hclearrange : 0 <= mutex_priority_cleared_row rows old_y old_bit < 256)
        by (apply mutex_priority_cleared_row_in_range__ready_bitmap_stages, Hrowranges; exact Holdy);
      assert (Hclear32 : unsigned_last_nbits
        (Znth old_y (replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bit) rows) 0) 32 =
        mutex_priority_cleared_row rows old_y old_bit)
        by (rewrite Znth_replace_Znth_Same by lia; apply unsigned_last_nbits_eq;
          change (0 <= mutex_priority_cleared_row rows old_y old_bit < 4294967296); lia);
      repeat rewrite Hclear32 in *;
      assert (Hclear : Z.eqb (mutex_priority_cleared_row rows old_y old_bit) 0 = cleared)
        by (destruct (Z.eqb (mutex_priority_cleared_row rows old_y old_bit) 0) eqn:E;
          [apply Z.eqb_eq in E|apply Z.eqb_neq in E]; try reflexivity;
          unfold mutex_priority_cleared_row in *; lia);
      assert (Hnewrowrange : 0 <= Znth (tcb_y_of_prio m.(mfPCP))
        (replace_Znth old_y (mutex_priority_cleared_row rows old_y old_bit) rows) 0 < 256)
        by (apply mutex_pend_replaced_row_range__priority_wait; assumption);
      pose proof (unsigned_last_nbits_eq _ 8 Hnewrowrange) as Hnewrowcast;
      unfold mutex_priority_cleared_row in Hnewrowcast;
      repeat rewrite Hnewrowcast in *;
      pose proof (unsigned_last_nbits_eq _ 8 Hgrouprange) as Hgroupcast;
      repeat rewrite Hgroupcast in *;
      unfold ready_group_after_relocation in Hfull; rewrite Hclear in Hfull
  | false => idtac
  end;
  unfold mutex_priority_cleared_row in Hfull;
  sep_apply_l_atomic Hfull;
  assert (Hobservations : mutex_pend_inherited_snapshot sg entry eid current m tid caller after /\
    kernel_call_task_source entered after /\ sched_current_consistency after.(TskState) after.(SchedState) /\
    sem_pend_blocking_call_stage sg entered after)
    by (eapply mutex_pend_inherited_observations__priority_wait;
      [exact Hfirst|exact Howner|exact Hentry|exact Hstage|exact Hbase|exact Henabled|exact Hstep]);
  destruct Hobservations as [Hinherit [Hsource [Hcache Hblocking]]];
  sep_apply_l_atomic (mutex_pend_masked_frame_inherit__priority_wait owned critical saved_local sg entered
    saved entry entry owner node base caller.(curPrio) m.(mfPCP) after Hnode Hstep);
  Exists after entered entry current m tid caller owned; entailer!;
    try (unfold os_sched_global_addresses, sched_new_global_addresses; tauto).


