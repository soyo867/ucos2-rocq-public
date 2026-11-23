Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From Ucos2Verify.VC.code.mutex Require Import pend_native_goal.
From Ucos2Verify.VC.code.mutex Require Import pend_native_proof_auto_checked.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope sac.

(* Required scope from root_entry group. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_idle_protocol_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_use_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The first protected observation is obtained from the actual Save
    history. Readiness is deliberately absent: only the later busy arm
    needs it. Existing handle, owner-use and Idle protocols transport
    their facts over this same interval. *)

(* Required scope from priority_wait group. *)
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

(* Required scope from wait_tail group. *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_accept_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_wait_sched_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_modular_history_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(* Required scope from entry_arithmetic group. *)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib Require Import Monad.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_api_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_pend_call_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.
Require Import Ucos2Verify.lib.mutex_query_spec.
Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_heap_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_wait_proof_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_wait_tail_proof_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_pend_entry_arithmetic_proof_spec.

Lemma proof_of_OSMutexPend_safety_wit_6 : OSMutexPend_safety_wit_6.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  prop_apply_p (store_ushort_range (&(pe # "os_event" ->ₛ "OSEventCnt"))
    (encode_event_cnt_value current)).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_safety_wit_14 : OSMutexPend_safety_wit_14.
Proof.
  left; intros.
  destruct (mutex_pend_shifted_priority_range__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [_ Hy].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; lia.
Qed.

Lemma proof_of_OSMutexPend_safety_wit_15 : OSMutexPend_safety_wit_15.
Proof.
  left; intros.
  destruct (mutex_pend_shifted_priority_range__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [_ Hy].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; lia.
Qed.

Lemma proof_of_OSMutexPend_safety_wit_16 : OSMutexPend_safety_wit_16.
Proof.
  left; intros.
  destruct (mutex_pend_shifted_priority_range__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [_ Hy].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; lia.
Qed.

Lemma proof_of_OSMutexPend_safety_wit_17 : OSMutexPend_safety_wit_17.
Proof.
  left; intros.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hx [_ [Heq _]]].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; lia.
Qed.

Lemma proof_of_OSMutexPend_safety_wit_18 : OSMutexPend_safety_wit_18.
Proof.
  left; intros.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hx [_ [Heq _]]].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; lia.
Qed.

Lemma proof_of_OSMutexPend_safety_wit_19 : OSMutexPend_safety_wit_19.
Proof.
  left; intros.
  destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hx [_ [Heq _]]].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; lia.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_1 : OSMutexPend_entail_wit_1.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  prop_apply_p (store_uchar_range (&(pe # "os_event" ->ₛ "OSEventType"))
    (event_slot_type_value (EventState before) eid)).
  prop_apply_p (store_uint_range (&("timeout")) timeout_pre).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_2 : OSMutexPend_entail_wit_2.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  prop_apply_p (store_uchar_range (&("OSIntNesting")) (intNesting (IntrState before))).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_3 : OSMutexPend_entail_wit_3.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  prop_apply_p (store_uchar_range (&("OSLockNesting")) (lockNesting (IntrState before))).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_1 : OSMutexPend_entail_wit_4_1.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  mutex_pend_promote__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2 owned_2 entered_2
    critical saved_local retval true false.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_2 : OSMutexPend_entail_wit_4_2.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  mutex_pend_promote__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2 owned_2 entered_2
    critical saved_local retval true true.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_3 : OSMutexPend_entail_wit_4_3.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  mutex_pend_promote__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2 owned_2 entered_2
    critical saved_local retval false false.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_4 : OSMutexPend_entail_wit_4_4.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  mutex_pend_no_change__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2 owned_2 entered_2.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_5 : OSMutexPend_entail_wit_4_5.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  match goal with H : mutex_pend_owner_snapshot sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node |- _ =>
    pose proof H as Howner end;
  pose proof Howner as [Hwait [Hm [Ho [Hnode [Hneq [Hptr [Hnotidle Huse]]]]]]];
  pose proof Hwait as [Hvalid [Hcur [Hcaller [He [Htype Hwait_rest]]]]];
  match goal with H : mutex_pend_first_snapshot owned_2 _ sg _ _ entered_2 _ _ _ entry_2 eid _ current_2 m_2 tid_2 caller_2 |- _ =>
    pose proof H as Hfirst end;
  match goal with H : mutex_pend_task_entry _ entered_2 entry_2 |- _ => pose proof H as Hentry end;
  match goal with H : sem_pend_blocking_call_stage sg entered_2 entry_2 |- _ => pose proof H as Hstage end;
  match goal with H : task_base_priority sg entry_2.(TskState).(prioTbl) owner retval_2 |- _ => pose proof H as Hbase end;
  destruct (mutex_pend_count_decode__priority_wait sg entry_2 eid current_2 m_2 Hvalid He Htype Hm)
    as [Hpcpbytes [Hdecode Hcast]];
  repeat rewrite Hcast in *; repeat rewrite Hdecode in *;
  assert (Hdisabled : sg.(osPrioMutexCeilDis) = 255)
    by (pose proof (proj1 Hvalid) as Hprofile;
      unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto);
  assert (Henabled : m_2.(mfPCP) <> sg.(osPrioMutexCeilDis)) by lia;
  assert (Hpcp : 0 <= m_2.(mfPCP) < 64) by lia;
  pose proof (sem_pend_task_priority_in_range sg entry_2 owner node Hvalid Hnode) as Hnodeprio;
  match goal with H : os_sched_global_addresses sg _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses;
    unfold os_sched_global_addresses, sched_new_global_addresses in Haddresses;
    destruct Haddresses as [Hi [Hl [Hhigh [Hcurrent [Hhightcb [Htable [Hctr [Hunmap [Hgrp [Hrows Hhigh2]]]]]]]]]] end;
  rewrite Htable, Hrows, Hgrp, Hcurrent;
  match goal with H : ?p = sg.(g_OSTCBCur) |- _ => rewrite H end.
  assert (Haction : Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.mutex_pend_inherit_action sg.(osPrioMutexCeilDis) retval_2 node.(curPrio)
    caller_2.(curPrio) m_2.(mfPCP) = Ucos2Verify.lib.mutex.RecordMutexDemand)
    by (apply Ucos2Verify.VC.code.mutex.spec.mutex_pend_priority_spec.mutex_pend_inherit_record_iff; lia).
  set (inherited := replace_TskS
    (mutex_pend_demand_tasks entry_2.(TskState) owner node Ucos2Verify.lib.mutex.RecordMutexDemand m_2.(mfPCP)) entry_2).
  assert (Hstep : mutex_pend_inherit_step sg entry_2 owner node retval_2 caller_2.(curPrio) m_2.(mfPCP) inherited)
    by (unfold mutex_pend_inherit_step; rewrite Haction; reflexivity).
  pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hmerge.
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Hmerge; sep_apply_l_atomic Hmerge.
  let Hcaller_merge := fresh "Hcaller_merge" in
  pose proof (mutex_del_priority_frame_merge_caller_prio sg entry_2 owner tid_2 caller_2
    (proj1 Hvalid) ltac:(congruence) Hcaller) as Hcaller_merge;
  cbn [tcb_field_address] in Hcaller_merge; sep_apply_l_atomic Hcaller_merge.
  pose proof (mutex_pend_record_array_merge__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2
    Howner Hbase Henabled ltac:(lia) ltac:(lia)) as Hfull.
  rewrite Hcur in Hfull; cbn [encode_task_link] in Hfull; fold inherited in Hfull.
  sep_apply_l_atomic Hfull.
  assert (Hobservations : mutex_pend_inherited_snapshot sg entry_2 eid current_2 m_2 tid_2 caller_2 inherited /\
    kernel_call_task_source entered_2 inherited /\ sched_current_consistency inherited.(TskState) inherited.(SchedState) /\
    sem_pend_blocking_call_stage sg entered_2 inherited)
    by (eapply mutex_pend_inherited_observations__priority_wait;
      [exact Hfirst|exact Howner|exact Hentry|exact Hstage|exact Hbase|exact Henabled|exact Hstep]);
  destruct Hobservations as [Hinherit [Hsource [Hcache Hblocking]]];
  sep_apply_l_atomic (mutex_pend_masked_frame_inherit__priority_wait owned_2 critical saved_local sg entered_2
    retval entry_2 entry_2 owner node retval_2 caller_2.(curPrio) m_2.(mfPCP) inherited Hnode Hstep);
  Exists inherited entered_2 entry_2 current_2 m_2 tid_2 caller_2 owned_2; entailer!;
    try (unfold os_sched_global_addresses, sched_new_global_addresses; tauto).
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_6 : OSMutexPend_entail_wit_4_6.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  mutex_pend_no_change__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2 owned_2 entered_2.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_7 : OSMutexPend_entail_wit_4_7.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  mutex_pend_no_change__priority_wait sg entry_2 eid current_2 m_2 tid_2 caller_2 owner node retval_2 owned_2 entered_2.
Qed.

Lemma proof_of_OSMutexPend_entail_wit_4_8 : OSMutexPend_entail_wit_4_8.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  assert (Hinherited : mutex_pend_inherited_snapshot sg entry_2 eid current_2 m_2 tid_2 caller_2 entry_2).
  { eapply mutex_pend_disabled_inherited_snapshot__priority_wait; [eassumption| |exact PreH1].
    match goal with Hfirst : mutex_pend_first_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold mutex_pend_first_snapshot, mutex_accept_event_snapshot in Hfirst; tauto end. }
  assert (Hsource : kernel_call_task_source entered_2 entry_2).
  { match goal with Hfirst : mutex_pend_first_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      unfold mutex_pend_first_snapshot in Hfirst; tauto end. }
  assert (Hcache : sched_current_consistency entry_2.(TskState) entry_2.(SchedState))
    by (eapply mutex_pend_task_entry_cache__priority_wait; eassumption).
  Exists entry_2 entered_2 entry_2 current_2 m_2 tid_2 caller_2 owned_2.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_1 : OSMutexPend_return_wit_1.
Proof.
  left; intros; unfold mutex_pend_fact; Intros; subst environment external platform.
  assert (Hfirst : mutex_pend_first_snapshot owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller) by assumption.
  pose proof Hfirst as [Hhistory [Hsaved _]].
  sep_apply_l_atomic (mutex_pend_acquired_api_return owned critical saved_local sg context entered
    mask retval before entry pe eid ticks 120
    (mutex_accept_owned_state entry eid current m tid caller.(curPrio)) pd X
    ltac:(assumption) Hsaved Hhistory ltac:(assumption) ltac:(assumption)).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_2 : OSMutexPend_return_wit_2.
Proof.
  left; intros; unfold mutex_pend_fact; Intros; subst environment external platform.
  assert (Hfirst : mutex_pend_first_snapshot owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller) by assumption.
  pose proof Hfirst as [Hhistory [Hsaved _]].
  sep_apply_l_atomic (mutex_pend_acquired_api_return owned critical saved_local sg context entered
    mask retval before entry pe eid ticks 0
    (mutex_accept_owned_state entry eid current m tid caller.(curPrio)) pd X
    ltac:(assumption) Hsaved Hhistory ltac:(assumption) ltac:(assumption)).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_3 : OSMutexPend_return_wit_3.
Proof.
  left; intros; unfold mutex_pend_fact; Intros; subst environment external platform.
  assert (Hfirst : mutex_pend_first_snapshot owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller) by assumption.
  pose proof Hfirst as [Hhistory [Hsaved _]].
  sep_apply_l_atomic (mutex_pend_acquired_api_return owned critical saved_local sg context entered
    mask retval before entry pe eid ticks 0
    (mutex_accept_owned_state entry eid current m tid caller.(curPrio)) pd X
    ltac:(assumption) Hsaved Hhistory ltac:(assumption) ltac:(assumption)).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_4 : OSMutexPend_return_wit_4.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses end.
  unfold os_sched_global_addresses in Haddresses.
  destruct Haddresses as [Hint [Hlock Hrest]].
  rewrite Hint, Hlock.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before Hvalid).
  assert (Herr : mutex_pend_precritical_error pe (event_slot_type_value (EventState before) eid)
    (intNesting (IntrState before)) (lockNesting (IntrState before)) = Some OS_ERR_PEND_LOCKED).
  { replace (event_slot_type_value (EventState before) eid) with 4 by lia.
    apply mutex_pend_precritical_locked; lia. }
  sep_apply_r_atomic (mutex_pend_early_post__entry_arithmetic external platform environment
    critical saved_local sg context mask pe eid ticks pd before X OS_ERR_PEND_LOCKED Herr
    ltac:(assumption)).
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSMutexPend_return_wit_5 : OSMutexPend_return_wit_5.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses end.
  unfold os_sched_global_addresses in Haddresses.
  destruct Haddresses as [Hint [Hlock Hrest]].
  rewrite Hint, Hlock.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before Hvalid).
  assert (Herr : mutex_pend_precritical_error pe (event_slot_type_value (EventState before) eid)
    (intNesting (IntrState before)) (lockNesting (IntrState before)) = Some OS_ERR_PEND_ISR).
  { replace (event_slot_type_value (EventState before) eid) with 4 by lia.
    apply mutex_pend_precritical_isr; lia. }
  sep_apply_r_atomic (mutex_pend_early_post__entry_arithmetic external platform environment
    critical saved_local sg context mask pe eid ticks pd before X OS_ERR_PEND_ISR Herr
    ltac:(assumption)).
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSMutexPend_return_wit_6 : OSMutexPend_return_wit_6.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  match goal with H : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    pose proof H as [Htype _] end.
  rewrite Htype.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  assert (Herr : mutex_pend_precritical_error pe (event_slot_type_value (EventState before) eid)
    (intNesting (IntrState before)) (lockNesting (IntrState before)) = Some OS_ERR_EVENT_TYPE).
  { apply mutex_pend_precritical_type; lia. }
  sep_apply_r_atomic (mutex_pend_early_post__entry_arithmetic external platform environment
    critical saved_local sg context mask pe eid ticks pd before X OS_ERR_EVENT_TYPE Herr
    ltac:(assumption)).
  unfold sem_pend_continuation_save_input; rewrite mutex_query_closed_equiv.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSMutexPend_return_wit_7 : OSMutexPend_return_wit_7.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Herr : mutex_pend_precritical_error pe (event_slot_type_value (EventState before) eid)
    (intNesting (IntrState before)) (lockNesting (IntrState before)) = Some OS_ERR_PEVENT_NULL).
  { replace pe with 0 by lia; apply mutex_pend_precritical_null. }
  sep_apply_r_atomic (mutex_pend_early_post__entry_arithmetic external platform environment
    critical saved_local sg context mask pe eid ticks pd before X OS_ERR_PEVENT_NULL Herr
    ltac:(assumption)).
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge; entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try solve [repeat apply derivable1s_emp_sepcon_unfold; apply derivable1s_coq_prop_r; tauto].
Qed.

Lemma proof_of_OSMutexPend_return_wit_8 : OSMutexPend_return_wit_8.
Proof.
  unfold OSMutexPend_return_wit_8; right; intros.
  assert (Hfact : forall P, mutex_pend_fact P |-- emp).
  { intro P; unfold mutex_pend_fact; apply derivable1_andp_elim2. }
  repeat match goal with |- context [mutex_pend_fact ?P] =>
    sep_apply_l_atomic (Hfact P)
  end.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_9 : OSMutexPend_return_wit_9.
Proof.
  unfold OSMutexPend_return_wit_9; right; intros.
  assert (Hfact : forall P, mutex_pend_fact P |-- emp).
  { intro P; unfold mutex_pend_fact; apply derivable1_andp_elim2. }
  repeat match goal with |- context [mutex_pend_fact ?P] =>
    sep_apply_l_atomic (Hfact P)
  end.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_10 : OSMutexPend_return_wit_10.
Proof.
  unfold OSMutexPend_return_wit_10; right; intros.
  assert (Hfact : forall P, mutex_pend_fact P |-- emp).
  { intro P; unfold mutex_pend_fact; apply derivable1_andp_elim2. }
  repeat match goal with |- context [mutex_pend_fact ?P] =>
    sep_apply_l_atomic (Hfact P)
  end.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_return_wit_11 : OSMutexPend_return_wit_11.
Proof.
  unfold OSMutexPend_return_wit_11; right; intros.
  assert (Hfact : forall P, mutex_pend_fact P |-- emp).
  { intro P; unfold mutex_pend_fact; apply derivable1_andp_elim2. }
  repeat match goal with |- context [mutex_pend_fact ?P] =>
    sep_apply_l_atomic (Hfact P)
  end.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_8_pure : OSMutexPend_partial_solve_wit_8_pure.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller ltac:(assumption) ltac:(assumption))
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  rewrite Hcast, Hprio in *; entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_10_pure : OSMutexPend_partial_solve_wit_10_pure.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller ltac:(assumption) ltac:(assumption))
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  rewrite Hcast, Hprio in *.
  assert (Hcode : encode_os_err_code (mutex_pend_acquire_error sg
    (Z.shiftr (encode_event_cnt_value current) 8) caller.(curPrio)) = 0).
  { unfold mutex_pend_acquire_error; rewrite Hdisabled.
    destruct (Z.eqb (Z.shiftr (encode_event_cnt_value current) 8) 255) eqn:En; [reflexivity|].
    assert (Hp : Z.leb caller.(curPrio) (Z.shiftr (encode_event_cnt_value current) 8) = false)
      by (apply Z.leb_gt; lia).
    rewrite Hp; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_11_pure : OSMutexPend_partial_solve_wit_11_pure.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask retval
    before entry eid observed current m tid caller ltac:(assumption) ltac:(assumption))
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  rewrite Hcast, Hprio in *.
  assert (Hpcpdisabled : Z.shiftr (encode_event_cnt_value current) 8 = 255) by assumption.
  assert (Hcode : encode_os_err_code (mutex_pend_acquire_error sg
    (Z.shiftr (encode_event_cnt_value current) 8) caller.(curPrio)) = 0).
  { unfold mutex_pend_acquire_error; rewrite Hdisabled, Hpcpdisabled; reflexivity. }
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_17_pure : OSMutexPend_partial_solve_wit_17_pure.
Proof. right; intros; unfold mutex_pend_fact; entailer!. Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_19_pure : OSMutexPend_partial_solve_wit_19_pure.
Proof.
  right; intros; unfold mutex_pend_fact; Intros.
  match goal with Hsnap : mutex_pend_owner_snapshot _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof Hsnap as [Hwait [Hm _]] end.
  destruct Hwait as [Hvalid [_ [_ [He [Htype _]]]]].
  destruct (mutex_pend_count_decode__priority_wait _ _ _ _ _ Hvalid He Htype Hm)
    as [_ [_ Hcast]].
  rewrite Hcast in *; entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_34_pure : OSMutexPend_partial_solve_wit_34_pure.
Proof.
  left; intros.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; try assumption; lia.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_35_pure : OSMutexPend_partial_solve_wit_35_pure.
Proof.
  left; intros.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; try assumption; lia.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_36_pure : OSMutexPend_partial_solve_wit_36_pure.
Proof.
  left; intros.
  destruct (mutex_pend_priority_native_fields__entry_arithmetic
    (Z.shiftr (encode_event_cnt_value current) 8) ltac:(lia)) as [Hy [Hx [Hrow Hcol]]].
  repeat match goal with |- _ |-- _ && _ => apply _derivable1_andp_intros end;
    apply dump_spatial_left; try assumption; lia.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_39_pure : OSMutexPend_partial_solve_wit_39_pure.
Proof.
  unfold OSMutexPend_partial_solve_wit_39_pure; left; intros.
  sepcon_assoc_change.
  match goal with |- context [mutex_pend_fact (os_sched_global_addresses ?sg ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j)] =>
    L_sepcon_lift' (mutex_pend_fact (os_sched_global_addresses sg a b c d e f g h i j)) end.
  unfold mutex_pend_fact at 1; Intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in H; entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_41_pure : OSMutexPend_partial_solve_wit_41_pure.
Proof.
  unfold OSMutexPend_partial_solve_wit_41_pure; left; intros.
  sepcon_assoc_change.
  match goal with |- context [mutex_pend_fact (os_sched_global_addresses ?sg ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j)] =>
    L_sepcon_lift' (mutex_pend_fact (os_sched_global_addresses sg a b c d e f g h i j)) end.
  unfold mutex_pend_fact at 1; Intros.
  unfold os_sched_global_addresses, sched_new_global_addresses in H; entailer!.
Qed.

Lemma proof_of_OSMutexPend_partial_solve_wit_44_pure : OSMutexPend_partial_solve_wit_44_pure.
Proof.
  unfold OSMutexPend_partial_solve_wit_44_pure; left; intros.
  sepcon_assoc_change.
  match goal with |- context [mutex_pend_fact (os_sched_global_addresses ?sg ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j)] =>
    L_sepcon_lift' (mutex_pend_fact (os_sched_global_addresses sg a b c d e f g h i j)) end.
  unfold mutex_pend_fact at 1; Intros; entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_1 : OSMutexPend_which_implies_wit_1.
Proof. left; intros; unfold sem_pend_error_cell; reflexivity. Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_2 : OSMutexPend_which_implies_wit_2.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hinput : mutex_pend_api_input critical sg (os_sched_call_invocation context)
    pe before eid observed) by assumption.
  destruct Hinput as [Hzero|[Hnonzero [Haddr [Hid [Hslot Hhandle]]]]]; [contradiction|].
  unfold sem_pend_continuation_save_input.
  rewrite mutex_query_closed_equiv.
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot).
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [Htype _]; rewrite Htype.
  rewrite Htype in Hlayout.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try assumption.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_3 : OSMutexPend_which_implies_wit_3.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [Htype _]; rewrite Htype.
  rewrite Htype in Hlayout.
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid Hvalid).
  sep_apply_l_atomic (sem_pend_interrupt_split sg before).
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses; pose proof H as Hglobals end.
  unfold os_sched_global_addresses in Haddresses.
  destruct Haddresses as [Hint [Hlock Hrest]].
  rewrite Hint, Hlock.
  rewrite Hint, Hlock in Hglobals.
  asrt_simpl_pure; sepcon_assoc_change.
  repeat sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  entailer!.
  all: try solve [repeat rewrite mutex_query_truep_sepcon_equiv; apply derivable1_truep_intros].
  all: try assumption.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_4 : OSMutexPend_which_implies_wit_4.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hprefix : mutex_pend_api_prefix pe before eid).
  { unfold mutex_pend_api_prefix; apply mutex_pend_precritical_continues_iff; tauto. }
  assert (Hadmission : mutex_pend_api_admission environment idle context pe before eid)
    by assumption.
  destruct (Hadmission Hprefix) as [[owned Henv] [Hsource Hnonidle]].
  subst environment.
  match goal with H : os_sched_global_addresses _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof H as Haddresses; pose proof H as Hglobals end.
  unfold os_sched_global_addresses in Haddresses.
  destruct Haddresses as [Hint [Hlock Hrest]].
  rewrite Hint, Hlock.
  rewrite Hint, Hlock in Hglobals.
  sep_apply_l_atomic (sem_pend_interrupt_merge sg before Hvalid).
  unfold sem_pend_optional_continuation_resources; Intros.
  assert (Hexternal : task_stack_call_external owned = external) by tauto.
  assert (Hplatform : task_stack_call_platform owned = platform) by tauto.
  subst external platform.
  Exists owned.
  entailer!.
  sep_apply_r_atomic (proj1 (sem_pend_continuation_save_input_owned
    owned critical saved_local sg context mask before)).
  unfold sem_pend_continuation_save_input, sem_pend_optional_continuation_resources.
  rewrite mutex_query_closed_equiv.
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_5 : OSMutexPend_which_implies_wit_5.
Proof.
  left; intros; subst environment; unfold mutex_pend_fact; Intros.
  assert (Hvalid : UCOS2_state_inv sg before) by assumption.
  assert (Hinput : mutex_pend_api_input critical sg (os_sched_call_invocation context)
    pe before eid observed) by assumption.
  assert (Hadmission : mutex_pend_api_admission (Some owned) idle context pe before eid) by assumption.
  assert (Hscope : mutex_pend_api_scope (Some owned) critical sg idle context pe before eid) by assumption.
  assert (Hprefix : mutex_pend_api_prefix pe before eid) by assumption.
  pose proof (proj1 (mutex_pend_precritical_continues_iff _ _ _ _) Hprefix)
    as [Hnonnull Hguards].
  assert (Hpe : pe = event_addr sg eid).
  { unfold mutex_pend_api_input in Hinput; tauto. }
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [Htype [Hptr Hcnt]].
  pose proof (mutex_pend_first_save_split owned critical saved_local sg idle context
    pe before eid observed mask cpu_sr Hvalid Hinput Hadmission Hscope Hprefix) as Hsplit.
  cbn [tcb_field_address] in Hsplit; sep_apply_l_atomic Hsplit.
  Intros entered entry current m tid caller.
  Exists entered entry current m tid caller.
  rewrite Hptr, Hcnt, PreH2.
  entailer!; try (unfold event_core_fields_layout_prop; tauto).
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_6 : OSMutexPend_which_implies_wit_6.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hfirst : mutex_pend_first_snapshot owned critical sg idle context entered mask cpu_sr
    before entry eid observed current m tid caller) by assumption.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask cpu_sr
    before entry eid observed current m tid caller Hfirst PreH1)
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  assert (Hcode : 120 = encode_os_err_code (mutex_pend_acquire_error sg m.(mfPCP) caller.(curPrio))).
  { unfold mutex_pend_acquire_error; rewrite Hdisabled.
    assert (Henabled : Z.eqb m.(mfPCP) 255 = false) by (apply Z.eqb_neq; lia).
    assert (Hlower : Z.leb caller.(curPrio) m.(mfPCP) = true) by (apply Z.leb_le; lia).
    rewrite Henabled, Hlower; reflexivity. }
  pose proof (mutex_pend_snapshot_acquired owned critical sg idle context entered mask cpu_sr
    before entry eid observed current m tid caller ticks 120 Hfirst PreH1 Hcode) as Hacquired.
  pose proof Hfirst as [Hhistory [_ [_ [Hfacts [_ [_ [_ [_ [_ [Hsnapshot Hcaller]]]]]]]]]].
  pose proof (proj1 (proj2 Hfacts)) as Hvalid.
  pose proof Hsnapshot as [Hlookup [Htype [Hfields Hencoding]]].
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite Hstore, Hptr_addr, Hcnt_addr, PreH6.
  pose proof (mutex_pend_acquire_restore_merge owned critical saved_local sg entered cpu_sr
    entry eid current m tid caller Hvalid Hlookup Htype Hfields Hnone Hcaller) as Hmerge.
  cbn [tcb_field_address] in Hmerge; sep_apply_l_atomic Hmerge.
  entailer!; try (unfold event_core_fields_layout_prop; tauto).
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_7 : OSMutexPend_which_implies_wit_7.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  assert (Hfirst : mutex_pend_first_snapshot owned critical sg idle context entered mask cpu_sr
    before entry eid observed current m tid caller) by assumption.
  destruct (mutex_pend_acquire_byte_observations owned critical sg idle context entered mask cpu_sr
    before entry eid observed current m tid caller Hfirst PreH1)
    as [Hnone [Hpcp [Hcast [Hprio [Hdisabled Hstore]]]]].
  assert (Hcode : 0 = encode_os_err_code (mutex_pend_acquire_error sg m.(mfPCP) caller.(curPrio)))
    by congruence.
  pose proof (mutex_pend_snapshot_acquired owned critical sg idle context entered mask cpu_sr
    before entry eid observed current m tid caller ticks 0 Hfirst PreH1 Hcode) as Hacquired.
  pose proof Hfirst as [Hhistory [_ [_ [Hfacts [_ [_ [_ [_ [_ [Hsnapshot Hcaller]]]]]]]]]].
  pose proof (proj1 (proj2 Hfacts)) as Hvalid.
  pose proof Hsnapshot as [Hlookup [Htype [Hfields Hencoding]]].
  assert (Hlayout : event_core_fields_layout_prop sg eid
    (&(pe # "os_event" ->ₛ "OSEventType")) (&(pe # "os_event" ->ₛ "OSEventPtr"))
    (&(pe # "os_event" ->ₛ "OSEventCnt"))) by assumption.
  pose proof Hlayout as [Htype_addr [Hptr_addr Hcnt_addr]].
  rewrite Hstore, Hptr_addr, Hcnt_addr, PreH5.
  pose proof (mutex_pend_acquire_restore_merge owned critical saved_local sg entered cpu_sr
    entry eid current m tid caller Hvalid Hlookup Htype Hfields Hnone Hcaller) as Hmerge.
  cbn [tcb_field_address] in Hmerge; sep_apply_l_atomic Hmerge.
  entailer!; try (unfold event_core_fields_layout_prop; tauto).
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_8 : OSMutexPend_which_implies_wit_8.
Proof.
  right; intros; subst pe; rewrite PreH4; unfold mutex_pend_fact; Intros.
  match goal with Hfirst : mutex_pend_first_snapshot _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof Hfirst as [_ [_ [_ [Hacq [_ [_ [_ [_ [_ [Hsnap Hcur]]]]]]]]]] end.
  pose proof Hacq as [_ [Hvalid _]]. pose proof Hsnap as [He Hrest].
  pose proof (mutex_accept_current_fields_merge sg entry eid current tid caller Hcur) as Hmerge.
  cbn [tcb_field_address] in Hmerge; sep_apply_l_atomic Hmerge.
  match goal with Hlayout : event_core_fields_layout_prop _ _ _ _ _ |- _ =>
    destruct Hlayout as [Htype_addr [Hptr_addr Hcnt_addr]] end.
  rewrite Hptr_addr, Hcnt_addr.
  sep_apply_l_atomic (mutex_accept_event_fields_merge_full sg entry eid current
    (encode_event_cnt_value current) (encode_event_ptr_value sg current) Hvalid He eq_refl eq_refl).
  prop_apply_p (Ucos2Verify.VC.code.sem.spec.sem_pend_modular_call_spec.sem_pend_inv_interrupt_range sg entry); Intros.
  destruct (mutex_pend_busy_observations__priority_wait owned critical sg idle context entered
    mask cpu_sr before entry eid observed current m tid caller (event_addr sg eid)
    ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
    ltac:(rewrite <- PreH1; assumption) ltac:(assumption) PreH2)
    as [Hwait [Hentry Hstage]].
  entailer!; try (unfold event_core_fields_layout_prop; tauto).
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_9 : OSMutexPend_which_implies_wit_9.
Proof.
  left; intros; subst pe; unfold mutex_pend_fact; Intros.
  destruct (mutex_pend_owner_observations__priority_wait _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 H)
    as [owner [node [Howner Hptr]]].
  pose proof H as [Hvalid [_ [_ [He [Htype Hrest]]]]].
  assert (Hlayout : event_object_layout_prop sg eid) by (unfold mutex_pend_wait_entry in H; tauto).
  destruct Hlayout as [[Htype_addr [Hptr_addr Hcnt_addr]] Hbitmap].
  rewrite Hptr_addr, Hcnt_addr.
  sep_apply_l_atomic (mutex_accept_event_fields_split_full sg entry eid current He Htype).
  Intros found; Exists owner node; rewrite Hptr; entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_10 : OSMutexPend_which_implies_wit_10.
Proof.
  right; intros; subst pe ptcb pcp; unfold mutex_pend_fact; Intros.
  pose proof H as [Hwait [Hm [Ho [Hnode [Hneq [Hnone Hrest]]]]]].
  pose proof Hwait as [Hvalid [Hcur [Hcaller [He [Htype Hwait_rest]]]]].
  destruct (mutex_pend_count_decode__priority_wait _ _ _ _ _ Hvalid He Htype Hm)
    as [_ [Hdecode Hcast]].
  rewrite Hcast in *.
  pose proof (mutex_pend_owner_ceiling_range__priority_wait _ _ _ _ _ _ _ _ _ H PreH2) as Hpcp.
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hnode) as Hprio.
  pose proof (mutex_del_priority_values_length sg entry.(TskState).(prioTbl)) as Hlen.
  assert (Hptr : encode_event_ptr_value sg current = task_slot_addr sg owner).
  { unfold encode_event_ptr_value; rewrite Htype, Hm, Ho; reflexivity. }
  assert (Hlayout : event_object_layout_prop sg eid) by (unfold mutex_pend_wait_entry in Hwait; tauto).
  destruct Hlayout as [[Htype_addr [Hptr_addr Hcnt_addr]] Hbitmap].
  pose proof H0 as Haddresses.
  unfold os_sched_global_addresses, sched_new_global_addresses in H0.
  destruct H0 as [Hi [Hl [Hhigh [Hcurrent [Hhightcb [Htable [Hctr [Hunmap [Hgrp [Hrows Hhigh2]]]]]]]]]].
  rewrite Hptr_addr, Hcnt_addr, Htable, Hrows, Hgrp, Hcurrent, PreH5.
  sep_apply_l_atomic (mutex_accept_event_fields_merge_full sg entry eid current
    (encode_event_cnt_value current) (task_slot_addr sg owner) Hvalid He eq_refl (eq_sym Hptr)).
  unfold UCOS2_inv; Intros.
  sep_apply_l_atomic (mutex_pend_priority_input_split sg entry owner node (proj1 Hvalid) Hnode).
  sep_apply_l_atomic (mutex_del_priority_frame_split_caller_prio sg entry owner tid caller
    (proj1 Hvalid) ltac:(congruence) Hcaller).
  unfold mutex_pend_priority_input, mutex_priority_fallback.
  rewrite Hcur; cbn [encode_task_link task_tcb64_image tcb_field_address]; entailer!;
    try (unfold os_sched_global_addresses, sched_new_global_addresses; tauto).
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_11 : OSMutexPend_which_implies_wit_11.
Proof.
  left; intros; subst ptcb; unfold mutex_pend_fact; Intros.
  pose proof H as [Hwait [_ [_ [Hnode Hrest]]]].
  pose proof (proj1 Hwait) as Hvalid.
  sep_apply_l_atomic (mutex_pend_tcb_not_reserved__priority_wait sg entry owner node Hvalid Hnode H0).
  Intros.
  assert (Hbase : task_base_priority sg entry.(TskState).(prioTbl) owner mprio)
    by (eapply mutex_pend_owner_base_result__priority_wait; eassumption).
  pose proof (tcb64_storage_split (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hsplit.
  cbn [tcb_cell tcb_field_address task_tcb64_image] in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_12 : OSMutexPend_which_implies_wit_12.
Proof.
  right; intros; subst pcp; unfold mutex_pend_fact; Intros.
  pose proof (mutex_pend_owner_ceiling_range__priority_wait _ _ _ _ _ _ _ _ _ H PreH2) as Hpcp.
  pose proof H as [Hwait [_ [_ [Hnode [_ [Hptr _]]]]]].
  destruct Hwait as [Hvalid Hwait].
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hnode) as Hprio.
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8).
  { unfold tcb_y_of_prio. split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  pose proof (mutex_pend_owner_fields_split__priority_wait ptcb (task_tcb64_image sg node)
    ltac:(cbn [task_tcb64_image]; rewrite Hptr; reflexivity)) as Hsplit.
  cbn [task_tcb64_image tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit; entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_13 : OSMutexPend_which_implies_wit_13.
Proof.
  left; intros pcp Hlo Hhi.
  assert (Hrow : 0 <= Z.shiftr pcp 3 < 8).
  { rewrite Z.shiftr_div_pow2 by lia; change (0 <= pcp / 8 < 8).
    split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia. }
  rewrite unsigned_last_nbits_eq by (change (0 <= Z.shiftr pcp 3 < 256); lia).
  entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_14 : OSMutexPend_which_implies_wit_14.
Proof.
  left; intros; unfold mutex_pend_fact; Intros.
  pose proof H as [_ [_ [_ [_ [_ [Hptr _]]]]]].
  pose proof (mutex_pend_owner_fields_merge__priority_wait ptcb (task_tcb64_image sg node) pcp
    ltac:(cbn [task_tcb64_image]; rewrite Hptr; reflexivity)) as Hmerge.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_15 : OSMutexPend_which_implies_wit_15.
Proof.
  left; intros; rewrite PreH1; unfold mutex_pend_fact; Intros.
  assert (Hwait : mutex_pend_wait_entry sg inherited eid current tid caller)
    by (destruct H as [owner [_ [_ Hwait]]]; exact Hwait).
  pose proof Hwait as [Hvalid [Hcurrent [Hnode Hrest]]].
  pose proof (encode_task_status_in_range caller.(stat)) as Hrange.
  change (0 <= encode_task_status caller.(stat) < 256) in Hrange.
  pose proof (mutex_pend_wait_prefix_split sg inherited tid caller Hvalid Hcurrent Hnode) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit; sep_apply_l_atomic Hsplit; entailer!; lia.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_16 : OSMutexPend_which_implies_wit_16.
Proof.
  left; intros; subst pe.
  rewrite PreH2, PreH3, PreH4.
  unfold mutex_pend_fact; Intros.
  pose proof (mutex_pend_wait_entry_row_in_range _ _ _ _ _ _ H) as Hrow.
  pose proof H as Hentry.
  destruct H as [Hvalid [Hcur [Hnode Hrest]]].
  pose proof (sem_pend_task_priority_in_range _ _ _ _ Hvalid Hnode) as Hprio.
  rewrite Z.quot_div_nonneg by lia.
  pose proof (mutex_pend_wait_prefix_split_call sg inherited eid current tid caller ticks
    Hentry) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  unfold mutex_pend_wait_call_pre; cbn [tcb_cell tcb_field_address]; entailer!.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_17 : OSMutexPend_which_implies_wit_17.
Proof.
  unfold OSMutexPend_which_implies_wit_17, mutex_pend_fact; left; intros; subst pevent_value pe.
  rewrite PreH3, PreH4, PreH5; Intros.
  pose proof H4 as [owner [_ [_ Hwait]]].
  pose proof (mutex_pend_wait_initial_observation_wait_tail owned critical sg idle context entered
    mask cpu_sr before entry eid observed current m tid caller inherited ticks H H4 H3 H2 H1 H0)
    as [Hwaiting [Hstage Hvalid]].
  pose proof (proj1 H) as Hhistory; pose proof (proj1 (proj2 H)) as Hsaved.
  rewrite (mutex_pend_wait_priority_quot_wait_tail _ _ _ _ _ _ Hwait).
  unfold mutex_pend_masked_frame; Intros.
  pose proof (mutex_pend_wait_call_restore_merge owned critical saved_local sg entered cpu_sr
    entry inherited eid current tid caller ticks Hwait H5) as Hmerge.
  unfold mutex_pend_wait_call_post in Hmerge.
  Exists (event_pend_state sg inherited eid current tid caller PendMutex ticks).
  unfold mutex_pend_api_restore_input.
  entailer!.
  all: try (sep_apply_r_atomic Hmerge; entailer!).
  all:
    try apply derivable1_truep_intros.
  all: repeat match goal with |- emp |-- ?A ** ?B =>
    apply (sepcon_cancel_end emp B A); [apply derivable1_truep_intros|] end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_18 : OSMutexPend_which_implies_wit_18.
Proof.
  unfold OSMutexPend_which_implies_wit_18, mutex_pend_fact; left; intros; subst environment external platform.
  unfold mutex_pend_api_restore_output; Intros released unmasked.
  assert (Hclients : forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action).
  { match goal with HS : mutex_pend_api_scope _ _ _ _ _ _ _ _,
      HP : mutex_pend_api_prefix _ _ _ |- _ =>
      pose proof (HS HP) as [_ [_ [_ [_ [_ [_ [HC _]]]]]]]; exact HC end. }
  match goal with HR : sem_pend_modular_call_history _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct HR as [Hhistory Hrely] end.
  assert (Hfacts : mutex_pend_wait_at sg context entry current eid ticks waiting released unmasked /\
    sem_pend_wait_sched_entry sg released unmasked).
  { eapply mutex_pend_wait_restore_facts; eassumption. }
  match goal with HS : interrupt_saved_value _ _ |- _ => rewrite (proj2 HS) end.
  unfold task_tcb_init_continuation_save_input.
  sep_apply_l_atomic (proj1 (task_create_continuation_input_closed_world owned critical saved_local
    sg released mask unmasked)).
  Exists released unmasked.
  unfold mutex_pend_continuation_phase_sched_input, mutex_pend_restore_phase_pre,
    sem_pend_continuation_sched_input, os_sched_continuation_pre.
  entailer!; try apply derivable1_truep_intros.
  all: repeat match goal with |- emp |-- ?A ** ?B =>
    apply (sepcon_cancel_end emp B A); [apply derivable1_truep_intros|] end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_19 : OSMutexPend_which_implies_wit_19.
Proof.
  unfold OSMutexPend_which_implies_wit_19, mutex_pend_fact; left; intros; subst environment external platform.
  unfold mutex_pend_continuation_phase_sched_output; Intros scheduled selected.
  sep_apply_l_atomic (proj1 (sem_pend_continuation_save_input_owned
    owned critical saved_local sg scheduled mask selected)).
  Exists scheduled selected; entailer!;
    apply sepcon_cancel_end; apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_20 : OSMutexPend_which_implies_wit_20.
Proof.
  unfold OSMutexPend_which_implies_wit_20, mutex_pend_fact; left; intros; subst environment; rewrite PreH2.
  unfold mutex_pend_api_save_output; Intros resumed resume_entry.
  assert (Hclients : forall action, critical.(critical_region_clients) action -> mutex_pend_projected_source_client action).
  { match goal with HS : mutex_pend_api_scope _ _ _ _ _ _ _ _,
      HP : mutex_pend_api_prefix _ _ _ |- _ =>
      pose proof (HS HP) as [_ [_ [_ [_ [_ [_ [HC _]]]]]]]; exact HC end. }
  match goal with HR : sem_pend_modular_call_history _ _ _ _ _ _ _ /\ _ |- _ =>
    destruct HR as [Hhistory [Hsaved [Hrely Hpreserved]]] end.
  assert (Hselected : mutex_pend_wait_selected_at sg context entry current eid ticks waiting resumed resume_entry).
  { eapply mutex_pend_wait_selected_modular_return; eassumption. }
  unfold task_tcb_init_continuation_restore_input; Intros.
  sep_apply_l_atomic (mutex_pend_selected_cleanup_split sg context entry current eid ticks waiting resumed resume_entry Hselected).
  Intros node.
  Exists context.(os_sched_call_stack).(stackLeaseSlot) node resumed resume_entry.
  unfold mutex_pend_masked_frame; cbn [tcb_cell tcb_field_address].
  entailer!; try apply derivable1_truep_intros.
  all: repeat match goal with |- emp |-- ?A ** ?B =>
    apply (sepcon_cancel_end emp B A); [apply derivable1_truep_intros|] end.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_21 : OSMutexPend_which_implies_wit_21.
Proof.
  unfold OSMutexPend_which_implies_wit_21, mutex_pend_fact; right; intros; Intros.
  assert (Hnot : node.(statPend) <> PendTimeout).
  { intro Hto; rewrite Hto in PreH1; discriminate. }
  pose proof (mutex_pend_resume_cleanup_without_timeout sg resume_entry eid resume_tid node H Hnot) as Hobs.
  rewrite PreH1 in Hobs; cbn [sem_pend_resume_error encode_os_err_code] in Hobs.
  change (mutex_pend_cleanup_observation sg resume_entry eid 0 resume_entry resume_tid node) in Hobs.
  Exists resume_entry node; entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_22 : OSMutexPend_which_implies_wit_22.
Proof.
  unfold OSMutexPend_which_implies_wit_22, mutex_pend_fact; right; intros; Intros.
  assert (Hnot : node.(statPend) <> PendTimeout).
  { intro Hto; rewrite Hto in PreH1; discriminate. }
  pose proof (mutex_pend_resume_cleanup_without_timeout sg resume_entry eid resume_tid node H Hnot) as Hobs.
  rewrite PreH1 in Hobs; cbn [sem_pend_resume_error encode_os_err_code] in Hobs.
  change (mutex_pend_cleanup_observation sg resume_entry eid 14 resume_entry resume_tid node) in Hobs.
  Exists resume_entry node; entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_23 : OSMutexPend_which_implies_wit_23.
Proof.
  unfold OSMutexPend_which_implies_wit_23, mutex_pend_fact; left; intros; subst pe; rewrite PreH3.
  unfold mutex_pend_masked_frame; Intros.
  assert (Hentry : sem_pend_resume_entry sg resume_entry eid resume_tid node) by assumption.
  assert (Hlinked : mutex_query_lookup resume_entry eid linked) by assumption.
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  assert (Hcoverage : task_stack_live_coverage resume_entry.(TskState) (task_stack_call_active_key resumed)) by assumption.
  rewrite (mutex_pend_resume_priority_quot_wait_tail _ _ _ _ _ Hentry).
  sepcon_assoc_change.
  pose proof (mutex_pend_remove_call_cleanup_split owned saved_local sg resumed resume_entry eid linked
    resume_tid node Hentry PreH1 Hlinked Hlayout Hcoverage) as Hmerge.
  sep_apply_l_atomic Hmerge; Intros.
  Exists (event_task_remove_state resume_entry eid linked resume_tid node) (task_set_event_ptr node None).
  cbn [tcb_cell tcb_field_address task_set_event_ptr stat statPend eventPtr encode_event_link].
  entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_24 : OSMutexPend_which_implies_wit_24.
Proof.
  unfold OSMutexPend_which_implies_wit_24, mutex_pend_fact; right; intros; subst pe; Intros.
  assert (Hentry : sem_pend_resume_entry sg resume_entry eid resume_tid node) by assumption.
  assert (Hlayout : event_object_layout_prop sg eid) by assumption.
  destruct (mutex_pend_resume_timeout_event sg resume_entry eid resume_tid node Hentry PreH1 PreH2)
    as [Htimeout [linked [Hlinked Hin]]].
  rewrite (mutex_pend_resume_priority_quot_wait_tail _ _ _ _ _ Hentry).
  pose proof (sem_pend_resume_split_remove_call sg resume_entry eid resume_tid node linked Hentry Hlinked Hlayout) as Hsplit.
  cbn [tcb_cell tcb_field_address] in Hsplit.
  sep_apply_l_atomic Hsplit.
  Exists linked; entailer!; try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_25 : OSMutexPend_which_implies_wit_25.
Proof.
  unfold OSMutexPend_which_implies_wit_25, mutex_pend_fact; right; intros; rewrite PreH2.
  unfold mutex_pend_masked_frame; Intros.
  assert (Hobs : mutex_pend_cleanup_observation sg resume_entry eid code_2 cleaning resume_tid clean_node) by assumption.
  assert (Hcoverage : task_stack_live_coverage cleaning.(TskState) (task_stack_call_active_key resumed)) by assumption.
  pose proof (mutex_pend_cleanup_observation_result _ _ _ _ _ _ _ Hobs) as Hresult.
  sepcon_assoc_change.
  pose proof (mutex_pend_cleanup_restore_merge owned critical saved_local sg resumed cpu_sr resume_entry
    resume_entry eid code_2 cleaning resume_tid clean_node Hobs Hcoverage) as Hmerge.
  cbn [tcb_cell tcb_field_address] in Hmerge.
  Exists (event_pend_cleanup_state sg false cleaning resume_tid clean_node).
  unfold mutex_pend_api_restore_input; entailer!.
  all: try (sep_apply_r_atomic Hmerge; entailer!).
  all: try apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexPend_which_implies_wit_26 : OSMutexPend_which_implies_wit_26.
Proof.
  unfold OSMutexPend_which_implies_wit_26, mutex_pend_fact; left; intros; subst environment external platform.
  unfold mutex_pend_api_restore_output; Intros returned after.
  match goal with HR : sem_pend_modular_call_history _ _ _ resumed cleaned returned after /\ _ |- _ =>
    destruct HR as [Hfinal Hrely] end.
  assert (Hresult : mutex_pend_api_program (Some owned) critical sg context pe eid ticks before code after /\
    kernel_stack_call_same_call returned context).
  { eapply mutex_pend_wait_execution_result_wait_tail; eassumption. }
  pose proof (mutex_pend_api_safe_return _ _ _ _ _ _ _ _ _ _ _ (proj1 Hresult) PreH4) as Hsafe.
  match goal with HS : interrupt_saved_value mask cpu_sr_value |- _ => rewrite (proj2 HS) end.
  sep_apply_l_atomic (proj2 (sem_pend_continuation_save_input_owned
    owned critical saved_local sg returned mask after)).
  unfold mutex_pend_api_post; Exists returned after code; entailer!.
Qed.
