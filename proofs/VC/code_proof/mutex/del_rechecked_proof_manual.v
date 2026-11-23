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
From Ucos2Verify.VC.code.mutex Require Import del_rechecked_goal.
From Ucos2Verify.VC.code.mutex Require Import del_rechecked_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_sched_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_continuation_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_program_storage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_callsite_proofs.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_resource_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_runtime_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_stage_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_source_contract_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_call_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_history_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_region_spec.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef.
Local Open Scope sac_scope.
Local Open Scope sac.



Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_parent_proofs.

Lemma proof_of_OSMutexDel_safety_wit_4 : OSMutexDel_safety_wit_4.
Proof.
  unfold OSMutexDel_safety_wit_4; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_5 : OSMutexDel_safety_wit_5.
Proof.
  unfold OSMutexDel_safety_wit_5; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_14 : OSMutexDel_safety_wit_14.
Proof.
  unfold OSMutexDel_safety_wit_14; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_15 : OSMutexDel_safety_wit_15.
Proof.
  unfold OSMutexDel_safety_wit_15; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_16 : OSMutexDel_safety_wit_16.
Proof.
  unfold OSMutexDel_safety_wit_16; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_17 : OSMutexDel_safety_wit_17.
Proof.
  unfold OSMutexDel_safety_wit_17; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_18 : OSMutexDel_safety_wit_18.
Proof.
  unfold OSMutexDel_safety_wit_18; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_19 : OSMutexDel_safety_wit_19.
Proof.
  unfold OSMutexDel_safety_wit_19; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_20 : OSMutexDel_safety_wit_20.
Proof.
  unfold OSMutexDel_safety_wit_20; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_21 : OSMutexDel_safety_wit_21.
Proof.
  unfold OSMutexDel_safety_wit_21; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_safety_wit_39 : OSMutexDel_safety_wit_39.
Proof.
  unfold OSMutexDel_safety_wit_39; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_1 : OSMutexDel_entail_wit_2_1.
Proof.
  unfold OSMutexDel_entail_wit_2_1; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 acquired entry_2;
 unfold mutex_del_parent_prepared; entailer!; sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_2 : OSMutexDel_entail_wit_2_2.
Proof.
  unfold OSMutexDel_entail_wit_2_2; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 acquired entry_2;
 unfold mutex_del_parent_prepared; entailer!; sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_3 : OSMutexDel_entail_wit_2_3.
Proof.
  unfold OSMutexDel_entail_wit_2_3; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 acquired entry_2;
 unfold mutex_del_parent_prepared; entailer!.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_4 : OSMutexDel_entail_wit_2_4.
Proof.
  unfold OSMutexDel_entail_wit_2_4; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 acquired entry_2;
 unfold mutex_del_parent_prepared; entailer!.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_5 : OSMutexDel_entail_wit_2_5.
Proof.
  unfold OSMutexDel_entail_wit_2_5; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 acquired entry_2;
  unfold mutex_del_parent_prepared; Intros; entailer!.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_6 : OSMutexDel_entail_wit_2_6.
Proof.
  unfold OSMutexDel_entail_wit_2_6; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 acquired entry_2;
  unfold mutex_del_parent_prepared; Intros; entailer!.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_7 : OSMutexDel_entail_wit_2_7.
Proof.
  unfold OSMutexDel_entail_wit_2_7; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 acquired entry_2;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_2_8 : OSMutexDel_entail_wit_2_8.
Proof.
  unfold OSMutexDel_entail_wit_2_8; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 acquired entry_2;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_1 : OSMutexDel_entail_wit_3_1.
Proof.
  unfold OSMutexDel_entail_wit_3_1; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_2 : OSMutexDel_entail_wit_3_2.
Proof.
  unfold OSMutexDel_entail_wit_3_2; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_3 : OSMutexDel_entail_wit_3_3.
Proof.
  unfold OSMutexDel_entail_wit_3_3; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_4 : OSMutexDel_entail_wit_3_4.
Proof.
  unfold OSMutexDel_entail_wit_3_4; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_5 : OSMutexDel_entail_wit_3_5.
Proof.
  unfold OSMutexDel_entail_wit_3_5; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_6 : OSMutexDel_entail_wit_3_6.
Proof.
  unfold OSMutexDel_entail_wit_3_6; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_7 : OSMutexDel_entail_wit_3_7.
Proof.
  unfold OSMutexDel_entail_wit_3_7; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_8 : OSMutexDel_entail_wit_3_8.
Proof.
  unfold OSMutexDel_entail_wit_3_8; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (mutex_priority_image (task_tcb64_image sg node) retval) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_update_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!; first [solve [sep_apply_r_atomic Hmerge; unfold mutex_del_priority_output; entailer!] | solve [
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence]].
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_9 : OSMutexDel_entail_wit_3_9.
Proof.
  unfold OSMutexDel_entail_wit_3_9; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_10 : OSMutexDel_entail_wit_3_10.
Proof.
  unfold OSMutexDel_entail_wit_3_10; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_11 : OSMutexDel_entail_wit_3_11.
Proof.
  unfold OSMutexDel_entail_wit_3_11; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_12 : OSMutexDel_entail_wit_3_12.
Proof.
  unfold OSMutexDel_entail_wit_3_12; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_13 : OSMutexDel_entail_wit_3_13.
Proof.
  unfold OSMutexDel_entail_wit_3_13; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_14 : OSMutexDel_entail_wit_3_14.
Proof.
  unfold OSMutexDel_entail_wit_3_14; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_15 : OSMutexDel_entail_wit_3_15.
Proof.
  unfold OSMutexDel_entail_wit_3_15; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_16 : OSMutexDel_entail_wit_3_16.
Proof.
  unfold OSMutexDel_entail_wit_3_16; right; intros;
 pose proof PreH21 as Hentry;
 pose proof Hentry as [Hvalid [He [Ht [Hm Hu]]]];
 destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
 pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
 pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
 pose proof PreH18 as [_ [Hpointer [Hcount _]]];
 rewrite Hcount, Hcast, Hdecode in *;
 rewrite PreH20, Hgroup in PreH19;
 rewrite PreH11 in *;
 pose proof (tcb64_storage_merge (task_slot_addr sg owner) (task_tcb64_image sg node) TCBPrio) as Hstorage;
 cbn [tcb_cell tcb_field_address task_tcb64_image] in Hstorage; sep_apply_l_atomic Hstorage;
 assert (Howner : mutex_2.(mfOwner) = Some owner) by (eapply mutex_del_parent_owner_from_pointer; eauto); 
 assert (Haddress : tcb_field_address (task_slot_addr sg owner) TCBStkPtr = task_slot_addr sg owner) by (unfold mutex_del_parent_layout in PreH29; intuition); 
 sep_apply_l_atomic (mutex_del_parent_storage_pointer_not_reserved
   (task_slot_addr sg owner) (task_tcb64_image sg node) node.(tcbStkPtr) Haddress eq_refl);
 Intros_p Hnotreserved;
 assert (Henabled : mutex_pcp_enabled sg mutex_2) by (pose proof (proj1 Hvalid) as Hprofile;
   unfold mutex_pcp_enabled, selected_kernel_profile, valid_stable_glob_vars in *; intuition congruence); 
 assert (Hprepare : mutex_del_prepare sg mutex_2 entry_2
   (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval)) by (unfold mutex_del_prepare;
   destruct (Z.eq_dec mutex_2.(mfPCP) sg.(osPrioMutexCeilDis)); [contradiction|];
   rewrite Howner; exists node, retval; auto); 
 pose proof PreH29 as [_ [_ [_ [_ [Htable [Hrows [Hgrp [Hcurrent [Hcurprio _]]]]]]]]];
 rewrite Htable, Hrows, Hgrp, Hcurrent, Hcurprio;
 pose proof (mutex_del_owner_priority_skip_merge sg entry_2 eid acquired mutex_2 owner node retval
   Hvalid Hu He Ht Hm Howner Henabled PreH12 Hnotreserved PreH2 PreH1) as Hmerge;
 unfold mutex_del_priority_input in Hmerge;
 sepcon_assoc_change;
 sep_apply_l_atomic Hmerge;
 Exists (mutex_del_owner_priority_state sg entry_2 mutex_2.(mfPCP) owner node retval) mutex_2 entry_2 acquired;
 unfold mutex_del_parent_prepared; entailer!;
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_17 : OSMutexDel_entail_wit_3_17.
Proof.
  unfold OSMutexDel_entail_wit_3_17; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_18 : OSMutexDel_entail_wit_3_18.
Proof.
  unfold OSMutexDel_entail_wit_3_18; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_19 : OSMutexDel_entail_wit_3_19.
Proof.
  unfold OSMutexDel_entail_wit_3_19; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_20 : OSMutexDel_entail_wit_3_20.
Proof.
  unfold OSMutexDel_entail_wit_3_20; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_21 : OSMutexDel_entail_wit_3_21.
Proof.
  unfold OSMutexDel_entail_wit_3_21; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_22 : OSMutexDel_entail_wit_3_22.
Proof.
  unfold OSMutexDel_entail_wit_3_22; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_23 : OSMutexDel_entail_wit_3_23.
Proof.
  unfold OSMutexDel_entail_wit_3_23; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_24 : OSMutexDel_entail_wit_3_24.
Proof.
  unfold OSMutexDel_entail_wit_3_24; right; intros;
  pose proof PreH9 as Hentry;
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) (proj1 Hentry)) as Hgroup;
  pose proof PreH6 as [_ [Hpointer [Hcount _]]];
  rewrite Hcount, Hcast, Hdecode in *;
  rewrite PreH8, Hgroup in PreH7;
  sep_apply_l_atomic (mutex_del_parent_prepare_unowned sg eid entry_2 acquired mutex_2 Hentry PreH5 ltac:(congruence));
  Exists (mutex_del_released_state entry_2 mutex_2.(mfPCP)) mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_25 : OSMutexDel_entail_wit_3_25.
Proof.
  unfold OSMutexDel_entail_wit_3_25; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_26 : OSMutexDel_entail_wit_3_26.
Proof.
  unfold OSMutexDel_entail_wit_3_26; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_27 : OSMutexDel_entail_wit_3_27.
Proof.
  unfold OSMutexDel_entail_wit_3_27; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_28 : OSMutexDel_entail_wit_3_28.
Proof.
  unfold OSMutexDel_entail_wit_3_28; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_29 : OSMutexDel_entail_wit_3_29.
Proof.
  unfold OSMutexDel_entail_wit_3_29; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_30 : OSMutexDel_entail_wit_3_30.
Proof.
  unfold OSMutexDel_entail_wit_3_30; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_31 : OSMutexDel_entail_wit_3_31.
Proof.
  unfold OSMutexDel_entail_wit_3_31; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_entail_wit_3_32 : OSMutexDel_entail_wit_3_32.
Proof.
  unfold OSMutexDel_entail_wit_3_32; right; intros;
  pose proof PreH5 as Hentry;
  pose proof Hentry as [Hvalid [He _]];
  destruct (mutex_del_parent_count_decode sg eid entry_2 acquired mutex_2 Hentry) as [_ [_ Hdecode]];
  pose proof (mutex_del_parent_cast_count sg eid entry_2 acquired mutex_2 Hentry) as Hcast;
  pose proof (mutex_del_parent_group_cast sg entry_2 acquired.(waitList) Hvalid) as Hgroup;
  pose proof PreH13 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH14) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite PreH11, Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH2 as [-> [-> [-> [-> ->]]]];
  rewrite Hcast, Hdecode in PreH1;
  rewrite PreH4, Hgroup in PreH3;
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg entry_2 eid acquired He);
  sep_apply_l_atomic (mutex_del_parent_prepare_disabled sg eid entry_2 acquired mutex_2 Hentry PreH1);
  Exists entry_2 mutex_2 entry_2 acquired;
  unfold mutex_del_parent_prepared; Intros; entailer!;
      try solve [match goal with
      | H : mutex_del_scheduler_admission ?s ?c ?p ?b ?e ?o |-
          mutex_del_scheduler_admission ?s ?c ?p2 ?b ?e ?o =>
          replace p2 with p by congruence; exact H
      end];
      try congruence; unfold mutex_del_parent_waiting_flag;
      destruct (Z.eqb (encode_event_wait_grp acquired.(waitList) entry_2.(TskState)) 0) eqn:Hflag;
      [apply Z.eqb_eq in Hflag|apply Z.eqb_neq in Hflag]; congruence.
Qed.

Lemma proof_of_OSMutexDel_return_wit_1 : OSMutexDel_return_wit_1.
Proof.
  unfold OSMutexDel_return_wit_1; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_2 : OSMutexDel_return_wit_2.
Proof.
  unfold OSMutexDel_return_wit_2; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_3 : OSMutexDel_return_wit_3.
Proof.
  unfold OSMutexDel_return_wit_3; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_4 : OSMutexDel_return_wit_4.
Proof.
  unfold OSMutexDel_return_wit_4; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_5 : OSMutexDel_return_wit_5.
Proof.
  unfold OSMutexDel_return_wit_5; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_6 : OSMutexDel_return_wit_6.
Proof.
  unfold OSMutexDel_return_wit_6; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_7 : OSMutexDel_return_wit_7.
Proof.
  unfold OSMutexDel_return_wit_7; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_8 : OSMutexDel_return_wit_8.
Proof.
  unfold OSMutexDel_return_wit_8; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_9 : OSMutexDel_return_wit_9.
Proof.
  unfold OSMutexDel_return_wit_9; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_10 : OSMutexDel_return_wit_10.
Proof.
  unfold OSMutexDel_return_wit_10; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_11 : OSMutexDel_return_wit_11.
Proof.
  unfold OSMutexDel_return_wit_11; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_12 : OSMutexDel_return_wit_12.
Proof.
  unfold OSMutexDel_return_wit_12; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_13 : OSMutexDel_return_wit_13.
Proof.
  unfold OSMutexDel_return_wit_13; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_14 : OSMutexDel_return_wit_14.
Proof.
  unfold OSMutexDel_return_wit_14; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_15 : OSMutexDel_return_wit_15.
Proof.
  unfold OSMutexDel_return_wit_15; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Left; Right.
  match goal with H : mutex_del_parent_critical_observation ?s ?e ?o ?r ?c ?request ?entry ?checkpoint |- _ =>
    Exists entry checkpoint request
  end.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  apply _derivable1_andp_intros; [entailer!|].
  try (unfold mutex_del_continuation_return;
    match goal with |- context [mutex_del_continuation_return_at _ _ _ _ _ _ _ ?returned ?current] =>
      Exists returned current end); entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_16 : OSMutexDel_return_wit_16.
Proof.
  unfold OSMutexDel_return_wit_16; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  unfold mutex_del_continuation_post; Right; Exists entry kind.
  unfold mutex_del_runtime_save_facts in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end; entailer!.
Qed.

Lemma proof_of_OSMutexDel_return_wit_17 : OSMutexDel_return_wit_17.
Proof.
  unfold OSMutexDel_return_wit_17; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  subst.
  unfold mutex_del_continuation_post; Left; Left.
  apply _derivable1_andp_intros; [|reflexivity].
  unfold mutex_del_continuation_entry; Intros environment.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources.
  rewrite kernel_program_inv_split_unmap.
  Intros.
  sep_apply_l_atomic (mutex_query_interrupt_split_full sg before); Intros_p Hvalid.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) before.(IntrState).(intNesting)); Intros_p Hrange.
  assert (Hcast : unsigned_last_nbits before.(IntrState).(intNesting) 32 = before.(IntrState).(intNesting)).
  { apply unsigned_last_nbits_eq; change (0 <= before.(IntrState).(intNesting) <= 255) in Hrange;
    change (0 <= before.(IntrState).(intNesting) < 4294967296); lia. }
  rewrite Hcast in PreH1.
  assert (Htype : event_slot_type_value before.(EventState) eid = 4).
  { unfold event_slot_type_value in *;
    destruct (inUsedEventStates (EventState before) eid) as [event|];
      [destruct event.(eventType)|]; vm_compute in PreH2 |- *; congruence. }
  entailer!; exists OS_ERR_DEL_ISR; split; [|reflexivity]; rewrite Htype;
    apply mutex_del_before_save_isr; [assumption|lia].
Qed.

Lemma proof_of_OSMutexDel_return_wit_18 : OSMutexDel_return_wit_18.
Proof.
  unfold OSMutexDel_return_wit_18; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  subst; unfold mutex_del_continuation_post; Left; Left.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists OS_ERR_EVENT_TYPE; split; [|reflexivity].
  apply mutex_del_before_save_wrong_type; [assumption|].
  intro Heq; rewrite Heq in PreH1; vm_compute in PreH1; contradiction.
Qed.

Lemma proof_of_OSMutexDel_return_wit_19 : OSMutexDel_return_wit_19.
Proof.
  unfold OSMutexDel_return_wit_19; right; intros.
  try (match goal with |- context [mutex_del_continuation_source_return_at ?env ?ext ?plat ?local ?s ?c ?m ?r ?st] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_at_forget env ext plat local s c m r st) end).
  try (match goal with |- context [mutex_del_continuation_source_return ?env ?ext ?plat ?local ?s ?c ?m] =>
    sep_apply_l_atomic (mutex_del_continuation_source_return_forget env ext plat local s c m) end).

  subst; unfold mutex_del_continuation_post; Left; Left.
  apply _derivable1_andp_intros; [|entailer!].
  entailer!; exists OS_ERR_PEVENT_NULL; split; reflexivity.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_15_pure : OSMutexDel_partial_solve_wit_15_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_15_pure; left; intros;
 match goal with |- context [store_uchar ?p ?v] =>
   prop_apply_p (store_uchar_range p v); Intros_p Hrange;
   assert (Hcast : unsigned_last_nbits v 32 = v) by
     (apply unsigned_last_nbits_eq; unfold Byte.max_unsigned in *; simpl in *; lia)
 end; rewrite Hcast in PreH1; entailer!.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_20_pure : OSMutexDel_partial_solve_wit_20_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_20_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_21_pure : OSMutexDel_partial_solve_wit_21_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_21_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_26_pure : OSMutexDel_partial_solve_wit_26_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_26_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_27_pure : OSMutexDel_partial_solve_wit_27_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_27_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_28_pure : OSMutexDel_partial_solve_wit_28_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_28_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_29_pure : OSMutexDel_partial_solve_wit_29_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_29_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_32_pure : OSMutexDel_partial_solve_wit_32_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_32_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_33_pure : OSMutexDel_partial_solve_wit_33_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_33_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_34_pure : OSMutexDel_partial_solve_wit_34_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_34_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_35_pure : OSMutexDel_partial_solve_wit_35_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_35_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_47_pure : OSMutexDel_partial_solve_wit_47_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_47_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_51_pure : OSMutexDel_partial_solve_wit_51_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_51_pure; left; intros;
  assert (Hwaiting : mutex_del_parent_waiting sg eid entry) by (exists acquired, mutex; split; [assumption|];
    intro Hz; rewrite PreH2, Hz in PreH1; vm_compute in PreH1; contradiction); 
  entailer!.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_52_pure : OSMutexDel_partial_solve_wit_52_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_52_pure; left; intros;
  assert (Hwaiting : mutex_del_parent_waiting sg eid entry) by (exists acquired, mutex; split; [assumption|];
    intro Hz; rewrite PreH2, Hz in PreH1; vm_compute in PreH1; contradiction); 
  entailer!.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_75_pure : OSMutexDel_partial_solve_wit_75_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_75_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_76_pure : OSMutexDel_partial_solve_wit_76_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_76_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_77_pure : OSMutexDel_partial_solve_wit_77_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_77_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_78_pure : OSMutexDel_partial_solve_wit_78_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_78_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_79_pure : OSMutexDel_partial_solve_wit_79_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_79_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_80_pure : OSMutexDel_partial_solve_wit_80_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_80_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_81_pure : OSMutexDel_partial_solve_wit_81_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_81_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_82_pure : OSMutexDel_partial_solve_wit_82_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_82_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_83_pure : OSMutexDel_partial_solve_wit_83_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_83_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_84_pure : OSMutexDel_partial_solve_wit_84_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_84_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_85_pure : OSMutexDel_partial_solve_wit_85_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_85_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_86_pure : OSMutexDel_partial_solve_wit_86_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_86_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_87_pure : OSMutexDel_partial_solve_wit_87_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_87_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_88_pure : OSMutexDel_partial_solve_wit_88_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_88_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_89_pure : OSMutexDel_partial_solve_wit_89_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_89_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_90_pure : OSMutexDel_partial_solve_wit_90_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_90_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_99_pure : OSMutexDel_partial_solve_wit_99_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_99_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_100_pure : OSMutexDel_partial_solve_wit_100_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_100_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_101_pure : OSMutexDel_partial_solve_wit_101_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_101_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_102_pure : OSMutexDel_partial_solve_wit_102_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_102_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_103_pure : OSMutexDel_partial_solve_wit_103_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_103_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_104_pure : OSMutexDel_partial_solve_wit_104_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_104_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_105_pure : OSMutexDel_partial_solve_wit_105_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_105_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_106_pure : OSMutexDel_partial_solve_wit_106_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_106_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_107_pure : OSMutexDel_partial_solve_wit_107_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_107_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_108_pure : OSMutexDel_partial_solve_wit_108_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_108_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_109_pure : OSMutexDel_partial_solve_wit_109_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_109_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_110_pure : OSMutexDel_partial_solve_wit_110_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_110_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_111_pure : OSMutexDel_partial_solve_wit_111_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_111_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_112_pure : OSMutexDel_partial_solve_wit_112_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_112_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_113_pure : OSMutexDel_partial_solve_wit_113_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_113_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_114_pure : OSMutexDel_partial_solve_wit_114_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_114_pure; first [left | idtac]; intros; unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_156_pure : OSMutexDel_partial_solve_wit_156_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_156_pure; left; intros;
  match goal with |- context [store_uchar ?p (encode_event_wait_grp ?w ?tasks)] =>
    prop_apply_p (store_uchar_range p (encode_event_wait_grp w tasks));
    let Hr := fresh "Hgroup_range" in Intros_p Hr;
    let HC := fresh "Hgroup_cast" in
    assert (HC : unsigned_last_nbits (encode_event_wait_grp w tasks) 32 = encode_event_wait_grp w tasks)
      by (apply unsigned_last_nbits_eq;
          change (0 <= encode_event_wait_grp w tasks <= 255) in Hr;
          change (0 <= encode_event_wait_grp w tasks < 4294967296); lia);
    rewrite HC in *
  end; entailer!.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_157_pure : OSMutexDel_partial_solve_wit_157_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_157_pure; left; intros;
  unfold mutex_del_parent_wake_call_rest; Intros; entailer!;
    unfold mutex_del_parent_layout in *; tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_159_pure : OSMutexDel_partial_solve_wit_159_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_159_pure; left; intros;
  match goal with |- context [store_uchar ?p (encode_event_wait_grp ?w ?tasks)] =>
    prop_apply_p (store_uchar_range p (encode_event_wait_grp w tasks));
    let Hr := fresh "Hgroup_range" in Intros_p Hr;
    let HC := fresh "Hgroup_cast" in
    assert (HC : unsigned_last_nbits (encode_event_wait_grp w tasks) 32 = encode_event_wait_grp w tasks)
      by (apply unsigned_last_nbits_eq;
          change (0 <= encode_event_wait_grp w tasks <= 255) in Hr;
          change (0 <= encode_event_wait_grp w tasks < 4294967296); lia);
    rewrite HC in *
  end; entailer!.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_161_pure : OSMutexDel_partial_solve_wit_161_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_161_pure; left; intros;
  unfold mutex_del_parent_drained_rest; Intros_p Hfacts;
  destruct (mutex_del_parent_loop_count_decode sg eid entry_2 prepared_2 state current_2 event mutex_2 priorities (proj1 Hfacts))
    as [_ [_ Hcast]];
  pose proof PreH1 as [_ [_ [Hcount _]]]; rewrite <- Hcount in Hcast; entailer!.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_166_pure : OSMutexDel_partial_solve_wit_166_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_166_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_167_pure : OSMutexDel_partial_solve_wit_167_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_167_pure; left; intros; try (match goal with |- context [store_ushort ?p ?v] => prop_apply_p (store_ushort_range p v); Intros_p Howned_range end); unfold mutex_del_parent_entry, mutex_del_parent_event_values, mutex_del_parent_recycle_values, mutex_del_runtime_save_facts, mutex_del_parent_ceiling, mutex_del_parent_waiting_flag in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; subst; entailer!; try lia; try tauto.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_214_pure : OSMutexDel_partial_solve_wit_214_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_214_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_215_pure : OSMutexDel_partial_solve_wit_215_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_215_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_216_pure : OSMutexDel_partial_solve_wit_216_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_216_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_217_pure : OSMutexDel_partial_solve_wit_217_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_217_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_218_pure : OSMutexDel_partial_solve_wit_218_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_218_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_219_pure : OSMutexDel_partial_solve_wit_219_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_219_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_220_pure : OSMutexDel_partial_solve_wit_220_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_220_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_partial_solve_wit_221_pure : OSMutexDel_partial_solve_wit_221_pure.
Proof.
  unfold OSMutexDel_partial_solve_wit_221_pure; left; intros;
  match goal with H : mutex_del_parent_entry ?sg ?eid ?entry ?event ?mutex |- _ =>
    pose proof (mutex_del_parent_count_decode sg eid entry event mutex H) as Hdecode;
    pose proof (mutex_del_parent_cast_count sg eid entry event mutex H) as Hcast
  end;
  unfold mutex_del_parent_event_values, mutex_del_parent_recycle_values in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end;
  subst;
  repeat match goal with HC : unsigned_last_nbits ?v 8 = ?v |- _ => rewrite HC in * end;
  unfold mutex_del_parent_ceiling_at, mutex_del_parent_owner_pointer,
    mutex_del_parent_ceiling, mutex_del_parent_live;
  entailer!; eauto 12.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_1 : OSMutexDel_which_implies_wit_1.
Proof.
  unfold OSMutexDel_which_implies_wit_1; left; intros.
  apply mutex_del_continuation_entry_split.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_2 : OSMutexDel_which_implies_wit_2.
Proof.
  unfold OSMutexDel_which_implies_wit_2; left; intros;
  destruct PreH3 as [Hz|[Hnz [Haddr [Hid Hslot]]]]; [contradiction|];
  subst pe; destruct PreH1 as [_ [Htable _]];
  pose proof (proj1 (proj1 (Htable eid Hid))) as Htype;
  rewrite mutex_query_closed_equiv, Htype;
  sep_apply_l_atomic (sem_query_type_split_full sg before eid observed Hslot);
  entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_3 : OSMutexDel_which_implies_wit_3.
Proof.
  unfold OSMutexDel_which_implies_wit_3; left; intros;
  subst pe; destruct PreH1 as [_ [Htable _]];
  pose proof (proj1 (proj1 (Htable eid PreH2))) as Htype;
  rewrite Htype, mutex_query_closed_equiv;
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH4);
  entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_4 : OSMutexDel_which_implies_wit_4.
Proof.
  unfold OSMutexDel_which_implies_wit_4; left; intros.
  apply mutex_del_continuation_entry_merge.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_5 : OSMutexDel_which_implies_wit_5.
Proof.
  unfold OSMutexDel_which_implies_wit_5; left; intros;
  subst pe; destruct PreH1 as [_ [Htable [Hint _]]];
  pose proof (proj1 (proj1 (Htable eid PreH2))) as Htype;
  rewrite Htype, Hint;
  sep_apply_l_atomic (sem_query_type_merge_full sg before eid PreH4);
  sep_apply_l_atomic (mutex_query_interrupt_split_full sg before);
  entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_6 : OSMutexDel_which_implies_wit_6.
Proof.
  unfold OSMutexDel_which_implies_wit_6; left; intros;
  destruct PreH1 as [_ [_ [Hint _]]];
  rewrite Hint, mutex_query_closed_equiv;
  sep_apply_l_atomic (mutex_query_interrupt_merge_full sg before
    before.(IntrState).(intNesting) PreH2 eq_refl);
  entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_7 : OSMutexDel_which_implies_wit_7.
Proof.
  unfold OSMutexDel_which_implies_wit_7; left; intros.
  apply mutex_del_continuation_entry_merge.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_8 : OSMutexDel_which_implies_wit_8.
Proof.
  unfold OSMutexDel_which_implies_wit_8; left; intros;
 destruct PreH1 as [_ [_ [Hint _]]];
 rewrite Hint;
 prop_apply_p (store_uchar_range sg.(g_OSIntNesting) before.(IntrState).(intNesting));
 Intros_p H;
 assert (Hcast : unsigned_last_nbits before.(IntrState).(intNesting) 32 = before.(IntrState).(intNesting)) by (apply unsigned_last_nbits_eq; change (0 <= before.(IntrState).(intNesting) < 4294967296);
   change (0 <= before.(IntrState).(intNesting) <= 255) in H; lia); 
 assert (Htype : event_slot_type_value before.(EventState) eid = 4) by (unfold event_slot_type_value in *;
   destruct (inUsedEventStates (EventState before) eid) as [event|]; [destruct event.(eventType)|];
   vm_compute in PreH4 |- *; congruence); 
 assert (Hprefix : mutex_del_parent_prefix_ok pe before eid) by (unfold mutex_del_parent_prefix_ok;
   apply (proj2 (mutex_del_before_save_continues_iff pe (event_slot_type_value before.(EventState) eid)
     before.(IntrState).(intNesting) ltac:(change (0 <= before.(IntrState).(intNesting) <= 255) in H; lia)));
   rewrite Hcast in PreH5; repeat split; try assumption;
   change (0 <= before.(IntrState).(intNesting) <= 255) in H; lia); 
 unfold mutex_del_parent_save_pre; rewrite mutex_query_closed_equiv;
 sep_apply_l_atomic (mutex_query_interrupt_merge_full sg before before.(IntrState).(intNesting) PreH2 eq_refl);
 entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_9 : OSMutexDel_which_implies_wit_9.
Proof.
  unfold OSMutexDel_which_implies_wit_9; left; intros.
  apply mutex_del_continuation_entry_merge.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_10 : OSMutexDel_which_implies_wit_10.
Proof.
  unfold OSMutexDel_which_implies_wit_10; left; intros.
  unfold mutex_del_continuation_entry; Intros environment.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources.
  Exists environment; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_11 : OSMutexDel_which_implies_wit_11.
Proof.
  unfold OSMutexDel_which_implies_wit_11; left; intros.
  apply _derivable1_andp_intros.
  - entailer!.
  - eapply mutex_del_continuation_source_save_admission; eassumption.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_12 : OSMutexDel_which_implies_wit_12.
Proof.
  unfold OSMutexDel_which_implies_wit_12; left; intros.
  unfold mutex_del_continuation_source_save_post; Intros entry; Exists entry; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_13 : OSMutexDel_which_implies_wit_13.
Proof.
  unfold OSMutexDel_which_implies_wit_13; left; intros.
  rewrite (mutex_del_parent_recheck_type_address sg pe eid PreH1 PreH2 PreH3), PreH3.
  apply mutex_del_continuation_type_split; exact PreH2.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_14 : OSMutexDel_which_implies_wit_14.
Proof.
  unfold OSMutexDel_which_implies_wit_14; left; intros.
  rewrite (mutex_del_parent_recheck_type_address sg pe eid PreH1 PreH2 PreH3), PreH3.
  sep_apply_l_atomic (mutex_del_continuation_type_merge source_env external platform saved_local sg context eid entry kind).
  unfold mutex_del_runtime_program_restore_pre; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_15 : OSMutexDel_which_implies_wit_15.
Proof.
  unfold OSMutexDel_which_implies_wit_15; left; intros.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_continuation_source_restore_merge; [left; reflexivity|assumption|assumption].
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_16 : OSMutexDel_which_implies_wit_16.
Proof.
  unfold OSMutexDel_which_implies_wit_16; left; intros.
  rewrite (mutex_del_parent_recheck_type_address sg pe eid PreH1 PreH2 PreH3), PreH3.
  prop_apply_p (store_uchar_range (event_addr sg eid) kind); Intros_p Hrange.
  assert (Hcast : unsigned_last_nbits kind 32 = kind).
  { apply unsigned_last_nbits_eq; change (0 <= kind <= 255) in Hrange;
      change (0 <= kind < 4294967296); lia. }
  assert (Hkind : kind = 4) by congruence; subst kind.
  apply mutex_del_continuation_type_mutex.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_17 : OSMutexDel_which_implies_wit_17.
Proof.
  unfold OSMutexDel_which_implies_wit_17; right; intros; subst pe;
  destruct PreH1 as [_ [Htable _]];
  pose proof (proj1 (proj2 (Htable eid PreH2))) as Hgrp;
  rewrite Hgrp;
  destruct PreH4 as [Hvalid [He _]];
  sep_apply_l_atomic (mutex_del_raw_split_event sg entry eid current He);
  pose proof (event_storage_split_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) (event_image sg entry.(TskState) current)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hsplit;
  cbn [event_cell event_image event_field_offset] in Hsplit;
  sep_apply_l_atomic Hsplit;
  unfold mutex_del_event_group_frame; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_18 : OSMutexDel_which_implies_wit_18.
Proof.
  unfold OSMutexDel_which_implies_wit_18; left; intros; subst pe initial_group;
  destruct PreH1 as [_ [Htable _]];
  pose proof (proj1 (proj2 (Htable eid PreH2))) as Hgrp;
  rewrite Hgrp;
  unfold mutex_del_event_group_frame;
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) (event_image sg entry.(TskState) current)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hmerge;
  cbn [event_cell event_image event_field_offset] in Hmerge;
  sep_apply_l_atomic Hmerge;
  sep_apply_l_atomic (mutex_del_raw_merge_event sg entry eid current PreH5);
  unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_19 : OSMutexDel_which_implies_wit_19.
Proof.
  unfold OSMutexDel_which_implies_wit_19; left; intros; unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_20 : OSMutexDel_which_implies_wit_20.
Proof.
  unfold OSMutexDel_which_implies_wit_20; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH4 as [Hvalid [He _]];
  sep_apply_l_atomic (mutex_del_parent_event_core_split sg entry eid current He);
  Exists (encode_event_type current.(eventType)) (encode_event_ptr_value sg current)
    (encode_event_cnt_value current) (encode_event_wait_grp current.(waitList) entry.(TskState))
    (event_encode_pool_link sg (hd_error entry.(EventState).(unUsedEventStates)));
  unfold mutex_del_parent_event_values; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_21 : OSMutexDel_which_implies_wit_21.
Proof.
  unfold OSMutexDel_which_implies_wit_21; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH5 as [-> [-> [-> [-> ->]]]];
  apply mutex_del_parent_event_core_merge; assumption.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_22 : OSMutexDel_which_implies_wit_22.
Proof.
  unfold OSMutexDel_which_implies_wit_22; left; intros;
  pose proof (mutex_del_parent_enabled_ceiling_in_range sg eid entry pcp_v PreH3 PreH2)
    as Hrange;
  destruct PreH1 as [_ [_ [_ [_ [Htable _]]]]];
  rewrite Htable, UCOS2_raw_rep_priority_table_equiv;
  sep_apply_l_atomic (store_prio_tbl_split_cell sg entry.(TskState).(prioTbl) pcp_v Hrange);
  Exists (prio_tbl_entry_to_addr sg (entry.(TskState).(prioTbl) pcp_v)); entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_23 : OSMutexDel_which_implies_wit_23.
Proof.
  unfold OSMutexDel_which_implies_wit_23; left; intros; match goal with H : mutex_del_parent_layout _ |- _ => destruct H as [_ [_ [_ [_ [Hprio _]]]]]; rewrite Hprio end; apply mutex_del_released_resources_merge_cell; lia.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_24 : OSMutexDel_which_implies_wit_24.
Proof.
  unfold OSMutexDel_which_implies_wit_24; left; intros;
  destruct PreH2 as [event [mutex [[Hvalid [He [Ht [Hm Hu]]]] [Hceiling Hpointer]]]];
  unfold encode_event_ptr_value in Hpointer; rewrite Ht, Hm in Hpointer;
  destruct mutex.(mfOwner) as [owner|] eqn:Ho; [|simpl in Hpointer; congruence];
  cbn in Hpointer;
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]];
  destruct Hcross as [_ [Hsnap _]];
  destruct (Hsnap eid event mutex owner He Ht Hm Ho) as [node [base [snapshot [Hnode _]]]];
  sep_apply_l_atomic (mutex_del_released_resources_split_priority sg entry pcp_v owner node Hprofile Hnode);
  Exists node owner; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_25 : OSMutexDel_which_implies_wit_25.
Proof.
  unfold OSMutexDel_which_implies_wit_25; left; intros; subst ptcb_v;
  pose proof PreH3 as [Hprofile [Htasks _]];
  assert (Hprio : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto);
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto);
  unfold task_priority_in_range in Hprio; rewrite Hlowest in Hprio;
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8) by (destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
      node.(curPrio) ltac:(lia)) as [_ [Hy _]]; exact Hy); 
  pose proof (mutex_del_priority_input_fields sg node) as Hfields;
  destruct PreH1 as [_ [_ [_ [_ [Htable [Hrows [Hgroup [Hcurrent [Hcurprio _]]]]]]]]];
  unfold mutex_del_priority_input, mutex_del_scan_pre, mutex_priority_fallback;
  rewrite Htable, Hrows, Hgroup, Hcurrent, Hcurprio;
  entailer!; try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_26 : OSMutexDel_which_implies_wit_26.
Proof.
  unfold OSMutexDel_which_implies_wit_26; left; intros; exact (tcb64_storage_split ptcb_v (task_tcb64_image sg node) TCBPrio).
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_27 : OSMutexDel_which_implies_wit_27.
Proof.
  unfold OSMutexDel_which_implies_wit_27; left; intros; exact (tcb64_storage_merge ptcb_v (task_tcb64_image sg node) TCBPrio).
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_28 : OSMutexDel_which_implies_wit_28.
Proof.
  unfold OSMutexDel_which_implies_wit_28; left; intros;
  assert (Hresult : 0 <= prio_v < 64) by (unfold mutex_effective_priority_result in PreH4; intuition lia); 
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8) by (destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
      node.(curPrio) ltac:(lia)) as [_ [Hy _]]; exact Hy); 
  pose proof (mutex_del_priority_input_fields sg node) as Hfields;
  unfold mutex_del_rdy_pre; entailer!; try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_29 : OSMutexDel_which_implies_wit_29.
Proof.
  unfold OSMutexDel_which_implies_wit_29; left; intros; subst pe;
 unfold mutex_del_parent_prepared, mutex_del_wake_rep; Intros;
 destruct H as [Hentry Hprepare];
 pose proof (mutex_del_prepare_event_state_eq sg mutex entry prepared Hprepare) as Hevents;
 assert (He : mutex_query_lookup prepared eid current) by (unfold mutex_query_lookup; rewrite Hevents; exact (proj1 (proj2 Hentry))); 
 destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
 destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
 rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
 sep_apply_l_atomic (mutex_del_parent_event_core_split sg prepared eid current He);
 Exists (encode_event_type current.(eventType)) (encode_event_ptr_value sg current)
   (encode_event_cnt_value current) (encode_event_wait_grp current.(waitList) prepared.(TskState))
   (event_encode_pool_link sg (hd_error prepared.(EventState).(unUsedEventStates)));
 unfold mutex_del_parent_recycle_rest, mutex_del_parent_event_values; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_30 : OSMutexDel_which_implies_wit_30.
Proof.
  unfold OSMutexDel_which_implies_wit_30; left; intros; subst pe opt_in;
 pose proof PreH7 as [Hvalid [He [Ht [Hm Hu]]]];
 pose proof Hvalid as [_ [_ [_ [Hevents _]]]];
 destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]];
 pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg entry.(TskState) current.(waitList)
   (proj1 (Hentries eid current He))) PreH6) as Hempty;
 assert (Hzero : encode_event_wait_grp current.(waitList) prepared.(TskState) = 0)
   by (rewrite Hempty; reflexivity);
 assert (Hlookup : prepared.(EventState).(inUsedEventStates) eid = Some current) by (rewrite (mutex_del_prepare_event_state_eq sg mutex entry prepared PreH8); exact He); 
 assert (Hobs : mutex_del_parent_critical_observation sg eid 0 0 0 0 entry
   (mutex_del_recycle_state sg eid current prepared)) by (exists OS_ERR_NONE, false; split; [|split; reflexivity];
   exists current, mutex; split; [exact He|]; split; [exact Ht|]; split; [exact Hm|];
   destruct (Z.eq_dec 0 0); [|contradiction];
   destruct (Z.eq_dec (encode_event_wait_grp current.(waitList) entry.(TskState)) 0); [|contradiction];
   exists prepared; auto); 
 destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
 destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
 rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
 destruct PreH4 as [-> ->];
 unfold mutex_del_parent_recycle_rest; Intros;
 change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
 change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
 change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
 change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
 Exists (mutex_del_recycle_state sg eid current prepared);
 unfold mutex_del_runtime_program_restore_pre; entailer!; sep_apply_r_atomic (mutex_del_program_recycle_fields_merge sg eid mutex prepared current PreH9 Hlookup Hzero); entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_31 : OSMutexDel_which_implies_wit_31.
Proof.
  unfold OSMutexDel_which_implies_wit_31; left; intros.
  pose proof (mutex_del_observation_preserves_call_stage sg eid opt_in result_v error_v request_v
    entry checkpoint context PreH1 PreH3) as Hstage.
  pose proof (mutex_del_observation_schedule_request sg eid opt_in result_v error_v request_v
    entry checkpoint context PreH1 PreH3) as Hrequest.
  pose proof (mutex_del_observation_preserves_call_available sg eid opt_in result_v error_v request_v
    entry checkpoint context PreH3 PreH2) as Havailable.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_continuation_source_restore_merge; [|exact Hstage|exact Havailable].
  right; destruct PreH3 as [code [scheduled [Hrun Hvalues]]].
  exists eid, opt_in, (result_v, (code, scheduled)); exact Hrun.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_32 : OSMutexDel_which_implies_wit_32.
Proof.
  unfold OSMutexDel_which_implies_wit_32; left; intros.
  sep_apply_l_atomic (mutex_del_continuation_source_return_open source_env external platform saved_local sg context mask).
  Intros returned current; Exists current returned; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_33 : OSMutexDel_which_implies_wit_33.
Proof.
  unfold OSMutexDel_which_implies_wit_33; left; intros; subst pe opt_in;
  destruct PreH6 as [event [mutex [[Hvalid [He [Ht [Hf Hu]]]] Hwaiting]]];
  assert (Hobs : mutex_del_parent_critical_observation sg eid 0
    (event_addr sg eid) 73 0 entry entry) by (exists OS_ERR_TASK_WAITING, false; split; [exists event, mutex; split; [exact He|]; split; [exact Ht|];
      split; [exact Hf|]; destruct (Z.eq_dec 0 0); [|contradiction];
      destruct (Z.eq_dec (encode_event_wait_grp event.(waitList) entry.(TskState)) 0);
        [contradiction|auto] | split; reflexivity]); 
  unfold mutex_del_runtime_program_restore_pre; try rewrite kernel_program_inv_split_unmap; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_34 : OSMutexDel_which_implies_wit_34.
Proof.
  unfold OSMutexDel_which_implies_wit_34; left; intros.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_continuation_source_restore_merge; [left; reflexivity|assumption|assumption].
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_35 : OSMutexDel_which_implies_wit_35.
Proof.
  unfold OSMutexDel_which_implies_wit_35; left; intros.
  sep_apply_l_atomic (mutex_del_continuation_source_return_open source_env external platform saved_local sg context mask).
  Intros returned current; Exists current returned; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_36 : OSMutexDel_which_implies_wit_36.
Proof.
  unfold OSMutexDel_which_implies_wit_36; left; intros; unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_37 : OSMutexDel_which_implies_wit_37.
Proof.
  unfold OSMutexDel_which_implies_wit_37; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH4 as [Hvalid [He _]];
  sep_apply_l_atomic (mutex_del_parent_event_core_split sg entry eid current He);
  Exists (encode_event_type current.(eventType)) (encode_event_ptr_value sg current)
    (encode_event_cnt_value current) (encode_event_wait_grp current.(waitList) entry.(TskState))
    (event_encode_pool_link sg (hd_error entry.(EventState).(unUsedEventStates)));
  unfold mutex_del_parent_event_values; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_38 : OSMutexDel_which_implies_wit_38.
Proof.
  unfold OSMutexDel_which_implies_wit_38; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  destruct PreH5 as [-> [-> [-> [-> ->]]]];
  apply mutex_del_parent_event_core_merge; assumption.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_39 : OSMutexDel_which_implies_wit_39.
Proof.
  unfold OSMutexDel_which_implies_wit_39; left; intros;
  pose proof (mutex_del_parent_enabled_ceiling_in_range sg eid entry pcp_v PreH3 PreH2)
    as Hrange;
  destruct PreH1 as [_ [_ [_ [_ [Htable _]]]]];
  rewrite Htable, UCOS2_raw_rep_priority_table_equiv;
  sep_apply_l_atomic (store_prio_tbl_split_cell sg entry.(TskState).(prioTbl) pcp_v Hrange);
  Exists (prio_tbl_entry_to_addr sg (entry.(TskState).(prioTbl) pcp_v)); entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_40 : OSMutexDel_which_implies_wit_40.
Proof.
  unfold OSMutexDel_which_implies_wit_40; left; intros; match goal with H : mutex_del_parent_layout _ |- _ => destruct H as [_ [_ [_ [_ [Hprio _]]]]]; rewrite Hprio end; apply mutex_del_released_resources_merge_cell; lia.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_41 : OSMutexDel_which_implies_wit_41.
Proof.
  unfold OSMutexDel_which_implies_wit_41; left; intros;
  destruct PreH2 as [event [mutex [[Hvalid [He [Ht [Hm Hu]]]] [Hceiling Hpointer]]]];
  unfold encode_event_ptr_value in Hpointer; rewrite Ht, Hm in Hpointer;
  destruct mutex.(mfOwner) as [owner|] eqn:Ho; [|simpl in Hpointer; congruence];
  cbn in Hpointer;
  pose proof Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]];
  destruct Hcross as [_ [Hsnap _]];
  destruct (Hsnap eid event mutex owner He Ht Hm Ho) as [node [base [snapshot [Hnode _]]]];
  sep_apply_l_atomic (mutex_del_released_resources_split_priority sg entry pcp_v owner node Hprofile Hnode);
  Exists node owner; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_42 : OSMutexDel_which_implies_wit_42.
Proof.
  unfold OSMutexDel_which_implies_wit_42; left; intros; subst ptcb_v;
  pose proof PreH3 as [Hprofile [Htasks _]];
  assert (Hprio : task_priority_in_range sg node.(curPrio))
    by (unfold task_in_range in Htasks; intuition eauto);
  assert (Hlowest : sg.(osLowestPrio) = 63)
    by (unfold selected_kernel_profile, valid_stable_glob_vars in Hprofile; tauto);
  unfold task_priority_in_range in Hprio; rewrite Hlowest in Hprio;
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8) by (destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
      node.(curPrio) ltac:(lia)) as [_ [Hy _]]; exact Hy); 
  pose proof (mutex_del_priority_input_fields sg node) as Hfields;
  destruct PreH1 as [_ [_ [_ [_ [Htable [Hrows [Hgroup [Hcurrent [Hcurprio _]]]]]]]]];
  unfold mutex_del_priority_input, mutex_del_scan_pre, mutex_priority_fallback;
  rewrite Htable, Hrows, Hgroup, Hcurrent, Hcurprio;
  entailer!; try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_43 : OSMutexDel_which_implies_wit_43.
Proof.
  unfold OSMutexDel_which_implies_wit_43; left; intros; exact (tcb64_storage_split ptcb_v (task_tcb64_image sg node) TCBPrio).
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_44 : OSMutexDel_which_implies_wit_44.
Proof.
  unfold OSMutexDel_which_implies_wit_44; left; intros; exact (tcb64_storage_merge ptcb_v (task_tcb64_image sg node) TCBPrio).
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_45 : OSMutexDel_which_implies_wit_45.
Proof.
  unfold OSMutexDel_which_implies_wit_45; left; intros;
  assert (Hresult : 0 <= prio_v < 64) by (unfold mutex_effective_priority_result in PreH4; intuition lia); 
  assert (Hy : 0 <= tcb_y_of_prio node.(curPrio) < 8) by (destruct (priority_coordinates_in_range_and_encoding_eq__priority_encoding
      node.(curPrio) ltac:(lia)) as [_ [Hy _]]; exact Hy); 
  pose proof (mutex_del_priority_input_fields sg node) as Hfields;
  unfold mutex_del_rdy_pre; entailer!; try reflexivity; lia.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_46 : OSMutexDel_which_implies_wit_46.
Proof.
  unfold OSMutexDel_which_implies_wit_46; left; intros;
 apply mutex_del_program_prepared_loop_entry; assumption.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_47 : OSMutexDel_which_implies_wit_47.
Proof.
  unfold OSMutexDel_which_implies_wit_47; left; intros; subst pe;
  destruct PreH1 as [_ [Htable _]];
  pose proof (Htable eid PreH2) as Hlayout;
  pose proof (proj1 (proj2 Hlayout)) as Hgrp; rewrite Hgrp;
  unfold mutex_del_parent_loop_rest; Intros_p Hfacts;
  pose proof Hfacts as [_ [_ [_ [Hphase He]]]];
  unfold mutex_del_event_group_frame;
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) (event_image sg state.(TskState) event)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hmerge;
  cbn [event_cell event_image event_field_offset] in Hmerge;
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic Hmerge;
  sep_apply_l_atomic (mutex_del_raw_merge_event sg state eid event He);
  assert (Hpack : UCOS2_raw_rep sg state |-- mutex_del_wake_rep sg eid mutex state)
    by (unfold mutex_del_wake_rep; entailer!);
  sep_apply_l_atomic Hpack;
  sep_apply_l_atomic (mutex_del_wake_split sg eid mutex state event Hphase He PreH4 Hlayout);
  Intros tid old;
  Exists tid old; unfold mutex_del_parent_wake_call_rest; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_48 : OSMutexDel_which_implies_wit_48.
Proof.
  unfold OSMutexDel_which_implies_wit_48; left; intros; subst pe;
  destruct PreH1 as [_ [Htable _]];
  pose proof (proj1 (proj2 (Htable eid PreH2))) as Hgrp; rewrite Hgrp;
  unfold mutex_del_parent_wake_call_rest; Intros_p Hfacts;
  destruct Hfacts as [Hloop [Hnonzero Hcall]];
  pose proof Hloop as [Hentry [Hprepare [Hprefix [Hphase He]]]];
  sep_apply_l_atomic (mutex_del_wake_merge sg eid mutex state event tid old priority Hphase He Hcall);
  Intros_p Hstep;
  pose proof (mutex_del_wake_prefix_snoc sg eid prepared priorities state event priority
    (Ucos2Verify.lib.cross_module_invariants.event_wake_state sg state eid event tid old PendMutex 0 PendAbort)
    Hprefix He Hnonzero Hstep) as Hprefix_after;
  sep_apply_l_atomic (mutex_del_wake_guard_split sg eid mutex
    (Ucos2Verify.lib.cross_module_invariants.event_wake_state sg state eid event tid old PendMutex 0 PendAbort));
  Intros next; unfold mutex_del_wake_guard_rep; Intros_p Hnext;
  Exists (Ucos2Verify.lib.cross_module_invariants.event_wake_state sg state eid event tid old PendMutex 0 PendAbort)
    next (priorities ++ (priority :: nil));
  unfold mutex_del_parent_loop_rest, mutex_del_parent_loop_facts; entailer!; tauto.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_49 : OSMutexDel_which_implies_wit_49.
Proof.
  unfold OSMutexDel_which_implies_wit_49; left; intros; subst pe;
  destruct PreH1 as [_ [Htable _]];
  pose proof (proj1 (proj2 (Htable eid PreH2))) as Hgrp;
  rewrite Hgrp;
  unfold mutex_del_parent_loop_rest; Intros_p Hfacts;
  pose proof Hfacts as [_ [_ [_ [_ He]]]];
  unfold mutex_del_event_group_frame;
  pose proof (event_storage_merge_field sg.(osKernelConfig).(cfgEventNames)
    (event_pool_addr sg eid) (event_image sg state.(TskState) event)
    EventGrpField ltac:(unfold event_fields; simpl; tauto)) as Hmerge;
  cbn [event_cell event_image event_field_offset] in Hmerge;
  rewrite PreH4 in Hmerge;
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc;
  sep_apply_l_atomic Hmerge;
  sep_apply_l_atomic (mutex_del_raw_merge_event sg state eid event He);
  unfold mutex_del_parent_drained; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_50 : OSMutexDel_which_implies_wit_50.
Proof.
  unfold OSMutexDel_which_implies_wit_50; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  unfold mutex_del_parent_drained; Intros_p Hfacts;
  pose proof Hfacts as [[_ [_ [_ [_ He]]]] Hzero];
  sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event He);
  Exists (encode_event_type event.(eventType)) (encode_event_ptr_value sg event)
    (encode_event_cnt_value event) (encode_event_wait_grp event.(waitList) state.(TskState))
    (event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)));
  unfold mutex_del_parent_event_values, mutex_del_parent_drained_rest; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_51 : OSMutexDel_which_implies_wit_51.
Proof.
  unfold OSMutexDel_which_implies_wit_51; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  unfold mutex_del_parent_drained_rest; Intros_p Hfacts;
  pose proof Hfacts as [Hloop Hzero];
  pose proof Hloop as [_ [_ [_ [_ He]]]];
  destruct (mutex_del_parent_loop_count_decode sg eid entry prepared state current event mutex priorities Hloop)
    as [_ [Hdecode _]];
  destruct PreH4 as [-> [-> [-> [-> ->]]]];
  change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
  change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
  change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
  change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
  sepcon_right_assoc; sep_apply_l_atomic (mutex_del_parent_event_core_merge sg state eid event He);
  unfold mutex_del_parent_ceiling, mutex_del_parent_drained; entailer!; congruence.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_52 : OSMutexDel_which_implies_wit_52.
Proof.
  unfold OSMutexDel_which_implies_wit_52; left; intros;
  unfold mutex_del_parent_drained; Intros_p Hfacts;
  destruct (mutex_del_parent_loop_enabled_ceiling sg eid entry prepared state current event mutex priorities pcp_v
    (proj1 Hfacts) PreH2 PreH3) as [Hrange Hclear];
  destruct PreH1 as [_ [_ [_ [_ [Htable _]]]]];
  rewrite Htable, UCOS2_raw_rep_priority_table_equiv;
  pose proof (store_prio_tbl_split_cell sg state.(TskState).(prioTbl) pcp_v Hrange) as Hsplit;
  rewrite Hclear in Hsplit; cbn [prio_tbl_entry_to_addr] in Hsplit;
  sep_apply_l_atomic Hsplit;
  unfold mutex_del_parent_drained_without_priority; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_53 : OSMutexDel_which_implies_wit_53.
Proof.
  unfold OSMutexDel_which_implies_wit_53; left; intros;
  unfold mutex_del_parent_drained_without_priority; Intros_p Hfacts;
  destruct (mutex_del_parent_loop_enabled_ceiling sg eid entry prepared state current event mutex priorities pcp_v
    (proj1 Hfacts) PreH2 PreH3) as [Hrange Hclear];
  destruct PreH1 as [_ [_ [_ [_ [Htable _]]]]];
  rewrite Htable;
  pose proof (store_prio_tbl_merge_cell sg state.(TskState).(prioTbl) pcp_v Hrange) as Hmerge;
  rewrite Hclear in Hmerge; cbn [prio_tbl_entry_to_addr] in Hmerge;
  sepcon_right_assoc; sep_apply_l_atomic Hmerge;
  unfold mutex_del_parent_drained;
  rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_54 : OSMutexDel_which_implies_wit_54.
Proof.
  unfold OSMutexDel_which_implies_wit_54; left; intros; subst pe;
  destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
  destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
  rewrite Htype, Hptr, Hcnt, Hgrp, Hfree;
  unfold mutex_del_parent_drained; Intros_p Hfacts;
  pose proof Hfacts as [[_ [_ [_ [_ He]]]] Hzero];
  sep_apply_l_atomic (mutex_del_parent_event_core_split sg state eid event He);
  Exists (encode_event_type event.(eventType)) (encode_event_ptr_value sg event)
    (encode_event_cnt_value event) (encode_event_wait_grp event.(waitList) state.(TskState))
    (event_encode_pool_link sg (hd_error state.(EventState).(unUsedEventStates)));
  unfold mutex_del_parent_event_values, mutex_del_parent_drained_rest; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_55 : OSMutexDel_which_implies_wit_55.
Proof.
  unfold OSMutexDel_which_implies_wit_55; intros; subst pe opt_in;
 unfold mutex_del_parent_drained_rest; Intros;
 destruct H as [Hfacts Hzero];
 destruct Hfacts as [Hentry [Hprepare [Hprefix [Hphase He]]]];
 pose proof Hentry as [Hvalid [Horiginal [Ht [Hm Hu]]]];
 assert (Hprepared : prepared.(EventState).(inUsedEventStates) eid = Some current) by (rewrite (mutex_del_prepare_event_state_eq sg mutex entry prepared Hprepare); exact Horiginal); 
 pose proof (mutex_del_wake_prefix_done sg eid prepared priorities state event Hprefix He Hzero) as Hbroadcast;
 pose proof (mutex_del_parent_prefix_event_fields sg eid prepared priorities state Hprefix current event Hprepared He) as Hfields;
 destruct (mutex_del_wake_state_ranges sg eid mutex state Hphase) as [_ [_ [_ Hevents]]];
 destruct Hevents as [_ [_ [_ [_ [_ [_ Hentries]]]]]];
 pose proof (proj1 (encode_event_wait_grp_zero_iff_empty sg state.(TskState) event.(waitList)
   (proj1 (Hentries eid event He))) Hzero) as Hempty;
 rewrite <- Hempty, event_set_wait_list_put_back in Hfields;
 rewrite Hempty in Hfields;
 assert (Hobs : mutex_del_parent_critical_observation sg eid 1 0 0 waiting_v entry
   (mutex_del_recycle_state sg eid event state)) by (exists OS_ERR_NONE, (negb (Z.eqb (encode_event_wait_grp current.(waitList) entry.(TskState)) 0));
   split; [exists current, mutex; split; [exact Horiginal|]; split; [exact Ht|]; split; [exact Hm|];
     destruct (Z.eq_dec 1 0); [lia|]; destruct (Z.eq_dec 1 1); [|contradiction];
     exists prepared, priorities, state; split; [exact Hprepare|]; split; [exact Hbroadcast|];
     split; [rewrite Hfields; reflexivity|reflexivity] | unfold mutex_del_parent_waiting_flag in PreH6;
     destruct (Z.eqb (encode_event_wait_grp current.(waitList) entry.(TskState)) 0); simpl in *; auto]); 
 destruct PreH1 as [_ [Htable [_ [Hfree _]]]];
 destruct (Htable eid PreH2) as [[Htype [Hptr Hcnt]] [Hgrp Htbl]];
 rewrite Htype, Hptr, Hcnt, Hgrp, Hfree; destruct PreH4 as [-> ->];
 change (event_addr sg eid + OSEventType_off) with (event_pool_addr sg eid + 0);
 change (event_addr sg eid + OSEventPtr_off) with (event_pool_addr sg eid + 4);
 change (event_addr sg eid + OSEventCnt_off) with (event_pool_addr sg eid + 8);
 change (event_addr sg eid + OSEventGrp_off) with (event_pool_addr sg eid + 10);
 assert (Hflag : waiting_v = 0 \/ waiting_v = 1) by (unfold mutex_del_parent_waiting_flag in PreH6;
   destruct (Z.eqb (encode_event_wait_grp current.(waitList) entry.(TskState)) 0); auto); 
 destruct Hflag as [Hflag|Hflag]; [Left|Right];
 Exists (mutex_del_recycle_state sg eid event state);
 unfold mutex_del_runtime_program_restore_pre; entailer!; sep_apply_r_atomic (mutex_del_program_recycle_fields_merge sg eid mutex state event Hphase He Hzero); entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_56 : OSMutexDel_which_implies_wit_56.
Proof.
  unfold OSMutexDel_which_implies_wit_56; left; intros.
  pose proof (mutex_del_observation_preserves_call_stage sg eid opt_in result_v error_v request_v
    entry checkpoint context PreH1 PreH3) as Hstage.
  pose proof (mutex_del_observation_schedule_request sg eid opt_in result_v error_v request_v
    entry checkpoint context PreH1 PreH3) as Hrequest.
  pose proof (mutex_del_observation_preserves_call_available sg eid opt_in result_v error_v request_v
    entry checkpoint context PreH3 PreH2) as Havailable.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_continuation_source_restore_merge; [|exact Hstage|exact Havailable].
  right; destruct PreH3 as [code [scheduled [Hrun Hvalues]]].
  exists eid, opt_in, (result_v, (code, scheduled)); exact Hrun.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_57 : OSMutexDel_which_implies_wit_57.
Proof.
  unfold OSMutexDel_which_implies_wit_57; left; intros.
  sep_apply_l_atomic (mutex_del_continuation_source_return_open source_env external platform saved_local sg context mask).
  Intros returned current; Exists current returned; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_58 : OSMutexDel_which_implies_wit_58.
Proof.
  unfold OSMutexDel_which_implies_wit_58; left; intros.
  apply mutex_del_continuation_source_return_sched_pre; exact PreH1.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_59 : OSMutexDel_which_implies_wit_59.
Proof.
  left; intros.
  assert (Haddress : forall base, tcb_field_address base TCBStkPtr = base).
  { unfold mutex_del_parent_layout in PreH1; tauto. }
  destruct (mutex_del_scheduler_admission_continue sg configuration pe before eid
    opt_in PreH2 PreH3 PreH4) as [Haddresses Hclients].
  assert (Hopen : mutex_del_continuation_source_sched_pre source_env external platform
      saved_local sg returned mask current |--
    coq_prop (mutex_del_callsite_environment source_env external platform) &&
    mutex_del_continuation_source_sched_pre source_env external platform saved_local sg returned mask current).
  { unfold mutex_del_continuation_source_sched_pre, mutex_del_continuation_entry.
    Intros selected; Exists selected; entailer!; destruct H as [Henv ->]; exact Henv. }
  sep_apply_l_atomic Hopen; Intros_p Henv.
  entailer!.
  apply mutex_del_continuation_sched_call_pre; exact Haddress.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_60 : OSMutexDel_which_implies_wit_60.
Proof.
  left; intros.
  destruct PreH1 as [Hexternal Hplatform]; subst external platform.
  apply (mutex_del_continuation_sched_post source_env source_env saved_local sg returned mask current eq_refl).
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_61 : OSMutexDel_which_implies_wit_61.
Proof.
  unfold OSMutexDel_which_implies_wit_61; left; intros.
  apply mutex_del_continuation_return_same_call; exact PreH1.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_62 : OSMutexDel_which_implies_wit_62.
Proof.
  unfold OSMutexDel_which_implies_wit_62; left; intros.
  sep_apply_l_atomic (mutex_del_continuation_source_return_open source_env external platform saved_local sg context mask).
  Intros returned current; Exists current returned; entailer!.
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_63 : OSMutexDel_which_implies_wit_63.
Proof.
  unfold OSMutexDel_which_implies_wit_63; left; intros.
  apply _derivable1_andp_intros; [entailer!|].
  apply mutex_del_continuation_source_restore_merge; [left; reflexivity|assumption|assumption].
Qed.

Lemma proof_of_OSMutexDel_which_implies_wit_64 : OSMutexDel_which_implies_wit_64.
Proof.
  unfold OSMutexDel_which_implies_wit_64; left; intros; subst pe;
  destruct PreH7 as [event [mutex [Hvalid [He [Ht [Hf Hu]]]]]];
  assert (Hobs : mutex_del_parent_critical_observation sg eid opt_in
    (event_addr sg eid) 7 0 entry entry) by (exists OS_ERR_INVALID_OPT, false; split; [exists event, mutex; split; [exact He|]; split; [exact Ht|];
      split; [exact Hf|]; destruct (Z.eq_dec opt_in 0); [contradiction|];
      destruct (Z.eq_dec opt_in 1); [contradiction|auto] | split; reflexivity]); 
  unfold mutex_del_runtime_program_restore_pre; try rewrite kernel_program_inv_split_unmap; entailer!.
Qed.

