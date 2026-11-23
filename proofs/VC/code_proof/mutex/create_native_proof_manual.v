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
From Ucos2Verify.VC.code.mutex Require Import create_native_goal.
Require Import Ucos2Verify.lib.error_codes.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Import MutexCreatePublication.
Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext.
Local Open Scope Z_scope.
Local Open Scope sac.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_publication_spec.
Import MutexCreatePublication.
Import UCOS2_C_Rules MutexCreateFull MutexCreateCall MutexCreateSpatial MutexCreateInitialization MutexCreatePrivateContext.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.


Lemma proof_of_OSMutexCreate_safety_wit_19_priority_enabled : OSMutexCreate_safety_wit_19_priority_enabled.
Proof.
  left; pre_process; subst prio_pre.
  assert (Hbits : signed_last_nbits (prio_in * 2 ^ 8) 32 = prio_in * 2 ^ 8).
  { apply signed_last_nbits_eq; [lia|].
    replace (2 ^ (32 - 1)) with 2147483648 by reflexivity.
    replace (2 ^ 8) with 256 by reflexivity; lia. }
  rewrite Hbits; split_pures.
  all: dump_pre_spatial.
  all: lia.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_1_priority_enabled : OSMutexCreate_return_wit_1_priority_enabled.
Proof.
  left; pre_process; pureIntros.
  assert (Haccepted : priority_rejected sg prio_in = false).
  { unfold priority_rejected.
    match goal with Hp : valid_mutex_pcp sg prio_in |- _ => destruct Hp as [Hdis|[Hlow Hhigh]] end.
    - rewrite Hdis, Z.eqb_refl; reflexivity.
    - destruct (prio_in =? osPrioMutexCeilDis sg); simpl; [reflexivity|apply Z.leb_gt; exact Hhigh]. }
  assert (HnotISR : (0 <? intNesting before.(IntrState)) = false) by (apply Z.ltb_ge; lia).
  assert (Hbusy : priority_slot_busy sg prio_in entry_4 = false).
  { apply (proj2 (priority_slot_available_iff sg prio_in entry_4)); assumption. }
  assert (Hhead : entry_4.(EventState).(unUsedEventStates) = eid :: rest).
  { match goal with Hfacts : free_head_facts sg entry_4 eid rest image |- _ => exact (proj1 Hfacts) end. }
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before
    (OS_ERR_NONE, Some eid) after_2).
  { unfold MutexCreatePublication.call_relation; rewrite Haccepted, HnotISR.
    exists entry_4, (mutex_create_state sg prio_in eid rest entry_4); split.
    - match goal with Ha : acquire_facts critical sg invocation mask retval before entry_4 |- _ => exact (proj1 Ha) end.
    - split; [unfold critical_operation; rewrite Hbusy, Hhead; split; reflexivity|assumption]. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before after_2
    (free_head sg entry) 0).
  { exists (OS_ERR_NONE, Some eid); split; [exact Hcall|]; split; [|reflexivity].
    unfold event_pointer_eq in *; assumption. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before (free_head sg entry) after_2).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen after_2) (return (free_head sg entry)) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) (free_head sg entry) (fun _ => LastSeen after_2)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs after_2); split.
    - exists before, after_2; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists after_2 0 (free_head sg entry).
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth; entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_2_priority_disabled : OSMutexCreate_return_wit_2_priority_disabled.
Proof.
  left; pre_process; pureIntros.
  assert (Haccepted : priority_rejected sg prio_in = false).
  { unfold priority_rejected.
    match goal with Hp : valid_mutex_pcp sg prio_in |- _ => destruct Hp as [Hdis|[Hlow Hhigh]] end.
    - rewrite Hdis, Z.eqb_refl; reflexivity.
    - destruct (prio_in =? osPrioMutexCeilDis sg); simpl; [reflexivity|apply Z.leb_gt; exact Hhigh]. }
  assert (HnotISR : (0 <? intNesting before.(IntrState)) = false) by (apply Z.ltb_ge; lia).
  assert (Hbusy : priority_slot_busy sg prio_in entry_3 = false).
  { apply (proj2 (priority_slot_available_iff sg prio_in entry_3)); assumption. }
  assert (Hhead : entry_3.(EventState).(unUsedEventStates) = eid :: rest).
  { match goal with Hfacts : free_head_facts sg entry_3 eid rest image |- _ => exact (proj1 Hfacts) end. }
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before
    (OS_ERR_NONE, Some eid) after_2).
  { unfold MutexCreatePublication.call_relation; rewrite Haccepted, HnotISR.
    exists entry_3, (mutex_create_state sg prio_in eid rest entry_3); split.
    - match goal with Ha : acquire_facts critical sg invocation mask retval before entry_3 |- _ => exact (proj1 Ha) end.
    - split; [unfold critical_operation; rewrite Hbusy, Hhead; split; reflexivity|replace prio_in with 255 by lia; assumption]. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before after_2
    (free_head sg entry) 0).
  { exists (OS_ERR_NONE, Some eid); split; [exact Hcall|]; split; [|reflexivity].
    unfold event_pointer_eq in *; assumption. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before (free_head sg entry) after_2).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen after_2) (return (free_head sg entry)) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) (free_head sg entry) (fun _ => LastSeen after_2)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs after_2); split.
    - exists before, after_2; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists after_2 0 (free_head sg entry).
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth; entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_3_priority_enabled : OSMutexCreate_return_wit_3_priority_enabled.
Proof.
  left; pre_process; pureIntros.
  assert (Haccepted : priority_rejected sg prio_in = false).
  { unfold priority_rejected.
    match goal with Hp : valid_mutex_pcp sg prio_in |- _ => destruct Hp as [Hdis|[Hlow Hhigh]] end.
    - rewrite Hdis, Z.eqb_refl; reflexivity.
    - destruct (prio_in =? osPrioMutexCeilDis sg); simpl; [reflexivity|apply Z.leb_gt; exact Hhigh]. }
  assert (HnotISR : (0 <? intNesting before.(IntrState)) = false) by (apply Z.ltb_ge; lia).
  assert (Hbusy : priority_slot_busy sg prio_in entry_5 = false).
  { apply (proj2 (priority_slot_available_iff sg prio_in entry_5)); eassumption. }
  assert (Hempty : entry_5.(EventState).(unUsedEventStates) = nil).
  { apply (proj1 (free_head_empty_iff sg entry_5 ltac:(assumption))); assumption. }
  assert (Htrace : critical_region_interval critical sg invocation before entry_5).
  { match goal with Ha : acquire_facts critical sg invocation mask retval before entry_5 |- _ => exact (proj1 Ha) end. }
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before (OS_ERR_PEVENT_NULL, None) after_2).
  { unfold MutexCreatePublication.call_relation; rewrite Haccepted, HnotISR.
    exists entry_5, entry_5; split; [exact Htrace|].
    split.
    - unfold critical_operation; rewrite Hbusy, Hempty; split; reflexivity.
    - assumption. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before after_2 0 4).
  { exists (OS_ERR_PEVENT_NULL, None); split; [exact Hcall|]; split; reflexivity. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before 0 after_2).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen after_2) (return 0) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) 0 (fun _ => LastSeen after_2)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs after_2); split.
    - exists before, after_2; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists after_2 4 0.
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_4_priority_disabled : OSMutexCreate_return_wit_4_priority_disabled.
Proof.
  left; pre_process; pureIntros.
  assert (Haccepted : priority_rejected sg prio_in = false).
  { unfold priority_rejected.
    match goal with Hp : valid_mutex_pcp sg prio_in |- _ => destruct Hp as [Hdis|[Hlow Hhigh]] end.
    - rewrite Hdis, Z.eqb_refl; reflexivity.
    - destruct (prio_in =? osPrioMutexCeilDis sg); simpl; [reflexivity|apply Z.leb_gt; exact Hhigh]. }
  assert (HnotISR : (0 <? intNesting before.(IntrState)) = false) by (apply Z.ltb_ge; lia).
  assert (Hbusy : priority_slot_busy sg prio_in entry_3 = false).
  { apply (proj2 (priority_slot_available_iff sg prio_in entry_3)); eassumption. }
  assert (Hempty : entry_3.(EventState).(unUsedEventStates) = nil).
  { apply (proj1 (free_head_empty_iff sg entry_3 ltac:(assumption))); assumption. }
  assert (Htrace : critical_region_interval critical sg invocation before entry_3).
  { match goal with Ha : acquire_facts critical sg invocation mask retval before entry_3 |- _ => exact (proj1 Ha) end. }
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before (OS_ERR_PEVENT_NULL, None) after_2).
  { unfold MutexCreatePublication.call_relation; rewrite Haccepted, HnotISR.
    exists entry_3, entry_3; split; [exact Htrace|].
    split.
    - unfold critical_operation; rewrite Hbusy, Hempty; split; reflexivity.
    - assumption. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before after_2 0 4).
  { exists (OS_ERR_PEVENT_NULL, None); split; [exact Hcall|]; split; reflexivity. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before 0 after_2).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen after_2) (return 0) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) 0 (fun _ => LastSeen after_2)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs after_2); split.
    - exists before, after_2; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists after_2 4 0.
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_5_priority_enabled : OSMutexCreate_return_wit_5_priority_enabled.
Proof.
  left; pre_process; pureIntros.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Haccepted : priority_rejected sg prio_in = false).
  { unfold priority_rejected.
    match goal with Hp : valid_mutex_pcp sg prio_in |- _ => destruct Hp as [Hdis|[Hlow Hhigh]] end.
    - rewrite Hdis, Z.eqb_refl; reflexivity.
    - destruct (prio_in =? osPrioMutexCeilDis sg); simpl; [reflexivity|apply Z.leb_gt; exact Hhigh]. }
  assert (HnotISR : (0 <? intNesting before.(IntrState)) = false) by (apply Z.ltb_ge; lia).
  assert (Hbusy : priority_slot_busy sg prio_in entry_2 = true).
  { unfold priority_slot_busy; rewrite Htag, (proj2 (Z.eqb_neq _ _) PreH4).
    unfold priority_value in PreH7.
    destruct (prioTbl (TskState entry_2) prio_in); [contradiction|reflexivity|reflexivity]. }
  assert (Htrace : critical_region_interval critical sg invocation before entry_2).
  { match goal with Ha : acquire_facts critical sg invocation mask retval before entry_2 |- _ => exact (proj1 Ha) end. }
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before (OS_ERR_PRIO_EXIST, None) after_2).
  { unfold MutexCreatePublication.call_relation; rewrite Haccepted, HnotISR.
    exists entry_2, entry_2; split; [exact Htrace|].
    split.
    - unfold critical_operation; rewrite Hbusy; split; reflexivity.
    - assumption. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before after_2 0 40).
  { exists (OS_ERR_PRIO_EXIST, None); split; [exact Hcall|]; split; reflexivity. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before 0 after_2).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen after_2) (return 0) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) 0 (fun _ => LastSeen after_2)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs after_2); split.
    - exists before, after_2; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists after_2 40 0.
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_6 : OSMutexCreate_return_wit_6.
Proof.
  left; pre_process; pureIntros.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hlowest : osLowestPrio sg = 63) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hbranch : priority_rejected sg prio_in = false).
  { unfold priority_rejected; rewrite Htag, Hlowest.
    destruct (prio_in =? 255); simpl; [reflexivity|apply Z.leb_gt; lia]. }
  assert (Hisr : (0 <? intNesting before.(IntrState)) = true) by (apply Z.ltb_lt; lia).
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before (OS_ERR_CREATE_ISR, None) before).
  { unfold MutexCreatePublication.call_relation; rewrite Hbranch, Hisr; split; reflexivity. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before before 0 16).
  { exists (OS_ERR_CREATE_ISR, None); split; [exact Hcall|]; split; reflexivity. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before 0 before).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen before) (return 0) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) 0 (fun _ => LastSeen before)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs before); split.
    - exists before, before; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists before 16 0.
  rewrite (closed_equiv platform critical sg invocation origin mask before).
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_7 : OSMutexCreate_return_wit_7.
Proof.
  left; pre_process; pureIntros.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hlowest : osLowestPrio sg = 63) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hbranch : priority_rejected sg prio_in = false).
  { unfold priority_rejected; rewrite Htag, Hlowest.
    replace prio_in with 255 by lia; reflexivity. }
  assert (Hisr : (0 <? intNesting before.(IntrState)) = true) by (apply Z.ltb_lt; lia).
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before (OS_ERR_CREATE_ISR, None) before).
  { unfold MutexCreatePublication.call_relation; rewrite Hbranch, Hisr; split; reflexivity. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before before 0 16).
  { exists (OS_ERR_CREATE_ISR, None); split; [exact Hcall|]; split; reflexivity. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before 0 before).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen before) (return 0) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) 0 (fun _ => LastSeen before)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs before); split.
    - exists before, before; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists before 16 0.
  rewrite (closed_equiv platform critical sg invocation origin mask before).
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_return_wit_8 : OSMutexCreate_return_wit_8.
Proof.
  left; pre_process; pureIntros.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hlowest : osLowestPrio sg = 63) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hbranch : priority_rejected sg prio_in = true).
  { unfold priority_rejected; rewrite Htag, Hlowest.
    rewrite (proj2 (Z.eqb_neq prio_in 255) ltac:(lia)),
      (proj2 (Z.leb_le 63 prio_in) ltac:(lia)); reflexivity. }
  assert (Hcall : MutexCreatePublication.call_relation critical sg invocation prio_in before (OS_ERR_PRIO_INVALID, None) before).
  { unfold MutexCreatePublication.call_relation; rewrite Hbranch; split; reflexivity. }
  assert (Hresult : publication_result_prop critical sg invocation prio_in before before 0 42).
  { exists (OS_ERR_PRIO_INVALID, None); split; [exact Hcall|]; split; reflexivity. }
  assert (Hprogram : publication_call_program critical sg invocation prio_in before 0 before).
  { eapply publication_result_prop_call_program; exact Hresult. }
  assert (Hreturn : safeExec (LastSeen before) (return 0) X).
  { eapply (highstependret_derive
      (atomic_cmd (publication_call_program critical sg invocation prio_in))
      (LastSeen before) 0 (fun _ => LastSeen before)).
    2: eassumption.
    unfold hs_eval, LastSeen, atomic_cmd; intros observed Hobserved.
    exists (RTrans_Abs before); split.
    - exists before, before; split; [apply Hobserved; exact I|].
      split; [exact Hprogram|reflexivity].
    - reflexivity. }
  Exists before 42 0.
  rewrite (closed_equiv platform critical sg invocation origin mask before).
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_partial_solve_wit_36_priority_enabled_pure : OSMutexCreate_partial_solve_wit_36_priority_enabled_pure.
Proof.
  left; pre_process.
  rewrite (mutex_create_pcp_cnt_encoding_exact__leaf_pure_and_global_localization prio_pre ltac:(lia)).
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_1 : OSMutexCreate_which_implies_wit_1.
Proof.
  left; pre_process.
  unfold os_int_nesting_addr in *; pureIntros.
  rewrite (UCOS2_inv_split_os_int_nesting sg before).
  unfold UCOS2_inv_os_int_nesting_cell.
  match goal with Haddr : _ = g_OSIntNesting sg |- _ => rewrite Haddr end.
  Intros.
  prop_apply_p (store_uchar_range (g_OSIntNesting sg) (intNesting before.(IntrState))).
  Intros_p Hrange.
  change (0 <= intNesting before.(IntrState) <= 255) in Hrange.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_2 : OSMutexCreate_which_implies_wit_2.
Proof.
  left; pre_process.
  unfold os_int_nesting_addr in *; pureIntros.
  rewrite (UCOS2_inv_split_os_int_nesting sg before).
  unfold UCOS2_inv_os_int_nesting_cell.
  match goal with Haddr : _ = g_OSIntNesting sg |- _ => rewrite Haddr end.
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_3 : OSMutexCreate_which_implies_wit_3.
Proof.
  left; pre_process.
  unfold os_int_nesting_addr in *; pureIntros.
  rewrite (UCOS2_inv_split_os_int_nesting sg before).
  unfold UCOS2_inv_os_int_nesting_cell.
  match goal with Haddr : _ = g_OSIntNesting sg |- _ => rewrite Haddr end.
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  sep_apply_l_atomic Htruth.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_4 : OSMutexCreate_which_implies_wit_4.
Proof.
  left; pre_process; pureIntros.
  apply derivable1s_coq_prop_l; intro Hstable.
  assert (Hlowest : osLowestPrio sg = 63).
  { unfold valid_stable_glob_vars in *; tauto. }
  assert (Hpcp : valid_mutex_pcp sg prio_in).
  { right; rewrite Hlowest; lia. }
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_5 : OSMutexCreate_which_implies_wit_5.
Proof.
  left; pre_process; pureIntros.
  apply derivable1s_coq_prop_l; intro Hstable.
  assert (Hdisabled : osPrioMutexCeilDis sg = 255).
  { unfold valid_stable_glob_vars in *; tauto. }
  assert (Hpcp : valid_mutex_pcp sg prio_in).
  { left; lia. }
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_6 : OSMutexCreate_which_implies_wit_6.
Proof.
  left; pre_process.
  rewrite closed_equiv.
  entailer!.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_7 : OSMutexCreate_which_implies_wit_7.
Proof.
  left; pre_process; pureIntros.
  unfold os_event_free_list_addr in *.
  Exists entry_2.
  rewrite (head_split_merge sg entry_2).
  Intros.
  unfold priority_table, free_head, event_free_root_rep.
  match goal with Haddr : _ = g_OSEventFreeList sg |- _ => rewrite Haddr end.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_8 : OSMutexCreate_which_implies_wit_8.
Proof.
  left; pre_process; pureIntros.
  unfold mutex_create_priority_input_prop, os_tcb_prio_tbl_addr in *; subst prio.
  Exists entry_2.
  match goal with Haddr : _ = g_OSTCBPrioTbl sg |- _ => rewrite Haddr end.
  sep_apply_l_atomic (priority_table_split_cell sg entry_2 prio_in ltac:(lia)).
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_9 : OSMutexCreate_which_implies_wit_9.
Proof.
  left; pre_process; pureIntros.
  unfold mutex_create_priority_input_prop, os_tcb_prio_tbl_addr, os_event_free_list_addr in *; subst prio.
  Exists entry_2.
  match goal with Haddr : _ = g_OSTCBPrioTbl sg |- _ => rewrite Haddr end.
  match goal with Haddr : _ = g_OSEventFreeList sg |- _ => rewrite Haddr end.
  sep_apply_l_atomic (priority_table_merge_cell sg entry_2 prio_in ltac:(lia)).
  rewrite (head_split_merge sg entry_2).
  unfold priority_table, free_head, event_free_root_rep.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_10 : OSMutexCreate_which_implies_wit_10.
Proof.
  left; pre_process; pureIntros.
  unfold mutex_create_priority_input_prop, os_tcb_prio_tbl_addr in *; subst prio.
  assert (Hlowest : osLowestPrio sg = 63) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Henabled : prio_in <> osPrioMutexCeilDis sg) by lia.
  assert (Hslot : slot_available sg entry_2 prio_in).
  { right; eapply priority_value_zero_is_free; [eassumption| |exact PreH7].
    unfold task_priority_in_range; rewrite Hlowest; lia. }
  Exists entry_2.
  match goal with Haddr : _ = g_OSTCBPrioTbl sg |- _ => rewrite Haddr end.
  sep_apply_l_atomic (priority_table_merge_reserved_cell sg entry_2 prio_in ltac:(lia) Henabled).
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_11 : OSMutexCreate_which_implies_wit_11.
Proof.
  left; pre_process; pureIntros.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hdisabled : prio_in = osPrioMutexCeilDis sg) by lia.
  assert (Hslot : slot_available sg entry_2 prio_in) by (left; exact Hdisabled).
  Exists entry_2.
  rewrite (reserved_priority_table_disabled sg entry_2 prio_in Hdisabled).
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_12 : OSMutexCreate_which_implies_wit_12.
Proof.
  left; pre_process; pureIntros.
  unfold mutex_create_priority_input_prop, os_tcb_prio_tbl_addr in *; subst prio.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Henabled : prio_in <> osPrioMutexCeilDis sg) by lia.
  Exists entry_2.
  match goal with Haddr : _ = g_OSTCBPrioTbl sg |- _ => rewrite Haddr end.
  sep_apply_l_atomic (reserved_priority_table_split_cell sg entry_2 prio_in ltac:(lia) Henabled).
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_13 : OSMutexCreate_which_implies_wit_13.
Proof.
  left; pre_process; pureIntros.
  unfold mutex_create_priority_input_prop, os_tcb_prio_tbl_addr in *; subst prio.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Henabled : prio_in <> osPrioMutexCeilDis sg) by lia.
  Exists entry_2.
  match goal with Haddr : _ = g_OSTCBPrioTbl sg |- _ => rewrite Haddr end.
  match goal with Hslot : slot_available sg entry_2 prio_in |- _ =>
    sep_apply_l_atomic (reserved_priority_table_rollback_cell sg entry_2 prio_in ltac:(lia) Henabled Hslot) end.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_14 : OSMutexCreate_which_implies_wit_14.
Proof.
  left; pre_process; pureIntros.
  assert (Htag : osPrioMutexCeilDis sg = 255) by (unfold valid_stable_glob_vars in *; tauto).
  assert (Hdisabled : prio_in = osPrioMutexCeilDis sg) by lia.
  Exists entry_2.
  rewrite (reserved_priority_table_disabled sg entry_2 prio_in Hdisabled).
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_15 : OSMutexCreate_which_implies_wit_15.
Proof.
  left; pre_process; pureIntros.
  unfold os_event_free_list_addr in *.
  Exists entry_2.
  match goal with Haddr : _ = g_OSEventFreeList sg |- _ => rewrite Haddr end.
  rewrite (head_split_merge sg entry_2).
  unfold priority_table, free_head, event_free_root_rep.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_16 : OSMutexCreate_which_implies_wit_16.
Proof.
  left; pre_process; pureIntros.
  assert (Hvalid : UCOS2_state_inv sg entry_2) by assumption.
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  sep_apply_l_atomic (head_residual_open_free_head sg entry_2 Hvalid PreH4).
  Intros eid0 rest0 image0.
  assert (Hfacts : free_head_facts sg entry_2 eid0 rest0 image0) by assumption.
  pose proof Hfacts as [Hhead [Himage [Hid [Hheadaddr [Hptr Htype]]]]].
  assert (Hlayout : event_object_layout_prop sg eid0).
  { apply event_table_layout_select; assumption. }
  assert (Hpevent : pevent = event_pool_addr sg eid0) by congruence.
  assert (Hbinding : event_pointer_eq sg eid0 pevent) by exact Hpevent.
  pose proof Hlayout as [[Htypeaddr [Hptraddr Hcntaddr]] [Hgrpaddr Htbladdr]].
  rewrite event_addr_shared_pool_binding in Hptraddr.
  unfold OSEventPtr_off in Hptraddr.
  rewrite Hnames.
  sep_apply_l_atomic (event_storage_split_field false (event_pool_addr sg eid0) image0 EventPtrField ltac:(simpl; tauto)).
  rewrite Hptr; cbn [event_cell event_field_offset].
  Exists eid0 rest0 image0 entry_2.
  rewrite Hpevent, Hptraddr.
  entailer!.
  unfold derivable1, sepcon, truep.
  intros heap Hcell.
  destruct (unit_join heap) as [unit [Hunit Hjoin]].
  do 3 (exists unit, heap; split; [apply join_comm; exact Hjoin|];
    split; [exact I|]).
  exact Hcell.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_17 : OSMutexCreate_which_implies_wit_17.
Proof.
  left; pre_process; pureIntros.
  assert (Hfacts : free_head_facts sg entry_2 eid_2 rest_2 image_2) by assumption.
  pose proof Hfacts as [Hhead [Himage [Hid [Hheadaddr [Hptr Htype]]]]].
  assert (Hlayout : event_object_layout_prop sg eid_2) by assumption.
  pose proof Hlayout as [[Htypeaddr [Hptraddr Hcntaddr]] [Hgrpaddr Htbladdr]].
  rewrite event_addr_shared_pool_binding in Htypeaddr, Hptraddr, Hcntaddr, Hgrpaddr, Htbladdr.
  unfold OSEventType_off, OSEventPtr_off, OSEventCnt_off, OSEventGrp_off, OSEventTbl_off
    in Htypeaddr, Hptraddr, Hcntaddr, Hgrpaddr, Htbladdr.
  unfold event_pointer_eq in *.
  match goal with Hp : pevent = event_pool_addr sg eid_2 |- _ => rewrite Hp end.
  rewrite Hptraddr.
  pose proof (event_storage_merge_field false (event_pool_addr sg eid_2) image_2
    EventPtrField ltac:(simpl; tauto)) as Hmerge.
  rewrite Hptr in Hmerge; cbn [event_cell event_field_offset] in Hmerge.
  rewrite Hmerge.
  sep_apply_l_atomic (initialization_storage_split (event_pool_addr sg eid_2) image_2).
  Exists eid_2 rest_2 image_2 entry_2.
  rewrite Htypeaddr, Hcntaddr, Hgrpaddr, Htbladdr.
  entailer!.
  all: apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSMutexCreate_which_implies_wit_18 : OSMutexCreate_which_implies_wit_18.
Proof.
  left; pre_process; pureIntros.
  assert (Hlayout : event_object_layout_prop sg eid_2) by assumption.
  pose proof Hlayout as [[Htypeaddr [Hptraddr Hcntaddr]] [Hgrpaddr Htbladdr]].
  rewrite event_addr_shared_pool_binding in Htypeaddr, Hptraddr, Hcntaddr, Hgrpaddr, Htbladdr.
  unfold OSEventType_off, OSEventPtr_off, OSEventCnt_off, OSEventGrp_off, OSEventTbl_off
    in Htypeaddr, Hptraddr, Hcntaddr, Hgrpaddr, Htbladdr.
  unfold event_pointer_eq, os_event_free_list_addr in *.
  match goal with Hp : pevent = event_pool_addr sg eid_2 |- _ => rewrite Hp end.
  match goal with Haddr : _ = g_OSEventFreeList sg |- _ => rewrite Haddr end.
  rewrite Htypeaddr, Hptraddr, Hcntaddr, Hgrpaddr, Htbladdr.
  sep_apply_l_atomic (initialization_storage_merge (event_pool_addr sg eid_2) image_2 prio_in).
  assert (Hmerge : node_residual sg entry_2 eid_2 **
    (reserved_priority_table sg entry_2 prio_in **
    (g_OSEventFreeList sg # Ptr |-> event_encode_pool_link sg (hd_error rest_2) **
    event_storage_rep false (event_pool_addr sg eid_2)
      (event_create_image false 4 (prio_in * 256 + 255) 0 0 image_2))) |--
    UCOS2_inv sg (mutex_create_state sg prio_in eid_2 rest_2 entry_2)).
  { sep_apply_r_atomic (initialized_storage_merge sg entry_2 prio_in eid_2 rest_2 image_2
      ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)).
    entailer!. }
  assert (Htruth : (TT ** TT) |-- TT) by apply derivable1_truep_intros.
  repeat sep_apply_l_atomic Htruth.
  Exists eid_2 rest_2 image_2 entry_2; entailer!.
  sep_apply_r_atomic Hmerge.
  entailer!.
  assert (Htruep : (TT ** TT) --||-- TT).
  { split; [apply derivable1_truep_intros|].
    apply sepcon_cancel_res_emp; apply derivable1_truep_intros. }
  repeat rewrite Htruep; apply derivable1_truep_intros.
Qed.
