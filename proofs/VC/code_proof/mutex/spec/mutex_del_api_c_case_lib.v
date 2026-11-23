Require Import Ucos2Verify.VC.code.mutex.spec.mutex_owner_protocol_source_spec.
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

Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_continuation_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_callee_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_api_scheduler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_api_program_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_del_history_spec.


Lemma mutex_del_api_restored_critical_return_same_x :
  forall environment external platform critical saved_local sg original mask
    before pe option eid acquired checkpoint pointer code returned current X,
  mutex_del_parent_prefix_ok pe before eid ->
  mutex_owner_source_history sg before acquired ->
  mutex_del_parent_critical_observation sg eid option pointer code 0 acquired checkpoint ->
  mutex_api_restore_history environment critical sg original checkpoint returned current ->
  mutex_del_api_refinement_pre environment critical sg original pe option eid before X ->
  mutex_del_continuation_source_return_at environment external platform saved_local
    sg original mask returned current |--
  mutex_del_api_return_post environment external platform critical saved_local
    sg original mask before pe option eid pointer code X.
Proof.
  intros * Hprefix Hsave Hcritical Hrestore Hsafe.
  pose proof (mutex_api_tail_history_without_schedule _ _ _ _ _ _ _ Hrestore) as Htail.
  pose proof (mutex_del_api_program_critical _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hprefix Hsave Hcritical Htail) as Hprogram.
  pose proof (mutex_del_api_safe_return _ _ _ _ _ _ _ _ _ _ _ _ Hprogram Hsafe) as Hreturn.
  unfold mutex_del_api_return_post; Exists returned current.
  unfold mutex_del_continuation_source_return_at; entailer!.
Qed.

Lemma mutex_del_api_entry_nesting_range :
  forall environment external platform saved_local sg original mask state,
  mutex_del_continuation_entry environment external platform saved_local sg original mask state |--
  coq_prop (0 <= state.(IntrState).(intNesting) <= 255) &&
  mutex_del_continuation_entry environment external platform saved_local sg original mask state.
Proof.
  intros; apply _derivable1_andp_intros; [|reflexivity].
  unfold mutex_del_continuation_entry; Intros selected.
  unfold kernel_continuation_call_closed, kernel_continuation_inv, mutex_del_stack_resources.
  rewrite kernel_program_inv_split_unmap; Intros.
  sep_apply_l_atomic (mutex_query_interrupt_split_full sg state); Intros_p Hvalid.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) state.(IntrState).(intNesting));
    Intros_p Hrange.
  entailer!.
Qed.
