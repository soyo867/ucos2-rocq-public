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
From Ucos2Verify.VC.code.core Require Import os_init_goal.
From Ucos2Verify.VC.code.core Require Import os_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_begin_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Require Import Ucos2Verify.VC.code.sched.spec.init_rdy_list_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_tcb_list_selected_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_init_spec.
Require Import Ucos2Verify.VC.code.memory.spec.mem_init_spec.
Require Import Ucos2Verify.VC.code.queue.spec.q_init_generic_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_idle_continuation_spec.
Require Import Ucos2Verify.VC.code.core.spec.init_task_stat_continuation_spec.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_end_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_debug_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.os_init_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Local Open Scope sac.

Lemma proof_of_OSInit_return_wit_1 : OSInit_return_wit_1.
Proof.
  left; intros X p idle stat timer; intros.
  unfold os_init_post; Exists idle stat timer; entailer!.
Qed. 

Lemma proof_of_OSInit_partial_solve_wit_33_pure : OSInit_partial_solve_wit_33_pure.
Proof.
  left; intros; unfold os_init_literals; entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_1 : OSInit_which_implies_wit_1.
Proof.
  left; intros X p.
  unfold os_init_pre, os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  unfold os_init_hook_port_pre, os_init_hook_begin_pre.
  entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_2 : OSInit_which_implies_wit_2.
Proof.
  left; intros X p.
  unfold os_init_hook_port_post, os_init_hook_begin_post.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 0%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 0%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  unfold os_init_hook_port_post, os_init_hook_begin_post.
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_3 : OSInit_which_implies_wit_3.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  unfold os_init_misc_raw.
  repeat match goal with H : ?a = ?b |- _ => progress rewrite H end.
  entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_4 : OSInit_which_implies_wit_4.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 1%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 1%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_5 : OSInit_which_implies_wit_5.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  repeat match goal with H : ?a = ?b |- _ => progress rewrite H end.
  entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_6 : OSInit_which_implies_wit_6.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 2%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 2%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  assert (Haddr0 : (os_init_sg p).(g_OSRdyGrp) = &("OSRdyGrp"))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Haddr1 : (os_init_sg p).(g_OSRdyTbl) = &("OSRdyTbl"))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Haddr2 : (os_init_sg p).(g_OSPrioCur) = &("OSPrioCur"))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Haddr3 : (os_init_sg p).(g_OSPrioHighRdy) = &("OSPrioHighRdy"))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Haddr4 : (os_init_sg p).(g_OSTCBHighRdy) = &("OSTCBHighRdy"))
    by (unfold os_init_source_binding in Hbinding; tauto).
  assert (Haddr5 : (os_init_sg p).(g_OSTCBCur) = &("OSTCBCur"))
    by (unfold os_init_source_binding in Hbinding; tauto).
  rewrite Haddr0, Haddr1, Haddr2, Haddr3, Haddr4, Haddr5.
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_7 : OSInit_which_implies_wit_7.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_8 : OSInit_which_implies_wit_8.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 3%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 3%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_9 : OSInit_which_implies_wit_9.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  entailer!; try lia.
  - change (Z.rem (g_OSEventTbl (os_init_sg p)) 4 = 0).
    rewrite Z.rem_mod_nonneg by lia; assumption.
  - change (sizeof_alias_type "os_event" * 10 = 200); lia.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_10 : OSInit_which_implies_wit_10.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 4%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 4%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_11 : OSInit_which_implies_wit_11.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  assert (Hsize : sizeof_alias_type "os_flag_grp" = 16).
  { match goal with H : flag_init_layout _ |- _ =>
      unfold flag_init_layout in H; tauto end. }
  entailer!; try lia.
  change (sizeof_alias_type "os_flag_grp" * 5 = 80); lia.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_12 : OSInit_which_implies_wit_12.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 5%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 5%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_13 : OSInit_which_implies_wit_13.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  assert (Hsize : sizeof_alias_type "os_mem" = 24).
  { match goal with H : mem_init_layout _ |- _ =>
      unfold mem_init_layout in H; tauto end. }
  entailer!; try lia.
  change (sizeof_alias_type "os_mem" * 5 = 120); lia.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_14 : OSInit_which_implies_wit_14.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 6%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 6%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_15 : OSInit_which_implies_wit_15.
Proof.
  left; intros X p.
  unfold os_init_raw_stage, os_init_raw_call_frame,
    os_init_components, os_init_component_frame.
  cbv [seq map filter fold_right Nat.ltb Nat.leb Nat.eqb negb os_init_component].
  Intros.
  match goal with
  | H : os_init_source_binding p |- _ => pose proof H as Hbinding
  | H : os_init_source_binding p /\ _ |- _ => pose proof (proj1 H) as Hbinding
  end.
  unfold os_init_source_binding in Hbinding; cbn zeta in Hbinding.
  decompose [and] Hbinding; clear Hbinding.
  assert (Hvalid : valid_stable_glob_vars (os_init_sg p)).
  { match goal with H : selected_kernel_profile _ |- _ => exact (proj1 H) end. }
  entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_16 : OSInit_which_implies_wit_16.
Proof.
  left; intros X p.
  unfold os_init_raw_call_frame; Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  assert (Hsafe : os_init_raw_safe p 7%nat X) by tauto.
  pose proof (os_init_raw_safe_step p 7%nat X ltac:(lia) Hsafe) as Hnext.
  unfold os_init_raw_stage, os_init_components, os_init_component_frame.
  cbn [seq map filter fold_right Nat.eqb Nat.ltb Nat.leb negb os_init_component].
  entailer!; tauto.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_17 : OSInit_which_implies_wit_17.
Proof.
  left; intros X p; apply os_init_raw_stage_to_idle.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_18 : OSInit_which_implies_wit_18.
Proof.
  left; intros X p.
  unfold os_init_before_idle, os_init_idle_call_frame, os_init_idle_entry.
  Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  unfold os_init_source_binding, tmr_init_source_binding in Hbinding.
  unfold os_init_sg, os_init_critical in *.
  entailer!; try tauto.
  repeat apply sepcon_cancel_end; entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_19 : OSInit_which_implies_wit_19.
Proof.
  left; intros X p; apply os_init_idle_post_next.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_20 : OSInit_which_implies_wit_20.
Proof.
  left; intros X p idle.
  unfold os_init_before_stat, os_init_stat_call_frame, os_init_stat_entry.
  Intros.
  assert (Hbinding : os_init_source_binding p) by tauto.
  unfold os_init_source_binding, tmr_init_source_binding in Hbinding.
  unfold os_init_sg, os_init_critical in *.
  entailer!; try tauto.
  repeat apply sepcon_cancel_end; entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_21 : OSInit_which_implies_wit_21.
Proof.
  left; intros X p idle; apply os_init_stat_post_next.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_22 : OSInit_which_implies_wit_22.
Proof.
  left; intros X p idle stat; unfold os_init_before_timer; entailer!.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_23 : OSInit_which_implies_wit_23.
Proof.
  left; intros X p idle stat; apply os_init_timer_post_next.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_24 : OSInit_which_implies_wit_24.
Proof.
  left; intros X p idle stat timer; apply os_init_end_safe_step.
Qed. 

Lemma proof_of_OSInit_which_implies_wit_25 : OSInit_which_implies_wit_25.
Proof.
  left; intros X p idle stat timer; apply os_init_debug_safe_step.
Qed. 

