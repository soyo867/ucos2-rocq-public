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
From Ucos2Verify.VC.code.timer Require Import tmr_init_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_init_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_task_timer_phase_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Local Open Scope sac.

Lemma proof_of_OSTmr_Init_return_wit_1 : OSTmr_Init_return_wit_1.
Proof.
  left; intros; apply tmr_init_post_absorb_coq_prop__call_refinement.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_1 : OSTmr_Init_which_implies_wit_1.
Proof.
  left; intros X initial call p.
  sep_apply (tmr_init_pre_split_pool p call initial X).
  unfold tmr_init_pool_context; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  pose proof (tmr_init_source_binding_config p Hbinding) as Hcfg.
  pose proof (tmr_init_mem_clr_bounds p.(tmr_init_sg) (proj1 Hbinding)) as Hbounds.
  assert (Hsize : sizeof("os_tmr") = 40) by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hwheel : sizeof("os_tmr_wheel") = 8) by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hbase : &("OSTmrTbl") = p.(tmr_init_sg).(stable_glob_vars.g_OSTmrTbl))
    by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hwbase : &("OSTmrWheelTbl") = p.(tmr_init_sg).(stable_glob_vars.g_OSTmrWheelTbl))
    by (unfold tmr_init_source_binding in Hbinding; tauto).
  rewrite Hsize, Hwheel, Hbase, Hwbase.
  change (sizeof(UCHAR)) with 1; change UINT_MAX with 4294967295.
  repeat rewrite Z.mul_0_l; repeat rewrite Z.add_0_r.
  sep_apply_l_atomic (proj1 (tmr_init_uninitialized_arrays_equiv p.(tmr_init_sg) Hcfg)).
  entailer!; lia.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_2 : OSTmr_Init_which_implies_wit_2.
Proof.
  left; intros X LitMap initial call p Hmap; subst LitMap.
  sep_apply (tmr_init_pool_context_split_question_mark__pool_resources p call initial X).
  unfold tmr_init_pool_literal_residual; Intros.
  assert (Hbinding : tmr_init_source_binding p) by assumption.
  assert (Hsize : sizeof("os_tmr") = 40) by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hwheel : sizeof("os_tmr_wheel") = 8) by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hbase : &("OSTmrTbl") = p.(tmr_init_sg).(stable_glob_vars.g_OSTmrTbl))
    by (unfold tmr_init_source_binding in Hbinding; tauto).
  assert (Hwbase : &("OSTmrWheelTbl") = p.(tmr_init_sg).(stable_glob_vars.g_OSTmrWheelTbl))
    by (unfold tmr_init_source_binding in Hbinding; tauto).
  rewrite Hsize, Hwheel, Hbase, Hwbase.
  repeat rewrite Z.mul_0_l; repeat rewrite Z.add_0_r.
  change (40 * 16) with 640; change (8 * 7) with 56.
  entailer!.
  sep_apply_r_atomic (tmr_init_mem_clr_posts_to_loop p.(tmr_init_sg) (tmr_init_question p)
    (proj1 Hbinding)).
  unfold tmr_init_question; entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_3 : OSTmr_Init_which_implies_wit_3.
Proof.
  left; intros X initial call p ix ptmr1 ptmr2 Hlo Hhi Hp1 Hp2.
  subst ptmr1 ptmr2.
  unfold tmr_init_pool_literal_residual; Intros.
  assert (Hbinding : tmr_init_source_binding p) by assumption.
  rewrite (tmr_init_source_pool_addr_eq__pool_resources p ix Hbinding).
  pose proof (tmr_init_source_slot_fields_eq__pool_resources p ix Hbinding ltac:(lia))
    as [Htype [Hstate [Hnext Hname]]].
  rewrite Htype, Hstate, Hnext, Hname.
  sep_apply (tmr_init_loop_focus_zero_slot p.(tmr_init_sg) (tmr_init_question p) ix
    (proj1 Hbinding) ltac:(lia)).
  unfold tmr_init_loop_focus, tmr_init_slot_cells, tmr_init_slot_context.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_4 : OSTmr_Init_which_implies_wit_4.
Proof.
  left; intros X LitMap initial call p ix ptmr1 ptmr2 Hmap Hlo Hhi Hp1 Hp2.
  subst LitMap ptmr1 ptmr2.
  unfold tmr_init_pool_literal_residual; Intros.
  assert (Hbinding : tmr_init_source_binding p) by assumption.
  pose proof (tmr_init_source_binding_config p Hbinding) as Hcfg.
  assert (Hnames : stable_glob_vars.cfgTimerNames (stable_glob_vars.osKernelConfig (tmr_init_sg p)) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hcap : stable_glob_vars.cfgMaxTimers (stable_glob_vars.osKernelConfig (tmr_init_sg p)) = 16)
    by (rewrite Hcfg; reflexivity).
  rewrite (tmr_init_source_pool_addr_eq__pool_resources p ix Hbinding).
  rewrite (tmr_init_source_pool_addr_eq__pool_resources p (ix + 1) Hbinding).
  pose proof (tmr_init_source_slot_fields_eq__pool_resources p ix Hbinding ltac:(lia))
    as [Htype [Hstate [Hnext Hname]]].
  rewrite Htype, Hstate, Hnext, Hname, Z.mul_0_l, Z.add_0_r.
  entailer!.
  sep_apply_r_atomic (tmr_init_loop_merge_completed_slot p.(tmr_init_sg)
    (tmr_init_question p) ix Hnames Hcap ltac:(lia)).
  unfold tmr_init_slot_context, tmr_init_slot_cells, tmr_init_question.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_5 : OSTmr_Init_which_implies_wit_5.
Proof.
  left; intros X initial call p ix ptmr1 Hlo Hhi Hexit Hp.
  assert (ix = 15) by lia; subst ix ptmr1.
  unfold tmr_init_pool_literal_residual; Intros.
  assert (Hbinding : tmr_init_source_binding p) by assumption.
  rewrite (tmr_init_source_pool_addr_eq__pool_resources p 15 Hbinding).
  pose proof (tmr_init_source_slot_fields_eq__pool_resources p 15 Hbinding ltac:(lia))
    as [Htype [Hstate [Hnext Hname]]].
  rewrite Htype, Hstate, Hnext, Hname.
  sep_apply (tmr_init_loop_focus_zero_slot p.(tmr_init_sg) (tmr_init_question p) 15
    (proj1 Hbinding) ltac:(lia)).
  unfold tmr_init_loop_focus, tmr_init_slot_cells, tmr_init_slot_context.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_6 : OSTmr_Init_which_implies_wit_6.
Proof.
  left; intros X LitMap initial call p ix ptmr1 Hmap Hlo Hhi Hexit Hp.
  assert (ix = 15) by lia; subst ix LitMap ptmr1.
  unfold tmr_init_pool_literal_residual; Intros.
  assert (Hbinding : tmr_init_source_binding p) by assumption.
  pose proof (tmr_init_source_binding_config p Hbinding) as Hcfg.
  assert (Hnames : stable_glob_vars.cfgTimerNames (stable_glob_vars.osKernelConfig (tmr_init_sg p)) = true)
    by (rewrite Hcfg; reflexivity).
  assert (Hcap : stable_glob_vars.cfgMaxTimers (stable_glob_vars.osKernelConfig (tmr_init_sg p)) = 16)
    by (rewrite Hcfg; reflexivity).
  rewrite (tmr_init_source_pool_addr_eq__pool_resources p 15 Hbinding).
  pose proof (tmr_init_source_slot_fields_eq__pool_resources p 15 Hbinding ltac:(lia))
    as [Htype [Hstate [Hnext Hname]]].
  rewrite Htype, Hstate, Hnext, Hname, Z.mul_0_l, Z.add_0_r.
  assert (Hmerge :
    stable_glob_vars.timer_pool_addr p.(tmr_init_sg) 15 # UChar |-> 100 **
    (stable_glob_vars.timer_pool_addr p.(tmr_init_sg) 15 + 37) # UChar |-> 0 **
    (stable_glob_vars.timer_pool_addr p.(tmr_init_sg) 15 + 12) # Ptr |-> 0 **
    (stable_glob_vars.timer_pool_addr p.(tmr_init_sg) 15 + 32) # Ptr |-> tmr_init_question p **
    tmr_init_slot_context p.(tmr_init_sg) (tmr_init_question p) 15 |--
    tmr_init_before_globals p.(tmr_init_sg) (tmr_init_question p)).
  { unfold tmr_init_slot_context.
    change (Z.to_nat 15) with 15%nat; change (15 + 1) with 16.
    sep_apply_r_atomic (tmr_init_tail_merge_completed_slot p.(tmr_init_sg)
      (tmr_init_question p) Hnames Hcap).
    unfold tmr_init_slot_cells; entailer!. }
  assert (Hreturn : store_stringLit (tmr_init_question p) "?" **
    GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals) **
    ((store_stringLit (tmr_init_question p) "?" **
      GlobalStrings_missing p.(tmr_init_literals) p.(tmr_init_missing_literals)) -*
      tmr_init_pool_context p call initial X) |--
    tmr_init_pool_context p call initial X).
  { apply derivable1_wand_elim2. }
  unfold tmr_init_question in Hreturn |- *.
  sep_apply Hreturn.
  unfold tmr_init_question in Hmerge; sep_apply Hmerge.
  unfold tmr_init_before_globals, tmr_init_four_globals, tmr_init_globals,
    tmr_init_globals_context.
  cbn [Nat.leb].
  unfold tmr_init_source_binding in Hbinding.
  destruct Hbinding as [Hl [Hs [Hw [Hb [Hwb [Ht [Hu [Hf [Hr [Hsem [Hsig Hrest]]]]]]]]]]].
  rewrite Ht, Hu, Hf, Hr, Hsem, Hsig.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_7 : OSTmr_Init_which_implies_wit_7.
Proof.
  left; intros X initial call p.
  unfold tmr_init_pool_context; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hentry : tmr_init_entry_facts p call initial) by tauto.
  assert (Hsafe : MonadLib.StateRelMonad.safeexec_lib.safeExec
    (eq initial) (tmr_init_program p call) X) by tauto.
  pose proof (tmr_init_pool_safe_first_call__pool_resources p call initial X Hsafe) as Hsem_safe.
  assert (Hnext_entry : tmr_init_entry_facts p call (tmr_init_after_pool p initial)).
  { unfold tmr_init_after_pool; rewrite tmr_init_entry_facts_timer_replace; exact Hentry. }
  assert (Hready := tmr_init_sem_pre_ready p call (tmr_init_after_pool p initial)
    true (tmr_init_sem_continuation p call true X) Hbinding Hnext_entry eq_refl Hsem_safe).
  entailer!.
  sep_apply_r_atomic Hready.
  assert (Hworld := tmr_init_after_globals_merge_call_world__pool_resources p call initial
    Hbinding ltac:(unfold tmr_init_task_spec.tmr_init_task_stopped in *; tauto) ltac:(tauto)).
  sep_apply_r_atomic Hworld.
  unfold tmr_init_pool_residual, tmr_init_after_globals, tmr_init_globals_context,
    tmr_init_four_globals, tmr_init_globals.
  cbn [Nat.leb]; rewrite Z.mul_0_l, Z.add_0_r.
  unfold tmr_init_source_binding in Hbinding.
  destruct Hbinding as [Hl [Hs [Hw [Hb [Hwb [Ht [Hu [Hf [Hr [Hsem [Hsig Hrest]]]]]]]]]]].
  rewrite Hb, Ht, Hu, Hf, Hr, Hsem, Hsig.
  entailer!.
  apply derivable1_truep_intros.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_8 : OSTmr_Init_which_implies_wit_8.
Proof.
  left; intros X initial call p lock_result current returned; Intros.
  assert (Hfacts : tmr_init_sem_return_facts p call (tmr_init_after_pool p initial)
    true (tmr_init_sem_continuation p call true X) lock_result returned current) by tauto.
  assert (Haddr : &("OSTmrSem") = (tmr_init_sg p).(g_OSTmrSem)).
  { unfold tmr_init_sem_return_facts, tmr_init_source_binding in Hfacts; tauto. }
  rewrite Haddr.
  sep_apply (tmr_init_lock_store_next_call p call initial lock_result returned current X Hfacts).
  Intros next; Exists next returned; entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_9 : OSTmr_Init_which_implies_wit_9.
Proof.
  left; intros X call p lock_call lock_state returned current signal_result; Intros.
  assert (Hsame : task_tcb_init_stack_same_call lock_call call) by tauto.
  assert (Hfacts : tmr_init_sem_return_facts p lock_call lock_state false
    (tmr_init_sem_continuation p call false X) signal_result returned current) by tauto.
  assert (Haddr : &("OSTmrSemSignal") = (tmr_init_sg p).(g_OSTmrSemSignal)).
  { unfold tmr_init_sem_return_facts, tmr_init_source_binding in Hfacts; tauto. }
  rewrite Haddr.
  sep_apply (tmr_init_signal_store_next_call p call lock_call lock_state signal_result
    returned current X Hsame Hfacts).
  Intros next; Exists next returned; entailer!.
  entailer!.
Qed.

Lemma proof_of_OSTmr_Init_which_implies_wit_10 : OSTmr_Init_which_implies_wit_10.
Proof.
  left; intros X call p task_call task_state; Intros.
  assert (Hsame : task_tcb_init_stack_same_call task_call call) by tauto.
  sep_apply (tmr_init_task_return_finish p call task_call task_state X Hsame).
  sep_apply_r_atomic (tmr_init_post_absorb_coq_prop__call_refinement p call X True).
  entailer!.
Qed.

Lemma proof_of_OSTmr_InitTask_derive_timer_init_spec_by_phase_spec : OSTmr_InitTask_derive_timer_init_spec_by_phase_spec.
Proof.
  intros X before call p; unfold tmr_init_task_pre; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hstopped : tmr_init_task_stopped before) by tauto.
  pose proof (task_create_call_protocol_spec.task_create_runtime_call_input_boot
    (tmr_init_task_create_args p.(tmr_init_entry_address) p.(tmr_init_stack_base))
    call before Hstopped) as Hruntime.
  Exists p.(tmr_init_environment) p.(tmr_init_critical) tmr_init_empty_local
    p.(tmr_init_sg) p.(tmr_init_entry_address) p.(tmr_init_stack_base)
    p.(tmr_init_return_address) p.(tmr_init_mask) p.(tmr_init_lower)
    p.(tmr_init_old_frame) p.(tmr_init_upper) call before p.(tmr_init_literals)
    p.(tmr_init_missing_literals) (tmr_init_task_continuation p call before X).
  unfold tmr_init_entry_resources, tmr_init_task_return.
  unfold tmr_init_source_binding in Hbinding.
  entailer!; try tauto.
  apply sepcon_cancel_end; [entailer!|].
  apply sepcon_cancel_end; [entailer!|].
  apply derivable1_wand_sepcon_adjoint; entailer!; tauto.
Qed.

Lemma proof_of_OSSemCreate_derive_timer_signal_spec_by_source_spec : OSSemCreate_derive_timer_signal_spec_by_source_spec.
Proof.
  intros cnt K before call p; Intros; subst cnt.
  sep_apply (tmr_init_sem_pre_implies_state_inv__call_refinement p call before false K); Intros.
  unfold tmr_init_sem_pre; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hentry : tmr_init_entry_facts p call before) by tauto.
  assert (Hphase : before.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase false) by tauto.
  assert (Hvalid : UCOS2_state_inv p.(tmr_init_sg) before) by tauto.
  assert (Haddr : &("OSTmrSemSignal") = p.(tmr_init_sg).(g_OSTmrSemSignal)).
  { unfold tmr_init_source_binding in Hbinding; tauto. }
  Exists p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg) call
    p.(tmr_init_mask) before (tmr_init_sem_call_continuation p call before false K).
  cbn [tmr_init_sem_count].
  entailer!.
  apply derivable1_wand_sepcon_adjoint; Intros result.
  sep_apply (tmr_init_sem_post_view p call before false K result Hbinding Hvalid Hentry Hphase).
  Intros returned current; Exists returned current result.
  rewrite Haddr; entailer!; entailer!.
Qed.

Lemma proof_of_OSSemCreate_derive_timer_lock_spec_by_source_spec : OSSemCreate_derive_timer_lock_spec_by_source_spec.
Proof.
  intros cnt K before call p; Intros; subst cnt.
  sep_apply (tmr_init_sem_pre_implies_state_inv__call_refinement p call before true K); Intros.
  unfold tmr_init_sem_pre; Intros.
  assert (Hbinding : tmr_init_source_binding p) by tauto.
  assert (Hentry : tmr_init_entry_facts p call before) by tauto.
  assert (Hphase : before.(TimerState).(timerInitPhase) = tmr_init_sem_stage_phase true) by tauto.
  assert (Hvalid : UCOS2_state_inv p.(tmr_init_sg) before) by tauto.
  assert (Haddr : &("OSTmrSem") = p.(tmr_init_sg).(g_OSTmrSem)).
  { unfold tmr_init_source_binding in Hbinding; tauto. }
  Exists p.(tmr_init_environment) p.(tmr_init_critical) p.(tmr_init_sg) call
    p.(tmr_init_mask) before (tmr_init_sem_call_continuation p call before true K).
  cbn [tmr_init_sem_count].
  entailer!.
  apply derivable1_wand_sepcon_adjoint; Intros result.
  sep_apply (tmr_init_sem_post_view p call before true K result Hbinding Hvalid Hentry Hphase).
  Intros returned current; Exists returned current result.
  rewrite Haddr; entailer!; entailer!.
Qed.

