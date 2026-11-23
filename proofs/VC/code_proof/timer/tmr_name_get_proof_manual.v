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
From Ucos2Verify.VC.code.timer Require Import tmr_name_get_goal.
From Ucos2Verify.VC.code.timer Require Import tmr_name_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_name_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTmrNameGet_entail_wit_1_1 : OSTmrNameGet_entail_wit_1_1.
Proof.
  left; intros; subst ptmr_pre pdest_pre perr_pre.
  sep_apply_l_atomic (tmr_name_get_strlen_post_bytes__name_resources
    (tmr_name_get_name view locked) chars retval
    (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars)).
  entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_entail_wit_1_2 : OSTmrNameGet_entail_wit_1_2.
Proof.
  left; intros; subst ptmr_pre pdest_pre perr_pre.
  sep_apply_l_atomic (tmr_name_get_strlen_post_bytes__name_resources
    (tmr_name_get_name view locked) chars retval
    (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars)).
  entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_entail_wit_1_3 : OSTmrNameGet_entail_wit_1_3.
Proof.
  left; intros; subst ptmr_pre pdest_pre perr_pre.
  sep_apply_l_atomic (tmr_name_get_strlen_post_bytes__name_resources
    (tmr_name_get_name view locked) chars retval
    (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars)).
  entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_1 : OSTmrNameGet_return_wit_1.
Proof.
  unfold OSTmrNameGet_return_wit_1; left; intros.
  subst perr_pre pdest_pre ptmr_pre.
  eapply tmr_name_get_normal_post__return_refinement
    with (locked := locked) (error := 141) (output := None); [eassumption|].
  assert (Hfalse : tmr_name_get_successful (tmr_name_get_state view locked) = false).
  { unfold tmr_name_get_successful.
    rewrite (proj2 (Z.eqb_neq _ _) PreH2), (proj2 (Z.eqb_neq _ _) PreH3),
      (proj2 (Z.eqb_neq _ _) PreH4); reflexivity. }
  pose proof (tmr_name_get_observe_error view locked Hfalse) as Hobserve.
  rewrite (proj2 (Z.eqb_neq _ _) PreH1) in Hobserve; exact Hobserve.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_2 : OSTmrNameGet_return_wit_2.
Proof.
  unfold OSTmrNameGet_return_wit_2; left; intros.
  subst perr_pre pdest_pre ptmr_pre.
  eapply tmr_name_get_normal_post__return_refinement
    with (locked := locked) (error := 135) (output := None); [eassumption|].
  assert (Hfalse : tmr_name_get_successful (tmr_name_get_state view locked) = false).
  { rewrite PreH1; reflexivity. }
  pose proof (tmr_name_get_observe_error view locked Hfalse) as Hobserve.
  rewrite PreH1 in Hobserve; exact Hobserve.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_3 : OSTmrNameGet_return_wit_3.
Proof.
  unfold OSTmrNameGet_return_wit_3; left; intros; subst len.
  eapply tmr_name_get_normal_post__return_refinement
    with (locked := locked) (error := 0)
      (output := Some (tmr_name_get_name view locked)); [eassumption|].
  apply tmr_name_get_observe_success; assumption.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_4 : OSTmrNameGet_return_wit_4.
Proof.
  unfold OSTmrNameGet_return_wit_4; left; intros.
  subst perr_pre pdest_pre ptmr_pre.
  apply tmr_name_get_early_post__return_refinement.
  unfold tmr_name_get_early_error.
  rewrite (proj2 (Z.eqb_neq _ _) PreH7), (proj2 (Z.eqb_neq _ _) PreH6), PreH8.
  change ((if 0 <? intNesting (IntrState before) then Some 17 else None) = Some 17).
  assert (Hpositive : (0 <? intNesting (IntrState before)) = true).
  { apply Z.ltb_lt; unfold task_name_get_nesting in PreH1; lia. }
  rewrite Hpositive; reflexivity.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_5 : OSTmrNameGet_return_wit_5.
Proof.
  unfold OSTmrNameGet_return_wit_5; left; intros.
  subst perr_pre pdest_pre ptmr_pre.
  apply tmr_name_get_early_post__return_refinement.
  unfold tmr_name_get_early_error.
  rewrite (proj2 (Z.eqb_neq _ _) PreH2), (proj2 (Z.eqb_neq _ _) PreH1),
    (proj2 (Z.eqb_neq _ _) PreH3); reflexivity.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_6 : OSTmrNameGet_return_wit_6.
Proof.
  unfold OSTmrNameGet_return_wit_6; left; intros.
  subst perr_pre pdest_pre ptmr_pre p.
  apply tmr_name_get_early_post__return_refinement.
  unfold tmr_name_get_early_error.
  rewrite (proj2 (Z.eqb_neq _ _) PreH2); reflexivity.
Qed.

Lemma proof_of_OSTmrNameGet_return_wit_7 : OSTmrNameGet_return_wit_7.
Proof.
  unfold OSTmrNameGet_return_wit_7; left; intros.
  subst perr_pre pdest_pre ptmr_pre dest.
  apply tmr_name_get_early_post__return_refinement; reflexivity.
Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_2_pure : OSTmrNameGet_partial_solve_wit_2_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    &((ptmr_pre) # "os_tmr" ->ₛ "OSTmrType") (tmr_name_get_type view before)).
  entailer!.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change compcert.lib.Integers.Byte.max_unsigned with 255 in *; lia).
  exact PreH1.
Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_3_pure : OSTmrNameGet_partial_solve_wit_3_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range
    &((ptmr_pre) # "os_tmr" ->ₛ "OSTmrType") (tmr_name_get_type view before)).
  entailer!.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change compcert.lib.Integers.Byte.max_unsigned with 255 in *; lia).
  exact PreH1.
Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_5_pure : OSTmrNameGet_partial_solve_wit_5_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range &("OSIntNesting") (task_name_get_nesting before)).
  entailer!.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change compcert.lib.Integers.Byte.max_unsigned with 255 in *; lia).
  exact PreH1.
Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_6_pure : OSTmrNameGet_partial_solve_wit_6_pure.
Proof.
  left; intros.
  prop_apply_p (store_uchar_range &("OSIntNesting") (task_name_get_nesting before)).
  entailer!.
  rewrite unsigned_last_nbits_eq in PreH1 by
    (change compcert.lib.Integers.Byte.max_unsigned with 255 in *; lia).
  change compcert.lib.Integers.Byte.max_unsigned with 255 in *; lia.
Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_11_pure : OSTmrNameGet_partial_solve_wit_11_pure.
Proof. left; intros; rewrite <- PreH31; entailer!. Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_12_pure : OSTmrNameGet_partial_solve_wit_12_pure.
Proof. left; intros; rewrite <- PreH30; entailer!. Qed.

Lemma proof_of_OSTmrNameGet_partial_solve_wit_13_pure : OSTmrNameGet_partial_solve_wit_13_pure.
Proof. left; intros; rewrite <- PreH29; entailer!. Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_1 : OSTmrNameGet_which_implies_wit_1.
Proof.
  left; intros.
  pose proof PreH3 as [Htype [_ [_ [_ [Henabled _]]]]].
  unfold tmr_name_get_pre; Intros; rename H into Hentry.
  pose proof (proj1 (proj2 Hentry) PreH1 PreH2) as Hview.
  sep_apply_l_atomic (tmr_name_get_resources_split_type__entry_guards
    external platform critical sg context mask view p dest before
    PreH1 PreH2 Henabled Hview).
  rewrite <- Htype at 1.
  entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_2 : OSTmrNameGet_which_implies_wit_2.
Proof.
  left; intros.
  pose proof PreH5 as [Htype [_ [_ [_ [Henabled _]]]]].
  pose proof (proj1 (proj2 PreH4) PreH1 PreH2) as Hview.
  pose proof (tmr_name_get_resources_merge_type__entry_guards
    external platform critical sg context mask view p dest before
    PreH1 PreH2 Henabled Hview) as Hmerge.
  rewrite <- Htype in Hmerge at 1.
  sep_apply Hmerge; unfold tmr_name_get_pre; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_3 : OSTmrNameGet_which_implies_wit_3.
Proof.
  left; intros.
  pose proof PreH5 as [Htype [_ [_ [_ [Henabled _]]]]].
  pose proof (proj1 (proj2 PreH4) PreH1 PreH2) as Hview.
  pose proof (tmr_name_get_resources_merge_type__entry_guards
    external platform critical sg context mask view p dest before
    PreH1 PreH2 Henabled Hview) as Hmerge.
  rewrite <- Htype in Hmerge at 1.
  sep_apply Hmerge; unfold tmr_name_get_pre; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_4 : OSTmrNameGet_which_implies_wit_4.
Proof.
  left; intros.
  pose proof PreH1 as [_ [_ [_ [Hints _]]]].
  unfold tmr_name_get_pre; Intros; rename H into Hentry.
  rewrite tmr_name_get_resources_split_nesting__entry_guards.
  rewrite <- Hints; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_5 : OSTmrNameGet_which_implies_wit_5.
Proof.
  left; intros.
  pose proof PreH3 as [_ [_ [_ [Hints _]]]].
  unfold tmr_name_get_pre.
  rewrite tmr_name_get_resources_split_nesting__entry_guards.
  rewrite <- Hints; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_6 : OSTmrNameGet_which_implies_wit_6.
Proof.
  left; intros.
  pose proof PreH3 as [_ [_ [_ [Hints _]]]].
  unfold tmr_name_get_pre.
  rewrite tmr_name_get_resources_split_nesting__entry_guards.
  rewrite <- Hints; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_7 : OSTmrNameGet_which_implies_wit_7.
Proof.
  left; intros.
  assert (Hearly : tmr_name_get_early_error view p dest before = None).
  { unfold tmr_name_get_early_error.
    apply Z.eqb_neq in PreH1; apply Z.eqb_neq in PreH2.
    unfold task_name_get_nesting in PreH4.
    rewrite PreH1, PreH2, PreH3, PreH4; reflexivity. }
  unfold tmr_name_get_pre; Intros; rename H into Hentry.
  unfold tmr_name_get_resources, tmr_name_get_extra; rewrite Hearly.
  rewrite os_sched_lock_pre_closed_equiv.
  unfold tmr_name_get_closed, task_name_get_closed.
  pose proof (proj1 Hentry) as Hinv; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_8 : OSTmrNameGet_which_implies_wit_8.
Proof.
  left; intros.
  rewrite os_sched_lock_post_closed_equiv; Intros entry locked.
  destruct H as [Hlock Hinv].
  assert (Hp : p <> 0).
  { unfold tmr_name_get_early_error in PreH3.
    destruct (dest =? 0); [discriminate|].
    destruct (p =? 0) eqn:Hp; [discriminate|apply Z.eqb_neq; exact Hp]. }
  assert (Hd : dest <> 0).
  { unfold tmr_name_get_early_error in PreH3.
    destruct (dest =? 0) eqn:Hd; [discriminate|apply Z.eqb_neq; exact Hd]. }
  pose proof (tmr_name_get_locked_view_present critical sg context view p before entry locked
    (proj1 (proj2 PreH2) Hp Hd) Hlock) as Hview.
  pose proof (proj1 ((proj1 (proj2 (proj2 PreH2))) PreH3 entry locked Hlock)) as Haccess.
  Exists locked.
  unfold tmr_name_get_locked, tmr_name_get_closed, task_name_get_closed.
  assert (Hfacts : tmr_name_get_lock_facts external critical sg context view p dest before old X locked).
  { unfold tmr_name_get_lock_facts; unfold task_name_get_nesting in PreH1.
    split; [exact PreH2|]. split; [exact PreH3|]. split; [exact PreH1|].
    split; [exists entry; exact Hlock|].
    exact (conj Hinv (conj Hview Haccess)). }
  entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_9 : OSTmrNameGet_which_implies_wit_9.
Proof.
  right; intros X old dest p before view mask context sg critical platform external locked ptmr Hfacts Hlayout.
  destruct Hlayout as [Htype [Hname [Hstate [Hirq [Henabled Hnames]]]]].
  rewrite Hstate.
  destruct Hfacts as [Hentry [Hearly [Hnest [Hlock [Hinv [Hview Hsafe]]]]]].
  unfold tmr_name_get_locked.
  rewrite (tmr_name_get_private_locked_eq__name_resources view p dest before Hearly Hnest).
  Intros.
  destruct view as [kind status name names chars|i].
  - unfold tmr_name_get_state_rest; cbn [tmr_name_get_state]; entailer!.
  - destruct Hview as [Hp [Hinit [v Himage]]].
    unfold tmr_name_get_state_rest; cbn [tmr_name_get_state].
    rewrite Himage, Hp.
    rewrite (tmr_name_get_pool_object_equiv__name_resources platform critical sg context mask locked i v Henabled Hinit Himage).
    rewrite (tmr_name_get_object_state_equiv__name_resources sg.(osKernelConfig) (timer_pool_addr sg i) v Hnames).
    Exists v; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_10 : OSTmrNameGet_which_implies_wit_10.
Proof.
  left; intros X old dest p before view mask context sg critical platform external locked ptmr pdest Hsuccess Hfacts Hlayout.
  pose proof Hfacts as Hfacts_saved.
  destruct Hfacts as [[Hbefore [Hpresent [Haccess Hsafe]]]
    [Hearly [Hnest [[entry Hlock] [Hinv [Hview Hacquire]]]]]].
  destruct (proj2 (Haccess Hearly entry locked Hlock) Hsuccess) as [previous Hold].
  subst old; unfold task_name_get_output_cell.
  pose proof Hlayout as [Htype [Hname [Hstate [Hirq [Henabled Hnames]]]]].
  unfold tmr_name_get_layout.
  rewrite Hstate, Hname.
  destruct view as [kind status name names chars|i].
  - cbn [tmr_name_get_state] in Hsuccess.
    unfold tmr_name_get_state_rest, tmr_name_get_name_rest, tmr_name_get_name_readable.
    cbn [tmr_name_get_state tmr_name_get_name tmr_name_get_names].
    rewrite Hsuccess; Intros.
    Exists chars previous; entailer!.
  - destruct Hview as [Hp [Hinit [v Himage]]].
    cbn [tmr_name_get_state] in Hsuccess; rewrite Himage in Hsuccess.
    assert (Hnonzero : v.(timerImageState) <> 0).
    { intro Hzero; rewrite Hzero in Hsuccess; discriminate. }
    destruct (tmr_name_get_pool_name_readable sg locked i v Hinv Henabled Hnames Hinit Himage Hnonzero)
      as [chars Hread].
    unfold tmr_name_get_state_rest, tmr_name_get_name_rest, tmr_name_get_name_readable.
    cbn [tmr_name_get_state tmr_name_get_name tmr_name_get_names].
    rewrite Himage.
    Intros current.
    assert (current = v) by (intuition congruence); subst current.
    subst p.
    sep_apply (proj2 (tmr_name_get_object_state_equiv__name_resources sg.(osKernelConfig) (timer_pool_addr sg i) v Hnames)).
    sep_apply_l_atomic (proj1 (tmr_name_get_object_name_equiv__name_resources sg.(osKernelConfig) (timer_pool_addr sg i) v Hnames)).
    Exists chars previous v; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_11 : OSTmrNameGet_which_implies_wit_11.
Proof.
  right; intros X old dest p before view mask context sg critical platform external locked chars ptmr Hfacts Hlayout Hsuccess Hread.
  destruct Hlayout as [Htype [Hname [Hstate [Hirq [Henabled Hnames]]]]].
  rewrite Hname.
  destruct Hfacts as [Hentry [Hearly [Hnest [Hlock [Hinv [Hview Hsafe]]]]]].
  destruct view as [kind status name names raw_chars|i].
  - cbn [tmr_name_get_name_readable] in Hread; destruct Hread as [-> Hread].
    unfold tmr_name_get_name_rest, tmr_name_get_strlen_frame.
    cbn [tmr_name_get_name tmr_name_get_names].
    unfold tmr_name_get_strlen_pre, task_name_get_name_bytes.
    destruct (name =? 0) eqn:Hnull.
    + apply Z.eqb_eq in Hnull; subst name.
      apply _derivable1_andp_intros; [entailer!|]. Left; entailer!.
    + apply Z.eqb_neq in Hnull.
      apply _derivable1_andp_intros; [entailer!|]. Right; entailer!.
  - destruct Hview as [Hp [Hinit [v Himage]]].
    cbn [tmr_name_get_name_readable tmr_name_get_name] in Hread; rewrite Himage in Hread.
    unfold tmr_name_get_name_rest, tmr_name_get_strlen_frame.
    cbn [tmr_name_get_name tmr_name_get_names].
    rewrite Himage.
    Intros current.
    assert (current = v) by (intuition congruence); subst current.
    rewrite Hp.
    sep_apply (proj2 (tmr_name_get_object_name_equiv__name_resources sg.(osKernelConfig) (timer_pool_addr sg i) v Hnames)).
    sep_apply (proj2 (tmr_name_get_pool_object_equiv__name_resources platform critical sg context mask locked i v Henabled Hinit Himage)).
    unfold tmr_name_get_closed.
    rewrite task_name_get_closed_raw_rep__resource_stages_strlen.
    rewrite (tmr_name_get_raw_rep_name_equiv__name_resources sg locked v.(timerImageName) chars Hread).
    unfold tmr_name_get_strlen_pre, task_name_get_name_bytes.
    destruct (v.(timerImageName) =? 0) eqn:Hnull.
    + apply Z.eqb_eq in Hnull.
      apply _derivable1_andp_intros; [entailer!|]. Left; entailer!.
    + apply Z.eqb_neq in Hnull.
      apply _derivable1_andp_intros; [entailer!|]. Right; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_12 : OSTmrNameGet_which_implies_wit_12.
Proof.
  right; intros X old dest p before view mask context sg critical platform external locked chars ptmr Hfacts Hlayout Hsuccess Hread.
  destruct Hfacts as [Hentry [Hearly [Hnest [Hlock [Hinv [Hview Hsafe]]]]]].
  rewrite os_sched_unlock_pre_closed_equiv.
  unfold os_sched_unlock_outside_frame.
  change (interrupt_platform_running platform (os_sched_call_invocation context)
    (os_sched_call_origin context) mask **
    critical_region_outside critical sg (os_sched_call_invocation context) locked)
    with (tmr_name_get_closed platform critical sg context mask locked).
  rewrite (tmr_name_get_private_locked_eq__name_resources view p dest before Hearly Hnest).
  destruct view as [kind status name names raw_chars|i].
  - cbn [tmr_name_get_name_readable] in Hread; destruct Hread as [-> Hread].
    cbn [tmr_name_get_state] in Hsuccess.
    unfold tmr_name_get_strlen_frame; cbn [tmr_name_get_name].
    rewrite Hsuccess.
    unfold tmr_name_get_continuation; entailer!.
  - cbn [tmr_name_get_name_readable] in Hread.
    unfold tmr_name_get_strlen_frame.
    Intros.
    sep_apply (proj2 (tmr_name_get_raw_rep_name_equiv__name_resources sg locked (tmr_name_get_name (TmrNameGetPool i) locked) chars Hread)).
    unfold tmr_name_get_closed.
    rewrite task_name_get_closed_raw_rep__resource_stages_strlen.
    unfold tmr_name_get_continuation; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_13 : OSTmrNameGet_which_implies_wit_13.
Proof.
  right; intros X old dest p before view mask context sg critical platform external locked ptmr Hzero Hfacts Hlayout.
  destruct Hlayout as [Htype [Hname [Hstate [Hirq [Henabled Hnames]]]]].
  rewrite Hstate.
  destruct Hfacts as [Hentry [Hearly [Hnest [Hlock [Hinv [Hview Hsafe]]]]]].
  rewrite os_sched_unlock_pre_closed_equiv.
  unfold os_sched_unlock_outside_frame.
  change (interrupt_platform_running platform (os_sched_call_invocation context)
    (os_sched_call_origin context) mask **
    critical_region_outside critical sg (os_sched_call_invocation context) locked)
    with (tmr_name_get_closed platform critical sg context mask locked).
  rewrite (tmr_name_get_private_locked_eq__name_resources view p dest before Hearly Hnest).
  destruct view as [kind status name names chars|i].
  - unfold tmr_name_get_state_rest; cbn [tmr_name_get_state].
    unfold tmr_name_get_continuation; entailer!.
  - destruct Hview as [Hp [Hinit [v Himage]]].
    unfold tmr_name_get_state_rest; cbn [tmr_name_get_state].
    rewrite Himage.
    Intros current.
    assert (current = v) by (intuition congruence); subst current.
    rewrite Hp.
    sep_apply (proj2 (tmr_name_get_object_state_equiv__name_resources sg.(osKernelConfig) (timer_pool_addr sg i) v Hnames)).
    sep_apply (proj2 (tmr_name_get_pool_object_equiv__name_resources platform critical sg context mask locked i v Henabled Hinit Himage)).
    unfold tmr_name_get_continuation; entailer!.
Qed.

Lemma proof_of_OSTmrNameGet_which_implies_wit_14 : OSTmrNameGet_which_implies_wit_14.
Proof.
  right; intros X old dest p before view mask context sg critical platform external locked ptmr Hzero Hone Htwo Hthree Hfacts Hlayout.
  destruct Hlayout as [Htype [Hname [Hstate [Hirq [Henabled Hnames]]]]].
  rewrite Hstate.
  destruct Hfacts as [Hentry [Hearly [Hnest [Hlock [Hinv [Hview Hsafe]]]]]].
  rewrite os_sched_unlock_pre_closed_equiv.
  unfold os_sched_unlock_outside_frame.
  change (interrupt_platform_running platform (os_sched_call_invocation context)
    (os_sched_call_origin context) mask **
    critical_region_outside critical sg (os_sched_call_invocation context) locked)
    with (tmr_name_get_closed platform critical sg context mask locked).
  rewrite (tmr_name_get_private_locked_eq__name_resources view p dest before Hearly Hnest).
  destruct view as [kind status name names chars|i].
  - unfold tmr_name_get_state_rest; cbn [tmr_name_get_state].
    unfold tmr_name_get_continuation; entailer!.
  - destruct Hview as [Hp [Hinit [v Himage]]].
    unfold tmr_name_get_state_rest; cbn [tmr_name_get_state].
    rewrite Himage.
    Intros current.
    assert (current = v) by (intuition congruence); subst current.
    rewrite Hp.
    sep_apply (proj2 (tmr_name_get_object_state_equiv__name_resources sg.(osKernelConfig) (timer_pool_addr sg i) v Hnames)).
    sep_apply (proj2 (tmr_name_get_pool_object_equiv__name_resources platform critical sg context mask locked i v Henabled Hinit Himage)).
    unfold tmr_name_get_continuation; entailer!.
Qed.

