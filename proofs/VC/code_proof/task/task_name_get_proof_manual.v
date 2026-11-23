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
From Ucos2Verify.VC.code.task Require Import task_name_get_goal.
From Ucos2Verify.VC.code.task Require Import task_name_get_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.task.spec.task_name_get_spec.
Require Import Ucos2Verify.VC.code.core.OS_StrLen_goal_check.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTaskNameGet_entail_wit_1_1 : OSTaskNameGet_entail_wit_1_1.
Proof.
  left; intros; subst prio_pre.
  assert (Hnest : task_name_get_nesting before = 0).
  { rewrite uchar_unsigned32_eq__critical_control in PreH6 by lia; lia. }
  assert (Hearly : task_name_get_early_error request pname_pre
      (task_name_get_nesting before) = None).
  { apply task_name_get_early_error_none__critical_control; auto. }
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before acquired_2 PreH1 PreH11)) as Hvalid.
  unfold task_name_get_guarded_private; rewrite Hearly.
  rewrite <- (task_name_get_private_acquired_eq critical sg invocation request
    before acquired_2 PreH11 PreH1).
  Exists acquired_2; unfold UCOS2_inv; entailer!.
  rewrite <- PreH15; reflexivity.
Qed.

Lemma proof_of_OSTaskNameGet_entail_wit_1_2 : OSTaskNameGet_entail_wit_1_2.
Proof.
  left; intros; subst prio_pre.
  assert (Hnest : task_name_get_nesting before = 0).
  { rewrite uchar_unsigned32_eq__critical_control in PreH6 by lia; lia. }
  assert (Hearly : task_name_get_early_error request pname_pre
      (task_name_get_nesting before) = None).
  { apply task_name_get_early_error_none__critical_control; auto; right; lia. }
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before acquired_2 PreH1 PreH10)) as Hvalid.
  unfold task_name_get_guarded_private; rewrite Hearly.
  rewrite <- (task_name_get_private_acquired_eq critical sg invocation request
    before acquired_2 PreH10 PreH1).
  Exists acquired_2; unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_entail_wit_2_2 : OSTaskNameGet_entail_wit_2_2.
Proof.
  left; intros.
  assert (Hnotself : request <> 255) by (intro Heq; subst request; vm_compute in PreH1; contradiction).
  destruct (PreH6 PreH5 acquired PreH7 PreH3) as [[priority Hresolved] Houtput].
  unfold task_name_get_resolved in *.
  assert (Hself : (request =? 255) = false) by (apply Z.eqb_neq; exact Hnotself).
  rewrite Hself in *; entailer!; tauto.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_1 : OSTaskNameGet_return_wit_1.
Proof.
  left; intros.
  unfold task_name_get_restore_post; Intros current.
  assert (Heffect : task_name_get_effect sg invocation before acquired request pname_pre
    retval 0 (Some (task_name_get_name node))).
  { unfold task_name_get_effect; rewrite PreH29.
    right; exists prio, (task_name_get_table_value sg acquired prio),
      (task_name_get_name node), chars; auto. }
  assert (Hsafe : task_name_get_return_safe current retval 0 (Some (task_name_get_name node)) X).
  { eapply task_name_get_safe_return; [exact Heffect|exact PreH19|tauto| |exact PreH34].
    rewrite PreH29; contradiction. }
  unfold task_name_get_post.
  Exists acquired current 0 (Some (task_name_get_name node)).
  rewrite PreH29.
  unfold interrupt_saved_value in PreH32; destruct PreH32 as [Hsaved Hmask].
  rewrite Hmask.
  unfold task_name_get_output_cell; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_2 : OSTaskNameGet_return_wit_2.
Proof.
  left; intros.
  unfold task_name_get_restore_post; Intros current.
  assert (Heffect : task_name_get_effect sg invocation before acquired request pname_pre
    0 67 None).
  { unfold task_name_get_effect; rewrite PreH14.
    left; exists prio, (task_name_get_table_value sg acquired prio); tauto. }
  assert (Hsafe : task_name_get_return_safe current 0 67 None X).
  { eapply task_name_get_safe_return; [exact Heffect|exact PreH4|tauto| |exact PreH19].
    rewrite PreH14; contradiction. }
  unfold task_name_get_post.
  Exists acquired current 67 (@None Z).
  rewrite PreH14.
  unfold interrupt_saved_value in PreH17; destruct PreH17 as [Hsaved Hmask].
  rewrite Hmask; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_3 : OSTaskNameGet_return_wit_3.
Proof.
  left; intros.
  unfold task_name_get_restore_post; Intros current.
  assert (Heffect : task_name_get_effect sg invocation before acquired request pname_pre
    0 67 None).
  { unfold task_name_get_effect; rewrite PreH13.
    left; exists prio, (task_name_get_table_value sg acquired prio); tauto. }
  assert (Hsafe : task_name_get_return_safe current 0 67 None X).
  { eapply task_name_get_safe_return; [exact Heffect|exact PreH3|tauto| |exact PreH18].
    rewrite PreH13; contradiction. }
  unfold task_name_get_post.
  Exists acquired current 67 (@None Z).
  rewrite PreH13.
  unfold interrupt_saved_value in PreH16; destruct PreH16 as [Hsaved Hmask].
  rewrite Hmask; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_4 : OSTaskNameGet_return_wit_4.
Proof.
  left; intros; subst prio_pre.
  sep_apply_l_atomic (task_name_get_closed_nesting_in_range__critical_control
    platform critical sg invocation origin mask before); Intros.
  assert (Hnest : 0 < task_name_get_nesting before).
  { rewrite uchar_unsigned32_eq__critical_control in PreH2 by lia; lia. }
  assert (Hearly : task_name_get_early_error request pname_pre
      (task_name_get_nesting before) = Some 17).
  { unfold task_name_get_early_error; replace request with 255 by lia; cbn.
    assert (Hp : (pname_pre =? 0) = false) by (apply Z.eqb_neq; auto).
    assert (Hn : (0 <? task_name_get_nesting before) = true) by (apply Z.ltb_lt; auto).
    rewrite Hp, Hn; reflexivity. }
  assert (Heffect : task_name_get_effect sg invocation before before request pname_pre 0 17 None).
  { unfold task_name_get_effect; rewrite Hearly; auto. }
  assert (Hsafe : task_name_get_return_safe before 0 17 None X).
  { eapply task_name_get_safe_return; [exact Heffect| | | |eassumption];
      try reflexivity; unfold critical_region_interval, kernel_resumption_trace; constructor. }
  unfold task_name_get_post, task_name_get_guarded_private; rewrite Hearly.
  Exists before before 17 (@None Z).
  unfold task_name_get_effect; rewrite Hearly; entailer!;
    unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_5 : OSTaskNameGet_return_wit_5.
Proof.
  left; intros; subst prio_pre.
  sep_apply_l_atomic (task_name_get_closed_nesting_in_range__critical_control
    platform critical sg invocation origin mask before); Intros.
  assert (Hnest : 0 < task_name_get_nesting before).
  { rewrite uchar_unsigned32_eq__critical_control in PreH2 by lia; lia. }
  assert (Hearly : task_name_get_early_error request pname_pre
      (task_name_get_nesting before) = Some 17).
  { unfold task_name_get_early_error.
    assert (Hr : (63 <? request) = false) by (apply Z.ltb_ge; lia).
    assert (Hp : (pname_pre =? 0) = false) by (apply Z.eqb_neq; auto).
    assert (Hn : (0 <? task_name_get_nesting before) = true) by (apply Z.ltb_lt; auto).
    rewrite Hr, Hp, Hn; reflexivity. }
  assert (Heffect : task_name_get_effect sg invocation before before request pname_pre 0 17 None).
  { unfold task_name_get_effect; rewrite Hearly; auto. }
  assert (Hsafe : task_name_get_return_safe before 0 17 None X).
  { eapply task_name_get_safe_return; [exact Heffect| | | |eassumption];
      try reflexivity; unfold critical_region_interval, kernel_resumption_trace; constructor. }
  unfold task_name_get_post, task_name_get_guarded_private; rewrite Hearly.
  Exists before before 17 (@None Z).
  unfold task_name_get_effect; rewrite Hearly; entailer!;
    unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_6 : OSTaskNameGet_return_wit_6.
Proof.
  left; intros; subst prio_pre pname_pre.
  assert (Hearly : task_name_get_early_error request 0
      (task_name_get_nesting before) = Some 12).
  { unfold task_name_get_early_error; replace request with 255 by lia; reflexivity. }
  assert (Heffect : task_name_get_effect sg invocation before before request 0 0 12 None).
  { unfold task_name_get_effect; rewrite Hearly; auto. }
  assert (Hsafe : task_name_get_return_safe before 0 12 None X).
  { eapply task_name_get_safe_return; [exact Heffect| | | |eassumption];
      try reflexivity; unfold critical_region_interval, kernel_resumption_trace; constructor. }
  unfold task_name_get_post, task_name_get_guarded_private; rewrite Hearly.
  Exists before before 12 (@None Z).
  unfold task_name_get_effect; rewrite Hearly; entailer!;
    unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_7 : OSTaskNameGet_return_wit_7.
Proof.
  left; intros; subst prio_pre pname_pre.
  assert (Hearly : task_name_get_early_error request 0
      (task_name_get_nesting before) = Some 12).
  { unfold task_name_get_early_error.
    assert (Hr : (63 <? request) = false) by (apply Z.ltb_ge; lia).
    rewrite Hr; reflexivity. }
  assert (Heffect : task_name_get_effect sg invocation before before request 0 0 12 None).
  { unfold task_name_get_effect; rewrite Hearly; auto. }
  assert (Hsafe : task_name_get_return_safe before 0 12 None X).
  { eapply task_name_get_safe_return; [exact Heffect| | | |eassumption];
      try reflexivity; unfold critical_region_interval, kernel_resumption_trace; constructor. }
  unfold task_name_get_post, task_name_get_guarded_private; rewrite Hearly.
  Exists before before 12 (@None Z).
  unfold task_name_get_effect; rewrite Hearly; entailer!;
    unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

Lemma proof_of_OSTaskNameGet_return_wit_8 : OSTaskNameGet_return_wit_8.
Proof.
  left; intros; subst prio_pre.
  assert (Hearly : task_name_get_early_error request pname_pre
      (task_name_get_nesting before) = Some 42).
  { unfold task_name_get_early_error.
    assert (Hr : (63 <? request) = true) by (apply Z.ltb_lt; lia).
    assert (Hs : (request =? 255) = false) by (apply Z.eqb_neq; auto).
    rewrite Hr, Hs; reflexivity. }
  assert (Heffect : task_name_get_effect sg invocation before before request pname_pre 0 42 None).
  { unfold task_name_get_effect; rewrite Hearly; auto. }
  assert (Hsafe : task_name_get_return_safe before 0 42 None X).
  { eapply task_name_get_safe_return; [exact Heffect| | | |eassumption];
      try reflexivity; unfold critical_region_interval, kernel_resumption_trace; constructor. }
  unfold task_name_get_post, task_name_get_guarded_private; rewrite Hearly.
  Exists before before 42 (@None Z).
  unfold task_name_get_effect; rewrite Hearly; entailer!;
    unfold critical_region_interval, kernel_resumption_trace; constructor.
Qed.

Lemma proof_of_OSTaskNameGet_partial_solve_wit_12_pure : OSTaskNameGet_partial_solve_wit_12_pure.
Proof.
  left; intros; unfold store_uchar; Intros.
  change Byte.max_unsigned with 255 in *.
  rewrite uchar_unsigned32_eq__critical_control in PreH1 by lia.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_1 : OSTaskNameGet_which_implies_wit_1.
Proof.
  left; intros; unfold task_name_get_pre, task_name_get_guarded_private; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_2 : OSTaskNameGet_which_implies_wit_2.
Proof.
  right; intros.
  destruct PreH1 as [Hnest _].
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen,
    task_name_get_raw_rep_split_nesting__resource_stages_strlen, Hnest.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_3 : OSTaskNameGet_which_implies_wit_3.
Proof.
  right; intros.
  destruct PreH1 as [Hnest _].
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen,
    task_name_get_raw_rep_split_nesting__resource_stages_strlen, Hnest.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_4 : OSTaskNameGet_which_implies_wit_4.
Proof.
  right; intros.
  destruct PreH1 as [Hnest _].
  sep_apply_l_atomic (store_uchar_with_range__resource_stages_strlen
    (&("OSIntNesting")) (task_name_get_nesting before)).
  rewrite task_name_get_closed_raw_rep__resource_stages_strlen,
    task_name_get_raw_rep_split_nesting__resource_stages_strlen, Hnest.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_5 : OSTaskNameGet_which_implies_wit_5.
Proof.
  left; intros; unfold task_name_get_closed; reflexivity.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_6 : OSTaskNameGet_which_implies_wit_6.
Proof.
  left; intros old request invocation before sg critical acquired pname
    Hvalid Hinterval Haccess Hearly Hrequest Haddresses.
  destruct (proj1 (Haccess Hearly acquired Hinterval Hvalid)) as [priority Hresolved].
  unfold task_name_get_resolved in Hresolved; rewrite Hrequest in Hresolved;
    cbn in Hresolved.
  destruct Hresolved as [view Hview].
  pose proof (proj1 (proj2 Haddresses)) as Hcurrent.
  Exists view priority; entailer!.
  unfold UCOS2_inv, task_name_get_private; rewrite Hrequest, Z.eqb_refl.
  pre_process; rewrite <- Hcurrent.
  rewrite (task_name_get_current_fields_equiv__task_lookup_fields
    sg invocation acquired view priority Hview).
  unfold tcb_cell, tcb_field_address; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_7 : OSTaskNameGet_which_implies_wit_7.
Proof.
  right; intros request invocation sg acquired view prio Hvalid Hrequest Hview Haddresses.
  assert (Hresolved : task_name_get_resolved sg invocation acquired 255 prio).
  { unfold task_name_get_resolved; cbn; exists view; exact Hview. }
  destruct Haddresses as [Hnesting [Hcurrent Hrest]].
  entailer!.
  unfold UCOS2_inv, task_name_get_private; rewrite Hrequest, Z.eqb_refl.
  rewrite <- Hcurrent.
  entailer!.
  sep_apply_r_atomic (proj2 (task_name_get_current_fields_equiv__task_lookup_fields
    sg invocation acquired view prio Hview)).
  unfold tcb_cell, tcb_field_address.
  entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_8 : OSTaskNameGet_which_implies_wit_8.
Proof.
  right; intros request invocation sg acquired prio Haddresses Hresolved.
  pose proof (task_name_get_resolved_in_range__task_lookup_fields
    sg invocation acquired request prio Hresolved) as Hprio.
  destruct Haddresses as [Hnesting [Hcurrent [Htable Hrest]]].
  unfold UCOS2_inv; pre_process; rewrite <- Htable.
  rewrite (task_name_get_table_cell_equiv__task_lookup_fields sg acquired prio Hprio).
  entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_9 : OSTaskNameGet_which_implies_wit_9.
Proof.
  right; intros request invocation sg acquired prio ptcb Haddresses Hresolved Hpointer Hvalid.
  pose proof (task_name_get_resolved_in_range__task_lookup_fields
    sg invocation acquired request prio Hresolved) as Hprio.
  assert (Hlookup : task_name_get_lookup sg invocation acquired request prio ptcb)
    by (split; assumption).
  destruct Haddresses as [Hnesting [Hcurrent [Htable Hrest]]].
  rewrite <- Htable.
  rewrite <- (task_name_get_table_cell_equiv__task_lookup_fields sg acquired prio Hprio).
  unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_10 : OSTaskNameGet_which_implies_wit_10.
Proof.
  right; intros request invocation before sg critical acquired Hvalid Hinterval.
  rewrite (task_name_get_private_acquired_eq critical sg invocation request before acquired
    Hvalid Hinterval); reflexivity.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_11 : OSTaskNameGet_which_implies_wit_11.
Proof.
  left; intros old request invocation before sg critical acquired ptcb prio pname
    Hvalid Hlookup Hnull Hreserved Haccess Hearly Hinterval.
  destruct (proj2 (Haccess Hearly acquired Hinterval Hvalid)
    prio ptcb Hlookup Hnull Hreserved) as [previous Hold].
  destruct (task_name_get_lookup_task__task_lookup_fields
    sg invocation acquired request prio ptcb Hvalid Hlookup Hnull Hreserved)
    as [tid [node [Htarget Hpointer]]].
  pose proof (proj1 Htarget) as Hentry.
  pose proof (proj2 Htarget) as Hnode.
  destruct (task_name_get_task_root_readable sg acquired tid node Hvalid Hnode)
    as [chars Hreadable].
  assert (Hsuccess : task_name_get_success sg invocation acquired request prio ptcb
    (task_name_get_name node) chars).
  { split; [exact Hlookup|]. exists tid, node.
    split; [exact Hentry|]. split; [exact Hnode|].
    split; [exact Hpointer|]. split; [exact Hnull|].
    split; [exact Hreserved|]. split; [reflexivity|].
    intros _; exact Hreadable. }
  Exists previous chars tid node; entailer!.
  rewrite Hold; unfold task_name_get_output_cell, UCOS2_inv; pre_process.
  rewrite Hpointer.
  sep_apply_l_atomic (proj1 (task_name_get_name_field_equiv__task_lookup_fields
    sg acquired tid node Hnode)); entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_12 : OSTaskNameGet_which_implies_wit_12.
Proof.
  right; intros request invocation sg acquired tid node chars prio ptcb
    Hvalid Htarget Hsuccess.
  destruct Htarget as [Hentry Hnode].
  destruct Hsuccess as [_ [target [found [Hentry' [Hnode' [Hpointer Hrest]]]]]].
  assert (target = tid) by congruence; subst target.
  rewrite Hpointer.
  rewrite <- (task_name_get_name_field_equiv__task_lookup_fields sg acquired tid node Hnode).
  unfold UCOS2_inv; entailer!.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_13 : OSTaskNameGet_which_implies_wit_13.
Proof.
  right; intros.
  assert (Hread : task_name_get_readable acquired.(NameState)
    (task_name_get_name node) chars).
  { unfold task_name_get_success in PreH2; destruct PreH2 as [_ [tid [actual Hfacts]]].
    tauto. }
  rewrite UCOS2_inv_split_names.
  unfold task_name_get_name_bytes, task_name_get_name_frame.
  destruct (Z.eqb (task_name_get_name node) 0) eqn:Hnull.
  - entailer!.
  - rewrite (task_name_get_name_split__resource_stages_strlen
      acquired.(NameState) (task_name_get_name node) chars).
    + entailer!.
    + apply Hread; apply Z.eqb_neq; exact Hnull.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_14 : OSTaskNameGet_which_implies_wit_14.
Proof.
  left; intros; unfold task_name_get_call_frame; reflexivity.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_15 : OSTaskNameGet_which_implies_wit_15.
Proof.
  left; intros; unfold task_name_get_call_frame; reflexivity.
Qed.

Lemma proof_of_OSTaskNameGet_which_implies_wit_16 : OSTaskNameGet_which_implies_wit_16.
Proof.
  right; intros.
  assert (Hread : task_name_get_readable acquired.(NameState)
    (task_name_get_name node) chars).
  { unfold task_name_get_success in PreH2; destruct PreH2 as [_ [tid [actual Hfacts]]].
    tauto. }
  rewrite UCOS2_inv_split_names.
  unfold task_name_get_name_bytes, task_name_get_name_frame.
  destruct (Z.eqb (task_name_get_name node) 0) eqn:Hnull.
  - entailer!.
  - rewrite (task_name_get_name_split__resource_stages_strlen
      acquired.(NameState) (task_name_get_name node) chars).
    + entailer!.
    + apply Hread; apply Z.eqb_neq; exact Hnull.
Qed.

Lemma proof_of_OS_StrLen_derive_task_name_get_spec_by_exact_frame_spec : OS_StrLen_derive_task_name_get_spec_by_exact_frame_spec.
Proof.
  unfold OS_StrLen_derive_task_name_get_spec_by_exact_frame_spec.
  intros psrc frame chars names entry; Intros; subst psrc.
  destruct (Z.eqb entry 0) eqn:Hnull.
  all: Exists entry entry names chars frame.
  all: match goal with |- _ |-- ?P ** (?Q -* ?R) =>
    assert (Hwand : emp |-- Q -* R)
  end.
  1,3: (apply_sepcon_adjoint; pre_process;
    apply derivable1_orp_elim; Intros retval; Exists retval;
    unfold task_name_get_length, task_name_get_name_bytes, os_strlen_result in *;
    rewrite Hnull; entailer!;
    first [apply Z.eqb_eq in Hnull; congruence | apply Z.eqb_neq in Hnull; congruence]).
  all: sep_apply_r_atomic Hwand.
  - Right.
    unfold task_name_get_name_bytes; rewrite Hnull.
    apply Z.eqb_eq in Hnull; entailer!.
  - Left.
    unfold task_name_get_name_bytes; rewrite Hnull.
    assert (entry <> 0) by (apply Z.eqb_neq; exact Hnull).
    unfold task_name_get_readable in *; entailer!.
Qed.

