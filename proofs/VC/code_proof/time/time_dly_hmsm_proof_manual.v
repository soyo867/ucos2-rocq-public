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
From Ucos2Verify.VC.code.time Require Import time_dly_hmsm_goal.
From Ucos2Verify.VC.code.time Require Import time_dly_hmsm_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.time.spec.time_dly_hmsm_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSTimeDlyHMSM_entail_wit_1_1 : OSTimeDlyHMSM_entail_wit_1_1.
Proof.
  unfold OSTimeDlyHMSM_entail_wit_1_1; left; intros.
  subst hours_pre minutes_pre seconds_pre ms_pre.
  pose proof (proj1 PreH12) as Hranges.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hh [Hm [Hs Hms]]].
  rewrite (unsigned_last_nbits_eq h 32
    ltac:(change (0 <= h < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq m 32
    ltac:(change (0 <= m < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq s 32
    ltac:(change (0 <= s < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq millis 32
    ltac:(change (0 <= millis < 4294967296); lia)) in *.
  assert (Hnonzero : ((h =? 0) && (m =? 0) && (s =? 0) && (millis =? 0))%bool = false).
  { apply Bool.not_true_is_false; intro Hzero.
    repeat rewrite Bool.andb_true_iff in Hzero.
    repeat rewrite Z.eqb_eq in Hzero; tauto. }
  assert (Hcode : time_dly_hmsm_error h m s millis before = 0).
  { unfold time_dly_hmsm_error.
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_ints before)) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_locks before)) ltac:(lia)).
    rewrite Hnonzero.
    rewrite (proj2 (Z.ltb_ge 59 m) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 59 s) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 999 millis) ltac:(lia)); reflexivity. }
  entailer!; lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_entail_wit_1_2 : OSTimeDlyHMSM_entail_wit_1_2.
Proof.
  unfold OSTimeDlyHMSM_entail_wit_1_2; left; intros.
  subst hours_pre minutes_pre seconds_pre ms_pre.
  pose proof (proj1 PreH11) as Hranges.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hh [Hm [Hs Hms]]].
  rewrite (unsigned_last_nbits_eq h 32
    ltac:(change (0 <= h < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq m 32
    ltac:(change (0 <= m < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq s 32
    ltac:(change (0 <= s < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq millis 32
    ltac:(change (0 <= millis < 4294967296); lia)) in *.
  assert (Hnonzero : ((h =? 0) && (m =? 0) && (s =? 0) && (millis =? 0))%bool = false).
  { apply Bool.not_true_is_false; intro Hzero.
    repeat rewrite Bool.andb_true_iff in Hzero.
    repeat rewrite Z.eqb_eq in Hzero; tauto. }
  assert (Hcode : time_dly_hmsm_error h m s millis before = 0).
  { unfold time_dly_hmsm_error.
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_ints before)) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_locks before)) ltac:(lia)).
    rewrite Hnonzero.
    rewrite (proj2 (Z.ltb_ge 59 m) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 59 s) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 999 millis) ltac:(lia)); reflexivity. }
  entailer!; lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_entail_wit_1_3 : OSTimeDlyHMSM_entail_wit_1_3.
Proof.
  unfold OSTimeDlyHMSM_entail_wit_1_3; left; intros.
  subst hours_pre minutes_pre seconds_pre ms_pre.
  pose proof (proj1 PreH10) as Hranges.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hh [Hm [Hs Hms]]].
  rewrite (unsigned_last_nbits_eq h 32
    ltac:(change (0 <= h < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq m 32
    ltac:(change (0 <= m < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq s 32
    ltac:(change (0 <= s < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq millis 32
    ltac:(change (0 <= millis < 4294967296); lia)) in *.
  assert (Hnonzero : ((h =? 0) && (m =? 0) && (s =? 0) && (millis =? 0))%bool = false).
  { apply Bool.not_true_is_false; intro Hzero.
    repeat rewrite Bool.andb_true_iff in Hzero.
    repeat rewrite Z.eqb_eq in Hzero; tauto. }
  assert (Hcode : time_dly_hmsm_error h m s millis before = 0).
  { unfold time_dly_hmsm_error.
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_ints before)) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_locks before)) ltac:(lia)).
    rewrite Hnonzero.
    rewrite (proj2 (Z.ltb_ge 59 m) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 59 s) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 999 millis) ltac:(lia)); reflexivity. }
  entailer!; lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_entail_wit_1_4 : OSTimeDlyHMSM_entail_wit_1_4.
Proof.
  unfold OSTimeDlyHMSM_entail_wit_1_4; left; intros.
  subst hours_pre minutes_pre seconds_pre ms_pre.
  pose proof (proj1 PreH9) as Hranges.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hh [Hm [Hs Hms]]].
  rewrite (unsigned_last_nbits_eq h 32
    ltac:(change (0 <= h < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq m 32
    ltac:(change (0 <= m < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq s 32
    ltac:(change (0 <= s < 4294967296); lia)) in *.
  rewrite (unsigned_last_nbits_eq millis 32
    ltac:(change (0 <= millis < 4294967296); lia)) in *.
  assert (Hnonzero : ((h =? 0) && (m =? 0) && (s =? 0) && (millis =? 0))%bool = false).
  { apply Bool.not_true_is_false; intro Hzero.
    repeat rewrite Bool.andb_true_iff in Hzero.
    repeat rewrite Z.eqb_eq in Hzero; tauto. }
  assert (Hcode : time_dly_hmsm_error h m s millis before = 0).
  { unfold time_dly_hmsm_error.
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_ints before)) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_locks before)) ltac:(lia)).
    rewrite Hnonzero.
    rewrite (proj2 (Z.ltb_ge 59 m) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 59 s) ltac:(lia)).
    rewrite (proj2 (Z.ltb_ge 999 millis) ltac:(lia)); reflexivity. }
  entailer!; lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_entail_wit_2 : OSTimeDlyHMSM_entail_wit_2.
Proof.
  unfold OSTimeDlyHMSM_entail_wit_2; left; intros.
  pose proof (time_dly_hmsm_c_ticks h m s millis
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hticks.
  pose proof (time_dly_hmsm_delay_safe environment critical sg caller mask
    h m s millis before X PreH9 PreH11) as Hsafe.
  pose proof (proj2 PreH12 PreH9) as Hadmit.
  unfold time_dly_call_pre; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_1 : OSTimeDlyHMSM_return_wit_1.
Proof.
  unfold OSTimeDlyHMSM_return_wit_1; left; intros.
  apply time_dly_hmsm_delay_call_post; assumption.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_2 : OSTimeDlyHMSM_return_wit_2.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_3 : OSTimeDlyHMSM_return_wit_3.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_4 : OSTimeDlyHMSM_return_wit_4.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_5 : OSTimeDlyHMSM_return_wit_5.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_6 : OSTimeDlyHMSM_return_wit_6.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_7 : OSTimeDlyHMSM_return_wit_7.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_8 : OSTimeDlyHMSM_return_wit_8.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_9 : OSTimeDlyHMSM_return_wit_9.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_10 : OSTimeDlyHMSM_return_wit_10.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_11 : OSTimeDlyHMSM_return_wit_11.
Proof.
  left; intros.
  subst ms_pre seconds_pre minutes_pre hours_pre.
  match goal with
  | Hentry : time_dly_hmsm_entry_facts _ _ _ _ _ _ _ _ _ _ |- _ =>
      pose proof (proj1 Hentry) as Hranges
  end.
  unfold time_dly_hmsm_input_ranges in Hranges.
  destruct Hranges as [Hhours [Hminutes [Hseconds Hmillis]]].
  repeat match goal with
  | Hguard : context [unsigned_last_nbits ?value 32] |- _ =>
      rewrite (unsigned_last_nbits_eq value 32) in Hguard by
        (change (0 <= value < 4294967296); lia)
  end.
  apply time_dly_hmsm_error_call_post; [|lia|assumption].
  unfold time_dly_hmsm_error.
  repeat match goal with
  | |- context [Z.ltb ?a ?b] =>
      destruct (Z.ltb_spec a b); cbn; try lia
  | |- context [Z.eqb ?a ?b] =>
      destruct (Z.eqb_spec a b); cbn; try lia
  end.
  all: lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_12 : OSTimeDlyHMSM_return_wit_12.
Proof.
  unfold OSTimeDlyHMSM_return_wit_12; left; intros.
  assert (Hcode : time_dly_hmsm_error h m s millis before = 50).
  { unfold time_dly_hmsm_error.
    rewrite (proj2 (Z.ltb_ge 0 (os_sched_ints before)) ltac:(lia)).
    rewrite (proj2 (Z.ltb_lt 0 (os_sched_locks before)) ltac:(lia)); reflexivity. }
  pose proof (time_dly_hmsm_error_call_post environment critical saved_local sg caller mask
    h m s millis before 50 frame X Hcode ltac:(lia) PreH14) as Hpost.
  pose proof PreH3 as Haddresses.
  unfold task_suspend_addresses, os_sched_global_addresses in Haddresses.
  destruct Haddresses as [_ [Hints [Hlocks Hrest]]].
  sep_apply_r_atomic Hpost.
  rewrite time_dly_closed_split_counters.
  rewrite <- Hints, <- Hlocks; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_return_wit_13 : OSTimeDlyHMSM_return_wit_13.
Proof.
  unfold OSTimeDlyHMSM_return_wit_13; left; intros.
  assert (Hcode : time_dly_hmsm_error h m s millis before = 85).
  { unfold time_dly_hmsm_error.
    rewrite (proj2 (Z.ltb_lt 0 (os_sched_ints before)) ltac:(lia)); reflexivity. }
  pose proof (time_dly_hmsm_error_call_post environment critical saved_local sg caller mask
    h m s millis before 85 frame X Hcode ltac:(lia) PreH13) as Hpost.
  pose proof PreH2 as Haddresses.
  unfold task_suspend_addresses, os_sched_global_addresses in Haddresses.
  destruct Haddresses as [_ [Hints [Hlocks Hrest]]].
  sep_apply_r_atomic Hpost.
  rewrite time_dly_closed_split_counters.
  rewrite <- Hints, <- Hlocks; entailer!.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_which_implies_wit_1 : OSTimeDlyHMSM_which_implies_wit_1.
Proof.
  unfold OSTimeDlyHMSM_which_implies_wit_1; left; intros.
  unfold time_dly_hmsm_call_pre; Intros.
  rewrite time_dly_closed_split_counters.
  prop_apply_p (store_uchar_range (g_OSIntNesting sg) (os_sched_ints before)); Intros.
  prop_apply_p (store_uchar_range (g_OSLockNesting sg) (os_sched_locks before)); Intros.
  change (0 <= os_sched_ints before <= 255) in H0.
  change (0 <= os_sched_locks before <= 255) in H1.
  pose proof PreH1 as Haddresses.
  unfold task_suspend_addresses, os_sched_global_addresses in Haddresses.
  destruct Haddresses as [_ [Hints [Hlocks Hrest]]].
  rewrite <- Hints, <- Hlocks; entailer!; lia.
Qed. 

Lemma proof_of_OSTimeDlyHMSM_which_implies_wit_2 : OSTimeDlyHMSM_which_implies_wit_2.
Proof.
  unfold OSTimeDlyHMSM_which_implies_wit_2; left; intros.
  pose proof PreH1 as Haddresses.
  unfold task_suspend_addresses, os_sched_global_addresses in Haddresses.
  destruct Haddresses as [_ [Hints [Hlocks Hrest]]].
  rewrite time_dly_closed_split_counters.
  rewrite <- Hints, <- Hlocks; entailer!.
Qed. 

