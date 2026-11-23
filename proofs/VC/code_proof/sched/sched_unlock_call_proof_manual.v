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
From Ucos2Verify.VC.code.sched Require Import sched_unlock_call_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.VC.code.sched.spec.sched_unlock_call_api_program_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

Lemma proof_of_OSSchedUnlock_entail_wit_1 : OSSchedUnlock_entail_wit_1.
Proof.
  left; intros.
  assert (Hrun : os_sched_unlock_running before = 1).
  { rewrite unsigned_last_nbits_eq in PreH3.
    - exact PreH3.
    - unfold os_sched_unlock_running.
      destruct before.(SchedState).(isRunning); cbn; lia. }
  pose proof (os_sched_unlock_acquire_facts external critical sg context mask retval
    before entry_2 PreH6 PreH7 Hrun PreH1 PreH2) as Hbody.
  pose proof PreH4 as Haddrs.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in Haddrs.
  destruct Haddrs as [_ [Hints [Hlocks _]]].
  Exists entry_2.
  sep_apply_l_atomic (os_sched_unlock_split_counters sg entry_2).
  Intros.
  rewrite <- Hints, <- Hlocks.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_entail_wit_2 : OSSchedUnlock_entail_wit_2.
Proof.
  left; intros.
  Exists entry_2.
  rewrite (os_sched_unlock_positive_counted_locks entry_2 PreH2 ltac:(lia)).
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_entail_wit_3 : OSSchedUnlock_entail_wit_3.
Proof.
  left; intros.
  pose proof (os_sched_unlock_positive_counted_locks entry_2 PreH5 PreH6) as Hcount.
  rewrite unsigned_last_nbits_eq in PreH1; [|rewrite Hcount; cbn; lia].
  assert (Hrequest : os_sched_unlock_requests entry_2 = true).
  { unfold os_sched_unlock_requests.
    apply sched_unlock_requests_schedule_iff.
    split; [reflexivity|].
    change (os_sched_ints entry_2 = 0 /\ os_sched_locks entry_2 = 1).
    split; [exact PreH5|lia]. }
  pose proof PreH4 as Hbody.
  destruct Hbody as [_ [_ [Hvalid _]]].
  pose proof PreH2 as Haddrs.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in Haddrs.
  destruct Haddrs as [_ [Hints [Hlocks _]]].
  Exists entry_2.
  rewrite Hints, Hlocks in PreH2 |- *.
  sep_apply_l_atomic (os_sched_unlock_merge_counters sg entry_2 Hvalid).
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_entail_wit_4 : OSSchedUnlock_entail_wit_4.
Proof.
  left; intros.
  pose proof PreH3 as (Hrunning & Hinterval & Hvalid & Hsaved & Hsafe).
  destruct Hsaved as [_ Hmask].
  pose proof (proj2 PreH1) as Hsched_addresses.
  Exists entry_2.
  rewrite Hmask.
  sep_apply_l_atomic (os_sched_unlock_sched_pre external platform critical sg
    context mask entry_2 Hvalid (Hsafe PreH4)).
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_entail_wit_5 : OSSchedUnlock_entail_wit_5.
Proof.
  left; intros.
  pose proof (os_sched_unlock_positive_counted_locks entry_2 PreH5 PreH6) as Hcount.
  rewrite unsigned_last_nbits_eq in PreH1; [|rewrite Hcount; cbn; lia].
  assert (Hrequest : os_sched_unlock_requests entry_2 = false).
  { unfold os_sched_unlock_requests, sched_unlock_requests_schedule.
    change (true && (os_sched_ints entry_2 =? 0) &&
      (os_sched_locks entry_2 =? 1) = false)%bool.
    rewrite PreH5; cbn.
    apply Z.eqb_neq; lia. }
  pose proof PreH4 as Hbody.
  destruct Hbody as [_ [_ [Hvalid _]]].
  pose proof PreH2 as Haddrs.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in Haddrs.
  destruct Haddrs as [_ [Hints [Hlocks _]]].
  Exists entry_2.
  rewrite Hints, Hlocks.
  sep_apply_l_atomic (os_sched_unlock_merge_counters sg entry_2 Hvalid).
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_entail_wit_6 : OSSchedUnlock_entail_wit_6.
Proof.
  left; intros.
  assert (Hlock : os_sched_locks entry_2 = 0) by lia.
  assert (Hcount : os_sched_unlock_counted_locks entry_2 = os_sched_locks entry_2).
  { unfold os_sched_unlock_counted_locks, sched_unlock_state.
    unfold os_sched_ints in PreH2; unfold os_sched_locks in Hlock |- *.
    rewrite PreH2, Hlock; cbn; exact Hlock. }
  assert (Hrequest : os_sched_unlock_requests entry_2 = false).
  { unfold os_sched_unlock_requests, sched_unlock_requests_schedule.
    change (true && (os_sched_ints entry_2 =? 0) &&
      (os_sched_locks entry_2 =? 1) = false)%bool.
    rewrite PreH2, Hlock; reflexivity. }
  pose proof PreH5 as Hbody.
  destruct Hbody as [_ [_ [Hvalid _]]].
  pose proof PreH3 as Haddrs.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in Haddrs.
  destruct Haddrs as [_ [Hints [Hlocks _]]].
  pose proof (os_sched_unlock_merge_counters sg entry_2 Hvalid) as Hmerge.
  rewrite Hcount in Hmerge.
  Exists entry_2.
  rewrite Hints, Hlocks.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_entail_wit_7 : OSSchedUnlock_entail_wit_7.
Proof.
  left; intros.
  assert (Hint : (entry_2.(IntrState).(intNesting) =? 0) = false).
  { apply Z.eqb_neq; exact PreH1. }
  assert (Hcount : os_sched_unlock_counted_locks entry_2 = os_sched_locks entry_2).
  { unfold os_sched_unlock_counted_locks, sched_unlock_state, os_sched_locks.
    rewrite Hint; reflexivity. }
  assert (Hrequest : os_sched_unlock_requests entry_2 = false).
  { unfold os_sched_unlock_requests, sched_unlock_requests_schedule.
    rewrite Hint; reflexivity. }
  pose proof PreH4 as Hbody.
  destruct Hbody as [_ [_ [Hvalid _]]].
  pose proof PreH2 as Haddrs.
  unfold os_sched_unlock_global_addresses, os_sched_global_addresses in Haddrs.
  destruct Haddrs as [_ [Hints [Hlocks _]]].
  pose proof (os_sched_unlock_merge_counters sg entry_2 Hvalid) as Hmerge.
  rewrite Hcount in Hmerge.
  Exists entry_2.
  rewrite Hints, Hlocks.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_return_wit_1 : OSSchedUnlock_return_wit_1.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_sched_unlock_continuation external critical sg context before X |- _ =>
      sep_apply_r_atomic (os_sched_unlock_post_program_post external platform critical
        sg context mask before X Hsafe)
  end.
  destruct PreH5 as (Hrunning & Hinterval & Hvalid & Hsaved & Hsafe).
  pose proof (os_sched_unlock_checkpoint_preserves_validity sg true entry Hvalid)
    as Hcheckpoint.
  unfold os_sched_unlock_post.
  Right; Exists entry.
  rewrite PreH6.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_return_wit_2 : OSSchedUnlock_return_wit_2.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_sched_unlock_continuation external critical sg context before X |- _ =>
      sep_apply_r_atomic (os_sched_unlock_post_program_post external platform critical
        sg context mask before X Hsafe)
  end.
  destruct PreH2 as (Hrunning & Hinterval & Hvalid & Hsaved & Hsafe).
  destruct Hsaved as [_ Hmask].
  pose proof (os_sched_unlock_checkpoint_preserves_validity sg true entry Hvalid)
    as Hcheckpoint.
  unfold os_sched_unlock_post.
  Right; Exists entry.
  rewrite PreH3, Hmask.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_return_wit_3 : OSSchedUnlock_return_wit_3.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_sched_unlock_continuation external critical sg context before X |- _ =>
      sep_apply_r_atomic (os_sched_unlock_post_program_post external platform critical
        sg context mask before X Hsafe)
  end.
  destruct PreH2 as (Hrunning & Hinterval & Hvalid & Hsaved & Hsafe).
  destruct Hsaved as [_ Hmask].
  pose proof (os_sched_unlock_checkpoint_preserves_validity sg true entry Hvalid)
    as Hcheckpoint.
  unfold os_sched_unlock_post.
  Right; Exists entry.
  rewrite PreH3, Hmask.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_return_wit_4 : OSSchedUnlock_return_wit_4.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_sched_unlock_continuation external critical sg context before X |- _ =>
      sep_apply_r_atomic (os_sched_unlock_post_program_post external platform critical
        sg context mask before X Hsafe)
  end.
  destruct PreH2 as (Hrunning & Hinterval & Hvalid & Hsaved & Hsafe).
  destruct Hsaved as [_ Hmask].
  pose proof (os_sched_unlock_checkpoint_preserves_validity sg true entry Hvalid)
    as Hcheckpoint.
  unfold os_sched_unlock_post.
  Right; Exists entry.
  rewrite PreH3, Hmask.
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_return_wit_5 : OSSchedUnlock_return_wit_5.
Proof.
  left; intros.
  lazymatch goal with
  | Hsafe : os_sched_unlock_continuation external critical sg context before X |- _ =>
      sep_apply_r_atomic (os_sched_unlock_post_program_post external platform critical
        sg context mask before X Hsafe)
  end.
  assert (Hrunning : before.(SchedState).(isRunning) = false).
  { unfold os_sched_unlock_running in PreH1.
    destruct before.(SchedState).(isRunning);
      [exfalso; apply PreH1; reflexivity|reflexivity]. }
  unfold os_sched_unlock_post.
  Left.
  rewrite (proj1 PreH2).
  entailer!.
Qed.

Lemma proof_of_OSSchedUnlock_which_implies_wit_1 : OSSchedUnlock_which_implies_wit_1.
Proof.
  left; intros.
  pose proof (proj1 PreH1) as Hrunning.
  unfold os_sched_unlock_program_pre, os_sched_unlock_pre.
  rewrite Hrunning in PreH1 |- *.
  entailer!.
Qed.
