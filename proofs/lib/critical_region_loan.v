Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.borrowable_region.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Import UCOS2_C_Rules.
Local Open Scope sac_scope.
Local Open Scope Z_scope.

(** The two physical pieces of the critical-region outside view.  The
    [OSRunning] byte is kept separate because a saved observation may carry
    it while the remaining kernel representation is acquired by another
    continuation.  This is a spatial split of existing C memory; neither
    definition adds a field to [UCOS2_Verify_State]. *)
Definition critical_region_running_rep (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRunning) # UChar |->
    (if s.(SchedState).(isRunning) then 1 else 0).

Definition critical_region_share_tokens (access running : bool) :
  BorrowableRegion.Token -> Prop :=
  fun token => match token with
  | BorrowableRegion.Access => access = true
  | BorrowableRegion.Loan => running = true
  end.

Definition critical_region_share_rep (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (s : UCOS2_Verify_State)
  (access running : bool) : Assertion :=
  (if access then
     critical_region_outside_without_running critical sg invocation s
   else emp) **
  (if running then critical_region_running_rep sg s else emp).

Definition critical_region_shared_access (region : BorrowableRegion.State) : bool :=
  match region with
  | BorrowableRegion.Closed _ => true
  | BorrowableRegion.Open _ => false
  end.

Definition critical_region_shared_running (region : BorrowableRegion.State) : bool :=
  match region with
  | BorrowableRegion.Closed None => true
  | _ => false
  end.

Definition critical_region_shared_rep (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (s : UCOS2_Verify_State)
  (region : BorrowableRegion.State) : Assertion :=
  critical_region_share_rep critical sg invocation s
    (critical_region_shared_access region)
    (critical_region_shared_running region).

Lemma critical_region_share_token_bits : forall region token,
  BorrowableRegion.invariant_tokens region token <->
  critical_region_share_tokens (critical_region_shared_access region)
    (critical_region_shared_running region) token.
Proof.
  intros [[owner|]|[owner|]] [];
    unfold BorrowableRegion.invariant_tokens,
      BorrowableRegion.available_tokens,
      BorrowableRegion.access_tokens,
      BorrowableRegion.full_tokens,
      BorrowableRegion.empty_tokens,
      critical_region_share_tokens,
      critical_region_shared_access,
      critical_region_shared_running;
    simpl; intuition discriminate.
Qed.

Lemma critical_region_full_share : forall critical sg invocation s,
  critical_region_share_rep critical sg invocation s true true --||--
    critical_region_outside critical sg invocation s.
Proof.
  intros critical sg invocation s.
  unfold critical_region_share_rep, critical_region_running_rep,
    critical_region_outside.
  split; entailer!.
Qed.

Lemma critical_region_share_join : forall critical sg invocation s
  access running other_access other_running,
  andb access other_access = false ->
  andb running other_running = false ->
  critical_region_share_rep critical sg invocation s access running **
    critical_region_share_rep critical sg invocation s other_access other_running
    --||--
    critical_region_share_rep critical sg invocation s
      (orb access other_access) (orb running other_running).
Proof.
  intros critical sg invocation s [] [] [] [] Haccess Hrunning;
    simpl in Haccess, Hrunning; try discriminate;
    unfold critical_region_share_rep; simpl; split; entailer!.
Qed.

(** The physical embedding of every valid token step.  The STS supplies
    conservation, while the two [share_join] applications account for the
    actual byte/resource assertions.  This theorem deliberately does not
    claim that an ARM/BSP primitive implements the step; its caller must
    still provide the source-level transition and platform contract. *)
Lemma critical_region_step_resources : forall critical sg invocation s
  action before after access running next_access next_running,
  BorrowableRegion.step action before
    (critical_region_share_tokens access running)
    after (critical_region_share_tokens next_access next_running) ->
  critical_region_share_rep critical sg invocation s access running **
    critical_region_shared_rep critical sg invocation s before --||--
  critical_region_share_rep critical sg invocation s next_access next_running **
    critical_region_shared_rep critical sg invocation s after.
Proof.
  intros critical sg invocation s action before after access running
    next_access next_running
    [_ [_ [Hbefore [Hafter Htotal]]]].
  pose proof (Hbefore BorrowableRegion.Access) as Hba.
  pose proof (Hbefore BorrowableRegion.Loan) as Hbr.
  pose proof (Hafter BorrowableRegion.Access) as Haa.
  pose proof (Hafter BorrowableRegion.Loan) as Har.
  pose proof (Htotal BorrowableRegion.Access) as Hta.
  pose proof (Htotal BorrowableRegion.Loan) as Htr.
  rewrite !critical_region_share_token_bits in Hba, Hbr, Haa, Har, Hta, Htr.
  rewrite (critical_region_share_token_bits after BorrowableRegion.Access) in Hta.
  rewrite (critical_region_share_token_bits after BorrowableRegion.Loan) in Htr.
  cbn [critical_region_share_tokens] in Hba, Hbr, Haa, Har, Hta, Htr.
  assert (Hba' : andb access (critical_region_shared_access before) = false).
  { destruct access, (critical_region_shared_access before); simpl in *; tauto. }
  assert (Hbr' : andb running (critical_region_shared_running before) = false).
  { destruct running, (critical_region_shared_running before); simpl in *; tauto. }
  assert (Haa' : andb next_access (critical_region_shared_access after) = false).
  { destruct next_access, (critical_region_shared_access after); simpl in *; tauto. }
  assert (Har' : andb next_running (critical_region_shared_running after) = false).
  { destruct next_running, (critical_region_shared_running after); simpl in *; tauto. }
  assert (Haccess : orb access (critical_region_shared_access before) =
    orb next_access (critical_region_shared_access after)).
  { apply Bool.eq_true_iff_eq; rewrite !Bool.orb_true_iff; exact Hta. }
  assert (Hrunning : orb running (critical_region_shared_running before) =
    orb next_running (critical_region_shared_running after)).
  { apply Bool.eq_true_iff_eq; rewrite !Bool.orb_true_iff; exact Htr. }
  unfold critical_region_shared_rep.
  rewrite (critical_region_share_join _ _ _ _ _ _ _ _ Hba' Hbr'),
    (critical_region_share_join _ _ _ _ _ _ _ _ Haa' Har'), Haccess, Hrunning.
  split; reflexivity.
Qed.

Lemma critical_region_shared_rep_closed : forall critical sg invocation s borrower,
  critical_region_shared_rep critical sg invocation s
    (BorrowableRegion.Closed borrower) --||--
  critical_region_share_rep critical sg invocation s true
    (match borrower with None => true | Some _ => false end).
Proof.
  intros; destruct borrower; unfold critical_region_shared_rep,
    critical_region_shared_access, critical_region_shared_running;
    reflexivity.
Qed.

Lemma critical_region_observation_cannot_duplicate_running :
  forall critical sg invocation s,
  critical_region_running_rep sg s **
    critical_region_outside critical sg invocation s |-- coq_prop False.
Proof.
  intros; apply critical_region_outside_excludes_running_loan.
Qed.
