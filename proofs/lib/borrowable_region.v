Require Import Coq.Lists.List.
Require Import SetsClass.SetsClass.
Require Import SimpleC.SL.ConAssertion.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
Import SetsNotation.
Local Open Scope sets.
Local Open Scope sac_scope.

(** A logical ownership protocol, not a new field of a C object.  The
    access token protects the shared complement; the loan token follows
    the borrowed resource.  The optional number identifies its borrower,
    not an execution mode or a permission obtained by knowing that number.

    In particular, opening a region with an outstanding loan transfers
    only Access.  An interrupt cannot return that loan merely by acquiring
    the complement.  Its caller's Loan token remains a disjoint frame.
    Connecting this protocol to CPU Save/Restore still requires the
    existing platform/CSL embedding and the actual heap partition. *)
Module BorrowableRegion.

Inductive Token : Type := Access | Loan.
Inductive State : Type :=
| Closed (borrower : option nat)
| Open (borrower : option nat).
Inductive Action : Type :=
| Acquire | Release | Borrow (owner : nat) | Return (owner : nat).

Definition empty_tokens : Token -> Prop := fun _ => False.
Definition full_tokens : Token -> Prop := fun _ => True.
Definition access_tokens : Token -> Prop := fun t => t = Access.
Definition loan_tokens : Token -> Prop := fun t => t = Loan.

Definition available_tokens (borrower : option nat) : Token -> Prop :=
  match borrower with None => full_tokens | Some _ => access_tokens end.

Definition invariant_tokens (s : State) : Token -> Prop :=
  match s with Closed borrower => available_tokens borrower | Open _ => empty_tokens end.

Inductive control_step : Action -> State -> State -> Prop :=
| AcquireStep : forall borrower, control_step Acquire (Closed borrower) (Open borrower)
| ReleaseStep : forall borrower, control_step Release (Open borrower) (Closed borrower)
| BorrowStep : forall owner, control_step (Borrow owner) (Open None) (Open (Some owner))
| ReturnStep : forall owner, control_step (Return owner) (Open (Some owner)) (Open None).

Definition required_tokens (action : Action) (s : State) : Token -> Prop :=
  match action with
  | Acquire => empty_tokens
  | Release => match s with Open borrower => available_tokens borrower | _ => full_tokens end
  | Borrow _ | Return _ => full_tokens
  end.

(** Conservation is stated for every token, including arbitrary caller
    frames.  A step never creates a token or duplicates one held by the
    shared invariant.  The local requirement on Borrow/Return is essential:
    their invariant-token sets are both empty, so conservation alone would
    otherwise let an ISR erase another continuation's outstanding loan. *)
Definition step (action : Action) (before : State) (owned_before : Token -> Prop)
  (after : State) (owned_after : Token -> Prop) : Prop :=
  control_step action before after /\
  (forall t, required_tokens action before t -> owned_before t) /\
  (forall t, ~ (owned_before t /\ invariant_tokens before t)) /\
  (forall t, ~ (owned_after t /\ invariant_tokens after t)) /\
  (forall t, owned_before t \/ invariant_tokens before t <->
             owned_after t \/ invariant_tokens after t).

Definition sts : ConAssertion.STS := {|
  ConAssertion.token := Token;
  ConAssertion.STS_state := State;
  ConAssertion.Transition := fun p q =>
    exists action, step action (fst p) (snd p) (fst q) (snd q);
  ConAssertion.InvownedToken := invariant_tokens
|}.

Lemma transition_disjoint_preserved :
  @ConAssertion.transtion_disjoint_preserved sts (@ConAssertion.Transition sts).
Proof.
  intros before after owned_before owned_after [action [_ [_ [Hbefore [Hafter _]]]]].
  cbn; sets_unfold; firstorder.
Qed.

Lemma transition_token_preserved :
  @ConAssertion.transition_token_preserved sts (@ConAssertion.Transition sts).
Proof.
  intros before after owned_before owned_after total
    [action [_ [_ [Hbefore [Hafter Htotal]]]]].
  unfold ConAssertion.TokenSet_join; cbn; sets_unfold; firstorder.
Qed.

Lemma step_frame : forall action before owned_before after owned_after frame,
  step action before owned_before after owned_after ->
  (forall t, ~ (owned_before t /\ frame t)) ->
  (forall t, ~ (invariant_tokens before t /\ frame t)) ->
  step action before (owned_before ∪ frame) after (owned_after ∪ frame).
Proof.
  intros action before owned_before after owned_after frame
    [Hstep [Hrequired [Hbefore [Hafter Htotal]]]] Hlocal Hshared.
  split; [exact Hstep|].
  cbn; sets_unfold; firstorder.
Qed.

Lemma transition_closed :
  @ConAssertion.Closed_transition sts (@ConAssertion.Transition sts).
Proof.
  intros before after owned_before owned_after frame [action Hstep] Hlocal Hshared.
  exists action; apply step_frame; [exact Hstep| |];
    cbn in *; sets_unfold in Hlocal; sets_unfold in Hshared; firstorder.
Qed.

Lemma acquire : forall borrower,
  step Acquire (Closed borrower) empty_tokens (Open borrower) (available_tokens borrower).
Proof.
  intro borrower; split; [constructor|].
  unfold required_tokens, invariant_tokens, empty_tokens; firstorder.
Qed.

Lemma release : forall borrower,
  step Release (Open borrower) (available_tokens borrower) (Closed borrower) empty_tokens.
Proof.
  intro borrower; split; [constructor|].
  unfold required_tokens, invariant_tokens, empty_tokens; firstorder.
Qed.

Lemma borrow : forall owner,
  step (Borrow owner) (Open None) full_tokens (Open (Some owner)) full_tokens.
Proof.
  intro owner; split; [constructor|].
  unfold required_tokens, invariant_tokens, full_tokens, empty_tokens; firstorder.
Qed.

Lemma return_loan : forall owner,
  step (Return owner) (Open (Some owner)) full_tokens (Open None) full_tokens.
Proof.
  intro owner; split; [constructor|].
  unfold required_tokens, invariant_tokens, full_tokens, empty_tokens; firstorder.
Qed.

Lemma return_requires_loan : forall owner before owned_before after owned_after,
  step (Return owner) before owned_before after owned_after -> owned_before Loan.
Proof. intros owner before owned_before after owned_after [_ [Hrequired _]]; apply Hrequired; exact I. Qed.

Lemma return_requires_access : forall owner before owned_before after owned_after,
  step (Return owner) before owned_before after owned_after -> owned_before Access.
Proof. intros owner before owned_before after owned_after [_ [Hrequired _]]; apply Hrequired; exact I. Qed.

Lemma return_owner_eq : forall owner borrower owned_before after owned_after,
  step (Return owner) (Open (Some borrower)) owned_before after owned_after -> owner = borrower.
Proof. intros owner borrower owned_before after owned_after [Hstep _]; inversion Hstep; reflexivity. Qed.

Lemma borrowed_acquire_preserves_loan : forall owner owned_before owned_after,
  step Acquire (Closed (Some owner)) owned_before (Open (Some owner)) owned_after ->
  (owned_before Loan <-> owned_after Loan).
Proof.
  intros owner owned_before owned_after [_ [_ [_ [_ Htotal]]]].
  specialize (Htotal Loan).
  change ((owned_before Loan \/ Loan = Access) <-> (owned_after Loan \/ False)) in Htotal.
  assert (Hdistinct : Loan <> Access) by discriminate.
  tauto.
Qed.

Lemma borrowed_acquire_cannot_return : forall owner owned_before acquired after released,
  ~ owned_before Loan ->
  step Acquire (Closed (Some owner)) owned_before (Open (Some owner)) acquired ->
  ~ step (Return owner) (Open (Some owner)) acquired after released.
Proof.
  intros owner owned_before acquired after released Habsent Hacquire Hreturn.
  apply Habsent; apply (proj2 (borrowed_acquire_preserves_loan _ _ _ Hacquire)).
  eapply return_requires_loan; exact Hreturn.
Qed.

(** This is the borrower's sequence: open the complement with its Loan
    token framed, reunite both tokens, then return the loan.  In contrast,
    the interrupt's Acquire above starts without that frame. *)
Lemma borrower_acquire : forall owner,
  step Acquire (Closed (Some owner)) loan_tokens (Open (Some owner)) full_tokens.
Proof.
  intro owner; split; [constructor|].
  unfold required_tokens, invariant_tokens, available_tokens, loan_tokens,
    access_tokens, full_tokens, empty_tokens.
  split; [intros t H; contradiction|].
  split; [intros t [Hloan Haccess]; congruence|].
  split; [intros t [_ H]; exact H|].
  intros []; simpl; intuition.
Qed.

Lemma borrower_release : forall owner,
  step Release (Open (Some owner)) full_tokens (Closed (Some owner)) loan_tokens.
Proof.
  intro owner; split; [constructor|].
  unfold required_tokens, invariant_tokens, available_tokens, loan_tokens,
    access_tokens, full_tokens, empty_tokens.
  split; [intros; exact I|].
  split; [intros t [_ H]; exact H|].
  split; [intros t [Hloan Haccess]; congruence|].
  intros []; simpl; intuition.
Qed.

Definition borrowed_by (owner : nat) (region : State) : Prop :=
  match region with Closed borrower | Open borrower => borrower = Some owner end.

(** The loan-holder's logical frame in the actual QCP STS model.  Its
    empty memory is only the ghost part; the physical pool is separate.
    Knowledge of [borrowed_by] without the Loan token is insufficient. *)
Definition loan_local_state (owner : nat) : @ConAssertion.Lstate sts :=
  @ConAssertion.mk_Lstate sts Mem.empty_mem (borrowed_by owner) loan_tokens.

Lemma loan_local_state_valid : forall owner,
  @ConAssertion.valid_Lstate sts (loan_local_state owner).
Proof.
  intros owner [borrower|borrower] Hstate;
    change (borrower = Some owner) in Hstate; subst borrower;
    cbn; sets_unfold;
    unfold loan_tokens, invariant_tokens, available_tokens, access_tokens, empty_tokens.
  all: intros t; split;
    [intros [Hloan Hinv]; subst t; first [discriminate Hinv | exact Hinv]
    | intros Hfalse; contradiction].
Qed.

Lemma loan_rely_closed : forall owner,
  @ConAssertion.rely_closed sts (loan_local_state owner) (@ConAssertion.Transition sts).
Proof.
  intros owner before after Hborrow [action [Hcontrol [Hrequired _]]].
  change (borrowed_by owner before) in Hborrow.
  change (borrowed_by owner after).
  change (control_step action before after) in Hcontrol.
  change (forall t, required_tokens action before t ->
    ~ (loan_tokens t \/ invariant_tokens before t)) in Hrequired.
  destruct Hcontrol; cbn [borrowed_by] in Hborrow |- *; try assumption; try discriminate.
  exfalso; specialize (Hrequired Loan I).
  cbn in Hrequired; sets_unfold in Hrequired.
  apply Hrequired; left; reflexivity.
Qed.

End BorrowableRegion.

(**
   An indexed observation/borrow protocol for a concrete shared-region
   embedding.  The STS above records conservation of logical tokens, but it
   intentionally does not identify a token with a C heap fragment.  This
   record is the missing linear interface used by functions which observe a
   field before Save, acquire the complete protected representation, mutate
   it, and return a completion-indexed view before Restore/Unlock.

   Every field is an entailment over actual assertions.  Consequently a
   client must provide a real source-backed instance; merely knowing the
   STS state or a borrower number cannot construct this protocol.  The
   protocol is generic in the caller index and abstract kernel state so
   Timer, Event, Task, and future modules can reuse it without adding fields
   to the kernel state record. *)
Record ObservationLoanProtocol (Index State : Type) : Type := {
  observation_source : Index -> State -> Assertion;
  observation_view : Index -> State -> Assertion;
  observation_remainder : Index -> State -> Assertion;
  observation_acquired : Index -> State -> Assertion;
  observation_completed_view : Index -> State -> Assertion;
  observation_transition : State -> State -> Prop;
  observation_open : forall index state,
    observation_source index state --||--
      observation_view index state ** observation_remainder index state;
  observation_acquire : forall index before after,
    observation_transition before after ->
    observation_view index before ** observation_remainder index before --||--
      observation_acquired index after;
  observation_release : forall index before after,
    observation_transition before after ->
    observation_acquired index after --||--
      observation_completed_view index after ** observation_remainder index after;
  observation_close : forall index state,
    observation_completed_view index state ** observation_remainder index state --||--
      observation_source index state
}.
