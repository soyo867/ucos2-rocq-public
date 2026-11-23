Require Export Ucos2Verify.VC.code.timer.spec.tmr_stop_call_cut_spec.
Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

(** An ordinary QCP predicate application is a spatial atom.  The full
    callback capability is environment-only, so using it directly as that
    atom would permit it to own an arbitrary leftover heap fragment.
    This carrier gives that atom exactly the separation unit.  The public
    precondition and the full callback specification keep their meanings. *)
Section StopCallResources.
Context {Application : Type} (AppRep : Application -> TmrStopRules.expr).
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (effects : TmrStopEffects Application) (mask perr : Z).
Context (domain : Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop).
Context (pooled : bool) (pointer index opt argument : Z)
  (raw_type raw_state : TmrStopState Application -> Z).

Local Notation capabilities :=
  (tmr_stop_call_callback_capabilities AppRep external platform critical sg effects
    mask perr domain pooled pointer index opt argument raw_type raw_state).

Definition tmr_stop_call_callback_resources (context : OsSchedCallContext)
  (before : TmrStopState Application) : TmrStopRules.expr :=
  TmrStopRules.andp TmrStopRules.emp (capabilities context before).

Lemma tmr_stop_call_callback_resources_emp : forall context before,
  TmrStopRules.derivable1 (tmr_stop_call_callback_resources context before)
    TmrStopRules.emp.
Proof. intros context before heap [Hunit Hcap]. exact Hunit. Qed.

Lemma tmr_stop_call_callback_resources_capabilities : forall context before,
  TmrStopRules.derivable1 (tmr_stop_call_callback_resources context before)
    (capabilities context before).
Proof. intros context before heap [Hunit Hcap]. exact Hcap. Qed.

Lemma tmr_stop_call_callback_resources_transport : forall context before first second,
  snd first = snd second -> TmrStopRules.emp second ->
  tmr_stop_call_callback_resources context before first ->
  tmr_stop_call_callback_resources context before second.
Proof.
  intros context before first second Henv Hunit [Hfirst Hcap].
  split; [exact Hunit|].
  exact (tmr_stop_call_callback_capabilities_environment_only AppRep external platform
    critical sg effects mask perr domain pooled pointer index opt argument raw_type
    raw_state context before first second Henv Hcap).
Qed.

(** The split chooses an actual unit supplied by the separation algebra;
    it does not turn an arbitrary capability-owning heap into emp. *)
Lemma tmr_stop_call_callback_capabilities_split_resources : forall context before P,
  TmrStopRules.derivable1
    (TmrStopRules.andp (capabilities context before) P)
    (TmrStopRules.sepcon (tmr_stop_call_callback_resources context before) P).
Proof.
  intros context before P heap [Hcap HP].
  destruct (TmrStopRules.unit_join heap) as [unit [Hunit Hjoin]].
  assert (Henv : snd heap = snd unit).
  { change (UCOS2_C_Rules.join (fst heap) (fst unit) (fst heap) /\
      snd heap = snd heap /\ snd unit = snd heap) in Hjoin.
    symmetry. exact (proj2 (proj2 Hjoin)). }
  exists unit, heap. split.
  - exact (TmrStopRules.join_comm heap unit heap Hjoin).
  - split; [|exact HP]. split; [exact Hunit|].
    exact (tmr_stop_call_callback_capabilities_environment_only AppRep external platform
      critical sg effects mask perr domain pooled pointer index opt argument raw_type
      raw_state context before heap unit Henv Hcap).
Qed.

(** Conversely the carrier's emp proof identifies the other resource
    fragment with the entire heap, so the public owned state is restored. *)
Lemma tmr_stop_call_callback_resources_merge : forall context before P,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon (tmr_stop_call_callback_resources context before) P)
    (TmrStopRules.andp (capabilities context before) P).
Proof.
  intros context before P heap
    [unit [rest [Hjoin [[Hunit Hcap] HP]]]].
  assert (Hequal : rest = heap).
  { exact (TmrStopRules.unit_spec rest heap unit Hunit
      (TmrStopRules.join_comm unit rest heap Hjoin)). }
  assert (Henv : snd unit = snd heap).
  { change (UCOS2_C_Rules.join (fst unit) (fst rest) (fst heap) /\
      snd unit = snd heap /\ snd rest = snd heap) in Hjoin.
    exact (proj1 (proj2 Hjoin)). }
  split.
  - exact (tmr_stop_call_callback_capabilities_environment_only AppRep external platform
      critical sg effects mask perr domain pooled pointer index opt argument raw_type
      raw_state context before unit heap Henv Hcap).
  - rewrite <- Hequal. exact HP.
Qed.

Lemma tmr_stop_call_callback_resources_forget : forall context before P,
  TmrStopRules.derivable1
    (TmrStopRules.sepcon (tmr_stop_call_callback_resources context before) P) P.
Proof.
  intros context before P heap Hresources.
  exact (proj2 (tmr_stop_call_callback_resources_merge context before P heap Hresources)).
Qed.
End StopCallResources.
