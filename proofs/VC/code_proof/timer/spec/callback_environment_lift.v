(** A conservative product extension of an arbitrary resource model.

    The environment is shared by every component of a resource join and is
    unchanged by lifted execution.  No algebraic property of the supplied
    resource join is postulated: every theorem below holds for that actual
    relation and unit predicate.

    Programs have separate normal and error components.  The Hoare judgment
    excludes errors and constrains every normal result; it does not assert
    termination.  All-frame adaptation includes frames that depend on the
    environment, by taking their slice at the current environment.

    These definitions do not supply a C function environment, establish a
    callback's behavior, or justify any concrete STS/token update.  A later
    source/resource correspondence must discharge those obligations. *)

Module CallbackEnvironmentLift.

Definition assertion (State : Type) : Type := State -> Prop.

Definition assertion_entails {State : Type}
  (P Q : assertion State) : Prop :=
  forall state, P state -> Q state.

Definition assertion_equiv {State : Type}
  (P Q : assertion State) : Prop :=
  forall state, P state <-> Q state.

Definition assertion_pure {State : Type} (P : Prop) : assertion State :=
  fun _ => P.

Definition assertion_exists {State Witness : Type}
  (P : Witness -> assertion State) : assertion State :=
  fun state => exists witness, P witness state.

Definition assertion_forall {State Witness : Type}
  (P : Witness -> assertion State) : assertion State :=
  fun state => forall witness, P witness state.

Record program (State Result : Type) : Type := {
  program_normal : State -> Result -> State -> Prop;
  program_error : State -> Prop
}.

Arguments program_normal {State Result} _ _ _ _.
Arguments program_error {State Result} _ _.

Definition program_hoare {State Result : Type}
  (P : assertion State) (command : program State Result)
  (Q : Result -> assertion State) : Prop :=
  (forall initial result final,
    P initial -> program_normal command initial result final -> Q result final) /\
  (forall initial, P initial -> program_error command initial -> False).

Lemma program_hoare_consequence {State Result : Type}
  (P P' : assertion State) (command : program State Result)
  (Q Q' : Result -> assertion State) :
  assertion_entails P' P ->
  (forall result, assertion_entails (Q result) (Q' result)) ->
  program_hoare P command Q ->
  program_hoare P' command Q'.
Proof.
  intros Hpre Hpost [Hnormal Herror].
  split.
  - intros initial result final HP Hrun.
    apply (Hpost result final).
    apply (Hnormal initial result final).
    + apply Hpre. exact HP.
    + exact Hrun.
  - intros initial HP Herr.
    apply (Herror initial).
    + apply Hpre. exact HP.
    + exact Herr.
Qed.

Section ProductEnvironment.

Context {State Environment : Type}.
Context (resource_join : State -> State -> State -> Prop).
Context (resource_unit : State -> Prop).

Definition environment_state : Type := (State * Environment)%type.

Definition environment_join
  (first second combined : environment_state) : Prop :=
  resource_join (fst first) (fst second) (fst combined) /\
  snd first = snd combined /\ snd second = snd combined.

Definition environment_unit (state : environment_state) : Prop :=
  resource_unit (fst state).

Definition assertion_lift (P : assertion State)
  : assertion environment_state :=
  fun state => P (fst state).

Definition assertion_slice (environment : Environment)
  (P : assertion environment_state) : assertion State :=
  fun state => P (state, environment).

Definition resource_sepcon (P Q : assertion State) : assertion State :=
  fun state => exists first second,
    resource_join first second state /\ P first /\ Q second.

Definition environment_sepcon
  (P Q : assertion environment_state) : assertion environment_state :=
  fun state => exists first second,
    environment_join first second state /\ P first /\ Q second.

Definition resource_wand (P Q : assertion State) : assertion State :=
  fun state => forall frame combined,
    resource_join state frame combined -> P frame -> Q combined.

Definition environment_wand
  (P Q : assertion environment_state) : assertion environment_state :=
  fun state => forall frame combined,
    environment_join state frame combined -> P frame -> Q combined.

Lemma assertion_slice_lift (environment : Environment)
  (P : assertion State) :
  assertion_equiv (assertion_slice environment (assertion_lift P)) P.
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_lift_slice_at_environment (environment : Environment)
  (P : assertion environment_state) (state : State) :
  assertion_lift (assertion_slice environment P) (state, environment) <->
  P (state, environment).
Proof. split; intro H; exact H. Qed.

Lemma assertion_lift_pure (P : Prop) :
  assertion_equiv (assertion_lift (assertion_pure P)) (assertion_pure P).
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_slice_pure (environment : Environment) (P : Prop) :
  assertion_equiv (assertion_slice environment (assertion_pure P))
    (assertion_pure P).
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_lift_emp :
  assertion_equiv (assertion_lift resource_unit) environment_unit.
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_slice_emp (environment : Environment) :
  assertion_equiv (assertion_slice environment environment_unit) resource_unit.
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_slice_sepcon (environment : Environment)
  (P Q : assertion environment_state) :
  assertion_equiv
    (assertion_slice environment (environment_sepcon P Q))
    (resource_sepcon (assertion_slice environment P)
      (assertion_slice environment Q)).
Proof.
  intros state. unfold assertion_slice, environment_sepcon, resource_sepcon.
  split.
  - intros [first [second [Hjoin [HP HQ]]]].
    destruct first as [first first_environment].
    destruct second as [second second_environment].
    change (resource_join first second state /\
      first_environment = environment /\ second_environment = environment)
      in Hjoin.
    destruct Hjoin as [Hjoin [Hfirst Hsecond]].
    subst first_environment. subst second_environment.
    exists first, second. split.
    + exact Hjoin.
    + split; assumption.
  - intros [first [second [Hjoin [HP HQ]]]].
    exists (first, environment), (second, environment). split.
    + split.
      * exact Hjoin.
      * split; reflexivity.
    + split; assumption.
Qed.

Lemma assertion_lift_sepcon (P Q : assertion State) :
  assertion_equiv (assertion_lift (resource_sepcon P Q))
    (environment_sepcon (assertion_lift P) (assertion_lift Q)).
Proof.
  intros [state environment].
  exact (iff_sym
    (assertion_slice_sepcon environment (assertion_lift P)
      (assertion_lift Q) state)).
Qed.

Lemma assertion_slice_wand (environment : Environment)
  (P Q : assertion environment_state) :
  assertion_equiv
    (assertion_slice environment (environment_wand P Q))
    (resource_wand (assertion_slice environment P)
      (assertion_slice environment Q)).
Proof.
  intros state. unfold assertion_slice, environment_wand, resource_wand.
  split.
  - intros H frame combined Hjoin HP.
    apply (H (frame, environment) (combined, environment)).
    + split.
      * exact Hjoin.
      * split; reflexivity.
    + exact HP.
  - intros H [frame frame_environment] [combined combined_environment]
      Hjoin HP.
    change (resource_join state frame combined /\
      environment = combined_environment /\
      frame_environment = combined_environment) in Hjoin.
    destruct Hjoin as [Hjoin [Hcurrent Hframe]].
    subst combined_environment. subst frame_environment.
    exact (H frame combined Hjoin HP).
Qed.

Lemma assertion_lift_wand (P Q : assertion State) :
  assertion_equiv (assertion_lift (resource_wand P Q))
    (environment_wand (assertion_lift P) (assertion_lift Q)).
Proof.
  intros [state environment].
  exact (iff_sym
    (assertion_slice_wand environment (assertion_lift P)
      (assertion_lift Q) state)).
Qed.

Lemma assertion_lift_exists {Witness : Type}
  (P : Witness -> assertion State) :
  assertion_equiv (assertion_lift (assertion_exists P))
    (assertion_exists (fun witness => assertion_lift (P witness))).
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_slice_exists {Witness : Type} (environment : Environment)
  (P : Witness -> assertion environment_state) :
  assertion_equiv (assertion_slice environment (assertion_exists P))
    (assertion_exists (fun witness => assertion_slice environment (P witness))).
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_lift_forall {Witness : Type}
  (P : Witness -> assertion State) :
  assertion_equiv (assertion_lift (assertion_forall P))
    (assertion_forall (fun witness => assertion_lift (P witness))).
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_slice_forall {Witness : Type} (environment : Environment)
  (P : Witness -> assertion environment_state) :
  assertion_equiv (assertion_slice environment (assertion_forall P))
    (assertion_forall (fun witness => assertion_slice environment (P witness))).
Proof. intros state. split; intro H; exact H. Qed.

Lemma assertion_lift_entailment (P Q : assertion State) :
  assertion_entails P Q ->
  assertion_entails (assertion_lift P) (assertion_lift Q).
Proof.
  intros H [state environment] HP.
  exact (H state HP).
Qed.

Lemma assertion_slice_entailment (environment : Environment)
  (P Q : assertion environment_state) :
  assertion_entails P Q ->
  assertion_entails (assertion_slice environment P)
    (assertion_slice environment Q).
Proof.
  intros H state HP.
  exact (H (state, environment) HP).
Qed.

(** Reflection explicitly takes an environment value.  If Environment were
    empty, an entailment on its product would hold vacuously. *)
Lemma assertion_lift_entailment_reflect (environment : Environment)
  (P Q : assertion State) :
  assertion_entails (assertion_lift P) (assertion_lift Q) ->
  assertion_entails P Q.
Proof.
  intros H state HP.
  exact (H (state, environment) HP).
Qed.

Lemma assertion_lift_entailment_iff (environment : Environment)
  (P Q : assertion State) :
  assertion_entails (assertion_lift P) (assertion_lift Q) <->
  assertion_entails P Q.
Proof.
  split.
  - apply (assertion_lift_entailment_reflect environment P Q).
  - apply assertion_lift_entailment.
Qed.

Lemma assertion_slices_entailment_iff
  (P Q : assertion environment_state) :
  assertion_entails P Q <->
  forall environment,
    assertion_entails (assertion_slice environment P)
      (assertion_slice environment Q).
Proof.
  split.
  - intros H environment. apply assertion_slice_entailment. exact H.
  - intros H [state environment] HP. exact (H environment state HP).
Qed.

Definition environment_program_lift {Result : Type}
  (command : program State Result) : program environment_state Result :=
  {| program_normal := fun initial result final =>
       program_normal command (fst initial) result (fst final) /\
       snd final = snd initial;
     program_error := fun initial => program_error command (fst initial) |}.

Lemma environment_program_lift_normal_iff {Result : Type}
  (command : program State Result) (initial final : State)
  (before_environment after_environment : Environment) (result : Result) :
  program_normal (environment_program_lift command)
    (initial, before_environment) result (final, after_environment) <->
  program_normal command initial result final /\
    after_environment = before_environment.
Proof. split; intro H; exact H. Qed.

Lemma environment_program_lift_error_iff {Result : Type}
  (command : program State Result) (initial : State)
  (environment : Environment) :
  program_error (environment_program_lift command) (initial, environment) <->
  program_error command initial.
Proof. split; intro H; exact H. Qed.

Lemma environment_program_hoare_iff {Result : Type}
  (P : assertion environment_state) (command : program State Result)
  (Q : Result -> assertion environment_state) :
  program_hoare P (environment_program_lift command) Q <->
  forall environment,
    program_hoare (assertion_slice environment P) command
      (fun result => assertion_slice environment (Q result)).
Proof.
  split.
  - intros [Hnormal Herror] environment. split.
    + intros initial result final HP Hrun.
      apply (Hnormal (initial, environment) result (final, environment)).
      * exact HP.
      * split; [exact Hrun | reflexivity].
    + intros initial HP Herr.
      exact (Herror (initial, environment) HP Herr).
  - intros H. split.
    + intros [initial environment] result [final final_environment] HP Hrun.
      change (program_normal command initial result final /\
        final_environment = environment) in Hrun.
      destruct Hrun as [Hrun Henvironment].
      subst final_environment.
      exact ((proj1 (H environment)) initial result final HP Hrun).
    + intros [initial environment] HP Herr.
      exact ((proj2 (H environment)) initial HP Herr).
Qed.

Definition resource_frame_hoare {Result : Type}
  (P : assertion State) (command : program State Result)
  (Q : Result -> assertion State) : Prop :=
  forall frame : assertion State,
    program_hoare (resource_sepcon P frame) command
      (fun result => resource_sepcon (Q result) frame).

Definition environment_frame_hoare {Result : Type}
  (P : assertion environment_state) (command : program environment_state Result)
  (Q : Result -> assertion environment_state) : Prop :=
  forall frame : assertion environment_state,
    program_hoare (environment_sepcon P frame) command
      (fun result => environment_sepcon (Q result) frame).

(** The right-hand side ranges over every environment.  The left-hand side
    ranges over every product-state frame, including environment-dependent
    frames.  No restriction to lifted frames is used in the reverse proof. *)
Lemma environment_frame_hoare_slices_iff {Result : Type}
  (P : assertion environment_state) (command : program State Result)
  (Q : Result -> assertion environment_state) :
  environment_frame_hoare P (environment_program_lift command) Q <->
  forall environment,
    resource_frame_hoare (assertion_slice environment P) command
      (fun result => assertion_slice environment (Q result)).
Proof.
  split.
  - intros H environment frame.
    pose proof (proj1
      (environment_program_hoare_iff
        (environment_sepcon P (assertion_lift frame)) command
        (fun result => environment_sepcon (Q result) (assertion_lift frame)))
      (H (assertion_lift frame)) environment) as Hslice.
    eapply program_hoare_consequence with
      (P := assertion_slice environment
        (environment_sepcon P (assertion_lift frame)))
      (Q := fun result => assertion_slice environment
        (environment_sepcon (Q result) (assertion_lift frame))).
    + intros state HP.
      apply (proj2 (assertion_slice_sepcon environment P
        (assertion_lift frame) state)).
      exact HP.
    + intros result state HQ.
      exact (proj1 (assertion_slice_sepcon environment (Q result)
        (assertion_lift frame) state) HQ).
    + exact Hslice.
  - intros H frame.
    apply (proj2
      (environment_program_hoare_iff (environment_sepcon P frame) command
        (fun result => environment_sepcon (Q result) frame))).
    intros environment.
    eapply program_hoare_consequence with
      (P := resource_sepcon (assertion_slice environment P)
        (assertion_slice environment frame))
      (Q := fun result => resource_sepcon
        (assertion_slice environment (Q result))
        (assertion_slice environment frame)).
    + intros state HP.
      exact (proj1 (assertion_slice_sepcon environment P frame state) HP).
    + intros result state HQ.
      exact (proj2 (assertion_slice_sepcon environment (Q result) frame state) HQ).
    + exact (H environment (assertion_slice environment frame)).
Qed.

Lemma environment_frame_hoare_lift {Result : Type}
  (P : assertion State) (command : program State Result)
  (Q : Result -> assertion State) :
  resource_frame_hoare P command Q ->
  environment_frame_hoare (assertion_lift P)
    (environment_program_lift command)
    (fun result => assertion_lift (Q result)).
Proof.
  intros H.
  apply (proj2 (environment_frame_hoare_slices_iff
    (assertion_lift P) command (fun result => assertion_lift (Q result)))).
  intros environment. exact H.
Qed.

Lemma environment_frame_hoare_lift_reflect {Result : Type}
  (environment : Environment) (P : assertion State)
  (command : program State Result) (Q : Result -> assertion State) :
  environment_frame_hoare (assertion_lift P)
    (environment_program_lift command)
    (fun result => assertion_lift (Q result)) ->
  resource_frame_hoare P command Q.
Proof.
  intros H.
  exact (proj1 (environment_frame_hoare_slices_iff
    (assertion_lift P) command (fun result => assertion_lift (Q result)))
    H environment).
Qed.

Lemma environment_frame_hoare_lift_iff {Result : Type}
  (environment : Environment) (P : assertion State)
  (command : program State Result) (Q : Result -> assertion State) :
  environment_frame_hoare (assertion_lift P)
    (environment_program_lift command)
    (fun result => assertion_lift (Q result)) <->
  resource_frame_hoare P command Q.
Proof.
  split.
  - apply (environment_frame_hoare_lift_reflect environment P command Q).
  - apply environment_frame_hoare_lift.
Qed.

End ProductEnvironment.

End CallbackEnvironmentLift.
