Require Import Coq.Structures.Equalities.
Require Import Coq.ZArith.ZArith.
From compcert.lib Require Import Integers.
From SimpleC.SL Require Import Mem CommonAssertion.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.timer.spec.callback_environment_lift.

(** A local C-rule extension of the existing UCOS2 resource model.

    [Environment] binds only a type through Coq's existing [Typ] signature.
    It is not a concrete callback environment or a claim about C addresses.
    No declaration in the existing UCOS2 rules or their dependency closure
    is changed.  The product retains the complete old Lstate, including its
    STS observations and tokens.

    [DerivedPredSig] below is instantiated with the same old Arch32 and
    LittleEndian definitions as UCOS2.  The storage correspondence lemmas
    connect its actual scalar predicates to explicit lifts of old ones.
    A later callback/source interpretation still has to supply the actual
    environment and prove its operational and resource correspondence. *)

Module TimerCallbackRules (Environment : Typ) <: SeparationLogicSig.

Module Old := UCOS2_C_Rules.
Module Product := CallbackEnvironmentLift.

Definition model : Type := (Old.model * Environment.t)%type.
Definition expr : Type := model -> Prop.

Definition join : model -> model -> model -> Prop :=
  @Product.environment_join Old.model Environment.t Old.join.

Definition is_unit : model -> Prop :=
  @Product.environment_unit Old.model Environment.t Old.is_unit.

Include DerivedNamesSig.

Definition lift (P : Old.expr) : expr :=
  @Product.assertion_lift Old.model Environment.t P.

Definition slice (environment : Environment.t) (P : expr) : Old.expr :=
  @Product.assertion_slice Old.model Environment.t environment P.

Theorem unit_join : forall state : model,
  exists unit : model, is_unit unit /\ join state unit state.
Proof.
  intros [state environment].
  destruct (Old.unit_join state) as [unit [Hunit Hjoin]].
  exists (unit, environment). split.
  - exact Hunit.
  - change (Old.join state unit state /\
      environment = environment /\ environment = environment).
    split; [exact Hjoin | split; reflexivity].
Qed.

Theorem unit_spec : forall state final unit : model,
  is_unit unit -> join state unit final -> state = final.
Proof.
  intros [state environment] [final final_environment] [unit unit_environment]
    Hunit Hjoin.
  change (Old.is_unit unit) in Hunit.
  change (Old.join state unit final /\ environment = final_environment /\
    unit_environment = final_environment) in Hjoin.
  destruct Hjoin as [Hjoin [Henvironment Hunit_environment]].
  pose proof (Old.unit_spec state final unit Hunit Hjoin) as Hstate.
  subst final. subst final_environment. reflexivity.
Qed.

Theorem join_comm : forall first second combined : model,
  join first second combined -> join second first combined.
Proof.
  intros [first first_environment] [second second_environment]
    [combined environment] Hjoin.
  change (Old.join first second combined /\
    first_environment = environment /\ second_environment = environment)
    in Hjoin.
  destruct Hjoin as [Hjoin [Hfirst Hsecond]].
  change (Old.join second first combined /\
    second_environment = environment /\ first_environment = environment).
  split.
  - apply Old.join_comm. exact Hjoin.
  - split; assumption.
Qed.

Theorem join_assoc : forall first second third first_second combined : model,
  join first second first_second -> join first_second third combined ->
  exists second_third : model,
    join second third second_third /\ join first second_third combined.
Proof.
  intros [first first_environment] [second second_environment]
    [third third_environment] [first_second pair_environment]
    [combined environment] Hpair Hcombined.
  change (Old.join first second first_second /\
    first_environment = pair_environment /\
    second_environment = pair_environment) in Hpair.
  change (Old.join first_second third combined /\
    pair_environment = environment /\ third_environment = environment)
    in Hcombined.
  destruct Hpair as [Hpair [Hfirst Hsecond]].
  destruct Hcombined as [Hcombined [Hpair_environment Hthird]].
  subst first_environment. subst second_environment.
  subst pair_environment. subst third_environment.
  destruct (Old.join_assoc first second third first_second combined
    Hpair Hcombined) as [second_third [Htail Hrest]].
  exists (second_third, environment). split.
  - change (Old.join second third second_third /\
      environment = environment /\ environment = environment).
    split; [exact Htail | split; reflexivity].
  - change (Old.join first second_third combined /\
      environment = environment /\ environment = environment).
    split; [exact Hrest | split; reflexivity].
Qed.

Include LogicTheoremSig'.

Lemma lift_entailment (P Q : Old.expr) :
  Old.derivable1 P Q -> derivable1 (lift P) (lift Q).
Proof.
  exact (@Product.assertion_lift_entailment Old.model Environment.t P Q).
Qed.

Lemma lift_entailment_reflect (environment : Environment.t)
  (P Q : Old.expr) :
  derivable1 (lift P) (lift Q) -> Old.derivable1 P Q.
Proof.
  exact (@Product.assertion_lift_entailment_reflect Old.model Environment.t
    environment P Q).
Qed.

Lemma slice_entailment (environment : Environment.t) (P Q : expr) :
  derivable1 P Q -> Old.derivable1 (slice environment P) (slice environment Q).
Proof.
  exact (@Product.assertion_slice_entailment Old.model Environment.t
    environment P Q).
Qed.

Lemma lift_sepcon (P Q : Old.expr) (state : model) :
  lift (Old.sepcon P Q) state <-> sepcon (lift P) (lift Q) state.
Proof.
  exact (@Product.assertion_lift_sepcon Old.model Environment.t Old.join
    P Q state).
Qed.

Lemma slice_sepcon (environment : Environment.t) (P Q : expr)
  (state : Old.model) :
  slice environment (sepcon P Q) state <->
  Old.sepcon (slice environment P) (slice environment Q) state.
Proof.
  exact (@Product.assertion_slice_sepcon Old.model Environment.t Old.join
    environment P Q state).
Qed.

Lemma lift_wand (P Q : Old.expr) (state : model) :
  lift (Old.wand P Q) state <-> wand (lift P) (lift Q) state.
Proof.
  exact (@Product.assertion_lift_wand Old.model Environment.t Old.join
    P Q state).
Qed.

Lemma slice_wand (environment : Environment.t) (P Q : expr)
  (state : Old.model) :
  slice environment (wand P Q) state <->
  Old.wand (slice environment P) (slice environment Q) state.
Proof.
  exact (@Product.assertion_slice_wand Old.model Environment.t Old.join
    environment P Q state).
Qed.

Lemma lift_emp (state : model) : lift Old.emp state <-> @emp state.
Proof.
  exact (@Product.assertion_lift_emp Old.model Environment.t Old.is_unit state).
Qed.

Lemma lift_coq_prop (P : Prop) (state : model) :
  lift (Old.coq_prop P) state <-> coq_prop P state.
Proof.
  exact (@Product.assertion_lift_pure Old.model Environment.t P state).
Qed.

Lemma lift_exp (Witness : Type) (P : Witness -> Old.expr) (state : model) :
  lift (@Old.exp Witness P) state <-> @exp Witness (fun x => lift (P x)) state.
Proof.
  exact (@Product.assertion_lift_exists Old.model Environment.t Witness P state).
Qed.

Lemma lift_allp (Witness : Type) (P : Witness -> Old.expr) (state : model) :
  lift (@Old.allp Witness P) state <-> @allp Witness (fun x => lift (P x)) state.
Proof.
  exact (@Product.assertion_lift_forall Old.model Environment.t Witness P state).
Qed.

(** These are the actual BasePredSig operations, not uninterpreted copies
    of the old predicates.  Every byte retains its complete old resources. *)
Definition mstore (pointer : addr) (value : Z) : expr :=
  lift (Old.mstore pointer value).

Definition mstore_noninit (pointer : addr) : expr :=
  lift (Old.mstore_noninit pointer).

Theorem mstore_mstore_noninit : forall pointer value state,
  mstore pointer value state -> mstore_noninit pointer state.
Proof.
  intros pointer value [state environment] Hstore.
  exact (Old.mstore_mstore_noninit pointer value state Hstore).
Qed.

Theorem mstore_eqm : forall pointer value replacement,
  Byte.eqm value replacement ->
  derivable1 (mstore pointer value) (mstore pointer replacement).
Proof.
  intros pointer value replacement Heqm.
  apply lift_entailment.
  apply Old.mstore_eqm. exact Heqm.
Qed.

Theorem dup_mstore_noninit : forall pointer,
  derivable1 (sepcon (mstore_noninit pointer) (mstore_noninit pointer))
    (coq_prop False).
Proof.
  intros pointer [state environment] Hduplicate.
  apply (Old.dup_mstore_noninit pointer state).
  exact (proj1 (slice_sepcon environment (mstore_noninit pointer)
    (mstore_noninit pointer) state) Hduplicate).
Qed.

(** This is the same 32-bit little-endian C storage layer as the existing
    UCOS2 module.  It also exports the C assertions/notation used by VCs. *)
Include DerivedPredSig Arch32 LittleEndian.

Lemma slice_sepcon_preserves (environment : Environment.t)
  (P Q : expr) (old_P old_Q : Old.expr) :
  (forall state, slice environment P state <-> old_P state) ->
  (forall state, slice environment Q state <-> old_Q state) ->
  forall state,
    slice environment (sepcon P Q) state <-> Old.sepcon old_P old_Q state.
Proof.
  intros HP HQ state.
  rewrite slice_sepcon.
  split.
  - intros [first [second [Hjoin [Hfirst Hsecond]]]].
    exists first, second. split; [exact Hjoin | split].
    + exact (proj1 (HP first) Hfirst).
    + exact (proj1 (HQ second) Hsecond).
  - intros [first [second [Hjoin [Hfirst Hsecond]]]].
    exists first, second. split; [exact Hjoin | split].
    + exact (proj2 (HP first) Hfirst).
    + exact (proj2 (HQ second) Hsecond).
Qed.

Lemma slice_exp_preserves (Witness : Type) (environment : Environment.t)
  (P : Witness -> expr) (old_P : Witness -> Old.expr) :
  (forall witness state, slice environment (P witness) state <->
    old_P witness state) ->
  forall state,
    slice environment (@exp Witness P) state <-> @Old.exp Witness old_P state.
Proof.
  intros H state. split.
  - intros [witness HP]. exists witness.
    exact (proj1 (H witness state) HP).
  - intros [witness HP]. exists witness.
    exact (proj2 (H witness state) HP).
Qed.

Lemma slice_guard_preserves (environment : Environment.t) (condition : Prop)
  (P : expr) (old_P : Old.expr) :
  (forall state, slice environment P state <-> old_P state) ->
  forall state,
    slice environment (andp (coq_prop condition) P) state <->
    Old.andp (Old.coq_prop condition) old_P state.
Proof.
  intros H state. split.
  - intros [Hcondition HP]. split; [exact Hcondition |].
    exact (proj1 (H state) HP).
  - intros [Hcondition HP]. split; [exact Hcondition |].
    exact (proj2 (H state) HP).
Qed.

Lemma slices_imply_lift_equiv (P : expr) (old_P : Old.expr) :
  (forall environment state, slice environment P state <-> old_P state) ->
  logic_equiv P (lift old_P).
Proof.
  intros H. split; intros [state environment] HP.
  - exact (proj1 (H environment state) HP).
  - exact (proj2 (H environment state) HP).
Qed.

Lemma store_byte_slice (environment : Environment.t) (pointer value : Z)
  (state : Old.model) :
  slice environment (store_byte pointer value) state <->
  Old.store_byte pointer value state.
Proof. split; intro H; exact H. Qed.

Lemma store_byte_noninit_slice (environment : Environment.t) (pointer : Z)
  (state : Old.model) :
  slice environment (store_byte_noninit pointer) state <->
  Old.store_byte_noninit pointer state.
Proof. split; intro H; exact H. Qed.

Lemma store_2byte_slice (environment : Environment.t) (pointer value : Z) :
  forall state,
    slice environment (store_2byte pointer value) state <->
    Old.store_2byte pointer value state.
Proof.
  unfold store_2byte, Old.store_2byte.
  apply slice_exp_preserves. intros first.
  apply slice_exp_preserves. intros second.
  apply slice_guard_preserves.
  apply slice_sepcon_preserves;
    intros state; apply store_byte_slice.
Qed.

Lemma store_4byte_slice (environment : Environment.t) (pointer value : Z) :
  forall state,
    slice environment (store_4byte pointer value) state <->
    Old.store_4byte pointer value state.
Proof.
  unfold store_4byte, Old.store_4byte.
  apply slice_exp_preserves. intros first.
  apply slice_exp_preserves. intros second.
  apply slice_exp_preserves. intros third.
  apply slice_exp_preserves. intros fourth.
  apply slice_guard_preserves.
  apply slice_sepcon_preserves.
  - intros state. apply store_byte_slice.
  - apply slice_sepcon_preserves.
    + intros state. apply store_byte_slice.
    + apply slice_sepcon_preserves;
        intros state; apply store_byte_slice.
Qed.

Lemma store_2byte_noninit_slice (environment : Environment.t) (pointer : Z) :
  forall state,
    slice environment (store_2byte_noninit pointer) state <->
    Old.store_2byte_noninit pointer state.
Proof.
  unfold store_2byte_noninit, Old.store_2byte_noninit.
  apply slice_sepcon_preserves;
    intros state; apply store_byte_noninit_slice.
Qed.

Lemma store_4byte_noninit_slice (environment : Environment.t) (pointer : Z) :
  forall state,
    slice environment (store_4byte_noninit pointer) state <->
    Old.store_4byte_noninit pointer state.
Proof.
  unfold store_4byte_noninit, Old.store_4byte_noninit.
  apply slice_sepcon_preserves.
  - intros state. apply store_byte_noninit_slice.
  - apply slice_sepcon_preserves.
    + intros state. apply store_byte_noninit_slice.
    + apply slice_sepcon_preserves;
        intros state; apply store_byte_noninit_slice.
Qed.

Lemma store_char_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_char pointer value) state <->
    Old.store_char pointer value state.
Proof.
  unfold store_char, Old.store_char.
  apply slice_guard_preserves. intros state. apply store_byte_slice.
Qed.

Lemma store_uchar_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_uchar pointer value) state <->
    Old.store_uchar pointer value state.
Proof.
  unfold store_uchar, Old.store_uchar.
  apply slice_guard_preserves. intros state. apply store_byte_slice.
Qed.

Lemma store_short_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_short pointer value) state <->
    Old.store_short pointer value state.
Proof.
  unfold store_short, Old.store_short.
  apply slice_guard_preserves. apply store_2byte_slice.
Qed.

Lemma store_ushort_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_ushort pointer value) state <->
    Old.store_ushort pointer value state.
Proof.
  unfold store_ushort, Old.store_ushort.
  apply slice_guard_preserves. apply store_2byte_slice.
Qed.

Lemma store_int_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_int pointer value) state <->
    Old.store_int pointer value state.
Proof.
  unfold store_int, Old.store_int.
  apply slice_guard_preserves. apply store_4byte_slice.
Qed.

Lemma store_uint_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_uint pointer value) state <->
    Old.store_uint pointer value state.
Proof.
  unfold store_uint, Old.store_uint.
  apply slice_guard_preserves. apply store_4byte_slice.
Qed.

Lemma store_ptr_slice (environment : Environment.t) (pointer value : Z) :
  forall state, slice environment (store_ptr pointer value) state <->
    Old.store_ptr pointer value state.
Proof.
  unfold store_ptr, Old.store_ptr.
  apply slice_guard_preserves. apply store_4byte_slice.
Qed.

Lemma undef_store_uchar_slice (environment : Environment.t) (pointer : Z) :
  forall state, slice environment (undef_store_uchar pointer) state <->
    Old.undef_store_uchar pointer state.
Proof.
  unfold undef_store_uchar, Old.undef_store_uchar.
  apply slice_guard_preserves. intros state. apply store_byte_noninit_slice.
Qed.

Lemma undef_store_ushort_slice (environment : Environment.t) (pointer : Z) :
  forall state, slice environment (undef_store_ushort pointer) state <->
    Old.undef_store_ushort pointer state.
Proof.
  unfold undef_store_ushort, Old.undef_store_ushort.
  apply slice_guard_preserves. apply store_2byte_noninit_slice.
Qed.

Lemma undef_store_uint_slice (environment : Environment.t) (pointer : Z) :
  forall state, slice environment (undef_store_uint pointer) state <->
    Old.undef_store_uint pointer state.
Proof.
  unfold undef_store_uint, Old.undef_store_uint.
  apply slice_guard_preserves. apply store_4byte_noninit_slice.
Qed.

Lemma undef_store_ptr_slice (environment : Environment.t) (pointer : Z) :
  forall state, slice environment (undef_store_ptr pointer) state <->
    Old.undef_store_ptr pointer state.
Proof.
  unfold undef_store_ptr, Old.undef_store_ptr.
  apply slice_guard_preserves. apply store_4byte_noninit_slice.
Qed.

Lemma store_uchar_lift (pointer value : Z) :
  logic_equiv (store_uchar pointer value) (lift (Old.store_uchar pointer value)).
Proof.
  apply slices_imply_lift_equiv. intros environment. apply store_uchar_slice.
Qed.

Lemma store_ushort_lift (pointer value : Z) :
  logic_equiv (store_ushort pointer value) (lift (Old.store_ushort pointer value)).
Proof.
  apply slices_imply_lift_equiv. intros environment. apply store_ushort_slice.
Qed.

Lemma store_uint_lift (pointer value : Z) :
  logic_equiv (store_uint pointer value) (lift (Old.store_uint pointer value)).
Proof.
  apply slices_imply_lift_equiv. intros environment. apply store_uint_slice.
Qed.

Lemma store_ptr_lift (pointer value : Z) :
  logic_equiv (store_ptr pointer value) (lift (Old.store_ptr pointer value)).
Proof.
  apply slices_imply_lift_equiv. intros environment. apply store_ptr_slice.
Qed.

End TimerCallbackRules.
