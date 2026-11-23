Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import Axioms Feq ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Import ListNotations.

(** Finite field inventories are adapted to QCP's existing store_map.
    There is no second recursive separating-conjunction representation.
    Values such as option Z remain uninterpreted; each OS owner supplies
    the actual typed cell predicate and its configuration-specific fields. *)
Definition field_update {Field Value : Type}
  (eq_dec : forall x y : Field, {x = y} + {x <> y})
  (image : Field -> Value) (field : Field) (value : Value) : Field -> Value :=
  fun f => if eq_dec f field then value else image f.

Lemma field_update_same : forall Field Value eq_dec
  (image : Field -> Value) field value,
  field_update eq_dec image field value field = value.
Proof. intros; unfold field_update; destruct eq_dec; congruence. Qed.

Lemma field_update_other : forall Field Value eq_dec
  (image : Field -> Value) field value other,
  other <> field -> field_update eq_dec image field value other = image other.
Proof. intros; unfold field_update; destruct eq_dec; congruence. Qed.

Definition fields_map {Field Value : Type}
  (eq_dec : forall x y : Field, {x = y} + {x <> y})
  (fields : list Field) (image : Field -> Value) : Field -> option Value :=
  fun f => if in_dec eq_dec f fields then Some (image f) else None.

Lemma fields_map_lookup : forall Field Value eq_dec fields
  (image : Field -> Value) f,
  In f fields -> fields_map eq_dec fields image f = Some (image f).
Proof. intros; unfold fields_map; destruct in_dec; [reflexivity|contradiction]. Qed.

Lemma fields_map_removed_lookup : forall Field Value eq_dec fields
  (image : Field -> Value) f,
  fields_map eq_dec (remove eq_dec f fields) image f = None.
Proof.
  intros; unfold fields_map; destruct in_dec; [exfalso; eapply remove_In; eauto|reflexivity].
Qed.

Lemma fields_map_remove_other : forall Field Value eq_dec fields
  (image : Field -> Value) f other,
  other <> f ->
  fields_map eq_dec (remove eq_dec f fields) image other = fields_map eq_dec fields image other.
Proof.
  intros; unfold fields_map; destruct in_dec as [Hsmall|Hsmall];
    destruct in_dec as [Hlarge|Hlarge]; try reflexivity.
  - exfalso; apply Hlarge; apply in_remove in Hsmall; tauto.
  - exfalso; apply Hsmall; apply in_in_remove; [congruence|exact Hlarge].
Qed.

Module FieldStorage
  (Arch : CArchSig) (Endian : CEndianSig) (Rules : SeparationLogicSig)
  (Pred : DerivedPredSig Arch Endian Rules)
  (Stores : StoreLibSig Arch Endian Rules Pred)
  (Maps : MapLibSig Arch Endian Rules Pred Stores).
Import Rules Pred Stores Maps.
Local Open Scope sac_scope.

(** These laws operate on QCP's store_map itself. Splitting every object's
    fields preserves the same finite support; it never duplicates a cell. *)
Lemma store_map_mono : forall A B (P Q : A -> B -> Assertion) m,
  (forall a b, m a = Some b -> P a b |-- Q a b) ->
  store_map P m |-- store_map Q m.
Proof.
  intros A B P Q m Hcell; unfold store_map; Intros l.
  Exists l; entailer!.
  clear H H0.
  apply (proj2 (__derivable1_provable _ _)).
  apply (proper_iter_sepcon_impp (L := Rules.L) (Gamma := Rules.GammaP)
    (minL := Rules.minL) (sepconL := Rules.sepconL) (empL := Rules.empL)
    (iter_sepcon_L := Rules.iter_sepcon_L) _ _).
  induction l as [|a rest IH]; simpl; constructor.
  - destruct (m a) as [b|] eqn:Hlookup;
      apply (proj1 (__derivable1_provable _ _)); [apply Hcell; exact Hlookup|reflexivity].
  - apply IH.
Qed.

Lemma iter_sepcon_cons_equiv : forall P rest,
  iter_sepcon (P :: rest) --||-- P ** iter_sepcon rest.
Proof.
  intros.
  assert (Hone : iter_sepcon [P] --||-- P).
  { split.
    - eapply derivable1_trans; [apply derivable1_iter_sepcon_l|]; simpl; entailer!.
    - eapply derivable1_trans; [|apply derivable1_iter_sepcon_r]; simpl; entailer!. }
  change (iter_sepcon ([P] ++ rest) --||-- P ** iter_sepcon rest).
  split.
  - eapply derivable1_trans; [apply derivable1_sepcon_iter_sepcon2|].
    rewrite (proj1 Hone); entailer!.
  - eapply derivable1_trans; [|apply derivable1_sepcon_iter_sepcon1].
    rewrite <- (proj2 Hone); entailer!.
Qed.

Lemma iter_sepcon_map_sepcon : forall A (P Q : A -> Assertion) l,
  iter_sepcon (map (fun a => P a ** Q a) l) --||--
  iter_sepcon (map P l) ** iter_sepcon (map Q l).
Proof.
  intros A P Q l; induction l as [|a rest IH]; simpl.
  - split; rewrite !derivable1_iter_sepcon_l;
      rewrite <- !derivable1_iter_sepcon_r; simpl; entailer!.
  - rewrite !iter_sepcon_cons_equiv, IH; split; entailer!.
Qed.

Lemma store_map_sepcon : forall A B (P Q : A -> B -> Assertion) m,
  store_map (fun a b => P a b ** Q a b) m --||--
  store_map P m ** store_map Q m.
Proof.
  intros A B P Q m.
  assert (Hmap : forall l, (forall a, In a l -> exists b, m a = Some b) ->
    map (fun a => match m a with Some b => P a b ** Q a b | None => emp end) l =
    map (fun a => (match m a with Some b => P a b | None => emp end) **
                  (match m a with Some b => Q a b | None => emp end)) l).
  { intros l Hdomain; apply map_ext_in; intros a Hin.
    destruct (Hdomain a Hin) as [b Hb]; rewrite Hb; reflexivity. }
  unfold store_map; split.
  - Intros l; Exists l l; entailer!.
    rewrite Hmap by (intros; apply H; assumption).
    sep_apply_l_atomic (proj1 (iter_sepcon_map_sepcon A
      (fun a => match m a with Some b => P a b | None => emp end)
      (fun a => match m a with Some b => Q a b | None => emp end) l)); entailer!.
  - Intros lp lq.
    assert (Hperm : Permutation lq lp).
    { apply NoDup_Permutation; [assumption|assumption|].
      intro a; rewrite H, H1; reflexivity. }
    assert (HQ : iter_sepcon (map (fun a => match m a with Some b => Q a b | None => emp end) lq)
      |-- iter_sepcon (map (fun a => match m a with Some b => Q a b | None => emp end) lp)).
    { apply (proj2 (__derivable1_provable _ _)).
      apply (provables_iffp_elim1 (L := Rules.L) (Gamma := Rules.GammaP)
        (minL := Rules.minL) (iffpL := Rules.iffpL) _ _).
      apply (proper_iter_sepcon_Permutation (L := Rules.L) (Gamma := Rules.GammaP)
        (minL := Rules.minL) (sepconL := Rules.sepconL) (empL := Rules.empL)
        (iter_sepcon_L := Rules.iter_sepcon_L)).
      apply Permutation_map; exact Hperm. }
    Exists lp; entailer!.
    rewrite HQ.
    rewrite Hmap by (intros; apply H; assumption).
    sep_apply_r_atomic (proj2 (iter_sepcon_map_sepcon A
      (fun a => match m a with Some b => P a b | None => emp end)
      (fun a => match m a with Some b => Q a b | None => emp end) lp)); entailer!.
Qed.

Lemma store_map_value_map : forall A B C (P : A -> C -> Assertion)
  (f : B -> C) m,
  store_map (fun a b => P a (f b)) m --||--
  store_map P (fun a => option_map f (m a)).
Proof.
  intros A B C P f m.
  assert (Hdomain : forall a,
    (exists b, m a = Some b) <-> exists c, option_map f (m a) = Some c).
  { intro a; destruct (m a) as [b|]; simpl;
      split; intros; try (eexists; reflexivity); destruct H as [v Hv]; discriminate. }
  assert (Hmap : forall l,
    map (fun a => match m a with Some b => P a (f b) | None => emp end) l =
    map (fun a => match option_map f (m a) with Some c => P a c | None => emp end) l).
  { intro l; apply map_ext; intro a; destruct (m a); reflexivity. }
  unfold store_map; split; Intros l; Exists l; entailer!.
  - rewrite Hmap; reflexivity.
  - intro a; rewrite <- Hdomain; apply H.
  - rewrite Hmap; reflexivity.
  - intro a; rewrite Hdomain; apply H.
Qed.

Definition store_fields {Field Value : Type}
  (eq_dec : forall x y : Field, {x = y} + {x <> y})
  (cell : Field -> Value -> Assertion) (fields : list Field) (image : Field -> Value) : Assertion :=
  store_map cell (fields_map eq_dec fields image).

Lemma store_fields_update_unlisted : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields image f value,
  ~ In f fields ->
  store_fields eq_dec cell fields (field_update eq_dec image f value) =
  store_fields eq_dec cell fields image.
Proof.
  intros; unfold store_fields; f_equal; apply functional_extensionality; intro other.
  unfold fields_map; destruct in_dec as [Hin|Hnot]; [|reflexivity].
  rewrite field_update_other by (intro Heq; subst other; contradiction); reflexivity.
Qed.

Lemma store_fields_missing_equiv : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields image f,
  store_map_missing_i cell (fields_map eq_dec fields image) f --||--
  store_fields eq_dec cell (remove eq_dec f fields) image.
Proof.
  intros; unfold store_fields.
  pose proof (fields_map_removed_lookup Field Value eq_dec fields image f) as Hnone.
  destruct (store_map_missing_i_equiv cell
    (fields_map eq_dec fields image) (fields_map eq_dec (remove eq_dec f fields) image) f
    ltac:(intros; symmetry; apply fields_map_remove_other; assumption)) as [Hforward Hbackward].
  split.
  - eapply derivable1_trans; [exact Hforward|apply store_map_missing_equiv_store_map; exact Hnone].
  - eapply derivable1_trans; [apply store_map_equiv_store_map_missing; exact Hnone|exact Hbackward].
Qed.

Lemma store_fields_split_field : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields image f,
  NoDup fields -> In f fields ->
  store_fields eq_dec cell fields image |--
  cell f (image f) ** store_fields eq_dec cell (remove eq_dec f fields) image.
Proof.
  intros; unfold store_fields at 1.
  sep_apply_l_atomic (store_map_split cell f (image f) _
    (fields_map_lookup Field Value eq_dec fields image f H0)).
  sep_apply_l_atomic (proj1 (store_fields_missing_equiv Field Value eq_dec cell fields image f)).
  entailer!.
Qed.

Lemma store_fields_merge_field : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields image f,
  NoDup fields -> In f fields ->
  cell f (image f) ** store_fields eq_dec cell (remove eq_dec f fields) image |--
  store_fields eq_dec cell fields image.
Proof.
  intros.
  sep_apply_l_atomic (proj2 (store_fields_missing_equiv Field Value eq_dec cell fields image f)).
  unfold store_fields.
  sep_apply_l_atomic (store_map_merge cell f (image f) _
    (fields_map_lookup Field Value eq_dec fields image f H0)).
  entailer!.
Qed.

Lemma store_fields_merge_updated_field : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields image f value,
  NoDup fields -> In f fields ->
  cell f value ** store_fields eq_dec cell (remove eq_dec f fields) image |--
  store_fields eq_dec cell fields (field_update eq_dec image f value).
Proof.
  intros Field Value eq_dec cell fields image f value Hnd Hin.
  pose proof (store_fields_merge_field Field Value eq_dec cell fields
    (field_update eq_dec image f value) f Hnd Hin) as Hmerge.
  rewrite field_update_same in Hmerge.
  rewrite store_fields_update_unlisted in Hmerge by apply remove_In.
  exact Hmerge.
Qed.

(** Lift a cell-level entailment using QCP's existing iter_sepcon
    monotonicity.  The finite support and its ownership are unchanged. *)
Lemma store_fields_mono : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields before after,
  (forall f, In f fields -> cell f (before f) |-- cell f (after f)) ->
  store_fields eq_dec cell fields before |-- store_fields eq_dec cell fields after.
Proof.
  intros Field Value eq_dec cell fields before after Hcells.
  unfold store_fields, store_map; Intros l.
  assert (Hdomain : forall f, In f l <->
    exists value, fields_map eq_dec fields after f = Some value).
  { intro f; rewrite H; unfold fields_map.
    destruct in_dec; split; intros [value Hvalue];
      try discriminate; eexists; reflexivity. }
  Exists l; entailer!.
  clear H H0 Hdomain.
  apply (proj2 (__derivable1_provable _ _)).
  apply (proper_iter_sepcon_impp (L := Rules.L) (Gamma := Rules.GammaP)
    (minL := Rules.minL) (sepconL := Rules.sepconL) (empL := Rules.empL)
    (iter_sepcon_L := Rules.iter_sepcon_L) _ _).
  induction l as [|f rest IH]; simpl; constructor; [|apply IH].
  unfold fields_map; destruct in_dec as [Hin|Hnot].
  - apply (proj1 (__derivable1_provable _ _)); apply Hcells; exact Hin.
  - apply (proj1 (__derivable1_provable _ _)); reflexivity.
Qed.

Lemma store_fields_nil : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) image,
  store_fields eq_dec cell [] image --||-- emp.
Proof.
  intros; unfold store_fields, fields_map; simpl.
  apply store_map_empty.
  - exists []; split; [|constructor].
    intro f; split; [contradiction|intros [value Hvalue]; discriminate].
  - intro f; left; reflexivity.
Qed.

Lemma store_fields_cons : forall Field Value eq_dec
  (cell : Field -> Value -> Assertion) fields image f,
  NoDup (f :: fields) ->
  store_fields eq_dec cell (f :: fields) image --||-- cell f (image f) ** store_fields eq_dec cell fields image.
Proof.
  intros Field Value eq_dec cell fields image f Hnd.
  assert (Hnot : ~ In f fields) by (inversion Hnd; assumption).
  pose proof (store_fields_split_field Field Value eq_dec cell
    (f :: fields) image f Hnd (or_introl eq_refl)) as Hsplit.
  pose proof (store_fields_merge_field Field Value eq_dec cell
    (f :: fields) image f Hnd (or_introl eq_refl)) as Hmerge.
  rewrite remove_cons, notin_remove in Hsplit, Hmerge by exact Hnot.
  split; assumption.
Qed.
End FieldStorage.
