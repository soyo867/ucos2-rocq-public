Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Import ListNotations.
Local Open Scope Z_scope.

(* === list 排序操作 === *)

Fixpoint insert_sorted_by {A : Type} (key : A -> Z) (a : A) (l : list A) : list A :=
  match l with
  | [] => [a]
  | h :: rest =>
      if Z.ltb (key a) (key h) then a :: l
      else h :: insert_sorted_by key a rest
  end.

Fixpoint strictly_sorted_by {A : Type} (key : A -> Z) (l : list A) : Prop :=
  match l with
  | [] => True
  | a :: rest =>
      match rest with
      | [] => True
      | b :: _ => key a < key b /\ strictly_sorted_by key rest
      end
  end.

Lemma strictly_sorted_by_key_eq_on : forall (A : Type) (key key' : A -> Z) ids,
  (forall x, In x ids -> key x = key' x) ->
  strictly_sorted_by key ids -> strictly_sorted_by key' ids.
Proof.
  intros A key key' ids; induction ids as [|a rest IH]; intros Heq Hsorted; [exact I|].
  destruct rest as [|b rest]; [exact I|].
  destruct Hsorted as [Hab Htail]; split.
  - rewrite <- Heq by (left; reflexivity).
    rewrite <- Heq by (right; left; reflexivity); exact Hab.
  - apply IH; [intros x Hin; apply Heq; right; exact Hin|exact Htail].
Qed.

(* strictly_sorted_by 在 key 函数点等下保持 *)
Lemma strictly_sorted_by_key_ext :
  forall (A : Type) (key key' : A -> Z) (l : list A),
    (forall x, key x = key' x) ->
    strictly_sorted_by key l -> strictly_sorted_by key' l.
Proof.
  intros A key key' l Hkey_eq.
  induction l as [| a rest IH]; intros Hsorted.
  - simpl. exact I.
  - simpl in *. destruct rest as [| b rest'].
    + simpl. exact I.
    + destruct Hsorted as [Hab Hrest].
      split.
      * rewrite <- (Hkey_eq a), <- (Hkey_eq b). exact Hab.
      * apply IH. exact Hrest.
Qed.

Lemma insert_sorted_by_preserves :
  forall (A : Type) (key : A -> Z) (a : A) (l : list A),
    strictly_sorted_by key l ->
    (forall x, In x l -> key x <> key a) ->
    strictly_sorted_by key (insert_sorted_by key a l).
Proof.
  intros A key a l. induction l as [| h rest IH]; intros Hsorted Hne.
  - (* l = [] *) simpl. exact I.
  - (* l = h :: rest *)
    simpl in *. destruct (Z.ltb (key a) (key h)) eqn:Hlt.
    + (* key a < key h *)
      split.
      * apply Z.ltb_lt. exact Hlt.
      * destruct rest as [| b rest'].
        -- simpl. exact I.
        -- simpl in Hsorted. exact Hsorted.
    + (* ~(key a < key h) *)
      apply Z.ltb_ge in Hlt.
      destruct rest as [| b rest'].
      * (* rest = [] *)
        split.
        -- assert (Hhne : key h <> key a) by (apply Hne; left; reflexivity).
           lia.
        -- simpl. exact I.
      * (* rest = b :: rest' *)
        simpl in Hsorted. destruct Hsorted as [Hhh Hrest].
        simpl.
        destruct (Z.ltb (key a) (key b)) eqn:Hlt2.
        -- (* key a < key b *)
           split.
           ++ assert (Hhne : key h <> key a) by (apply Hne; left; reflexivity).
              lia.
           ++ split.
              ** apply Z.ltb_lt. exact Hlt2.
              ** exact Hrest.
        -- (* ~(key a < key b):用 helper 展开 insert_sorted_by on (b :: rest') *)
           apply Z.ltb_ge in Hlt2.
           assert (Heq : insert_sorted_by key a (b :: rest') =
                        b :: insert_sorted_by key a rest').
           { simpl. destruct (Z.ltb (key a) (key b)) eqn:E; [| reflexivity].
             apply Z.ltb_lt in E. lia. }
           split.
           ++ exact Hhh.
           ++ rewrite <- Heq. apply IH.
              ** exact Hrest.
              ** intros x Hin. apply Hne. right. exact Hin.
Qed.

(* === insert_sorted_by 与 NoDup(用于 ready_list_order 不变式)== *)

Lemma insert_sorted_by_in :
  forall (A : Type) (key : A -> Z) (a x : A) (l : list A),
    In x (insert_sorted_by key a l) <-> In x (a :: l).
Proof.
  intros A key a x l. induction l as [| h rest IH]; simpl.
  - reflexivity.
  - destruct (Z.ltb (key a) (key h)) eqn:E; simpl.
    + reflexivity.
    + rewrite IH. split.
      * intros [H | [H | H]]; subst; auto; right; auto.
      * intros [H | [H | H]]; subst; auto; right; [left | right]; auto.
Qed.

Lemma insert_sorted_by_perm :
  forall (A : Type) (key : A -> Z) (a : A) (l : list A),
    Permutation (a :: l) (insert_sorted_by key a l).
Proof.
  intros A key a l. induction l as [| h rest IH].
  - simpl. apply Permutation_refl.
  - simpl. destruct (Z.ltb (key a) (key h)) eqn:E.
    + simpl. apply Permutation_refl.
    + eapply Permutation_trans.
      * apply perm_swap.
      * apply perm_skip. exact IH.
Qed.

Lemma insert_sorted_by_preserves_NoDup :
  forall (A : Type) (key : A -> Z) (a : A) (l : list A),
    NoDup l ->
    ~ In a l ->
    NoDup (insert_sorted_by key a l).
Proof.
  intros A key a l Hnd Hnin.
  apply Permutation_NoDup with (l := a :: l).
  - apply insert_sorted_by_perm.
  - apply NoDup_cons; assumption.
Qed.

(* === 任务 ID 移除(基于 Z.eqb)=== *)

Fixpoint remove_Z_eqb (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eqb h x then remove_Z_eqb x t else h :: remove_Z_eqb x t
  end.

Lemma remove_Z_eqb_notin : forall x l,
  ~ In x (remove_Z_eqb x l).
Proof.
  intros x l. induction l as [| h t IH]; simpl in *.
  - auto.
  - destruct (Z.eqb h x) eqn:E.
    + exact IH.
    + intro Hin. destruct Hin as [Hin1 | Hin2].
      * subst. exfalso. apply Z.eqb_neq in E. lia.
      * apply IH. exact Hin2.
Qed.

(* === remove_Z_eqb 与 NoDup === *)

Lemma remove_Z_eqb_in :
  forall (x y : Z) (l : list Z), In y (remove_Z_eqb x l) -> In y l.
Proof.
  intros x y l. induction l as [| h rest IH].
  - simpl. auto.
  - simpl. destruct (Z.eqb h x) eqn:E.
    + intros Hin. right. apply IH. exact Hin.
    + intros [Hin | Hin].
      * left. exact Hin.
      * right. apply IH. exact Hin.
Qed.

(* 辅助:若 y ∈ l 且 y ≠ x,则 y ∈ remove_Z_eqb x l *)
Lemma remove_Z_eqb_in_neq :
  forall (x y : Z) (l : list Z), y <> x -> In y l -> In y (remove_Z_eqb x l).
Proof.
  intros x y l. induction l as [| h rest IH]; intros Hne Hin.
  - simpl in Hin. inversion Hin.
  - simpl in *. destruct (Z.eqb h x) eqn:E.
    + destruct Hin as [Hin1 | Hin2].
      * subst y. apply Z.eqb_eq in E. exfalso. apply Hne. exact E.
      * apply IH; assumption.
    + destruct Hin as [Hin1 | Hin2].
      * left. exact Hin1.
      * right. apply IH; assumption.
Qed.

Lemma remove_Z_eqb_NoDup :
  forall (x : Z) (l : list Z), NoDup l -> NoDup (remove_Z_eqb x l).
Proof.
  intros x l. induction l as [| h rest IH]; intros Hnd.
  - simpl. constructor.
  - simpl. destruct (Z.eqb h x) eqn:E.
    + apply IH. inversion Hnd; subst. assumption.
    + inversion Hnd as [| ?h ?rest0 ?Hnin_h Hnd_rest].
      apply NoDup_cons.
      * intro Hin. apply Hnin_h. apply (remove_Z_eqb_in x h rest). exact Hin.
      * apply IH. exact Hnd_rest.
Qed.

(* === remove_Z_eqb 与 strictly_sorted_by === *)

(* 辅助:若 x ∉ l,则 remove_Z_eqb x l = l。 *)
Lemma remove_Z_eqb_notin_eq :
  forall (x : Z) (l : list Z), ~ In x l -> remove_Z_eqb x l = l.
Proof.
  intros x l. induction l as [| h rest IH]; intros Hnin.
  - reflexivity.
  - simpl. destruct (Z.eqb h x) eqn:Heq.
    + apply Z.eqb_eq in Heq. subst h. exfalso. apply Hnin. left. reflexivity.
    + f_equal. apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

(* 辅助:remove_Z_eqb 在 head = x 时与跳过 head 等价。 *)
Lemma remove_Z_eqb_x_cons_x :
  forall (x : Z) (l : list Z), remove_Z_eqb x (x :: l) = remove_Z_eqb x l.
Proof.
  intros x l. simpl. rewrite Z.eqb_refl. reflexivity.
Qed.

(* 辅助:remove_Z_eqb 在 head ≠ x 时与保留 head 等价。 *)
Lemma remove_Z_eqb_ne_cons :
  forall (x y : Z) (l : list Z),
    Z.eqb y x = false -> remove_Z_eqb x (y :: l) = y :: remove_Z_eqb x l.
Proof.
  intros x y l Hne. simpl. rewrite Hne. reflexivity.
Qed.

(* 辅助:remove_Z_eqb x (x :: y :: l) 在 y ≠ x 时归约为 y :: remove_Z_eqb x l。 *)
Lemma remove_Z_eqb_x_then_ne_cons :
  forall (x y : Z) (l : list Z),
    Z.eqb y x = false -> remove_Z_eqb x (x :: y :: l) = y :: remove_Z_eqb x l.
Proof.
  intros x y l Hne.
  simpl. rewrite Z.eqb_refl. simpl. rewrite Hne. reflexivity.
Qed.

(* 主 Lemma:从 sorted list 中移除任一元素,sorted 保持。 *)
Lemma remove_Z_eqb_strictly_sorted_by :
  forall (key : Z -> Z) (x : Z) (l : list Z),
    strictly_sorted_by key l ->
    strictly_sorted_by key (remove_Z_eqb x l).
Proof.
  intros key x l. induction l as [| h rest IH]; intros Hsorted.
  - simpl. exact I.
  - destruct (Z.eqb h x) eqn:Heq_h.
    + (* h = x *)
      apply Z.eqb_eq in Heq_h. subst h.
      destruct rest as [| b rest'].
      * (* rest = [] *)
        rewrite remove_Z_eqb_x_cons_x. simpl. exact I.
      * (* rest = b :: rest' *)
        rewrite remove_Z_eqb_x_cons_x.
        simpl in Hsorted. destruct Hsorted as [_ Hrest'].
        apply IH. exact Hrest'.
    + (* h ≠ x *)
      destruct rest as [| b rest'].
      * (* rest = [] *)
        rewrite (remove_Z_eqb_ne_cons x h [] Heq_h). simpl. exact I.
      * (* rest = b :: rest' *)
        simpl in Hsorted. destruct Hsorted as [Hhh Hrest'].
        rewrite (remove_Z_eqb_ne_cons x h (b :: rest') Heq_h).
        (* goal: strictly_sorted_by key (h :: remove_Z_eqb x (b :: rest')) *)
        destruct (Z.eqb b x) eqn:Heq_b.
        -- (* b = x *)
           apply Z.eqb_eq in Heq_b. subst b.
           rewrite remove_Z_eqb_x_cons_x.
           destruct rest' as [| c rest''].
           ++ (* rest' = [] *)
              simpl. exact I.
           ++ (* rest' = c :: rest'' *)
              simpl in Hrest'. destruct Hrest' as [Hxc Hrest''].
              destruct (Z.eqb c x) eqn:Heq_c.
              ** apply Z.eqb_eq in Heq_c. subst c. exfalso. lia.
              ** rewrite (remove_Z_eqb_ne_cons x c rest'' Heq_c).
                 (* goal: strictly_sorted_by key (h :: c :: remove_Z_eqb x rest'') *)
                 rewrite (remove_Z_eqb_x_then_ne_cons x c rest'' Heq_c) in IH.
                 (* IH : strictly_sorted_by key (x :: c :: rest'') -> strictly_sorted_by key (c :: remove_Z_eqb x rest'') *)
                 assert (Hfull : strictly_sorted_by key (x :: c :: rest'')).
                 { simpl. split. exact Hxc. exact Hrest''. }
                 specialize (IH Hfull).
                 (* goal: strictly_sorted_by key (h :: c :: remove_Z_eqb x rest'') *)
                 (* unfolds to: key h < key c /\ strictly_sorted_by key (c :: remove_Z_eqb x rest'') *)
                 change (key h < key c /\ strictly_sorted_by key (c :: remove_Z_eqb x rest'')).
                 split. lia. exact IH.
        -- (* b ≠ x *)
           rewrite (remove_Z_eqb_ne_cons x b rest' Heq_b) in IH |- *.
           (* IH : strictly_sorted_by key (b :: rest') -> strictly_sorted_by key (b :: remove_Z_eqb x rest') *)
           (* goal: strictly_sorted_by key (h :: b :: remove_Z_eqb x rest') *)
           change (key h < key b /\ strictly_sorted_by key (b :: remove_Z_eqb x rest')).
           split. exact Hhh. apply IH. exact Hrest'.
Qed.

Lemma fold_right_lor_permutation : forall (A : Type) (mask : A -> Z) xs ys,
  Permutation xs ys ->
  fold_right (fun x acc => Z.lor (mask x) acc) 0 xs =
  fold_right (fun x acc => Z.lor (mask x) acc) 0 ys.
Proof.
  intros A mask xs ys Hperm; induction Hperm; simpl.
  - reflexivity.
  - rewrite IHHperm; reflexivity.
  - apply Z.bits_inj; intro n; rewrite !Z.lor_spec.
    destruct (Z.testbit (mask x) n), (Z.testbit (mask y) n); reflexivity.
  - etransitivity; eassumption.
Qed.

Lemma fold_right_lor_remove_absorbed : forall (mask : Z -> Z) tid ids,
  Z.lor (mask tid) (fold_right (fun x acc => Z.lor (mask x) acc) 0 (remove_Z_eqb tid ids)) =
  Z.lor (mask tid) (fold_right (fun x acc => Z.lor (mask x) acc) 0 ids).
Proof.
  intros mask tid ids; induction ids as [|head rest IH]; [reflexivity|].
  simpl; destruct (Z.eqb head tid) eqn:E.
  - apply Z.eqb_eq in E; subst head; rewrite IH.
    apply Z.bits_inj; intro n; rewrite !Z.lor_spec.
    destruct (Z.testbit (mask tid) n); reflexivity.
  - simpl; apply Z.bits_inj; intro n; cbn beta.
    pose proof (f_equal (fun z => Z.testbit z n) IH) as Hbits.
    cbn beta in Hbits; rewrite !Z.lor_spec in Hbits.
    repeat rewrite Z.lor_spec.
    destruct (Z.testbit (mask tid) n), (Z.testbit (mask head) n);
      simpl in *; assumption || reflexivity.
Qed.

Lemma fold_right_lor_insert_sorted_remove : forall (mask key : Z -> Z) tid ids,
  fold_right (fun x acc => Z.lor (mask x) acc) 0
    (insert_sorted_by key tid (remove_Z_eqb tid ids)) =
  Z.lor (mask tid) (fold_right (fun x acc => Z.lor (mask x) acc) 0 ids).
Proof.
  intros; rewrite <- (fold_right_lor_permutation Z mask _ _
    (insert_sorted_by_perm Z key tid (remove_Z_eqb tid ids))).
  simpl; apply fold_right_lor_remove_absorbed.
Qed.

Lemma remove_Z_eqb_perm_cons : forall tid ids,
  In tid ids -> NoDup ids -> Permutation ids (tid :: remove_Z_eqb tid ids).
Proof.
  intros tid ids Hin Hnd; induction ids as [|head rest IH]; [contradiction|].
  inversion Hnd as [|? ? Habsent Hrest]; subst.
  simpl in Hin; destruct Hin as [->|Hin].
  - simpl; rewrite Z.eqb_refl, remove_Z_eqb_notin_eq by exact Habsent; reflexivity.
  - simpl; destruct (Z.eqb head tid) eqn:E.
    + apply Z.eqb_eq in E; subst head; contradiction.
    + eapply Permutation_trans; [apply perm_skip; apply IH; assumption|apply perm_swap].
Qed.
