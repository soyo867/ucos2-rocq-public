Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
Local Open Scope sac.

Record Recordos_flag_node : Type := make_record_os_flag_node {
  os_flag_node_OSFlagNodeNext : Z;
  os_flag_node_OSFlagNodePrev : Z;
  os_flag_node_OSFlagNodeTCB : Z;
  os_flag_node_OSFlagNodeFlagGrp : Z;
  os_flag_node_OSFlagNodeFlags : Z;
  os_flag_node_OSFlagNodeWaitType : Z
}.

Definition zero_record_os_flag_node : Recordos_flag_node :=
  make_record_os_flag_node 0 0 0 0 0 0.

Definition StructPredos_flag_node (x : Z) (v : Recordos_flag_node) : Assertion :=
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |-> v.(os_flag_node_OSFlagNodeNext)) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |-> v.(os_flag_node_OSFlagNodePrev)) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |-> v.(os_flag_node_OSFlagNodeTCB)) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |-> v.(os_flag_node_OSFlagNodeFlagGrp)) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |-> v.(os_flag_node_OSFlagNodeFlags)) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |-> v.(os_flag_node_OSFlagNodeWaitType)).

Definition UndefStructPredos_flag_node (x : Z) : Assertion :=
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeNext")) # Ptr  |->_) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodePrev")) # Ptr  |->_) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeTCB")) # Ptr  |->_) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeFlagGrp")) # Ptr  |->_) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeFlags")) # UShort  |->_) **
  ((&(x # "os_flag_node" ->ₛ "OSFlagNodeWaitType")) # UChar  |->_).

Lemma store_Predos_flag_node_to_undef : forall x v,
  StructPredos_flag_node x v |-- UndefStructPredos_flag_node x.
Proof.
  intros.
  unfold StructPredos_flag_node, UndefStructPredos_flag_node.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply store_ushort_undef_store_ushort.
  sep_apply store_uchar_undef_store_uchar.
  cancel.
Qed.

Lemma undefstore_Predos_flag_node_to_align : forall x,
  UndefStructPredos_flag_node x |-- store_align_n ((((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(USHORT)) + sizeof(UCHAR)).
Proof.
  intros.
  unfold UndefStructPredos_flag_node.
  sep_apply undef_store_ptr_align4.
  sep_apply undef_store_ptr_align4.
  sep_apply undef_store_ptr_align4.
  sep_apply undef_store_ptr_align4.
  sep_apply undef_store_ushort_align.
  sep_apply undef_store_uchar_align.
  sep_apply (store_align4_to_store_align 1).
  sep_apply (store_align_merge (4 * 1) (4 * 1)).
  sep_apply (store_align_merge ((4 * 1 + 4 * 1)) (4 * 1)).
  sep_apply (store_align_merge (((4 * 1 + 4 * 1) + 4 * 1)) (4 * 1)).
  sep_apply (store_align_merge ((((4 * 1 + 4 * 1) + 4 * 1) + 4 * 1)) (2)).
  sep_apply (store_align_merge (((((4 * 1 + 4 * 1) + 4 * 1) + 4 * 1) + 2)) (1)).
  try rewrite sizeof_ptr.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ushort.
  try rewrite sizeof_uchar.
  replace (((((((0 + 4) + 4) + 4) + 4) + 2) + 1)) with 19 by lia.
  replace ((((((4 * 1 + 4 * 1) + 4 * 1) + 4 * 1) + 2) + 1)) with 19 by lia.
  cancel.
  all: try reflexivity.
Qed.

Lemma store_Predos_flag_node_to_align : forall x v,
  StructPredos_flag_node x v |-- store_align_n ((((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(USHORT)) + sizeof(UCHAR)).
Proof.
  intros.
  sep_apply store_Predos_flag_node_to_undef.
  sep_apply undefstore_Predos_flag_node_to_align.
  cancel.
Qed.

Module StoreStructos_flag_nodeAsElement <: ELEMENT_STORE.
  Definition A := Recordos_flag_node.
  Definition sizeA := ((((((0 + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(PTR)) + sizeof(USHORT)) + sizeof(UCHAR)).
  Definition storeA (x: addr) (lo: Z) (a: Recordos_flag_node): Assertion :=
    (StructPredos_flag_node (x + lo * sizeA) a).
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (UndefStructPredos_flag_node (x + lo * sizeA)).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    unfold storeA, undefstoreA.
    sep_apply store_Predos_flag_node_to_undef.
    cancel.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA.
    replace (x + n * sizeA + lo * sizeA) with (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA.
    replace (x + n * sizeA + lo * sizeA) with (x + (lo + n) * sizeA) by lia.
    reflexivity.
  Qed.

  Lemma store_to_align : forall x lo a, storeA x lo a |-- store_align_n sizeA.
  Proof.
    intros.
    unfold storeA, sizeA.
    sep_apply store_Predos_flag_node_to_align.
    cancel.
  Qed.

  Lemma undefstore_to_align : forall x lo, undefstoreA x lo |-- store_align_n sizeA.
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    sep_apply undefstore_Predos_flag_node_to_align.
    cancel.
  Qed.

  Lemma sizeA_valid : 0 < sizeA < Int.max_unsigned.
  Proof.
  unfold sizeA.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ptr.
  try rewrite sizeof_ushort.
  try rewrite sizeof_uchar.
  replace Int.max_unsigned with 4294967295 by reflexivity.
  change (0 < 19 < 4294967295).
  lia.
Qed.

End StoreStructos_flag_nodeAsElement.

Module Structos_flag_nodeArray := ArrayLib (StoreStructos_flag_nodeAsElement).

