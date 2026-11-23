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
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import Snaive_C_Rules.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.VC.code.core.spec.mem_copy_spec.
Require Import AUXLib.ListLib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_MemCopy -----*)

Definition OS_MemCopy_entail_wit_1 := 
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre <= 65535)) (PreH3 : ((Zlength (bytes)) = size_pre)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (0 <= psrc_pre)) (PreH7 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) ,
  (mem_copy_pre pdest_pre psrc_pre size_pre bytes )
|--
  “ (0 <= size_pre) ” 
  &&  “ (size_pre <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest_pre = (pdest_pre + ((size_pre - size_pre ) * sizeof(UCHAR)))) ” 
  &&  “ (psrc_pre = (psrc_pre + ((size_pre - size_pre ) * sizeof(UCHAR)))) ”
  &&  (UCharArray.seg pdest_pre 0 (size_pre - size_pre ) (sublist (0) ((size_pre - size_pre )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size_pre ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
) \/
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre <= 65535)) (PreH3 : ((Zlength (bytes)) = size_pre)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (0 <= psrc_pre)) (PreH7 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) ,
  (mem_copy_pre pdest_pre psrc_pre size_pre bytes )
|--
  (UCharArray.seg pdest_pre 0 (size_pre - size_pre ) (sublist (0) ((size_pre - size_pre )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size_pre ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
).

Definition OS_MemCopy_entail_wit_1_split_goal_spatial := 
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (PreH1 : (0 <= size_pre)) (PreH2 : (size_pre <= 65535)) (PreH3 : ((Zlength (bytes)) = size_pre)) (PreH4 : (0 <= pdest_pre)) (PreH5 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH6 : (0 <= psrc_pre)) (PreH7 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) ,
  (mem_copy_pre pdest_pre psrc_pre size_pre bytes )
|--
  (UCharArray.seg pdest_pre 0 (size_pre - size_pre ) (sublist (0) ((size_pre - size_pre )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size_pre ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
.

Definition OS_MemCopy_entail_wit_2 := 
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : ((Zlength (bytes)) = size_pre)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= psrc_pre)) (PreH8 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (size > 0)) (PreH10 : (0 <= size)) (PreH11 : (size <= size_pre)) (PreH12 : (size_pre <= 65535)) (PreH13 : ((Zlength (bytes)) = size_pre)) (PreH14 : (0 <= pdest_pre)) (PreH15 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : (0 <= psrc_pre)) (PreH17 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH18 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH19 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.full psrc_pre size_pre bytes )
  **  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> (Znth (size_pre - size ) bytes 0))
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre ((size_pre - size ) + 1 ) size_pre )
|--
  “ (0 <= (size - 1 )) ” 
  &&  “ ((size - 1 ) <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((pdest_pre + (((size_pre - size ) + 1 ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - (size - 1 ) ) * sizeof(UCHAR)))) ” 
  &&  “ ((psrc_pre + (((size_pre - size ) + 1 ) * sizeof(UCHAR))) = (psrc_pre + ((size_pre - (size - 1 ) ) * sizeof(UCHAR)))) ”
  &&  (UCharArray.seg pdest_pre 0 (size_pre - (size - 1 ) ) (sublist (0) ((size_pre - (size - 1 ) )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - (size - 1 ) ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
) \/
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : ((Zlength (bytes)) = size_pre)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= psrc_pre)) (PreH8 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (size > 0)) (PreH10 : (0 <= size)) (PreH11 : (size <= size_pre)) (PreH12 : (size_pre <= 65535)) (PreH13 : ((Zlength (bytes)) = size_pre)) (PreH14 : (0 <= pdest_pre)) (PreH15 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : (0 <= psrc_pre)) (PreH17 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH18 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH19 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> (Znth (size_pre - size ) bytes 0))
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
|--
  (UCharArray.seg pdest_pre 0 (size_pre - (size - 1 ) ) (sublist (0) ((size_pre - (size - 1 ) )) (bytes)) )
).

Definition OS_MemCopy_entail_wit_2_split_goal_spatial := 
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : ((Zlength (bytes)) = size_pre)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= psrc_pre)) (PreH8 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (size > 0)) (PreH10 : (0 <= size)) (PreH11 : (size <= size_pre)) (PreH12 : (size_pre <= 65535)) (PreH13 : ((Zlength (bytes)) = size_pre)) (PreH14 : (0 <= pdest_pre)) (PreH15 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH16 : (0 <= psrc_pre)) (PreH17 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH18 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH19 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> (Znth (size_pre - size ) bytes 0))
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
|--
  (UCharArray.seg pdest_pre 0 (size_pre - (size - 1 ) ) (sublist (0) ((size_pre - (size - 1 ) )) (bytes)) )
.

Definition OS_MemCopy_return_wit_1 := 
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : ((Zlength (bytes)) = size_pre)) (PreH6 : (0 <= pdest_pre)) (PreH7 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= psrc_pre)) (PreH9 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH11 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  (mem_copy_post pdest_pre psrc_pre size_pre bytes )
) \/
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : ((Zlength (bytes)) = size_pre)) (PreH6 : (0 <= pdest_pre)) (PreH7 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= psrc_pre)) (PreH9 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH11 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  (mem_copy_post pdest_pre psrc_pre size_pre bytes )
).

Definition OS_MemCopy_return_wit_1_split_goal_spatial := 
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : ((Zlength (bytes)) = size_pre)) (PreH6 : (0 <= pdest_pre)) (PreH7 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= psrc_pre)) (PreH9 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH11 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  (mem_copy_post pdest_pre psrc_pre size_pre bytes )
.

Definition OS_MemCopy_partial_solve_wit_1_pure := 
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : ((Zlength (bytes)) = size_pre)) (PreH6 : (0 <= pdest_pre)) (PreH7 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= psrc_pre)) (PreH9 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH11 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  ((( &( "size" ) )) # UShort  |-> size)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ ((psrc_pre + ((size_pre - size ) * sizeof(UCHAR))) = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
.

Definition OS_MemCopy_partial_solve_wit_1_aux := 
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (0 <= size)) (PreH3 : (size <= size_pre)) (PreH4 : (size_pre <= 65535)) (PreH5 : ((Zlength (bytes)) = size_pre)) (PreH6 : (0 <= pdest_pre)) (PreH7 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH8 : (0 <= psrc_pre)) (PreH9 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH10 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH11 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  ((( &( "pdest" ) )) # Ptr  |-> pdest)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ ((psrc_pre + ((size_pre - size ) * sizeof(UCHAR))) = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ (size > 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  ((( &( "pdest" ) )) # Ptr  |-> (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))
  **  ((( &( "psrc" ) )) # Ptr  |-> (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
.

Definition OS_MemCopy_partial_solve_wit_1 := OS_MemCopy_partial_solve_wit_1_pure -> OS_MemCopy_partial_solve_wit_1_aux.

Definition OS_MemCopy_partial_solve_wit_2 := 
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (psrc: Z) (pdest: Z) (size: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : ((Zlength (bytes)) = size_pre)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= psrc_pre)) (PreH8 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : ((pdest_pre + ((size_pre - size ) * sizeof(UCHAR))) = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH10 : ((psrc_pre + ((size_pre - size ) * sizeof(UCHAR))) = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH11 : (size > 0)) (PreH12 : (0 <= size)) (PreH13 : (size <= size_pre)) (PreH14 : (size_pre <= 65535)) (PreH15 : ((Zlength (bytes)) = size_pre)) (PreH16 : (0 <= pdest_pre)) (PreH17 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH18 : (0 <= psrc_pre)) (PreH19 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH20 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH21 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.full psrc_pre size_pre bytes )
  **  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre ((size_pre - size ) + 1 ) size_pre )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (size > 0) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  (((psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |-> (Znth (size_pre - size ) bytes 0))
  **  (UCharArray.missing_i psrc_pre (size_pre - size ) 0 size_pre bytes )
  **  (((pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre ((size_pre - size ) + 1 ) size_pre )
.

Definition OS_MemCopy_which_implies_wit_1 := 
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (size: Z) (pdest: Z) (psrc: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : ((Zlength (bytes)) = size_pre)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= psrc_pre)) (PreH8 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH10 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre (size_pre - size ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  ((pdest) # UChar  |->_)
  **  ((psrc) # UChar  |-> (Znth (size_pre - size ) bytes 0))
  **  (UCharArray.missing_i psrc_pre (size_pre - size ) 0 size_pre bytes )
  **  (UCharArray.seg pdest_pre 0 (size_pre - size ) (sublist (0) ((size_pre - size )) (bytes)) )
  **  (UCharArray.undef_seg pdest_pre ((size_pre - size ) + 1 ) size_pre )
) \/
(
forall (size_pre: Z) (psrc_pre: Z) (pdest_pre: Z) (bytes: (@list Z)) (size: Z) (pdest: Z) (psrc: Z) (PreH1 : (0 < size)) (PreH2 : (size <= size_pre)) (PreH3 : (size_pre <= 65535)) (PreH4 : ((Zlength (bytes)) = size_pre)) (PreH5 : (0 <= pdest_pre)) (PreH6 : ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH7 : (0 <= psrc_pre)) (PreH8 : ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR))))) (PreH10 : (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR))))) ,
  (UCharArray.undef_seg pdest_pre (size_pre - size ) size_pre )
  **  (UCharArray.full psrc_pre size_pre bytes )
|--
  EX (x: Z) ,
  “ (0 < size) ” 
  &&  “ (size <= size_pre) ” 
  &&  “ (size_pre <= 65535) ” 
  &&  “ ((Zlength (bytes)) = size_pre) ” 
  &&  “ (0 <= pdest_pre) ” 
  &&  “ ((pdest_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= psrc_pre) ” 
  &&  “ ((psrc_pre + (size_pre * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (pdest = (pdest_pre + ((size_pre - size ) * sizeof(UCHAR)))) ” 
  &&  “ (psrc = (psrc_pre + ((size_pre - size ) * sizeof(UCHAR)))) ”
  &&  ((pdest) # UChar  |-> x)
  **  ((psrc) # UChar  |-> (Znth (size_pre - size ) bytes 0))
  **  (UCharArray.missing_i psrc_pre (size_pre - size ) 0 size_pre bytes )
  **  (UCharArray.undef_seg pdest_pre ((size_pre - size ) + 1 ) size_pre )
).

Module Type VC_Correct.


Axiom proof_of_OS_MemCopy_entail_wit_1 : OS_MemCopy_entail_wit_1.
Axiom proof_of_OS_MemCopy_entail_wit_2 : OS_MemCopy_entail_wit_2.
Axiom proof_of_OS_MemCopy_return_wit_1 : OS_MemCopy_return_wit_1.
Axiom proof_of_OS_MemCopy_partial_solve_wit_1_pure : OS_MemCopy_partial_solve_wit_1_pure.
Axiom proof_of_OS_MemCopy_partial_solve_wit_1 : OS_MemCopy_partial_solve_wit_1.
Axiom proof_of_OS_MemCopy_partial_solve_wit_2 : OS_MemCopy_partial_solve_wit_2.
Axiom proof_of_OS_MemCopy_which_implies_wit_1 : OS_MemCopy_which_implies_wit_1.

End VC_Correct.
