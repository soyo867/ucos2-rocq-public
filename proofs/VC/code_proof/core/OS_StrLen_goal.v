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
Require Import Ucos2Verify.VC.code.core.spec.os_strlen_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_StrLen -----*)

Definition OS_StrLen_safety_wit_1 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre = entry_exact_frame_spec)) (PreH2 : (psrc_pre <> 0)) (PreH3 : (psrc_pre = base_exact_frame_spec)) (PreH4 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc_pre)
  **  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_StrLen_safety_wit_2 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre = entry_exact_frame_spec)) (PreH2 : (psrc_pre = 0)) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc_pre)
  **  (frame_exact_frame_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_StrLen_safety_wit_3 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre = 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre <> 0)) (PreH4 : (psrc_pre = base_exact_frame_spec)) (PreH5 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc_pre)
  **  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  “ False ”
.

Definition OS_StrLen_safety_wit_4 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre <> 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre = 0)) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "psrc" ) )) # Ptr  |-> psrc_pre)
  **  (frame_exact_frame_spec )
|--
  “ False ”
.

Definition OS_StrLen_safety_wit_5 := 
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : (base_exact_frame_spec <> 0)) (PreH2 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH3 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH4 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH5 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH6 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH7 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((( &( "psrc" ) )) # Ptr  |-> psrc)
  **  ((( &( "len" ) )) # UChar  |-> len)
  **  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_StrLen_entail_wit_1 := 
(
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre <> 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre <> 0)) (PreH4 : (psrc_pre = base_exact_frame_spec)) (PreH5 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  “ (base_exact_frame_spec <> 0) ” 
  &&  “ (psrc_pre = (psrc_pre + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR)))) ” 
  &&  “ (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec ) ” 
  &&  “ (0 <= (psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ” 
  &&  “ ((psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec))) ” 
  &&  “ (0 = (kernel_u8 ((psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR)))))) ” 
  &&  “ (entry_exact_frame_spec = base_exact_frame_spec) ”
  &&  ((psrc_pre) # UChar  |-> (Znth ((psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR))) 0 frame_exact_frame_spec )
) \/
(
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre <> 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre <> 0)) (PreH4 : (psrc_pre = base_exact_frame_spec)) (PreH5 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  “ (0 = (kernel_u8 ((psrc_pre + ((-psrc_pre) * sizeof(UCHAR)))))) ” 
  &&  “ ((psrc_pre + ((-psrc_pre) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec))) ”
  &&  ((psrc_pre) # UChar  |-> (Znth ((psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR))) 0 frame_exact_frame_spec )
).

Definition OS_StrLen_entail_wit_1_split_goal_1 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre <> 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre <> 0)) (PreH4 : (psrc_pre = base_exact_frame_spec)) (PreH5 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  “ (0 = (kernel_u8 ((psrc_pre + ((-psrc_pre) * sizeof(UCHAR)))))) ”
.

Definition OS_StrLen_entail_wit_1_split_goal_2 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre <> 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre <> 0)) (PreH4 : (psrc_pre = base_exact_frame_spec)) (PreH5 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  “ ((psrc_pre + ((-psrc_pre) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec))) ”
.

Definition OS_StrLen_entail_wit_1_split_goal_spatial := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre <> 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre <> 0)) (PreH4 : (psrc_pre = base_exact_frame_spec)) (PreH5 : (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec )) ,
  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
|--
  ((psrc_pre) # UChar  |-> (Znth ((psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc_pre + ((-base_exact_frame_spec) * sizeof(UCHAR))) 0 frame_exact_frame_spec )
.

Definition OS_StrLen_entail_wit_2 := 
(
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) <> 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ (base_exact_frame_spec <> 0) ” 
  &&  “ ((psrc + (1 * sizeof(UCHAR))) = ((psrc + (1 * sizeof(UCHAR))) + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR)))) ” 
  &&  “ (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec ) ” 
  &&  “ (0 <= ((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ” 
  &&  “ (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec))) ” 
  &&  “ ((unsigned_last_nbits ((len + 1 )) (8)) = (kernel_u8 (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))))) ” 
  &&  “ (entry_exact_frame_spec = base_exact_frame_spec) ”
  &&  (((psrc + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec ((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR))) (unsigned_last_nbits ((len + 1 )) (8)) frame_exact_frame_spec )
) \/
(
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) <> 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ ((unsigned_last_nbits ((len + 1 )) (8)) = (kernel_u8 (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))))) ” 
  &&  “ (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec))) ”
  &&  (((psrc + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec ((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR))) (unsigned_last_nbits ((len + 1 )) (8)) frame_exact_frame_spec )
).

Definition OS_StrLen_entail_wit_2_split_goal_1 := 
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) <> 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ ((unsigned_last_nbits ((len + 1 )) (8)) = (kernel_u8 (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))))) ”
.

Definition OS_StrLen_entail_wit_2_split_goal_2 := 
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) <> 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec))) ”
.

Definition OS_StrLen_entail_wit_2_split_goal_spatial := 
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) <> 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  (((psrc + (1 * sizeof(UCHAR)))) # UChar  |-> (Znth (((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec ((psrc + (1 * sizeof(UCHAR))) + ((-base_exact_frame_spec) * sizeof(UCHAR))) (unsigned_last_nbits ((len + 1 )) (8)) frame_exact_frame_spec )
.

Definition OS_StrLen_return_wit_1 := 
(
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) = 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ (entry_exact_frame_spec <> 0) ” 
  &&  “ (entry_exact_frame_spec = base_exact_frame_spec) ” 
  &&  “ (os_strlen_result chars_exact_frame_spec len ) ”
  &&  (os_strlen_bytes entry_exact_frame_spec chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
) \/
(
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) = 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ (os_strlen_result chars_exact_frame_spec len ) ”
  &&  (os_strlen_bytes entry_exact_frame_spec chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
).

Definition OS_StrLen_return_wit_1_split_goal_1 := 
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) = 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  “ (os_strlen_result chars_exact_frame_spec len ) ”
.

Definition OS_StrLen_return_wit_1_split_goal_spatial := 
forall (frame_exact_frame_spec: Assertion) (chars_exact_frame_spec: (@list Z)) (names_exact_frame_spec: NameResourceState) (base_exact_frame_spec: Z) (entry_exact_frame_spec: Z) (len: Z) (psrc: Z) (PreH1 : ((Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)) = 0)) (PreH2 : (base_exact_frame_spec <> 0)) (PreH3 : (psrc = (psrc + (((-base_exact_frame_spec) + base_exact_frame_spec ) * sizeof(UCHAR))))) (PreH4 : (readable_name names_exact_frame_spec base_exact_frame_spec chars_exact_frame_spec )) (PreH5 : (0 <= (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))) (PreH6 : ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) <= (Zlength (chars_exact_frame_spec)))) (PreH7 : (len = (kernel_u8 ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))))))) (PreH8 : (entry_exact_frame_spec = base_exact_frame_spec)) ,
  ((psrc) # UChar  |-> (Znth ((psrc + ((-base_exact_frame_spec) * sizeof(UCHAR)))) ((os_strlen_source (chars_exact_frame_spec))) (0)))
  **  (os_strlen_loop_residual base_exact_frame_spec chars_exact_frame_spec (psrc + ((-base_exact_frame_spec) * sizeof(UCHAR))) len frame_exact_frame_spec )
|--
  (os_strlen_bytes entry_exact_frame_spec chars_exact_frame_spec )
  **  (frame_exact_frame_spec )
.

Definition OS_StrLen_return_wit_2 := 
forall (psrc_pre: Z) (frame_exact_frame_spec: Assertion) (entry_exact_frame_spec: Z) (PreH1 : (psrc_pre = 0)) (PreH2 : (psrc_pre = entry_exact_frame_spec)) (PreH3 : (psrc_pre = 0)) ,
  (frame_exact_frame_spec )
|--
  “ (entry_exact_frame_spec = 0) ” 
  &&  “ (0 = 0) ”
  &&  (frame_exact_frame_spec )
.

Definition OS_StrLen_derive_no_wrap_spec_by_source_spec := 
forall (psrc_pre: Z) (frame_no_wrap_spec: Assertion) (chars_no_wrap_spec: (@list Z)) (names_no_wrap_spec: NameResourceState) (base_no_wrap_spec: Z) (entry_no_wrap_spec: Z) ,
  (“ (psrc_pre = entry_no_wrap_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_no_wrap_spec) ”
  &&  (coq_prop (readable_name (names_no_wrap_spec) (psrc_pre) (chars_no_wrap_spec)) )
  **  (coq_prop (os_strlen_length_valid (chars_no_wrap_spec)) )
  **  (os_strlen_bytes psrc_pre chars_no_wrap_spec )
  **  (frame_no_wrap_spec ))
  ||
  (“ (psrc_pre = entry_no_wrap_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_no_wrap_spec ))
|--
EX (entry_source_spec: Z) (base_source_spec: Z) (names_source_spec: NameResourceState) (chars_source_spec: (@list Z)) (frame_source_spec: Assertion) ,
  ((“ (psrc_pre = entry_source_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_source_spec) ”
  &&  (coq_prop (readable_name (names_source_spec) (psrc_pre) (chars_source_spec)) )
  **  (os_strlen_bytes psrc_pre chars_source_spec )
  **  (frame_source_spec ))
  ||
  (“ (psrc_pre = entry_source_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_source_spec )))
  **
  (((EX retval_2,
  “ (entry_source_spec = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (frame_source_spec ))
  ||
  (EX retval_2,
  “ (entry_source_spec <> 0) ” 
  &&  “ (entry_source_spec = base_source_spec) ”
  &&  (coq_prop (os_strlen_result (chars_source_spec) (retval_2)) )
  **  (os_strlen_bytes entry_source_spec chars_source_spec )
  **  (frame_source_spec )))
  -*
  ((EX retval,
  “ (entry_no_wrap_spec = 0) ” 
  &&  “ (retval = 0) ”
  &&  (frame_no_wrap_spec ))
  ||
  (EX retval,
  “ (entry_no_wrap_spec <> 0) ” 
  &&  “ (entry_no_wrap_spec = base_no_wrap_spec) ”
  &&  (coq_prop (os_strlen_success (chars_no_wrap_spec) (retval)) )
  **  (os_strlen_bytes entry_no_wrap_spec chars_no_wrap_spec )
  **  (frame_no_wrap_spec ))))
.

Definition OS_StrLen_derive_source_spec_by_exact_frame_spec := 
forall (psrc_pre: Z) (frame_source_spec: Assertion) (chars_source_spec: (@list Z)) (names_source_spec: NameResourceState) (base_source_spec: Z) (entry_source_spec: Z) ,
  (“ (psrc_pre = entry_source_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_source_spec) ”
  &&  (coq_prop (readable_name (names_source_spec) (psrc_pre) (chars_source_spec)) )
  **  (os_strlen_bytes psrc_pre chars_source_spec )
  **  (frame_source_spec ))
  ||
  (“ (psrc_pre = entry_source_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_source_spec ))
|--
EX (entry_exact_frame_spec: Z) (base_exact_frame_spec: Z) (names_exact_frame_spec: NameResourceState) (chars_exact_frame_spec: (@list Z)) (frame_exact_frame_spec: Assertion) ,
  ((“ (psrc_pre = entry_exact_frame_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_exact_frame_spec) ” 
  &&  “ (readable_name names_exact_frame_spec psrc_pre chars_exact_frame_spec ) ”
  &&  (os_strlen_bytes psrc_pre chars_exact_frame_spec )
  **  (frame_exact_frame_spec ))
  ||
  (“ (psrc_pre = entry_exact_frame_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_exact_frame_spec )))
  **
  (((EX retval_2,
  “ (entry_exact_frame_spec = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (frame_exact_frame_spec ))
  ||
  (EX retval_2,
  “ (entry_exact_frame_spec <> 0) ” 
  &&  “ (entry_exact_frame_spec = base_exact_frame_spec) ” 
  &&  “ (os_strlen_result chars_exact_frame_spec retval_2 ) ”
  &&  (os_strlen_bytes entry_exact_frame_spec chars_exact_frame_spec )
  **  (frame_exact_frame_spec )))
  -*
  ((EX retval,
  “ (entry_source_spec = 0) ” 
  &&  “ (retval = 0) ”
  &&  (frame_source_spec ))
  ||
  (EX retval,
  “ (entry_source_spec <> 0) ” 
  &&  “ (entry_source_spec = base_source_spec) ”
  &&  (coq_prop (os_strlen_result (chars_source_spec) (retval)) )
  **  (os_strlen_bytes entry_source_spec chars_source_spec )
  **  (frame_source_spec ))))
.

Module Type VC_Correct.


Axiom proof_of_OS_StrLen_safety_wit_1 : OS_StrLen_safety_wit_1.
Axiom proof_of_OS_StrLen_safety_wit_2 : OS_StrLen_safety_wit_2.
Axiom proof_of_OS_StrLen_safety_wit_3 : OS_StrLen_safety_wit_3.
Axiom proof_of_OS_StrLen_safety_wit_4 : OS_StrLen_safety_wit_4.
Axiom proof_of_OS_StrLen_safety_wit_5 : OS_StrLen_safety_wit_5.
Axiom proof_of_OS_StrLen_entail_wit_1 : OS_StrLen_entail_wit_1.
Axiom proof_of_OS_StrLen_entail_wit_2 : OS_StrLen_entail_wit_2.
Axiom proof_of_OS_StrLen_return_wit_1 : OS_StrLen_return_wit_1.
Axiom proof_of_OS_StrLen_return_wit_2 : OS_StrLen_return_wit_2.
Axiom proof_of_OS_StrLen_derive_no_wrap_spec_by_source_spec : OS_StrLen_derive_no_wrap_spec_by_source_spec.
Axiom proof_of_OS_StrLen_derive_source_spec_by_exact_frame_spec : OS_StrLen_derive_source_spec_by_exact_frame_spec.

End VC_Correct.
