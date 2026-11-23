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
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Import UCOS2_C_Rules.
Import ucos2_rules_lib.
Local Open Scope sac_scope.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Import UCOS2_C_Rules.
Import ucos2_rules_lib.
Local Open Scope sac_scope.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_priority_spec.
Import UCOS2_C_Rules.
Import ucos2_rules_lib.
Local Open Scope sac_scope.
Local Open Scope sac.

(*----- Function OSMutex_BasePrio -----*)

Definition OSMutex_BasePrio_entail_wit_1 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 64) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_base_priority_prefix table ptcb_pre fallback 0 fallback ) ”
  &&  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  TT && emp 
|--
  “ (mutex_base_priority_prefix table ptcb_pre fallback 0 fallback ) ”
  &&  emp
).

Definition OSMutex_BasePrio_entail_wit_1_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  (mutex_base_priority_prefix table ptcb_pre fallback 0 fallback )
.

Definition OSMutex_BasePrio_entail_wit_2_1 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : ((Znth i table 0) = ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 256)) (PreH7 : (0 <= fallback)) (PreH8 : (fallback < 256)) (PreH9 : ((Zlength (table)) = 64)) (PreH10 : (mutex_priority_fallback image fallback )) (PreH11 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 64) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < 256) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_base_priority_prefix table ptcb_pre fallback (i + 1 ) i ) ”
  &&  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : ((Znth i table 0) = ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 256)) (PreH7 : (0 <= fallback)) (PreH8 : (fallback < 256)) (PreH9 : ((Zlength (table)) = 64)) (PreH10 : (mutex_priority_fallback image fallback )) (PreH11 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  TT && emp 
|--
  “ (mutex_base_priority_prefix table ptcb_pre fallback (i + 1 ) i ) ”
  &&  emp
).

Definition OSMutex_BasePrio_entail_wit_2_1_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : ((Znth i table 0) = ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 256)) (PreH7 : (0 <= fallback)) (PreH8 : (fallback < 256)) (PreH9 : ((Zlength (table)) = 64)) (PreH10 : (mutex_priority_fallback image fallback )) (PreH11 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  (mutex_base_priority_prefix table ptcb_pre fallback (i + 1 ) i )
.

Definition OSMutex_BasePrio_entail_wit_2_2 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : ((Znth i table 0) <> ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 256)) (PreH7 : (0 <= fallback)) (PreH8 : (fallback < 256)) (PreH9 : ((Zlength (table)) = 64)) (PreH10 : (mutex_priority_fallback image fallback )) (PreH11 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 64) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 256) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_base_priority_prefix table ptcb_pre fallback (i + 1 ) prio ) ”
  &&  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : ((Znth i table 0) <> ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 256)) (PreH7 : (0 <= fallback)) (PreH8 : (fallback < 256)) (PreH9 : ((Zlength (table)) = 64)) (PreH10 : (mutex_priority_fallback image fallback )) (PreH11 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  TT && emp 
|--
  “ (mutex_base_priority_prefix table ptcb_pre fallback (i + 1 ) prio ) ”
  &&  emp
).

Definition OSMutex_BasePrio_entail_wit_2_2_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : ((Znth i table 0) <> ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= prio)) (PreH6 : (prio < 256)) (PreH7 : (0 <= fallback)) (PreH8 : (fallback < 256)) (PreH9 : ((Zlength (table)) = 64)) (PreH10 : (mutex_priority_fallback image fallback )) (PreH11 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  (mutex_base_priority_prefix table ptcb_pre fallback (i + 1 ) prio )
.

Definition OSMutex_BasePrio_return_wit_1 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 256)) (PreH6 : (0 <= fallback)) (PreH7 : (fallback < 256)) (PreH8 : ((Zlength (table)) = 64)) (PreH9 : (mutex_priority_fallback image fallback )) (PreH10 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_base_priority_result table ptcb_pre fallback prio ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 256)) (PreH6 : (0 <= fallback)) (PreH7 : (fallback < 256)) (PreH8 : ((Zlength (table)) = 64)) (PreH9 : (mutex_priority_fallback image fallback )) (PreH10 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  TT && emp 
|--
  “ (mutex_base_priority_result table ptcb_pre fallback prio ) ”
  &&  emp
).

Definition OSMutex_BasePrio_return_wit_1_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 256)) (PreH6 : (0 <= fallback)) (PreH7 : (fallback < 256)) (PreH8 : ((Zlength (table)) = 64)) (PreH9 : (mutex_priority_fallback image fallback )) (PreH10 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  (mutex_base_priority_result table ptcb_pre fallback prio )
.

Definition OSMutex_BasePrio_partial_solve_wit_1_pure := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  ((( &( "i" ) )) # UShort  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_priority_fallback image fallback ) ”
.

Definition OSMutex_BasePrio_partial_solve_wit_1_aux := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
.

Definition OSMutex_BasePrio_partial_solve_wit_1 := OSMutex_BasePrio_partial_solve_wit_1_pure -> OSMutex_BasePrio_partial_solve_wit_1_aux.

Definition OSMutex_BasePrio_partial_solve_wit_2 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : (i <= 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 256)) (PreH6 : (0 <= fallback)) (PreH7 : (fallback < 256)) (PreH8 : ((Zlength (table)) = 64)) (PreH9 : (mutex_priority_fallback image fallback )) (PreH10 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (i <= 63) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 64) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 256) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_base_priority_prefix table ptcb_pre fallback i prio ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (i * sizeof(PTR)))) # Ptr  |-> (Znth i table 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) i 0 64 table )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
.

Definition OSMutex_BasePrio_partial_solve_wit_3_pure := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 256)) (PreH6 : (0 <= fallback)) (PreH7 : (fallback < 256)) (PreH8 : ((Zlength (table)) = 64)) (PreH9 : (mutex_priority_fallback image fallback )) (PreH10 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  ((( &( "i" ) )) # UShort  |-> i)
  **  ((( &( "prio" ) )) # UChar  |-> prio)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_priority_fallback image fallback ) ”
.

Definition OSMutex_BasePrio_partial_solve_wit_3_aux := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (prio: Z) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= prio)) (PreH5 : (prio < 256)) (PreH6 : (0 <= fallback)) (PreH7 : (fallback < 256)) (PreH8 : ((Zlength (table)) = 64)) (PreH9 : (mutex_priority_fallback image fallback )) (PreH10 : (mutex_base_priority_prefix table ptcb_pre fallback i prio )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (i > 63) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 64) ” 
  &&  “ (0 <= prio) ” 
  &&  “ (prio < 256) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_base_priority_prefix table ptcb_pre fallback i prio ) ”
  &&  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
.

Definition OSMutex_BasePrio_partial_solve_wit_3 := OSMutex_BasePrio_partial_solve_wit_3_pure -> OSMutex_BasePrio_partial_solve_wit_3_aux.

Definition OSMutex_BasePrio_which_implies_wit_1 := 
(
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb image )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
) \/
(
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb image )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
).

Definition OSMutex_BasePrio_which_implies_wit_1_split_goal_spatial := 
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb image )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
.

Definition OSMutex_BasePrio_which_implies_wit_2 := 
(
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
|--
  (tcb64_storage_rep ptcb image )
) \/
(
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
|--
  (tcb64_storage_rep ptcb image )
).

Definition OSMutex_BasePrio_which_implies_wit_2_split_goal_spatial := 
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
|--
  (tcb64_storage_rep ptcb image )
.

(*----- Function OSMutex_EffectivePrio -----*)

Definition OSMutex_EffectivePrio_entail_wit_1 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 64) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_priority_no_match table ptcb_pre 0 ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  TT && emp 
|--
  “ (mutex_priority_no_match table ptcb_pre 0 ) ”
  &&  emp
).

Definition OSMutex_EffectivePrio_entail_wit_1_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= fallback)) (PreH2 : (fallback < 256)) (PreH3 : ((Zlength (table)) = 64)) (PreH4 : (mutex_priority_fallback image fallback )) ,
  (mutex_priority_no_match table ptcb_pre 0 )
.

Definition OSMutex_EffectivePrio_entail_wit_2 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : ((Znth i table 0) <> ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= fallback)) (PreH6 : (fallback < 256)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : (mutex_priority_fallback image fallback )) (PreH9 : (mutex_priority_no_match table ptcb_pre i )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (tcb64_storage_rep ptcb_pre image )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 64) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_priority_no_match table ptcb_pre (i + 1 ) ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : ((Znth i table 0) <> ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= fallback)) (PreH6 : (fallback < 256)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : (mutex_priority_fallback image fallback )) (PreH9 : (mutex_priority_no_match table ptcb_pre i )) ,
  TT && emp 
|--
  “ (mutex_priority_no_match table ptcb_pre (i + 1 ) ) ”
  &&  emp
).

Definition OSMutex_EffectivePrio_entail_wit_2_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : ((Znth i table 0) <> ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= fallback)) (PreH6 : (fallback < 256)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : (mutex_priority_fallback image fallback )) (PreH9 : (mutex_priority_no_match table ptcb_pre i )) ,
  (mutex_priority_no_match table ptcb_pre (i + 1 ) )
.

Definition OSMutex_EffectivePrio_return_wit_1 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_effective_priority_result table ptcb_pre fallback fallback ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
|--
  “ (mutex_effective_priority_result table ptcb_pre fallback fallback ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
).

Definition OSMutex_EffectivePrio_return_wit_1_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
|--
  “ (mutex_effective_priority_result table ptcb_pre fallback fallback ) ”
.

Definition OSMutex_EffectivePrio_return_wit_1_split_goal_spatial := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb_pre TCBPrio image )
|--
  (tcb64_storage_rep ptcb_pre image )
.

Definition OSMutex_EffectivePrio_return_wit_2 := 
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : ((Znth i table 0) = ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= fallback)) (PreH6 : (fallback < 256)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : (mutex_priority_fallback image fallback )) (PreH9 : (mutex_priority_no_match table ptcb_pre i )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (tcb64_storage_rep ptcb_pre image )
|--
  “ (mutex_effective_priority_result table ptcb_pre fallback i ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
) \/
(
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : ((Znth i table 0) = ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= fallback)) (PreH6 : (fallback < 256)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : (mutex_priority_fallback image fallback )) (PreH9 : (mutex_priority_no_match table ptcb_pre i )) ,
  TT && emp 
|--
  “ (mutex_effective_priority_result table ptcb_pre fallback i ) ”
  &&  emp
).

Definition OSMutex_EffectivePrio_return_wit_2_split_goal_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : ((Znth i table 0) = ptcb_pre)) (PreH2 : (i <= 63)) (PreH3 : (0 <= i)) (PreH4 : (i <= 64)) (PreH5 : (0 <= fallback)) (PreH6 : (fallback < 256)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : (mutex_priority_fallback image fallback )) (PreH9 : (mutex_priority_no_match table ptcb_pre i )) ,
  (mutex_effective_priority_result table ptcb_pre fallback i )
.

Definition OSMutex_EffectivePrio_partial_solve_wit_1 := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i <= 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (i <= 63) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 64) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_priority_no_match table ptcb_pre i ) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (i * sizeof(PTR)))) # Ptr  |-> (Znth i table 0))
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) i 0 64 table )
  **  (tcb64_storage_rep ptcb_pre image )
.

Definition OSMutex_EffectivePrio_partial_solve_wit_2_pure := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  ((( &( "i" ) )) # UShort  |-> i)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_priority_fallback image fallback ) ”
.

Definition OSMutex_EffectivePrio_partial_solve_wit_2_aux := 
forall (ptcb_pre: Z) (fallback: Z) (table: (@list Z)) (image: TCBCommonImage) (i: Z) (PreH1 : (i > 63)) (PreH2 : (0 <= i)) (PreH3 : (i <= 64)) (PreH4 : (0 <= fallback)) (PreH5 : (fallback < 256)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : (mutex_priority_fallback image fallback )) (PreH8 : (mutex_priority_no_match table ptcb_pre i )) ,
  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
|--
  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (i > 63) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 64) ” 
  &&  “ (0 <= fallback) ” 
  &&  “ (fallback < 256) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ (mutex_priority_fallback image fallback ) ” 
  &&  “ (mutex_priority_no_match table ptcb_pre i ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
.

Definition OSMutex_EffectivePrio_partial_solve_wit_2 := OSMutex_EffectivePrio_partial_solve_wit_2_pure -> OSMutex_EffectivePrio_partial_solve_wit_2_aux.

Definition OSMutex_EffectivePrio_which_implies_wit_1 := 
(
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb image )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
) \/
(
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb image )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
).

Definition OSMutex_EffectivePrio_which_implies_wit_1_split_goal_spatial := 
forall (fallback: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_fallback image fallback )) ,
  (tcb64_storage_rep ptcb image )
|--
  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> fallback)
  **  (tcb64_storage_without ptcb TCBPrio image )
.

(*----- Function OSMutex_RdyAtPrio -----*)

Definition OSMutex_RdyAtPrio_safety_wit_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (3 <= 31) ” 
  &&  “ (0 <= 3) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_3 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
).

Definition OSMutex_RdyAtPrio_safety_wit_3_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_3_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_4 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ” 
  &&  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
).

Definition OSMutex_RdyAtPrio_safety_wit_4_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land (Z.shiftr prio_pre 3) 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_4_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= (Z.land (Z.shiftr prio_pre 3) 7)) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_5 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OSMutex_RdyAtPrio_safety_wit_5_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_5_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_6 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land prio_pre 7) <= 63) ” 
  &&  “ (0 <= (Z.land prio_pre 7)) ”
).

Definition OSMutex_RdyAtPrio_safety_wit_6_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land prio_pre 7) <= 63) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_6_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= (Z.land prio_pre 7)) ”
.

Definition OSMutex_RdyAtPrio_safety_wit_7 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ False ”
.

Definition OSMutex_RdyAtPrio_safety_wit_8 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  ((( &( "y" ) )) # UChar  |-> old_y)
  **  ((( &( "rdy" ) )) # UChar  |-> rdy)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ False ”
.

Definition OSMutex_RdyAtPrio_entail_wit_1_1 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) = 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land group (Z.lnot old_bity)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (1 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
) \/
(
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) = 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  TT && emp 
|--
  “ (1 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ” 
  &&  “ ((Z.land group (Z.lnot old_bity)) = (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) ” 
  &&  “ ((replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) = (mutex_priority_removed_rows (rows) (old_y) (old_bitx))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_entail_wit_1_1_split_goal_1 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) = 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (1 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_1_split_goal_2 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) = 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  ((Z.land group (Z.lnot old_bity)) = (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_1_split_goal_3 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) = 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  ((replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) = (mutex_priority_removed_rows (rows) (old_y) (old_bitx)))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_2 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) <> 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (1 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
) \/
(
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) <> 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  TT && emp 
|--
  “ (1 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ” 
  &&  “ (group = (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) ” 
  &&  “ ((replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) = (mutex_priority_removed_rows (rows) (old_y) (old_bitx))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_entail_wit_1_2_split_goal_1 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) <> 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (1 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_2_split_goal_2 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) <> 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (group = (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_2_split_goal_3 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((unsigned_last_nbits ((Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0)) (32)) <> 0)) (PreH2 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH3 : (0 <= group)) (PreH4 : (group < 256)) (PreH5 : (0 <= old_bitx)) (PreH6 : (old_bitx < 256)) (PreH7 : (0 <= old_bity)) (PreH8 : (old_bity < 256)) (PreH9 : ((Zlength (rows)) = 8)) (PreH10 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH11 : (0 <= prio_pre)) (PreH12 : (prio_pre < 64)) (PreH13 : (0 <= old_y)) (PreH14 : (old_y < 8)) (PreH15 : ((Zlength (table)) = 64)) (PreH16 : ((Zlength (rows)) = 8)) (PreH17 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  ((replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) = (mutex_priority_removed_rows (rows) (old_y) (old_bitx)))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_3 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
) \/
(
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  TT && emp 
|--
  “ (0 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ” 
  &&  “ (group = (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) ” 
  &&  “ (rows = (mutex_priority_removed_rows (rows) (old_y) (old_bitx))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_entail_wit_1_3_split_goal_1 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (0 = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_3_split_goal_2 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (group = (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
.

Definition OSMutex_RdyAtPrio_entail_wit_1_3_split_goal_3 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) = 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (rows = (mutex_priority_removed_rows (rows) (old_y) (old_bitx)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> prio_pre)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  TT && emp 
|--
  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((Z.land prio_pre 7) = (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((Z.land (Z.shiftr prio_pre 3) 7) = (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (tcb_bit_x_of_prio (prio_pre))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)) = (tcb_bit_y_of_prio (prio_pre))) ” 
  &&  “ (prio_pre = (mutex_priority_current (ptcb_pre) (ptcb_pre) (current_prio) (prio_pre))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((tcb_x_of_prio (prio_pre)) < 8)
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (0 <= (tcb_x_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((tcb_y_of_prio (prio_pre)) < 8)
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (0 <= (tcb_y_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_5 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((Z.land prio_pre 7) = (tcb_x_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_6 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((Z.land (Z.shiftr prio_pre 3) 7) = (tcb_y_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_7 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (tcb_bit_x_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_8 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)) = (tcb_bit_y_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_1_split_goal_9 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre = current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (prio_pre = (mutex_priority_current (ptcb_pre) (ptcb_pre) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (Z.land prio_pre 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (Z.land (Z.shiftr prio_pre 3) 7))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
) \/
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  TT && emp 
|--
  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((Z.land prio_pre 7) = (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((Z.land (Z.shiftr prio_pre 3) 7) = (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (tcb_bit_x_of_prio (prio_pre))) ” 
  &&  “ ((unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)) = (tcb_bit_y_of_prio (prio_pre))) ” 
  &&  “ (current_prio = (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_1 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((tcb_x_of_prio (prio_pre)) < 8)
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_2 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (0 <= (tcb_x_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((tcb_y_of_prio (prio_pre)) < 8)
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (0 <= (tcb_y_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_5 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((Z.land prio_pre 7) = (tcb_x_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_6 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((Z.land (Z.shiftr prio_pre 3) 7) = (tcb_y_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_7 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (Z.land prio_pre 7))) (8)) = (tcb_bit_x_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_8 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((unsigned_last_nbits ((Z.shiftl 1 (Z.land (Z.shiftr prio_pre 3) 7))) (8)) = (tcb_bit_y_of_prio (prio_pre)))
.

Definition OSMutex_RdyAtPrio_entail_wit_2_2_split_goal_9 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : (ptcb_pre <> current)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index_2: Z) , (((0 <= index_2) /\ (index_2 < 8)) -> ((0 <= (Znth (index_2) (rows) (0))) /\ ((Znth (index_2) (rows) (0)) < 256)))) (PreH15 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (current_prio = (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_return_wit_1 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (tcb64_storage_rep ptcb_pre (mutex_priority_image (image) (prio_pre)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  (tcb64_storage_rep ptcb_pre (mutex_priority_image (image) (prio_pre)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_rows (rows) (old_y) (old_bitx) (prio_pre)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_group (rows) (group) (old_y) (old_bitx) (old_bity) (prio_pre)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
) \/
(
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  TT && emp 
|--
  “ ((Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))) = (mutex_priority_group (rows) (group) (old_y) (old_bitx) (old_bity) (prio_pre))) ” 
  &&  “ ((replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) = (mutex_priority_rows (rows) (old_y) (old_bitx) (prio_pre))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_return_wit_1_split_goal_1 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))) = (mutex_priority_group (rows) (group) (old_y) (old_bitx) (old_bity) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_return_wit_1_split_goal_2 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) = (mutex_priority_rows (rows) (old_y) (old_bitx) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_return_wit_2 := 
(
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (tcb64_storage_rep ptcb_pre (mutex_priority_image (image) (prio_pre)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  (tcb64_storage_rep ptcb_pre (mutex_priority_image (image) (prio_pre)) )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_rows (rows) (old_y) (old_bitx) (prio_pre)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_group (rows) (group) (old_y) (old_bitx) (old_bity) (prio_pre)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
) \/
(
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  TT && emp 
|--
  “ ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)) = (mutex_priority_group (rows) (group) (old_y) (old_bitx) (old_bity) (prio_pre))) ” 
  &&  “ ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)) = (mutex_priority_rows (rows) (old_y) (old_bitx) (prio_pre))) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_return_wit_2_split_goal_1 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)) = (mutex_priority_group (rows) (group) (old_y) (old_bitx) (old_bity) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_return_wit_2_split_goal_2 := 
forall (prio_pre: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)) = (mutex_priority_rows (rows) (old_y) (old_bitx) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_1_pure := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 64)) (PreH3 : (0 <= old_y)) (PreH4 : (old_y < 8)) (PreH5 : ((Zlength (table)) = 64)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  ((( &( "rdy" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_1_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 64)) (PreH3 : (0 <= old_y)) (PreH4 : (old_y < 8)) (PreH5 : ((Zlength (table)) = 64)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
  &&  (tcb64_storage_rep ptcb_pre image )
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_1 := OSMutex_RdyAtPrio_partial_solve_wit_1_pure -> OSMutex_RdyAtPrio_partial_solve_wit_1_aux.

Definition OSMutex_RdyAtPrio_partial_solve_wit_2_pure := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 64)) (PreH3 : (0 <= old_y)) (PreH4 : (old_y < 8)) (PreH5 : ((Zlength (table)) = 64)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  ((( &( "rdy" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "prio" ) )) # UChar  |-> prio_pre)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Zlength (rows)) = 8) ”
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_2_aux := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= prio_pre)) (PreH2 : (prio_pre < 64)) (PreH3 : (0 <= old_y)) (PreH4 : (old_y < 8)) (PreH5 : ((Zlength (table)) = 64)) (PreH6 : ((Zlength (rows)) = 8)) (PreH7 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_2 := OSMutex_RdyAtPrio_partial_solve_wit_2_pure -> OSMutex_RdyAtPrio_partial_solve_wit_2_aux.

Definition OSMutex_RdyAtPrio_partial_solve_wit_3 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : (0 <= group)) (PreH2 : (group < 256)) (PreH3 : (0 <= old_bitx)) (PreH4 : (old_bitx < 256)) (PreH5 : (0 <= old_bity)) (PreH6 : (old_bity < 256)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH9 : (0 <= prio_pre)) (PreH10 : (prio_pre < 64)) (PreH11 : (0 <= old_y)) (PreH12 : (old_y < 8)) (PreH13 : ((Zlength (table)) = 64)) (PreH14 : ((Zlength (rows)) = 8)) (PreH15 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
  &&  (((( &( "OSRdyTbl" ) ) + (old_y * sizeof(UCHAR)))) # UChar  |-> (Znth old_y rows 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) old_y 0 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_4 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land (Znth old_y rows 0) old_bitx) <> 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
  &&  (((( &( "OSRdyTbl" ) ) + (old_y * sizeof(UCHAR)))) # UChar  |-> (Znth old_y rows 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) old_y 0 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_5 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land (Znth old_y rows 0) old_bitx) <> 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
  &&  (((( &( "OSRdyTbl" ) ) + (old_y * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) old_y 0 8 rows )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_6 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (PreH1 : ((Z.land (Znth old_y rows 0) old_bitx) <> 0)) (PreH2 : (0 <= group)) (PreH3 : (group < 256)) (PreH4 : (0 <= old_bitx)) (PreH5 : (old_bitx < 256)) (PreH6 : (0 <= old_bity)) (PreH7 : (old_bity < 256)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH10 : (0 <= prio_pre)) (PreH11 : (prio_pre < 64)) (PreH12 : (0 <= old_y)) (PreH13 : (old_y < 8)) (PreH14 : ((Zlength (table)) = 64)) (PreH15 : ((Zlength (rows)) = 8)) (PreH16 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
|--
  “ ((Z.land (Znth old_y rows 0) old_bitx) <> 0) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity ) ”
  &&  (((( &( "OSRdyTbl" ) ) + (old_y * sizeof(UCHAR)))) # UChar  |-> (Znth old_y (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) old_y 0 8 (replace_Znth (old_y) ((Z.land (Znth old_y rows 0) (unsigned_last_nbits ((Z.lnot old_bitx)) (8)))) (rows)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> current_prio)
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_7 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH16 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH17 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH18 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH19 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ ((unsigned_last_nbits (rdy) (32)) = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio (prio_pre)) * sizeof(UCHAR)))) # UChar  |-> (Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0))
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio (prio_pre)) 0 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_8 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH16 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH17 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH18 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH19 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ ((unsigned_last_nbits (rdy) (32)) = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio (prio_pre)) * sizeof(UCHAR)))) # UChar  |->_)
  **  (UCharArray.missing_i ( &( "OSRdyTbl" ) ) (tcb_y_of_prio (prio_pre)) 0 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_9 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH16 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH17 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH18 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH19 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ ((unsigned_last_nbits (rdy) (32)) = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) prio_pre 0 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_10 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : (0 <= prio_pre)) (PreH3 : (prio_pre < 64)) (PreH4 : (0 <= old_y)) (PreH5 : (old_y < 8)) (PreH6 : ((Zlength (table)) = 64)) (PreH7 : ((Zlength (rows)) = 8)) (PreH8 : (0 <= group)) (PreH9 : (group < 256)) (PreH10 : (0 <= old_bitx)) (PreH11 : (old_bitx < 256)) (PreH12 : (0 <= old_bity)) (PreH13 : (old_bity < 256)) (PreH14 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH15 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH16 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH17 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH18 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH19 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 table )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ ((unsigned_last_nbits (rdy) (32)) <> 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (((( &( "OSTCBPrioTbl" ) ) + (prio_pre * sizeof(PTR)))) # Ptr  |->_)
  **  (PtrArray.missing_i ( &( "OSTCBPrioTbl" ) ) prio_pre 0 64 table )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_11 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) <> 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ ((unsigned_last_nbits (rdy) (32)) <> 1) ” 
  &&  “ ((unsigned_last_nbits (rdy) (32)) <> 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_partial_solve_wit_12 := 
forall (prio_pre: Z) (ptcb_pre: Z) (current_prio: Z) (current: Z) (group: Z) (old_bity: Z) (old_bitx: Z) (old_y: Z) (rows: (@list Z)) (table: (@list Z)) (image: TCBCommonImage) (rdy: Z) (PreH1 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH2 : ((unsigned_last_nbits (rdy) (32)) = 1)) (PreH3 : (0 <= prio_pre)) (PreH4 : (prio_pre < 64)) (PreH5 : (0 <= old_y)) (PreH6 : (old_y < 8)) (PreH7 : ((Zlength (table)) = 64)) (PreH8 : ((Zlength (rows)) = 8)) (PreH9 : (0 <= group)) (PreH10 : (group < 256)) (PreH11 : (0 <= old_bitx)) (PreH12 : (old_bitx < 256)) (PreH13 : (0 <= old_bity)) (PreH14 : (old_bity < 256)) (PreH15 : forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))) (PreH16 : (0 <= (tcb_y_of_prio (prio_pre)))) (PreH17 : ((tcb_y_of_prio (prio_pre)) < 8)) (PreH18 : (0 <= (tcb_x_of_prio (prio_pre)))) (PreH19 : ((tcb_x_of_prio (prio_pre)) < 8)) (PreH20 : (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx)))))) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) )
  **  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
|--
  “ ((unsigned_last_nbits (rdy) (32)) = 1) ” 
  &&  “ ((unsigned_last_nbits (rdy) (32)) = 1) ” 
  &&  “ (0 <= prio_pre) ” 
  &&  “ (prio_pre < 64) ” 
  &&  “ (0 <= old_y) ” 
  &&  “ (old_y < 8) ” 
  &&  “ ((Zlength (table)) = 64) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (0 <= (tcb_y_of_prio (prio_pre))) ” 
  &&  “ ((tcb_y_of_prio (prio_pre)) < 8) ” 
  &&  “ (0 <= (tcb_x_of_prio (prio_pre))) ” 
  &&  “ ((tcb_x_of_prio (prio_pre)) < 8) ” 
  &&  “ (rdy = (encode_bool ((mutex_priority_was_ready (rows) (old_y) (old_bitx))))) ”
  &&  (mutex_priority_tcb_rest ptcb_pre image )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio_pre)))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio_pre)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (replace_Znth (prio_pre) (ptcb_pre) (table)) )
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 (replace_Znth ((tcb_y_of_prio (prio_pre))) ((Z.lor (unsigned_last_nbits ((Znth (tcb_y_of_prio (prio_pre)) (mutex_priority_removed_rows (rows) (old_y) (old_bitx)) 0)) (8)) (unsigned_last_nbits ((tcb_bit_x_of_prio (prio_pre))) (8)))) ((mutex_priority_removed_rows (rows) (old_y) (old_bitx)))) )
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.lor (unsigned_last_nbits ((mutex_priority_removed_group (rows) (group) (old_y) (old_bitx) (old_bity))) (8)) (unsigned_last_nbits ((tcb_bit_y_of_prio (prio_pre))) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> current)
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (mutex_priority_current (ptcb_pre) (current) (current_prio) (prio_pre)))
.

Definition OSMutex_RdyAtPrio_which_implies_wit_1 := 
(
forall (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (tcb64_storage_rep ptcb image )
|--
  (mutex_priority_tcb_rest ptcb image )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
) \/
(
forall (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (tcb64_storage_rep ptcb image )
|--
  (mutex_priority_tcb_rest ptcb image )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
).

Definition OSMutex_RdyAtPrio_which_implies_wit_1_split_goal_spatial := 
forall (old_bity: Z) (old_bitx: Z) (old_y: Z) (old_x: Z) (old_prio: Z) (image: TCBCommonImage) (ptcb: Z) (PreH1 : (mutex_priority_image_fields image old_prio old_x old_y old_bitx old_bity )) ,
  (tcb64_storage_rep ptcb image )
|--
  (mutex_priority_tcb_rest ptcb image )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> old_prio)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> old_x)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> old_y)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2 := 
(
forall (group: Z) (old_bity: Z) (old_bitx: Z) (rows: (@list Z)) (ptcb: Z) (PreH1 : ((Zlength (rows)) = 8)) ,
  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
|--
  “ (0 <= group) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ ((Zlength (rows)) = 8) ” 
  &&  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ”
  &&  ((( &( "OSRdyGrp" ) )) # UChar  |-> group)
  **  (UCharArray.full ( &( "OSRdyTbl" ) ) 8 rows )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> old_bitx)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> old_bity)
) \/
(
forall (group: Z) (old_bity: Z) (old_bitx: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  TT && emp 
|--
  “ forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256))) ” 
  &&  “ (old_bity < 256) ” 
  &&  “ (0 <= old_bity) ” 
  &&  “ (old_bitx < 256) ” 
  &&  “ (0 <= old_bitx) ” 
  &&  “ (group < 256) ” 
  &&  “ (0 <= group) ”
  &&  emp
).

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_1 := 
forall (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  forall (index: Z) , (((0 <= index) /\ (index < 8)) -> ((0 <= (Znth (index) (rows) (0))) /\ ((Znth (index) (rows) (0)) < 256)))
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_2 := 
forall (old_bity: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  (old_bity < 256)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_3 := 
forall (old_bity: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  (0 <= old_bity)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_4 := 
forall (old_bitx: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  (old_bitx < 256)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_5 := 
forall (old_bitx: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  (0 <= old_bitx)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_6 := 
forall (group: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  (group < 256)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_2_split_goal_7 := 
forall (group: Z) (rows: (@list Z)) (PreH1 : ((Zlength (rows)) = 8)) ,
  (0 <= group)
.

Definition OSMutex_RdyAtPrio_which_implies_wit_3 := 
(
forall (image: TCBCommonImage) (ptcb: Z) (prio: Z) ,
  (mutex_priority_tcb_rest ptcb image )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio)))
|--
  (tcb64_storage_rep ptcb (mutex_priority_image (image) (prio)) )
) \/
(
forall (image: TCBCommonImage) (ptcb: Z) (prio: Z) ,
  (mutex_priority_tcb_rest ptcb image )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio)))
|--
  (tcb64_storage_rep ptcb (mutex_priority_image (image) (prio)) )
).

Definition OSMutex_RdyAtPrio_which_implies_wit_3_split_goal_spatial := 
forall (image: TCBCommonImage) (ptcb: Z) (prio: Z) ,
  (mutex_priority_tcb_rest ptcb image )
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBPrio")) # UChar  |-> prio)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBX")) # UChar  |-> (tcb_x_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio (prio)))
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio (prio)))
|--
  (tcb64_storage_rep ptcb (mutex_priority_image (image) (prio)) )
.

Module Type VC_Correct.


Axiom proof_of_OSMutex_BasePrio_entail_wit_1 : OSMutex_BasePrio_entail_wit_1.
Axiom proof_of_OSMutex_BasePrio_entail_wit_2_1 : OSMutex_BasePrio_entail_wit_2_1.
Axiom proof_of_OSMutex_BasePrio_entail_wit_2_2 : OSMutex_BasePrio_entail_wit_2_2.
Axiom proof_of_OSMutex_BasePrio_return_wit_1 : OSMutex_BasePrio_return_wit_1.
Axiom proof_of_OSMutex_BasePrio_partial_solve_wit_1_pure : OSMutex_BasePrio_partial_solve_wit_1_pure.
Axiom proof_of_OSMutex_BasePrio_partial_solve_wit_1 : OSMutex_BasePrio_partial_solve_wit_1.
Axiom proof_of_OSMutex_BasePrio_partial_solve_wit_2 : OSMutex_BasePrio_partial_solve_wit_2.
Axiom proof_of_OSMutex_BasePrio_partial_solve_wit_3_pure : OSMutex_BasePrio_partial_solve_wit_3_pure.
Axiom proof_of_OSMutex_BasePrio_partial_solve_wit_3 : OSMutex_BasePrio_partial_solve_wit_3.
Axiom proof_of_OSMutex_BasePrio_which_implies_wit_1 : OSMutex_BasePrio_which_implies_wit_1.
Axiom proof_of_OSMutex_BasePrio_which_implies_wit_2 : OSMutex_BasePrio_which_implies_wit_2.
Axiom proof_of_OSMutex_EffectivePrio_entail_wit_1 : OSMutex_EffectivePrio_entail_wit_1.
Axiom proof_of_OSMutex_EffectivePrio_entail_wit_2 : OSMutex_EffectivePrio_entail_wit_2.
Axiom proof_of_OSMutex_EffectivePrio_return_wit_1 : OSMutex_EffectivePrio_return_wit_1.
Axiom proof_of_OSMutex_EffectivePrio_return_wit_2 : OSMutex_EffectivePrio_return_wit_2.
Axiom proof_of_OSMutex_EffectivePrio_partial_solve_wit_1 : OSMutex_EffectivePrio_partial_solve_wit_1.
Axiom proof_of_OSMutex_EffectivePrio_partial_solve_wit_2_pure : OSMutex_EffectivePrio_partial_solve_wit_2_pure.
Axiom proof_of_OSMutex_EffectivePrio_partial_solve_wit_2 : OSMutex_EffectivePrio_partial_solve_wit_2.
Axiom proof_of_OSMutex_EffectivePrio_which_implies_wit_1 : OSMutex_EffectivePrio_which_implies_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_1 : OSMutex_RdyAtPrio_safety_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_2 : OSMutex_RdyAtPrio_safety_wit_2.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_3 : OSMutex_RdyAtPrio_safety_wit_3.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_4 : OSMutex_RdyAtPrio_safety_wit_4.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_5 : OSMutex_RdyAtPrio_safety_wit_5.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_6 : OSMutex_RdyAtPrio_safety_wit_6.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_7 : OSMutex_RdyAtPrio_safety_wit_7.
Axiom proof_of_OSMutex_RdyAtPrio_safety_wit_8 : OSMutex_RdyAtPrio_safety_wit_8.
Axiom proof_of_OSMutex_RdyAtPrio_entail_wit_1_1 : OSMutex_RdyAtPrio_entail_wit_1_1.
Axiom proof_of_OSMutex_RdyAtPrio_entail_wit_1_2 : OSMutex_RdyAtPrio_entail_wit_1_2.
Axiom proof_of_OSMutex_RdyAtPrio_entail_wit_1_3 : OSMutex_RdyAtPrio_entail_wit_1_3.
Axiom proof_of_OSMutex_RdyAtPrio_entail_wit_2_1 : OSMutex_RdyAtPrio_entail_wit_2_1.
Axiom proof_of_OSMutex_RdyAtPrio_entail_wit_2_2 : OSMutex_RdyAtPrio_entail_wit_2_2.
Axiom proof_of_OSMutex_RdyAtPrio_return_wit_1 : OSMutex_RdyAtPrio_return_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_return_wit_2 : OSMutex_RdyAtPrio_return_wit_2.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_1_pure : OSMutex_RdyAtPrio_partial_solve_wit_1_pure.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_1 : OSMutex_RdyAtPrio_partial_solve_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_2_pure : OSMutex_RdyAtPrio_partial_solve_wit_2_pure.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_2 : OSMutex_RdyAtPrio_partial_solve_wit_2.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_3 : OSMutex_RdyAtPrio_partial_solve_wit_3.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_4 : OSMutex_RdyAtPrio_partial_solve_wit_4.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_5 : OSMutex_RdyAtPrio_partial_solve_wit_5.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_6 : OSMutex_RdyAtPrio_partial_solve_wit_6.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_7 : OSMutex_RdyAtPrio_partial_solve_wit_7.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_8 : OSMutex_RdyAtPrio_partial_solve_wit_8.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_9 : OSMutex_RdyAtPrio_partial_solve_wit_9.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_10 : OSMutex_RdyAtPrio_partial_solve_wit_10.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_11 : OSMutex_RdyAtPrio_partial_solve_wit_11.
Axiom proof_of_OSMutex_RdyAtPrio_partial_solve_wit_12 : OSMutex_RdyAtPrio_partial_solve_wit_12.
Axiom proof_of_OSMutex_RdyAtPrio_which_implies_wit_1 : OSMutex_RdyAtPrio_which_implies_wit_1.
Axiom proof_of_OSMutex_RdyAtPrio_which_implies_wit_2 : OSMutex_RdyAtPrio_which_implies_wit_2.
Axiom proof_of_OSMutex_RdyAtPrio_which_implies_wit_3 : OSMutex_RdyAtPrio_which_implies_wit_3.

End VC_Correct.
