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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_link_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmr_Link -----*)

Definition OSTmr_Link_safety_wit_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))) (PreH2 : (time_raw_spec <= UINT_MAX)) (PreH3 : (period_raw_spec <= UINT_MAX)) (PreH4 : (delay_raw_spec <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : (kind_raw_spec = 1)) (PreH9 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH10 : (tmr_link_wheel_size )) (PreH11 : (0 < p_raw_spec)) (PreH12 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH13 : (0 < base_raw_spec)) (PreH14 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH15 : (0 <= kind_raw_spec)) (PreH16 : (kind_raw_spec < 256)) (PreH17 : (0 <= time_raw_spec)) (PreH18 : (time_raw_spec < 4294967296)) (PreH19 : (0 <= delay_raw_spec)) (PreH20 : (delay_raw_spec < 4294967296)) (PreH21 : (0 <= period_raw_spec)) (PreH22 : (period_raw_spec < 4294967296)) (PreH23 : (0 <= entries_raw_spec)) (PreH24 : (entries_raw_spec < 65536)) (PreH25 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH26 : (ptmr_pre = p_raw_spec)) (PreH27 : (type_pre = kind_raw_spec)) (PreH28 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH29 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (7 <> 0) ”
.

Definition OSTmr_Link_safety_wit_2 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))) (PreH2 : (time_raw_spec <= UINT_MAX)) (PreH3 : (period_raw_spec <= UINT_MAX)) (PreH4 : (delay_raw_spec <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : (delay_raw_spec = 0)) (PreH9 : (kind_raw_spec <> 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (7 <> 0) ”
.

Definition OSTmr_Link_safety_wit_3 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))) (PreH2 : (time_raw_spec <= UINT_MAX)) (PreH3 : (period_raw_spec <= UINT_MAX)) (PreH4 : (delay_raw_spec <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : (delay_raw_spec <> 0)) (PreH9 : (kind_raw_spec <> 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (7 <> 0) ”
.

Definition OSTmr_Link_safety_wit_4 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_5 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_6 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_7 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec <> 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_8 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec = 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_9 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (kind_raw_spec = 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_10 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec <> 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_11 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec = 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_12 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (kind_raw_spec = 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_13 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |-> first_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_14 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |-> first_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_safety_wit_15 := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |-> first_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Link_entail_wit_1_1 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (kind_raw_spec = 1)) (PreH2 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH3 : (tmr_link_wheel_size )) (PreH4 : (0 < p_raw_spec)) (PreH5 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH6 : (0 < base_raw_spec)) (PreH7 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH8 : (0 <= kind_raw_spec)) (PreH9 : (kind_raw_spec < 256)) (PreH10 : (0 <= time_raw_spec)) (PreH11 : (time_raw_spec < 4294967296)) (PreH12 : (0 <= delay_raw_spec)) (PreH13 : (delay_raw_spec < 4294967296)) (PreH14 : (0 <= period_raw_spec)) (PreH15 : (period_raw_spec < 4294967296)) (PreH16 : (0 <= entries_raw_spec)) (PreH17 : (entries_raw_spec < 65536)) (PreH18 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH19 : (ptmr_pre = p_raw_spec)) (PreH20 : (type_pre = kind_raw_spec)) (PreH21 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH22 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec))) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (kind_raw_spec = 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (time_raw_spec <= UINT_MAX)) (PreH2 : (period_raw_spec <= UINT_MAX)) (PreH3 : (delay_raw_spec <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) >= 0)) (PreH9 : (kind_raw_spec = 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) = (tmr_link_match (1) (delay_raw_spec) (period_raw_spec) (time_raw_spec))) ”
  &&  emp
).

Definition OSTmr_Link_entail_wit_1_1_split_goal_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (time_raw_spec <= UINT_MAX)) (PreH2 : (period_raw_spec <= UINT_MAX)) (PreH3 : (delay_raw_spec <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) >= 0)) (PreH9 : (kind_raw_spec = 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) = (tmr_link_match (1) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
.

Definition OSTmr_Link_entail_wit_1_2 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (delay_raw_spec = 0)) (PreH2 : (kind_raw_spec <> 1)) (PreH3 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH4 : (tmr_link_wheel_size )) (PreH5 : (0 < p_raw_spec)) (PreH6 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH7 : (0 < base_raw_spec)) (PreH8 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH9 : (0 <= kind_raw_spec)) (PreH10 : (kind_raw_spec < 256)) (PreH11 : (0 <= time_raw_spec)) (PreH12 : (time_raw_spec < 4294967296)) (PreH13 : (0 <= delay_raw_spec)) (PreH14 : (delay_raw_spec < 4294967296)) (PreH15 : (0 <= period_raw_spec)) (PreH16 : (period_raw_spec < 4294967296)) (PreH17 : (0 <= entries_raw_spec)) (PreH18 : (entries_raw_spec < 65536)) (PreH19 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH20 : (ptmr_pre = p_raw_spec)) (PreH21 : (type_pre = kind_raw_spec)) (PreH22 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH23 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec))) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec = 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (time_raw_spec <= UINT_MAX)) (PreH2 : (period_raw_spec <= UINT_MAX)) (PreH3 : (delay_raw_spec <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) >= 0)) (PreH9 : (delay_raw_spec = 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) = (tmr_link_match (type_pre) (0) (period_raw_spec) (time_raw_spec))) ”
  &&  emp
).

Definition OSTmr_Link_entail_wit_1_2_split_goal_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (time_raw_spec <= UINT_MAX)) (PreH2 : (period_raw_spec <= UINT_MAX)) (PreH3 : (delay_raw_spec <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) >= 0)) (PreH9 : (delay_raw_spec = 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((unsigned_last_nbits ((period_raw_spec + time_raw_spec )) (32)) = (tmr_link_match (type_pre) (0) (period_raw_spec) (time_raw_spec)))
.

Definition OSTmr_Link_entail_wit_1_3 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (delay_raw_spec <> 0)) (PreH2 : (kind_raw_spec <> 1)) (PreH3 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH4 : (tmr_link_wheel_size )) (PreH5 : (0 < p_raw_spec)) (PreH6 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH7 : (0 < base_raw_spec)) (PreH8 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH9 : (0 <= kind_raw_spec)) (PreH10 : (kind_raw_spec < 256)) (PreH11 : (0 <= time_raw_spec)) (PreH12 : (time_raw_spec < 4294967296)) (PreH13 : (0 <= delay_raw_spec)) (PreH14 : (delay_raw_spec < 4294967296)) (PreH15 : (0 <= period_raw_spec)) (PreH16 : (period_raw_spec < 4294967296)) (PreH17 : (0 <= entries_raw_spec)) (PreH18 : (entries_raw_spec < 65536)) (PreH19 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH20 : (ptmr_pre = p_raw_spec)) (PreH21 : (type_pre = kind_raw_spec)) (PreH22 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH23 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec))) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec <> 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (time_raw_spec <= UINT_MAX)) (PreH2 : (period_raw_spec <= UINT_MAX)) (PreH3 : (delay_raw_spec <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)) <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : ((unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)) >= 0)) (PreH9 : (delay_raw_spec <> 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)) = (tmr_link_match (type_pre) (delay_raw_spec) (period_raw_spec) (time_raw_spec))) ”
  &&  emp
).

Definition OSTmr_Link_entail_wit_1_3_split_goal_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (time_raw_spec <= UINT_MAX)) (PreH2 : (period_raw_spec <= UINT_MAX)) (PreH3 : (delay_raw_spec <= UINT_MAX)) (PreH4 : ((unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)) <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : ((unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)) >= 0)) (PreH9 : (delay_raw_spec <> 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((unsigned_last_nbits ((delay_raw_spec + time_raw_spec )) (32)) = (tmr_link_match (type_pre) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
.

Definition OSTmr_Link_entail_wit_2_1 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))) (PreH2 : (time_raw_spec <= UINT_MAX)) (PreH3 : (period_raw_spec <= UINT_MAX)) (PreH4 : (delay_raw_spec <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : (kind_raw_spec = 1)) (PreH9 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH10 : (tmr_link_wheel_size )) (PreH11 : (0 < p_raw_spec)) (PreH12 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH13 : (0 < base_raw_spec)) (PreH14 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH15 : (0 <= kind_raw_spec)) (PreH16 : (kind_raw_spec < 256)) (PreH17 : (0 <= time_raw_spec)) (PreH18 : (time_raw_spec < 4294967296)) (PreH19 : (0 <= delay_raw_spec)) (PreH20 : (delay_raw_spec < 4294967296)) (PreH21 : (0 <= period_raw_spec)) (PreH22 : (period_raw_spec < 4294967296)) (PreH23 : (0 <= entries_raw_spec)) (PreH24 : (entries_raw_spec < 65536)) (PreH25 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH26 : (ptmr_pre = p_raw_spec)) (PreH27 : (type_pre = kind_raw_spec)) (PreH28 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH29 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |-> (unsigned_last_nbits (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)))
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) = ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (kind_raw_spec = 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (kind_raw_spec = 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (((tmr_link_match (1) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)) = ((tmr_link_match (1) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) ”
  &&  emp
).

Definition OSTmr_Link_entail_wit_2_1_split_goal_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (kind_raw_spec = 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((unsigned_last_nbits (((tmr_link_match (1) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)) = ((tmr_link_match (1) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
.

Definition OSTmr_Link_entail_wit_2_2 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))) (PreH2 : (time_raw_spec <= UINT_MAX)) (PreH3 : (period_raw_spec <= UINT_MAX)) (PreH4 : (delay_raw_spec <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : (delay_raw_spec = 0)) (PreH9 : (kind_raw_spec <> 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |-> (unsigned_last_nbits (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)))
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) = ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec = 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (delay_raw_spec = 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (((tmr_link_match (type_pre) (0) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)) = ((tmr_link_match (type_pre) (0) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) ”
  &&  emp
).

Definition OSTmr_Link_entail_wit_2_2_split_goal_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (delay_raw_spec = 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((unsigned_last_nbits (((tmr_link_match (type_pre) (0) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)) = ((tmr_link_match (type_pre) (0) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
.

Definition OSTmr_Link_entail_wit_2_3 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) = (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))) (PreH2 : (time_raw_spec <= UINT_MAX)) (PreH3 : (period_raw_spec <= UINT_MAX)) (PreH4 : (delay_raw_spec <= UINT_MAX)) (PreH5 : (time_raw_spec >= 0)) (PreH6 : (period_raw_spec >= 0)) (PreH7 : (delay_raw_spec >= 0)) (PreH8 : (delay_raw_spec <> 0)) (PreH9 : (kind_raw_spec <> 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |-> (unsigned_last_nbits (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)))
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) = ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec <> 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (delay_raw_spec <> 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits (((tmr_link_match (type_pre) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)) = ((tmr_link_match (type_pre) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) ”
  &&  emp
).

Definition OSTmr_Link_entail_wit_2_3_split_goal_1 := 
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (delay_raw_spec <> 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((unsigned_last_nbits (((tmr_link_match (type_pre) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) )) (16)) = ((tmr_link_match (type_pre) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
.

Definition OSTmr_Link_entail_wit_3_1 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) = ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |-> (( &( "OSTmrWheelTbl" ) ) + (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) * sizeof( "os_tmr_wheel" ))))
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) )) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (kind_raw_spec = 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (kind_raw_spec = 1)) (PreH10 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH11 : (tmr_link_wheel_size )) (PreH12 : (0 < p_raw_spec)) (PreH13 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH14 : (0 < base_raw_spec)) (PreH15 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH16 : (0 <= kind_raw_spec)) (PreH17 : (kind_raw_spec < 256)) (PreH18 : (0 <= time_raw_spec)) (PreH19 : (time_raw_spec < 4294967296)) (PreH20 : (0 <= delay_raw_spec)) (PreH21 : (delay_raw_spec < 4294967296)) (PreH22 : (0 <= period_raw_spec)) (PreH23 : (period_raw_spec < 4294967296)) (PreH24 : (0 <= entries_raw_spec)) (PreH25 : (entries_raw_spec < 65536)) (PreH26 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH27 : (ptmr_pre = p_raw_spec)) (PreH28 : (type_pre = kind_raw_spec)) (PreH29 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH30 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  TT && emp 
).

Definition OSTmr_Link_entail_wit_3_2 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) = ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |-> (( &( "OSTmrWheelTbl" ) ) + (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) * sizeof( "os_tmr_wheel" ))))
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) )) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec = 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (delay_raw_spec = 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  TT && emp 
).

Definition OSTmr_Link_entail_wit_3_3 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) = ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |-> (( &( "OSTmrWheelTbl" ) ) + (((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) * sizeof( "os_tmr_wheel" ))))
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) )) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec <> 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH3 : (time_raw_spec <= UINT_MAX)) (PreH4 : (period_raw_spec <= UINT_MAX)) (PreH5 : (delay_raw_spec <= UINT_MAX)) (PreH6 : (time_raw_spec >= 0)) (PreH7 : (period_raw_spec >= 0)) (PreH8 : (delay_raw_spec >= 0)) (PreH9 : (delay_raw_spec <> 0)) (PreH10 : (kind_raw_spec <> 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  TT && emp 
|--
  TT && emp 
).

Definition OSTmr_Link_return_wit_1 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec <> 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Link_return_wit_1_split_goal_spatial := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_return_wit_2 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec = 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Link_return_wit_2_split_goal_spatial := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_return_wit_3 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (kind_raw_spec = 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Link_return_wit_3_split_goal_spatial := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> 1)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_return_wit_4 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Link_return_wit_4_split_goal_spatial := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec <> 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_return_wit_5 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Link_return_wit_5_split_goal_spatial := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (delay_raw_spec = 0)) (PreH11 : (kind_raw_spec <> 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_return_wit_6 := 
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Link_return_wit_6_split_goal_spatial := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH4 : (time_raw_spec <= UINT_MAX)) (PreH5 : (period_raw_spec <= UINT_MAX)) (PreH6 : (delay_raw_spec <= UINT_MAX)) (PreH7 : (time_raw_spec >= 0)) (PreH8 : (period_raw_spec >= 0)) (PreH9 : (delay_raw_spec >= 0)) (PreH10 : (kind_raw_spec = 1)) (PreH11 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH12 : (tmr_link_wheel_size )) (PreH13 : (0 < p_raw_spec)) (PreH14 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH15 : (0 < base_raw_spec)) (PreH16 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH17 : (0 <= kind_raw_spec)) (PreH18 : (kind_raw_spec < 256)) (PreH19 : (0 <= time_raw_spec)) (PreH20 : (time_raw_spec < 4294967296)) (PreH21 : (0 <= delay_raw_spec)) (PreH22 : (delay_raw_spec < 4294967296)) (PreH23 : (0 <= period_raw_spec)) (PreH24 : (period_raw_spec < 4294967296)) (PreH25 : (0 <= entries_raw_spec)) (PreH26 : (entries_raw_spec < 65536)) (PreH27 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH28 : (ptmr_pre = p_raw_spec)) (PreH29 : (type_pre = kind_raw_spec)) (PreH30 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH31 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> first_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> p_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec + 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_partial_solve_wit_1_pure := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (ptmr_pre = p_raw_spec)) (PreH2 : (type_pre = kind_raw_spec)) (PreH3 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH4 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "type" ) )) # UChar  |-> type_pre)
  **  (tmr_link_raw_pre p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
.

Definition OSTmr_Link_partial_solve_wit_1_aux := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (ptmr_pre = p_raw_spec)) (PreH2 : (type_pre = kind_raw_spec)) (PreH3 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH4 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "type" ) )) # UChar  |-> type_pre)
  **  (tmr_link_raw_pre p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  (tmr_link_raw_pre p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Link_partial_solve_wit_1 := OSTmr_Link_partial_solve_wit_1_pure -> OSTmr_Link_partial_solve_wit_1_aux.

Definition OSTmr_Link_partial_solve_wit_2_pure := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (kind_raw_spec = 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (first_raw_spec <> 0) ”
.

Definition OSTmr_Link_partial_solve_wit_2_aux := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (kind_raw_spec = 1)) (PreH12 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH13 : (tmr_link_wheel_size )) (PreH14 : (0 < p_raw_spec)) (PreH15 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH16 : (0 < base_raw_spec)) (PreH17 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH18 : (0 <= kind_raw_spec)) (PreH19 : (kind_raw_spec < 256)) (PreH20 : (0 <= time_raw_spec)) (PreH21 : (time_raw_spec < 4294967296)) (PreH22 : (0 <= delay_raw_spec)) (PreH23 : (delay_raw_spec < 4294967296)) (PreH24 : (0 <= period_raw_spec)) (PreH25 : (period_raw_spec < 4294967296)) (PreH26 : (0 <= entries_raw_spec)) (PreH27 : (entries_raw_spec < 65536)) (PreH28 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH29 : (ptmr_pre = p_raw_spec)) (PreH30 : (type_pre = kind_raw_spec)) (PreH31 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH32 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  “ (first_raw_spec <> 0) ” 
  &&  “ (first_raw_spec <> 0) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (kind_raw_spec = 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  (tmr_link_neighbor_pre first_raw_spec )
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
.

Definition OSTmr_Link_partial_solve_wit_2 := OSTmr_Link_partial_solve_wit_2_pure -> OSTmr_Link_partial_solve_wit_2_aux.

Definition OSTmr_Link_partial_solve_wit_3_pure := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec = 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (first_raw_spec <> 0) ”
.

Definition OSTmr_Link_partial_solve_wit_3_aux := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec = 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  “ (first_raw_spec <> 0) ” 
  &&  “ (first_raw_spec <> 0) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec = 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  (tmr_link_neighbor_pre first_raw_spec )
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
.

Definition OSTmr_Link_partial_solve_wit_3 := OSTmr_Link_partial_solve_wit_3_pure -> OSTmr_Link_partial_solve_wit_3_aux.

Definition OSTmr_Link_partial_solve_wit_4_pure := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec <> 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((( &( "type" ) )) # UChar  |-> kind_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (first_raw_spec <> 0) ”
.

Definition OSTmr_Link_partial_solve_wit_4_aux := 
forall (type_pre: Z) (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) (PreH2 : ((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ) = (base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))) (PreH3 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX)) (PreH4 : ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0)) (PreH5 : (time_raw_spec <= UINT_MAX)) (PreH6 : (period_raw_spec <= UINT_MAX)) (PreH7 : (delay_raw_spec <= UINT_MAX)) (PreH8 : (time_raw_spec >= 0)) (PreH9 : (period_raw_spec >= 0)) (PreH10 : (delay_raw_spec >= 0)) (PreH11 : (delay_raw_spec <> 0)) (PreH12 : (kind_raw_spec <> 1)) (PreH13 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) (PreH14 : (tmr_link_wheel_size )) (PreH15 : (0 < p_raw_spec)) (PreH16 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH17 : (0 < base_raw_spec)) (PreH18 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH19 : (0 <= kind_raw_spec)) (PreH20 : (kind_raw_spec < 256)) (PreH21 : (0 <= time_raw_spec)) (PreH22 : (time_raw_spec < 4294967296)) (PreH23 : (0 <= delay_raw_spec)) (PreH24 : (delay_raw_spec < 4294967296)) (PreH25 : (0 <= period_raw_spec)) (PreH26 : (period_raw_spec < 4294967296)) (PreH27 : (0 <= entries_raw_spec)) (PreH28 : (entries_raw_spec < 65536)) (PreH29 : (tmr_link_neighbor_bounds first_raw_spec )) (PreH30 : (ptmr_pre = p_raw_spec)) (PreH31 : (type_pre = kind_raw_spec)) (PreH32 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) (PreH33 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
|--
  “ (first_raw_spec <> 0) ” 
  &&  “ (first_raw_spec <> 0) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) <= UINT_MAX) ” 
  &&  “ ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) >= 0) ” 
  &&  “ (time_raw_spec <= UINT_MAX) ” 
  &&  “ (period_raw_spec <= UINT_MAX) ” 
  &&  “ (delay_raw_spec <= UINT_MAX) ” 
  &&  “ (time_raw_spec >= 0) ” 
  &&  “ (period_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec >= 0) ” 
  &&  “ (delay_raw_spec <> 0) ” 
  &&  “ (kind_raw_spec <> 1) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  (tmr_link_neighbor_pre first_raw_spec )
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> (tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)))
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
.

Definition OSTmr_Link_partial_solve_wit_4 := OSTmr_Link_partial_solve_wit_4_pure -> OSTmr_Link_partial_solve_wit_4_aux.

Definition OSTmr_Link_which_implies_wit_1 := 
(
forall (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  (tmr_link_raw_pre p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ”
  &&  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |->_)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
) \/
(
forall (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (period_raw_spec: Z) (delay_raw_spec: Z) (time_raw_spec: Z) (kind_raw_spec: Z) (clock_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (( &( "OSTmrTime" ) ) = clock_raw_spec)) ,
  (tmr_link_raw_pre p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  EX (x_4: Z)  (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ” 
  &&  “ (tmr_link_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= kind_raw_spec) ” 
  &&  “ (kind_raw_spec < 256) ” 
  &&  “ (0 <= time_raw_spec) ” 
  &&  “ (time_raw_spec < 4294967296) ” 
  &&  “ (0 <= delay_raw_spec) ” 
  &&  “ (delay_raw_spec < 4294967296) ” 
  &&  “ (0 <= period_raw_spec) ” 
  &&  “ (period_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_link_neighbor_bounds first_raw_spec ) ”
  &&  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> x_4)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> x_3)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> x_2)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> x)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> delay_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_raw_spec)
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> time_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * ((tmr_link_match (kind_raw_spec) (delay_raw_spec) (period_raw_spec) (time_raw_spec)) % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_link_neighbor_pre first_raw_spec )
  **  (R_raw_spec )
).

Definition OSTmr_Link_which_implies_wit_2 := 
(
forall (first_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) ,
  (tmr_link_neighbor_pre first_raw_spec )
|--
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |->_)
) \/
(
forall (first_raw_spec: Z) (PreH1 : (first_raw_spec <> 0)) ,
  (tmr_link_neighbor_pre first_raw_spec )
|--
  EX (x: Z) ,
  ((&((first_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> x)
).

Definition OSTmr_Link_derive_configured_spec_by_raw_spec := 
forall (type_pre: Z) (ptmr_pre: Z) (R_configured_spec: Assertion) (kind_configured_spec: Z) (i_configured_spec: Z) (s_configured_spec: GlobTimerState) (sg_configured_spec: StableGlobVars) ,
  “ (tmr_link_layout ) ” 
  &&  “ (tmr_link_profile sg_configured_spec ) ” 
  &&  “ (timer_api_initialized s_configured_spec ) ” 
  &&  “ (tmr_link_eligible s_configured_spec i_configured_spec ) ” 
  &&  “ (ptmr_pre = (timer_pool_addr (sg_configured_spec) (i_configured_spec))) ” 
  &&  “ (type_pre = kind_configured_spec) ” 
  &&  “ (0 <= kind_configured_spec) ” 
  &&  “ (kind_configured_spec < 256) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg_configured_spec))) ” 
  &&  “ (( &( "OSTmrTime" ) ) = (g_OSTmrTime (sg_configured_spec))) ”
  &&  (timer_inv sg_configured_spec s_configured_spec )
  **  (R_configured_spec )
|--
EX (p_raw_spec: Z) (base_raw_spec: Z) (clock_raw_spec: Z) (kind_raw_spec: Z) (time_raw_spec: Z) (delay_raw_spec: Z) (period_raw_spec: Z) (first_raw_spec: Z) (entries_raw_spec: Z) (R_raw_spec: Assertion) ,
  (“ (ptmr_pre = p_raw_spec) ” 
  &&  “ (type_pre = kind_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ” 
  &&  “ (( &( "OSTmrTime" ) ) = clock_raw_spec) ”
  &&  (tmr_link_raw_pre p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec ))
  **
  (((tmr_link_raw_post p_raw_spec base_raw_spec clock_raw_spec kind_raw_spec time_raw_spec delay_raw_spec period_raw_spec first_raw_spec entries_raw_spec R_raw_spec ))
  -*
  ((tmr_link_configured_post sg_configured_spec s_configured_spec i_configured_spec kind_configured_spec )
  **  (R_configured_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSTmr_Link_safety_wit_1 : OSTmr_Link_safety_wit_1.
Axiom proof_of_OSTmr_Link_safety_wit_2 : OSTmr_Link_safety_wit_2.
Axiom proof_of_OSTmr_Link_safety_wit_3 : OSTmr_Link_safety_wit_3.
Axiom proof_of_OSTmr_Link_safety_wit_4 : OSTmr_Link_safety_wit_4.
Axiom proof_of_OSTmr_Link_safety_wit_5 : OSTmr_Link_safety_wit_5.
Axiom proof_of_OSTmr_Link_safety_wit_6 : OSTmr_Link_safety_wit_6.
Axiom proof_of_OSTmr_Link_safety_wit_7 : OSTmr_Link_safety_wit_7.
Axiom proof_of_OSTmr_Link_safety_wit_8 : OSTmr_Link_safety_wit_8.
Axiom proof_of_OSTmr_Link_safety_wit_9 : OSTmr_Link_safety_wit_9.
Axiom proof_of_OSTmr_Link_safety_wit_10 : OSTmr_Link_safety_wit_10.
Axiom proof_of_OSTmr_Link_safety_wit_11 : OSTmr_Link_safety_wit_11.
Axiom proof_of_OSTmr_Link_safety_wit_12 : OSTmr_Link_safety_wit_12.
Axiom proof_of_OSTmr_Link_safety_wit_13 : OSTmr_Link_safety_wit_13.
Axiom proof_of_OSTmr_Link_safety_wit_14 : OSTmr_Link_safety_wit_14.
Axiom proof_of_OSTmr_Link_safety_wit_15 : OSTmr_Link_safety_wit_15.
Axiom proof_of_OSTmr_Link_entail_wit_1_1 : OSTmr_Link_entail_wit_1_1.
Axiom proof_of_OSTmr_Link_entail_wit_1_2 : OSTmr_Link_entail_wit_1_2.
Axiom proof_of_OSTmr_Link_entail_wit_1_3 : OSTmr_Link_entail_wit_1_3.
Axiom proof_of_OSTmr_Link_entail_wit_2_1 : OSTmr_Link_entail_wit_2_1.
Axiom proof_of_OSTmr_Link_entail_wit_2_2 : OSTmr_Link_entail_wit_2_2.
Axiom proof_of_OSTmr_Link_entail_wit_2_3 : OSTmr_Link_entail_wit_2_3.
Axiom proof_of_OSTmr_Link_entail_wit_3_1 : OSTmr_Link_entail_wit_3_1.
Axiom proof_of_OSTmr_Link_entail_wit_3_2 : OSTmr_Link_entail_wit_3_2.
Axiom proof_of_OSTmr_Link_entail_wit_3_3 : OSTmr_Link_entail_wit_3_3.
Axiom proof_of_OSTmr_Link_return_wit_1 : OSTmr_Link_return_wit_1.
Axiom proof_of_OSTmr_Link_return_wit_2 : OSTmr_Link_return_wit_2.
Axiom proof_of_OSTmr_Link_return_wit_3 : OSTmr_Link_return_wit_3.
Axiom proof_of_OSTmr_Link_return_wit_4 : OSTmr_Link_return_wit_4.
Axiom proof_of_OSTmr_Link_return_wit_5 : OSTmr_Link_return_wit_5.
Axiom proof_of_OSTmr_Link_return_wit_6 : OSTmr_Link_return_wit_6.
Axiom proof_of_OSTmr_Link_partial_solve_wit_1_pure : OSTmr_Link_partial_solve_wit_1_pure.
Axiom proof_of_OSTmr_Link_partial_solve_wit_1 : OSTmr_Link_partial_solve_wit_1.
Axiom proof_of_OSTmr_Link_partial_solve_wit_2_pure : OSTmr_Link_partial_solve_wit_2_pure.
Axiom proof_of_OSTmr_Link_partial_solve_wit_2 : OSTmr_Link_partial_solve_wit_2.
Axiom proof_of_OSTmr_Link_partial_solve_wit_3_pure : OSTmr_Link_partial_solve_wit_3_pure.
Axiom proof_of_OSTmr_Link_partial_solve_wit_3 : OSTmr_Link_partial_solve_wit_3.
Axiom proof_of_OSTmr_Link_partial_solve_wit_4_pure : OSTmr_Link_partial_solve_wit_4_pure.
Axiom proof_of_OSTmr_Link_partial_solve_wit_4 : OSTmr_Link_partial_solve_wit_4.
Axiom proof_of_OSTmr_Link_which_implies_wit_1 : OSTmr_Link_which_implies_wit_1.
Axiom proof_of_OSTmr_Link_which_implies_wit_2 : OSTmr_Link_which_implies_wit_2.
Axiom proof_of_OSTmr_Link_derive_configured_spec_by_raw_spec : OSTmr_Link_derive_configured_spec_by_raw_spec.

End VC_Correct.
