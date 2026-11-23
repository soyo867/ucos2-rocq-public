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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmr_Unlink -----*)

Definition OSTmr_Unlink_safety_wit_1 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (tmr_unlink_wheel_size )) (PreH2 : (0 < p_raw_spec)) (PreH3 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH4 : (0 < base_raw_spec)) (PreH5 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH6 : (0 <= match_time_raw_spec)) (PreH7 : (match_time_raw_spec < 4294967296)) (PreH8 : (0 <= entries_raw_spec)) (PreH9 : (entries_raw_spec < 65536)) (PreH10 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH11 : (ptmr_pre = p_raw_spec)) (PreH12 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |->_)
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (7 <> 0) ”
.

Definition OSTmr_Unlink_safety_wit_2 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (first_raw_spec = p_raw_spec)) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_3 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (first_raw_spec = p_raw_spec)) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_4 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ False ”
.

Definition OSTmr_Unlink_safety_wit_5 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ False ”
.

Definition OSTmr_Unlink_safety_wit_6 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_7 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (first_raw_spec <> p_raw_spec)) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_8 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (first_raw_spec <> p_raw_spec)) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_9 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ False ”
.

Definition OSTmr_Unlink_safety_wit_10 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ False ”
.

Definition OSTmr_Unlink_safety_wit_11 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_12 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_13 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_14 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_15 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_16 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> next_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_17 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_safety_wit_18 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |-> next_raw_spec)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> prev_raw_spec)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Unlink_entail_wit_1 := 
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (tmr_unlink_wheel_size )) (PreH2 : (0 < p_raw_spec)) (PreH3 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH4 : (0 < base_raw_spec)) (PreH5 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH6 : (0 <= match_time_raw_spec)) (PreH7 : (match_time_raw_spec < 4294967296)) (PreH8 : (0 <= entries_raw_spec)) (PreH9 : (entries_raw_spec < 65536)) (PreH10 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH11 : (ptmr_pre = p_raw_spec)) (PreH12 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "spoke" ) )) # UShort  |-> (unsigned_last_nbits ((match_time_raw_spec % ( 7 ) )) (16)))
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((match_time_raw_spec % ( 7 ) ) = (match_time_raw_spec % ( 7 ) )) ” 
  &&  “ (match_time_raw_spec <= UINT_MAX) ” 
  &&  “ (match_time_raw_spec >= 0) ” 
  &&  “ (tmr_unlink_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= match_time_raw_spec) ” 
  &&  “ (match_time_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ”
  &&  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (match_time_raw_spec <= UINT_MAX)) (PreH2 : (match_time_raw_spec >= 0)) (PreH3 : (tmr_unlink_wheel_size )) (PreH4 : (0 < p_raw_spec)) (PreH5 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH6 : (0 < base_raw_spec)) (PreH7 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH8 : (0 <= match_time_raw_spec)) (PreH9 : (match_time_raw_spec < 4294967296)) (PreH10 : (0 <= entries_raw_spec)) (PreH11 : (entries_raw_spec < 65536)) (PreH12 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH13 : (ptmr_pre = p_raw_spec)) (PreH14 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((match_time_raw_spec % ( 7 ) )) (16)) = (match_time_raw_spec % ( 7 ) )) ”
  &&  emp
).

Definition OSTmr_Unlink_entail_wit_1_split_goal_1 := 
forall (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (match_time_raw_spec <= UINT_MAX)) (PreH2 : (match_time_raw_spec >= 0)) (PreH3 : (tmr_unlink_wheel_size )) (PreH4 : (0 < p_raw_spec)) (PreH5 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH6 : (0 < base_raw_spec)) (PreH7 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH8 : (0 <= match_time_raw_spec)) (PreH9 : (match_time_raw_spec < 4294967296)) (PreH10 : (0 <= entries_raw_spec)) (PreH11 : (entries_raw_spec < 65536)) (PreH12 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH13 : (ptmr_pre = p_raw_spec)) (PreH14 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((unsigned_last_nbits ((match_time_raw_spec % ( 7 ) )) (16)) = (match_time_raw_spec % ( 7 ) ))
.

Definition OSTmr_Unlink_entail_wit_2 := 
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : ((match_time_raw_spec % ( 7 ) ) = (match_time_raw_spec % ( 7 ) ))) (PreH2 : (match_time_raw_spec <= UINT_MAX)) (PreH3 : (match_time_raw_spec >= 0)) (PreH4 : (tmr_unlink_wheel_size )) (PreH5 : (0 < p_raw_spec)) (PreH6 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH7 : (0 < base_raw_spec)) (PreH8 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH9 : (0 <= match_time_raw_spec)) (PreH10 : (match_time_raw_spec < 4294967296)) (PreH11 : (0 <= entries_raw_spec)) (PreH12 : (entries_raw_spec < 65536)) (PreH13 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH14 : (ptmr_pre = p_raw_spec)) (PreH15 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "pspoke" ) )) # Ptr  |-> (( &( "OSTmrWheelTbl" ) ) + ((match_time_raw_spec % ( 7 ) ) * sizeof( "os_tmr_wheel" ))))
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ ((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ) = (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) )) ” 
  &&  “ (match_time_raw_spec <= UINT_MAX) ” 
  &&  “ (match_time_raw_spec >= 0) ” 
  &&  “ (tmr_unlink_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= match_time_raw_spec) ” 
  &&  “ (match_time_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ”
  &&  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
) \/
(
forall (ptmr_pre: Z) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (match_time_raw_spec <= UINT_MAX)) (PreH2 : (match_time_raw_spec >= 0)) (PreH3 : (tmr_unlink_wheel_size )) (PreH4 : (0 < p_raw_spec)) (PreH5 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH6 : (0 < base_raw_spec)) (PreH7 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH8 : (0 <= match_time_raw_spec)) (PreH9 : (match_time_raw_spec < 4294967296)) (PreH10 : (0 <= entries_raw_spec)) (PreH11 : (entries_raw_spec < 65536)) (PreH12 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH13 : (ptmr_pre = p_raw_spec)) (PreH14 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  TT && emp 
|--
  TT && emp 
).

Definition OSTmr_Unlink_return_wit_1 := 
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Unlink_return_wit_1_split_goal_spatial := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Unlink_return_wit_2 := 
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Unlink_return_wit_2_split_goal_spatial := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec = p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> next_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Unlink_return_wit_3 := 
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Unlink_return_wit_3_split_goal_spatial := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec <> 0)) (PreH2 : (next_raw_spec <> 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Unlink_return_wit_4 := 
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
) \/
(
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
).

Definition OSTmr_Unlink_return_wit_4_split_goal_spatial := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (next_raw_spec = 0)) (PreH2 : (next_raw_spec = 0)) (PreH3 : (first_raw_spec <> p_raw_spec)) (PreH4 : (match_time_raw_spec <= UINT_MAX)) (PreH5 : (match_time_raw_spec >= 0)) (PreH6 : (tmr_unlink_wheel_size )) (PreH7 : (0 < p_raw_spec)) (PreH8 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH9 : (0 < base_raw_spec)) (PreH10 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH11 : (0 <= match_time_raw_spec)) (PreH12 : (match_time_raw_spec < 4294967296)) (PreH13 : (0 <= entries_raw_spec)) (PreH14 : (entries_raw_spec < 65536)) (PreH15 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH16 : (ptmr_pre = p_raw_spec)) (PreH17 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> 0)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> (unsigned_last_nbits ((entries_raw_spec - 1 )) (16)))
  **  (R_raw_spec )
|--
  (tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Unlink_partial_solve_wit_1 := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (ptmr_pre = p_raw_spec)) (PreH2 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (tmr_unlink_raw_pre p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  (tmr_unlink_raw_pre p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
.

Definition OSTmr_Unlink_partial_solve_wit_2_pure := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = p_raw_spec)) (PreH2 : ((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ) = (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (first_raw_spec = p_raw_spec) ”
.

Definition OSTmr_Unlink_partial_solve_wit_2_aux := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = p_raw_spec)) (PreH2 : ((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ) = (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
|--
  “ (first_raw_spec = p_raw_spec) ” 
  &&  “ (first_raw_spec = p_raw_spec) ” 
  &&  “ (match_time_raw_spec <= UINT_MAX) ” 
  &&  “ (match_time_raw_spec >= 0) ” 
  &&  “ (tmr_unlink_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= match_time_raw_spec) ” 
  &&  “ (match_time_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ”
  &&  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
.

Definition OSTmr_Unlink_partial_solve_wit_2 := OSTmr_Unlink_partial_solve_wit_2_pure -> OSTmr_Unlink_partial_solve_wit_2_aux.

Definition OSTmr_Unlink_partial_solve_wit_3_pure := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> p_raw_spec)) (PreH2 : ((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ) = (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((( &( "pspoke" ) )) # Ptr  |-> (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))
  **  ((( &( "spoke" ) )) # UShort  |-> (match_time_raw_spec % ( 7 ) ))
  **  ((( &( "ptmr" ) )) # Ptr  |-> p_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
|--
  “ (first_raw_spec <> p_raw_spec) ”
.

Definition OSTmr_Unlink_partial_solve_wit_3_aux := 
forall (ptmr_pre: Z) (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> p_raw_spec)) (PreH2 : ((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ) = (base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))) (PreH3 : (match_time_raw_spec <= UINT_MAX)) (PreH4 : (match_time_raw_spec >= 0)) (PreH5 : (tmr_unlink_wheel_size )) (PreH6 : (0 < p_raw_spec)) (PreH7 : ((p_raw_spec + 40 ) <= 4294967296)) (PreH8 : (0 < base_raw_spec)) (PreH9 : ((base_raw_spec + 56 ) <= 4294967296)) (PreH10 : (0 <= match_time_raw_spec)) (PreH11 : (match_time_raw_spec < 4294967296)) (PreH12 : (0 <= entries_raw_spec)) (PreH13 : (entries_raw_spec < 65536)) (PreH14 : (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )) (PreH15 : (ptmr_pre = p_raw_spec)) (PreH16 : (( &( "OSTmrWheelTbl" ) ) = base_raw_spec)) ,
  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
|--
  “ (first_raw_spec <> p_raw_spec) ” 
  &&  “ (first_raw_spec <> p_raw_spec) ” 
  &&  “ (match_time_raw_spec <= UINT_MAX) ” 
  &&  “ (match_time_raw_spec >= 0) ” 
  &&  “ (tmr_unlink_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= match_time_raw_spec) ” 
  &&  “ (match_time_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec ) ” 
  &&  “ (ptmr_pre = p_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ”
  &&  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (R_raw_spec )
.

Definition OSTmr_Unlink_partial_solve_wit_3 := OSTmr_Unlink_partial_solve_wit_3_pure -> OSTmr_Unlink_partial_solve_wit_3_aux.

Definition OSTmr_Unlink_which_implies_wit_1 := 
(
forall (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) ,
  (tmr_unlink_raw_pre p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  “ (tmr_unlink_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= match_time_raw_spec) ” 
  &&  “ (match_time_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec ) ”
  &&  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |->_)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
) \/
(
forall (R_raw_spec: Assertion) (entries_raw_spec: Z) (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (match_time_raw_spec: Z) (base_raw_spec: Z) (p_raw_spec: Z) ,
  (tmr_unlink_raw_pre p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec )
|--
  EX (x: Z) ,
  “ (tmr_unlink_wheel_size ) ” 
  &&  “ (0 < p_raw_spec) ” 
  &&  “ ((p_raw_spec + 40 ) <= 4294967296) ” 
  &&  “ (0 < base_raw_spec) ” 
  &&  “ ((base_raw_spec + 56 ) <= 4294967296) ” 
  &&  “ (0 <= match_time_raw_spec) ” 
  &&  “ (match_time_raw_spec < 4294967296) ” 
  &&  “ (0 <= entries_raw_spec) ” 
  &&  “ (entries_raw_spec < 65536) ” 
  &&  “ (tmr_unlink_neighbor_bounds p_raw_spec next_raw_spec prev_raw_spec first_raw_spec ) ”
  &&  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> x)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrMatch")) # UInt  |-> match_time_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> next_raw_spec)
  **  ((&((p_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> prev_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrFirst")) # Ptr  |-> first_raw_spec)
  **  ((&(((base_raw_spec + (8 * (match_time_raw_spec % ( 7 ) ) ) ))  # "os_tmr_wheel" ->ₛ "OSTmrEntries")) # UShort  |-> entries_raw_spec)
  **  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
  **  (R_raw_spec )
).

Definition OSTmr_Unlink_which_implies_wit_2 := 
forall (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec = p_raw_spec)) ,
  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
|--
  (“ (next_raw_spec = 0) ”
  &&  emp)
  ||
  (“ (next_raw_spec <> 0) ”
  &&  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec))
.

Definition OSTmr_Unlink_which_implies_wit_3 := 
forall (first_raw_spec: Z) (prev_raw_spec: Z) (next_raw_spec: Z) (p_raw_spec: Z) (PreH1 : (first_raw_spec <> p_raw_spec)) ,
  (tmr_unlink_neighbor_pre p_raw_spec next_raw_spec prev_raw_spec first_raw_spec )
|--
  (“ (next_raw_spec <> 0) ”
  &&  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> p_raw_spec)
  **  ((&((next_raw_spec)  # "os_tmr" ->ₛ "OSTmrPrev")) # Ptr  |-> p_raw_spec))
  ||
  (“ (next_raw_spec = 0) ”
  &&  ((&((prev_raw_spec)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> p_raw_spec))
.

Definition OSTmr_Unlink_derive_configured_spec_by_raw_spec := 
forall (ptmr_pre: Z) (R_configured_spec: Assertion) (i_configured_spec: Z) (s_configured_spec: GlobTimerState) (sg_configured_spec: StableGlobVars) ,
  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg_configured_spec ) ” 
  &&  “ (timer_api_initialized s_configured_spec ) ” 
  &&  “ (tmr_unlink_running s_configured_spec i_configured_spec ) ” 
  &&  “ (ptmr_pre = (timer_pool_addr (sg_configured_spec) (i_configured_spec))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg_configured_spec))) ”
  &&  (timer_inv sg_configured_spec s_configured_spec )
  **  (R_configured_spec )
|--
EX (p_raw_spec: Z) (base_raw_spec: Z) (match_time_raw_spec: Z) (next_raw_spec: Z) (prev_raw_spec: Z) (first_raw_spec: Z) (entries_raw_spec: Z) (R_raw_spec: Assertion) ,
  (“ (ptmr_pre = p_raw_spec) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = base_raw_spec) ”
  &&  (tmr_unlink_raw_pre p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec ))
  **
  (((tmr_unlink_raw_post p_raw_spec base_raw_spec match_time_raw_spec next_raw_spec prev_raw_spec first_raw_spec entries_raw_spec R_raw_spec ))
  -*
  ((tmr_unlink_configured_post sg_configured_spec s_configured_spec i_configured_spec )
  **  (R_configured_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSTmr_Unlink_safety_wit_1 : OSTmr_Unlink_safety_wit_1.
Axiom proof_of_OSTmr_Unlink_safety_wit_2 : OSTmr_Unlink_safety_wit_2.
Axiom proof_of_OSTmr_Unlink_safety_wit_3 : OSTmr_Unlink_safety_wit_3.
Axiom proof_of_OSTmr_Unlink_safety_wit_4 : OSTmr_Unlink_safety_wit_4.
Axiom proof_of_OSTmr_Unlink_safety_wit_5 : OSTmr_Unlink_safety_wit_5.
Axiom proof_of_OSTmr_Unlink_safety_wit_6 : OSTmr_Unlink_safety_wit_6.
Axiom proof_of_OSTmr_Unlink_safety_wit_7 : OSTmr_Unlink_safety_wit_7.
Axiom proof_of_OSTmr_Unlink_safety_wit_8 : OSTmr_Unlink_safety_wit_8.
Axiom proof_of_OSTmr_Unlink_safety_wit_9 : OSTmr_Unlink_safety_wit_9.
Axiom proof_of_OSTmr_Unlink_safety_wit_10 : OSTmr_Unlink_safety_wit_10.
Axiom proof_of_OSTmr_Unlink_safety_wit_11 : OSTmr_Unlink_safety_wit_11.
Axiom proof_of_OSTmr_Unlink_safety_wit_12 : OSTmr_Unlink_safety_wit_12.
Axiom proof_of_OSTmr_Unlink_safety_wit_13 : OSTmr_Unlink_safety_wit_13.
Axiom proof_of_OSTmr_Unlink_safety_wit_14 : OSTmr_Unlink_safety_wit_14.
Axiom proof_of_OSTmr_Unlink_safety_wit_15 : OSTmr_Unlink_safety_wit_15.
Axiom proof_of_OSTmr_Unlink_safety_wit_16 : OSTmr_Unlink_safety_wit_16.
Axiom proof_of_OSTmr_Unlink_safety_wit_17 : OSTmr_Unlink_safety_wit_17.
Axiom proof_of_OSTmr_Unlink_safety_wit_18 : OSTmr_Unlink_safety_wit_18.
Axiom proof_of_OSTmr_Unlink_entail_wit_1 : OSTmr_Unlink_entail_wit_1.
Axiom proof_of_OSTmr_Unlink_entail_wit_2 : OSTmr_Unlink_entail_wit_2.
Axiom proof_of_OSTmr_Unlink_return_wit_1 : OSTmr_Unlink_return_wit_1.
Axiom proof_of_OSTmr_Unlink_return_wit_2 : OSTmr_Unlink_return_wit_2.
Axiom proof_of_OSTmr_Unlink_return_wit_3 : OSTmr_Unlink_return_wit_3.
Axiom proof_of_OSTmr_Unlink_return_wit_4 : OSTmr_Unlink_return_wit_4.
Axiom proof_of_OSTmr_Unlink_partial_solve_wit_1 : OSTmr_Unlink_partial_solve_wit_1.
Axiom proof_of_OSTmr_Unlink_partial_solve_wit_2_pure : OSTmr_Unlink_partial_solve_wit_2_pure.
Axiom proof_of_OSTmr_Unlink_partial_solve_wit_2 : OSTmr_Unlink_partial_solve_wit_2.
Axiom proof_of_OSTmr_Unlink_partial_solve_wit_3_pure : OSTmr_Unlink_partial_solve_wit_3_pure.
Axiom proof_of_OSTmr_Unlink_partial_solve_wit_3 : OSTmr_Unlink_partial_solve_wit_3.
Axiom proof_of_OSTmr_Unlink_which_implies_wit_1 : OSTmr_Unlink_which_implies_wit_1.
Axiom proof_of_OSTmr_Unlink_which_implies_wit_2 : OSTmr_Unlink_which_implies_wit_2.
Axiom proof_of_OSTmr_Unlink_which_implies_wit_3 : OSTmr_Unlink_which_implies_wit_3.
Axiom proof_of_OSTmr_Unlink_derive_configured_spec_by_raw_spec : OSTmr_Unlink_derive_configured_spec_by_raw_spec.

End VC_Correct.
