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
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_EventTaskRemove -----*)

Definition OS_EventTaskRemove_safety_wit_1 := 
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.land group_value (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "y" ) )) # UChar  |-> row)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_EventTaskRemove_safety_wit_2 := 
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group_value)
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "y" ) )) # UChar  |-> row)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_EventTaskRemove_return_wit_1 := 
(
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.land group_value (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
|--
  (event_task_remove_post ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
) \/
(
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.land group_value (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
|--
  (event_task_remove_post ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
).

Definition OS_EventTaskRemove_return_wit_1_split_goal_spatial := 
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.land group_value (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
|--
  (event_task_remove_post ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
.

Definition OS_EventTaskRemove_return_wit_2 := 
(
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group_value)
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
|--
  (event_task_remove_post ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
) \/
(
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group_value)
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
|--
  (event_task_remove_post ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
).

Definition OS_EventTaskRemove_return_wit_2_split_goal_spatial := 
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (PreH1 : ((Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= row)) (PreH3 : (row < 8)) ,
  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group_value)
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land row_value (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
|--
  (event_task_remove_post ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
.

Definition OS_EventTaskRemove_partial_solve_wit_1 := 
forall (pevent_pre: Z) (ptcb_pre: Z) (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) ,
  (event_task_remove_pre ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
|--
  (event_task_remove_pre ptcb_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
.

Definition OS_EventTaskRemove_which_implies_wit_1 := 
(
forall (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_pre ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
|--
  “ (0 <= row) ” 
  &&  “ (row < 8) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |->_)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group_value)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> row_value)
) \/
(
forall (group_value: Z) (row_value: Z) (bit_y: Z) (bit_x: Z) (row: Z) (pevent: Z) (ptcb: Z) ,
  (event_task_remove_pre ptcb &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") row bit_x bit_y row_value group_value )
|--
  EX (x: Z) ,
  “ (0 <= row) ” 
  &&  “ (row < 8) ”
  &&  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> x)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((ptcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> group_value)
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> row_value)
).

Module Type VC_Correct.


Axiom proof_of_OS_EventTaskRemove_safety_wit_1 : OS_EventTaskRemove_safety_wit_1.
Axiom proof_of_OS_EventTaskRemove_safety_wit_2 : OS_EventTaskRemove_safety_wit_2.
Axiom proof_of_OS_EventTaskRemove_return_wit_1 : OS_EventTaskRemove_return_wit_1.
Axiom proof_of_OS_EventTaskRemove_return_wit_2 : OS_EventTaskRemove_return_wit_2.
Axiom proof_of_OS_EventTaskRemove_partial_solve_wit_1 : OS_EventTaskRemove_partial_solve_wit_1.
Axiom proof_of_OS_EventTaskRemove_which_implies_wit_1 : OS_EventTaskRemove_which_implies_wit_1.

End VC_Correct.
