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
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_EventTaskWait -----*)

Definition OS_EventTaskWait_return_wit_1 := 
(
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= event_row)) (PreH3 : (event_row < 256)) (PreH4 : (0 <= event_group)) (PreH5 : (event_group < 256)) (PreH6 : (0 <= row)) (PreH7 : (row < 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.lor event_row (unsigned_last_nbits (bit_x) (8))))
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor event_group (unsigned_last_nbits (bit_y) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> pevent_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land ready_group (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (frame )
|--
  (event_task_wait_post ( &( "OSTCBCur" ) ) tcb pevent_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) row bit_x bit_y event_row event_group ready_row ready_group )
  **  (frame )
) \/
(
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= event_row)) (PreH3 : (event_row < 256)) (PreH4 : (0 <= event_group)) (PreH5 : (event_group < 256)) (PreH6 : (0 <= row)) (PreH7 : (row < 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.lor event_row (unsigned_last_nbits (bit_x) (8))))
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor event_group (unsigned_last_nbits (bit_y) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> pevent_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land ready_group (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (frame )
|--
  (event_task_wait_post ( &( "OSTCBCur" ) ) tcb pevent_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) row bit_x bit_y event_row event_group ready_row ready_group )
  **  (frame )
).

Definition OS_EventTaskWait_return_wit_1_split_goal_spatial := 
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))) = 0)) (PreH2 : (0 <= event_row)) (PreH3 : (event_row < 256)) (PreH4 : (0 <= event_group)) (PreH5 : (event_group < 256)) (PreH6 : (0 <= row)) (PreH7 : (row < 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.lor event_row (unsigned_last_nbits (bit_x) (8))))
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor event_group (unsigned_last_nbits (bit_y) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> pevent_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land ready_group (unsigned_last_nbits ((Z.lnot bit_y)) (8))))
  **  (frame )
|--
  (event_task_wait_post ( &( "OSTCBCur" ) ) tcb pevent_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) row bit_x bit_y event_row event_group ready_row ready_group )
  **  (frame )
.

Definition OS_EventTaskWait_return_wit_2 := 
(
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= event_row)) (PreH3 : (event_row < 256)) (PreH4 : (0 <= event_group)) (PreH5 : (event_group < 256)) (PreH6 : (0 <= row)) (PreH7 : (row < 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.lor event_row (unsigned_last_nbits (bit_x) (8))))
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor event_group (unsigned_last_nbits (bit_y) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> pevent_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_group)
  **  (frame )
|--
  (event_task_wait_post ( &( "OSTCBCur" ) ) tcb pevent_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) row bit_x bit_y event_row event_group ready_row ready_group )
  **  (frame )
) \/
(
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= event_row)) (PreH3 : (event_row < 256)) (PreH4 : (0 <= event_group)) (PreH5 : (event_group < 256)) (PreH6 : (0 <= row)) (PreH7 : (row < 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.lor event_row (unsigned_last_nbits (bit_x) (8))))
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor event_group (unsigned_last_nbits (bit_y) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> pevent_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_group)
  **  (frame )
|--
  (event_task_wait_post ( &( "OSTCBCur" ) ) tcb pevent_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) row bit_x bit_y event_row event_group ready_row ready_group )
  **  (frame )
).

Definition OS_EventTaskWait_return_wit_2_split_goal_spatial := 
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))) <> 0)) (PreH2 : (0 <= event_row)) (PreH3 : (event_row < 256)) (PreH4 : (0 <= event_group)) (PreH5 : (event_group < 256)) (PreH6 : (0 <= row)) (PreH7 : (row < 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> (Z.lor event_row (unsigned_last_nbits (bit_x) (8))))
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor event_group (unsigned_last_nbits (bit_y) (8))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> pevent_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot bit_x)) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_group)
  **  (frame )
|--
  (event_task_wait_post ( &( "OSTCBCur" ) ) tcb pevent_pre ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) row bit_x bit_y event_row event_group ready_row ready_group )
  **  (frame )
.

Definition OS_EventTaskWait_partial_solve_wit_1 := 
forall (pevent_pre: Z) (frame: Assertion) (ready_group: Z) (ready_row: Z) (event_group: Z) (event_row: Z) (old_event: Z) (bit_y: Z) (bit_x: Z) (row: Z) (tcb: Z) (PreH1 : (0 <= row)) (PreH2 : (row < 8)) ,
  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> old_event)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> event_row)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> event_group)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_group)
  **  (frame )
|--
  “ (0 <= row) ” 
  &&  “ (row < 8) ”
  &&  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> event_row)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> event_group)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventPtr")) # Ptr  |-> old_event)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> row)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> bit_x)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> bit_y)
  **  (((( &( "OSRdyTbl" ) ) + (row * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_group)
  **  (frame )
.

Definition OS_EventTaskWait_which_implies_wit_1 := 
(
forall (event_group: Z) (event_row: Z) (row: Z) (pevent: Z) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> event_row)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> event_group)
|--
  “ (0 <= event_row) ” 
  &&  “ (event_row < 256) ” 
  &&  “ (0 <= event_group) ” 
  &&  “ (event_group < 256) ”
  &&  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (row * sizeof(UCHAR)))) # UChar  |-> event_row)
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> event_group)
) \/
(
forall (event_group: Z) (event_row: Z) ,
  TT && emp 
|--
  “ (event_group < 256) ” 
  &&  “ (0 <= event_group) ” 
  &&  “ (event_row < 256) ” 
  &&  “ (0 <= event_row) ”
  &&  emp
).

Definition OS_EventTaskWait_which_implies_wit_1_split_goal_1 := 
forall (event_group: Z) ,
  (event_group < 256)
.

Definition OS_EventTaskWait_which_implies_wit_1_split_goal_2 := 
forall (event_group: Z) ,
  (0 <= event_group)
.

Definition OS_EventTaskWait_which_implies_wit_1_split_goal_3 := 
forall (event_row: Z) ,
  (event_row < 256)
.

Definition OS_EventTaskWait_which_implies_wit_1_split_goal_4 := 
forall (event_row: Z) ,
  (0 <= event_row)
.

Module Type VC_Correct.


Axiom proof_of_OS_EventTaskWait_return_wit_1 : OS_EventTaskWait_return_wit_1.
Axiom proof_of_OS_EventTaskWait_return_wit_2 : OS_EventTaskWait_return_wit_2.
Axiom proof_of_OS_EventTaskWait_partial_solve_wit_1 : OS_EventTaskWait_partial_solve_wit_1.
Axiom proof_of_OS_EventTaskWait_which_implies_wit_1 : OS_EventTaskWait_which_implies_wit_1.

End VC_Correct.
