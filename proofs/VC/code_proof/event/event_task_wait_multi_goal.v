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
Require Import Ucos2Verify.VC.code.event.spec.event_task_wait_multi_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_EventTaskWaitMulti -----*)

Definition OS_EventTaskWaitMulti_safety_wit_1 := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH4 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (pevents_wait_pre = base)) (PreH9 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_EventTaskWaitMulti_safety_wit_2 := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index )) (PreH2 : (event_task_wait_multi_value pevent pointers index )) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH8 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (event_task_wait_multi_cursor base base 0 )) (PreH11 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH12 : (event_multi_array_valid base pointers )) (PreH13 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH14 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH15 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH18 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH20 : (pevents_wait_pre = base)) (PreH21 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_EventTaskWaitMulti_entail_wit_1 := 
(
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (pevents_wait_pre = base)) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
) \/
(
forall (pevents_wait_pre: Z) (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (pevents_wait_pre = base)) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  TT && emp 
|--
  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ”
  &&  emp
).

Definition OS_EventTaskWaitMulti_entail_wit_1_split_goal_1 := 
forall (pevents_wait_pre: Z) (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (pevents_wait_pre = base)) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)
.

Definition OS_EventTaskWaitMulti_entail_wit_1_split_goal_2 := 
forall (pevents_wait_pre: Z) (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (pevents_wait_pre = base)) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))
.

Definition OS_EventTaskWaitMulti_entail_wit_2 := 
(
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (pevents_wait_pre = base)) (PreH7 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
) \/
(
forall (pevents_wait_pre: Z) (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (pevents_wait_pre = base)) (PreH7 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  TT && emp 
|--
  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ”
  &&  emp
).

Definition OS_EventTaskWaitMulti_entail_wit_2_split_goal_1 := 
forall (pevents_wait_pre: Z) (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (pevents_wait_pre = base)) (PreH7 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)
.

Definition OS_EventTaskWaitMulti_entail_wit_2_split_goal_2 := 
forall (pevents_wait_pre: Z) (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (pevents_wait_pre = base)) (PreH7 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))
.

Definition OS_EventTaskWaitMulti_entail_wit_3 := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((event_task_wait_multi_pointer (pointers) (0)) = (event_task_wait_multi_pointer (pointers) (0)))) (PreH2 : (event_task_wait_multi_cursor base base 0 )) (PreH3 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH4 : (event_multi_array_valid base pointers )) (PreH5 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH6 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH9 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH10 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH12 : (pevents_wait_pre = base)) (PreH13 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (index: Z) ,
  “ (event_task_wait_multi_cursor base base index ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_entail_wit_4 := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index_2: Z) (eid: Z) (e: OSEventAbstractState) (events_2: Glob_EventAbstractState) (index_3: Z) (next_2: Z) (next: Z) (after: Glob_EventAbstractState) (next_3: Z) (PreH1 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next_3 )) (PreH2 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (next)) pointers next_3 )) (PreH3 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next )) (PreH4 : (event_multi_array_valid base pointers )) (PreH5 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next_2 )) (PreH6 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_wait_multi_cursor pevents base index_3 )) (PreH8 : (event_task_wait_multi_value pevent pointers index_3 )) (PreH9 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH10 : (event_task_wait_multi_selected sg events_2 pointers instances index_3 eid e )) (PreH11 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH12 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH13 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH14 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH15 : (pevent <> 0)) (PreH16 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH17 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH18 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH19 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH21 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH24 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH25 : (event_task_wait_multi_cursor base base 0 )) (PreH26 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH27 : (event_multi_array_valid base pointers )) (PreH28 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH31 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH32 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH33 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH34 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH35 : (pevents_wait_pre = base)) (PreH36 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next_3 after )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (index: Z) ,
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base index ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (next)) pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_return_wit_1 := 
(
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))) = 0)) (PreH2 : (pevent = 0)) (PreH3 : (event_task_wait_multi_cursor pevents base index )) (PreH4 : (event_task_wait_multi_value pevent pointers index )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (event_task_wait_multi_cursor base base 0 )) (PreH13 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH14 : (event_multi_array_valid base pointers )) (PreH15 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH20 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH22 : (pevents_wait_pre = base)) (PreH23 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land ready_grp (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((t.(curPrio) ))))) (8))))
  **  (frame )
|--
  (event_task_wait_multi_post sg tasks entry tid t instances pointers ( &( "OSTCBCur" ) ) tcb base ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ready_row ready_grp )
  **  (frame )
) \/
(
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))) = 0)) (PreH2 : (pevent = 0)) (PreH3 : (event_task_wait_multi_cursor pevents base index )) (PreH4 : (event_task_wait_multi_value pevent pointers index )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (event_task_wait_multi_cursor base base 0 )) (PreH13 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH14 : (event_multi_array_valid base pointers )) (PreH15 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH20 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH22 : (pevents_wait_pre = base)) (PreH23 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land ready_grp (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((t.(curPrio) ))))) (8))))
  **  (frame )
|--
  (event_task_wait_multi_post sg tasks entry tid t instances pointers ( &( "OSTCBCur" ) ) tcb base ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ready_row ready_grp )
  **  (frame )
).

Definition OS_EventTaskWaitMulti_return_wit_1_split_goal_spatial := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))) = 0)) (PreH2 : (pevent = 0)) (PreH3 : (event_task_wait_multi_cursor pevents base index )) (PreH4 : (event_task_wait_multi_value pevent pointers index )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (event_task_wait_multi_cursor base base 0 )) (PreH13 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH14 : (event_multi_array_valid base pointers )) (PreH15 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH20 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH22 : (pevents_wait_pre = base)) (PreH23 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> (Z.land ready_grp (unsigned_last_nbits ((Z.lnot (tcb_bit_y_of_prio ((t.(curPrio) ))))) (8))))
  **  (frame )
|--
  (event_task_wait_multi_post sg tasks entry tid t instances pointers ( &( "OSTCBCur" ) ) tcb base ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ready_row ready_grp )
  **  (frame )
.

Definition OS_EventTaskWaitMulti_return_wit_2 := 
(
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))) <> 0)) (PreH2 : (pevent = 0)) (PreH3 : (event_task_wait_multi_cursor pevents base index )) (PreH4 : (event_task_wait_multi_value pevent pointers index )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (event_task_wait_multi_cursor base base 0 )) (PreH13 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH14 : (event_multi_array_valid base pointers )) (PreH15 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH20 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH22 : (pevents_wait_pre = base)) (PreH23 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  (event_task_wait_multi_post sg tasks entry tid t instances pointers ( &( "OSTCBCur" ) ) tcb base ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ready_row ready_grp )
  **  (frame )
) \/
(
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))) <> 0)) (PreH2 : (pevent = 0)) (PreH3 : (event_task_wait_multi_cursor pevents base index )) (PreH4 : (event_task_wait_multi_value pevent pointers index )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (event_task_wait_multi_cursor base base 0 )) (PreH13 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH14 : (event_multi_array_valid base pointers )) (PreH15 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH20 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH22 : (pevents_wait_pre = base)) (PreH23 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  (event_task_wait_multi_post sg tasks entry tid t instances pointers ( &( "OSTCBCur" ) ) tcb base ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ready_row ready_grp )
  **  (frame )
).

Definition OS_EventTaskWaitMulti_return_wit_2_split_goal_spatial := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : ((Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))) <> 0)) (PreH2 : (pevent = 0)) (PreH3 : (event_task_wait_multi_cursor pevents base index )) (PreH4 : (event_task_wait_multi_value pevent pointers index )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH10 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (event_task_wait_multi_cursor base base 0 )) (PreH13 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH14 : (event_multi_array_valid base pointers )) (PreH15 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH20 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH22 : (pevents_wait_pre = base)) (PreH23 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.land ready_row (unsigned_last_nbits ((Z.lnot (tcb_bit_x_of_prio ((t.(curPrio) ))))) (8))))
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  (event_task_wait_multi_post sg tasks entry tid t instances pointers ( &( "OSTCBCur" ) ) tcb base ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ready_row ready_grp )
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_1_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (pevents_wait_pre = base)) (PreH2 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_1_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (pevents_wait_pre = base)) (PreH2 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_raw_rep sg tasks entry )
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |->_)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_1 := OS_EventTaskWaitMulti_partial_solve_wit_1_pure -> OS_EventTaskWaitMulti_partial_solve_wit_1_aux.

Definition OS_EventTaskWaitMulti_partial_solve_wit_2 := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH4 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (pevents_wait_pre = base)) (PreH9 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "pevents" ) )) # Ptr  |-> pevents_wait_pre)
  **  (event_multi_array_rep base pointers )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  ((( &( "pevents" ) )) # Ptr  |-> base)
  **  (event_multi_array_rep base pointers )
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_3_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_multi_array_valid base pointers )) (PreH2 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH6 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH9 : (pevents_wait_pre = base)) (PreH10 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> base)
  **  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> pevents_wait_pre)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ ((event_task_wait_multi_pointer (pointers) (0)) = (event_task_wait_multi_pointer (pointers) (0))) ” 
  &&  “ (event_multi_array_valid base pointers ) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_3_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_multi_array_valid base pointers )) (PreH2 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH6 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH9 : (pevents_wait_pre = base)) (PreH10 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ ((event_task_wait_multi_pointer (pointers) (0)) = (event_task_wait_multi_pointer (pointers) (0))) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> pevents_wait_pre)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_3 := OS_EventTaskWaitMulti_partial_solve_wit_3_pure -> OS_EventTaskWaitMulti_partial_solve_wit_3_aux.

Definition OS_EventTaskWaitMulti_partial_solve_wit_4_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent <> 0)) (PreH2 : (event_task_wait_multi_cursor pevents base index )) (PreH3 : (event_task_wait_multi_value pevent pointers index )) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH6 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH9 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH10 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH11 : (event_task_wait_multi_cursor base base 0 )) (PreH12 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH13 : (event_multi_array_valid base pointers )) (PreH14 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH19 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH21 : (pevents_wait_pre = base)) (PreH22 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_4_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent <> 0)) (PreH2 : (event_task_wait_multi_cursor pevents base index )) (PreH3 : (event_task_wait_multi_value pevent pointers index )) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH6 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH9 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH10 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH11 : (event_task_wait_multi_cursor base base 0 )) (PreH12 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH13 : (event_multi_array_valid base pointers )) (PreH14 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH19 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH21 : (pevents_wait_pre = base)) (PreH22 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_4 := OS_EventTaskWaitMulti_partial_solve_wit_4_pure -> OS_EventTaskWaitMulti_partial_solve_wit_4_aux.

Definition OS_EventTaskWaitMulti_partial_solve_wit_5_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index_2: Z) (eid: Z) (e: OSEventAbstractState) (events: Glob_EventAbstractState) (index: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index )) (PreH2 : (event_task_wait_multi_value pevent pointers index )) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_wait_multi_selected sg events pointers instances index eid e )) (PreH5 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH6 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH7 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH8 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH9 : (pevent <> 0)) (PreH10 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH11 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH12 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH13 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH14 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH15 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_cursor base base 0 )) (PreH20 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH21 : (event_multi_array_valid base pointers )) (PreH22 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH24 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH25 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH26 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH27 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH28 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH29 : (pevents_wait_pre = base)) (PreH30 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (tcb_bit_x_of_prio ((t.(curPrio) )))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor (encode_event_wait_grp ((e.(waitList) )) (tasks)) (tcb_bit_y_of_prio ((t.(curPrio) )))))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index eid e ) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_5_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index_2: Z) (eid: Z) (e: OSEventAbstractState) (events: Glob_EventAbstractState) (index: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index )) (PreH2 : (event_task_wait_multi_value pevent pointers index )) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_wait_multi_selected sg events pointers instances index eid e )) (PreH5 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH6 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH7 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH8 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH9 : (pevent <> 0)) (PreH10 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH11 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH12 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH13 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH14 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH15 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (event_task_wait_multi_cursor base base 0 )) (PreH20 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH21 : (event_multi_array_valid base pointers )) (PreH22 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH24 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH25 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH26 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH27 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH28 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH29 : (pevents_wait_pre = base)) (PreH30 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (tcb_bit_x_of_prio ((t.(curPrio) )))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor (encode_event_wait_grp ((e.(waitList) )) (tasks)) (tcb_bit_y_of_prio ((t.(curPrio) )))))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index_2 ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index_2 ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (tcb_bit_x_of_prio ((t.(curPrio) )))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor (encode_event_wait_grp ((e.(waitList) )) (tasks)) (tcb_bit_y_of_prio ((t.(curPrio) )))))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_5 := OS_EventTaskWaitMulti_partial_solve_wit_5_pure -> OS_EventTaskWaitMulti_partial_solve_wit_5_aux.

Definition OS_EventTaskWaitMulti_partial_solve_wit_6_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (eid: Z) (e: OSEventAbstractState) (events: Glob_EventAbstractState) (index_2: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next )) (PreH2 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH3 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH4 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (event_task_wait_multi_selected sg events pointers instances index_2 eid e )) (PreH7 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH8 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH9 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH10 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH11 : (pevent <> 0)) (PreH12 : (event_task_wait_multi_cursor pevents base index )) (PreH13 : (event_task_wait_multi_value pevent pointers index )) (PreH14 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH15 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_wait_multi_cursor base base 0 )) (PreH22 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH23 : (event_multi_array_valid base pointers )) (PreH24 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH25 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH26 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH29 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH30 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH31 : (pevents_wait_pre = base)) (PreH32 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> (pevents + (1 * sizeof(PTR))))
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_6_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (eid: Z) (e: OSEventAbstractState) (events: Glob_EventAbstractState) (index_2: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next )) (PreH2 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH3 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH4 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH5 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (event_task_wait_multi_selected sg events pointers instances index_2 eid e )) (PreH7 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH8 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH9 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH10 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH11 : (pevent <> 0)) (PreH12 : (event_task_wait_multi_cursor pevents base index )) (PreH13 : (event_task_wait_multi_value pevent pointers index )) (PreH14 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH15 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH16 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH17 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_wait_multi_cursor base base 0 )) (PreH22 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH23 : (event_multi_array_valid base pointers )) (PreH24 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH25 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH26 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH29 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH30 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH31 : (pevents_wait_pre = base)) (PreH32 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index_2 ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index_2 ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index_2 eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_6 := OS_EventTaskWaitMulti_partial_solve_wit_6_pure -> OS_EventTaskWaitMulti_partial_solve_wit_6_aux.

Definition OS_EventTaskWaitMulti_partial_solve_wit_7_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (eid: Z) (e: OSEventAbstractState) (events: Glob_EventAbstractState) (index_2: Z) (next_2: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next )) (PreH2 : (event_multi_array_valid base pointers )) (PreH3 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next_2 )) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH6 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH7 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (event_task_wait_multi_selected sg events pointers instances index_2 eid e )) (PreH9 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH10 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH11 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH12 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH13 : (pevent <> 0)) (PreH14 : (event_task_wait_multi_cursor pevents base index )) (PreH15 : (event_task_wait_multi_value pevent pointers index )) (PreH16 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH17 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (event_task_wait_multi_cursor base base 0 )) (PreH24 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH25 : (event_multi_array_valid base pointers )) (PreH26 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH31 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH32 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH33 : (pevents_wait_pre = base)) (PreH34 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> (pevents + (1 * sizeof(PTR))))
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (((pevents + (1 * sizeof(PTR)))) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next)))
  **  (event_task_wait_multi_array_missing base pointers next )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next)))
  **  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ ((event_task_wait_multi_pointer (pointers) (next)) = (event_task_wait_multi_pointer (pointers) (next))) ” 
  &&  “ (event_multi_array_valid base pointers ) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_7_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (pevent: Z) (pevents: Z) (index: Z) (eid: Z) (e: OSEventAbstractState) (events: Glob_EventAbstractState) (index_2: Z) (next_2: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next )) (PreH2 : (event_multi_array_valid base pointers )) (PreH3 : (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next_2 )) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH6 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH7 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (event_task_wait_multi_selected sg events pointers instances index_2 eid e )) (PreH9 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH10 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH11 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH12 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH13 : (pevent <> 0)) (PreH14 : (event_task_wait_multi_cursor pevents base index )) (PreH15 : (event_task_wait_multi_value pevent pointers index )) (PreH16 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH17 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (event_task_wait_multi_cursor base base 0 )) (PreH24 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH25 : (event_multi_array_valid base pointers )) (PreH26 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH31 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH32 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH33 : (pevents_wait_pre = base)) (PreH34 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (((pevents + (1 * sizeof(PTR)))) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next)))
  **  (event_task_wait_multi_array_missing base pointers next )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ ((event_task_wait_multi_pointer (pointers) (next)) = (event_task_wait_multi_pointer (pointers) (next))) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next_2 ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index_2 ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index_2 ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index_2 eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (((pevents + (1 * sizeof(PTR)))) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next)))
  **  (event_task_wait_multi_array_missing base pointers next )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_7 := OS_EventTaskWaitMulti_partial_solve_wit_7_pure -> OS_EventTaskWaitMulti_partial_solve_wit_7_aux.

Definition OS_EventTaskWaitMulti_partial_solve_wit_8_pure := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_wait_multi_cursor pevents base index )) (PreH3 : (event_task_wait_multi_value pevent pointers index )) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH6 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH9 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH10 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH11 : (event_task_wait_multi_cursor base base 0 )) (PreH12 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH13 : (event_multi_array_valid base pointers )) (PreH14 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH19 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH21 : (pevents_wait_pre = base)) (PreH22 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents_wait" ) )) # Ptr  |-> base)
  **  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
  **  ((( &( "y" ) )) # UChar  |->_)
|--
  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (pevent <= 0) ” 
  &&  “ (0 <= pevent) ”
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_8_aux := 
forall (pevents_wait_pre: Z) (frame: Assertion) (ready_grp: Z) (ready_row: Z) (base: Z) (tcb: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_wait_multi_cursor pevents base index )) (PreH3 : (event_task_wait_multi_value pevent pointers index )) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH6 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH9 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH10 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH11 : (event_task_wait_multi_cursor base base 0 )) (PreH12 : (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 )) (PreH13 : (event_multi_array_valid base pointers )) (PreH14 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH19 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH21 : (pevents_wait_pre = base)) (PreH22 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
|--
  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (pevent <= 0) ” 
  &&  “ (0 <= pevent) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value (event_task_wait_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid base pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (pevents_wait_pre = base) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> tcb)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiPtr")) # Ptr  |-> base)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBEventMultiRdy")) # Ptr  |-> 0)
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((tcb)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (((( &( "OSRdyTbl" ) ) + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> ready_row)
  **  ((( &( "OSRdyGrp" ) )) # UChar  |-> ready_grp)
  **  (frame )
.

Definition OS_EventTaskWaitMulti_partial_solve_wit_8 := OS_EventTaskWaitMulti_partial_solve_wit_8_pure -> OS_EventTaskWaitMulti_partial_solve_wit_8_aux.

Definition OS_EventTaskWaitMulti_which_implies_wit_1 := 
(
forall (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
) \/
(
forall (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_1_split_goal_1 := 
forall (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ”
.

Definition OS_EventTaskWaitMulti_which_implies_wit_1_split_goal_2 := 
forall (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ”
.

Definition OS_EventTaskWaitMulti_which_implies_wit_1_split_goal_spatial := 
forall (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
.

Definition OS_EventTaskWaitMulti_which_implies_wit_2 := 
(
forall (base: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep base pointers )
|--
  “ (event_multi_array_valid base pointers ) ”
  &&  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
) \/
(
forall (base: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep base pointers )
|--
  “ (event_multi_array_valid base pointers ) ”
  &&  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_2_split_goal_1 := 
forall (base: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep base pointers )
|--
  “ (event_multi_array_valid base pointers ) ”
.

Definition OS_EventTaskWaitMulti_which_implies_wit_2_split_goal_spatial := 
forall (base: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep base pointers )
|--
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
.

Definition OS_EventTaskWaitMulti_which_implies_wit_3 := 
(
forall (base: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_wait_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid base pointers )) ,
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
|--
  “ (pevent = (event_task_wait_multi_pointer (pointers) (0))) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers 0 ) ”
  &&  (event_multi_array_rep base pointers )
) \/
(
forall (base: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_wait_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid base pointers )) ,
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
|--
  “ (event_task_wait_multi_value pevent pointers 0 ) ” 
  &&  “ (event_task_wait_multi_cursor base base 0 ) ”
  &&  (event_multi_array_rep base pointers )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_3_split_goal_1 := 
forall (base: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_wait_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid base pointers )) ,
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
|--
  “ (event_task_wait_multi_value pevent pointers 0 ) ”
.

Definition OS_EventTaskWaitMulti_which_implies_wit_3_split_goal_2 := 
forall (base: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_wait_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid base pointers )) ,
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
|--
  “ (event_task_wait_multi_cursor base base 0 ) ”
.

Definition OS_EventTaskWaitMulti_which_implies_wit_3_split_goal_spatial := 
forall (base: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_wait_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid base pointers )) ,
  ((base) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (0)))
  **  (event_task_wait_multi_array_missing base pointers 0 )
|--
  (event_multi_array_rep base pointers )
.

Definition OS_EventTaskWaitMulti_which_implies_wit_4 := 
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events_2: Glob_EventAbstractState) (index_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH2 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH3 : (pevent <> 0)) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index_2 events_2 )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events_2 )
|--
  EX (eid: Z)  (e: OSEventAbstractState)  (events: Glob_EventAbstractState)  (index: Z) ,
  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e.(waitList) )) (tasks)))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
) \/
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events_2: Glob_EventAbstractState) (index_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index_2 )) (PreH2 : (event_task_wait_multi_value pevent pointers index_2 )) (PreH3 : (pevent <> 0)) (PreH4 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index_2 events_2 )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events_2 )
|--
  EX (eid: Z)  (e: OSEventAbstractState)  (events: Glob_EventAbstractState)  (index: Z) ,
  “ (event_task_wait_multi_cursor pevents base index ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers index ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_wait_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e.(waitList) )) (tasks)))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_5 := 
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (e: OSEventAbstractState) (eid: Z) (events: Glob_EventAbstractState) (index: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index )) (PreH2 : (event_task_wait_multi_value pevent pointers index )) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_wait_multi_selected sg events pointers instances index eid e )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (tcb_bit_x_of_prio ((t.(curPrio) )))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor (encode_event_wait_grp ((e.(waitList) )) (tasks)) (tcb_bit_y_of_prio ((t.(curPrio) )))))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
) \/
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (e: OSEventAbstractState) (eid: Z) (events: Glob_EventAbstractState) (index: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_cursor pevents base index )) (PreH2 : (event_task_wait_multi_value pevent pointers index )) (PreH3 : (event_task_wait_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_wait_multi_selected sg events pointers instances index eid e )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (Z.lor (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (tcb_bit_x_of_prio ((t.(curPrio) )))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.lor (encode_event_wait_grp ((e.(waitList) )) (tasks)) (tcb_bit_y_of_prio ((t.(curPrio) )))))
  **  (event_task_wait_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_wait_multi_cursor (pevents + (1 * sizeof(PTR))) base next ) ” 
  &&  “ (event_task_wait_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_6 := 
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (PreH1 : (event_task_wait_multi_cursor pevents base next_2 )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_wait_multi_cursor pevents base next ) ” 
  &&  “ (event_multi_array_valid base pointers ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((pevents) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next)))
  **  (event_task_wait_multi_array_missing base pointers next )
  **  (event_raw_rep sg tasks after )
) \/
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (PreH1 : (event_task_wait_multi_cursor pevents base next_2 )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_wait_multi_cursor pevents base next ) ” 
  &&  “ (event_multi_array_valid base pointers ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((pevents) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next)))
  **  (event_task_wait_multi_array_missing base pointers next )
  **  (event_raw_rep sg tasks after )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_7 := 
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_cursor pevents base next_2 )) (PreH2 : (pevent = (event_task_wait_multi_pointer (pointers) (next_2)))) (PreH3 : (event_multi_array_valid base pointers )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  ((pevents) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next_2)))
  **  (event_task_wait_multi_array_missing base pointers next_2 )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_wait_multi_cursor pevents base next ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers next ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
) \/
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_cursor pevents base next_2 )) (PreH2 : (pevent = (event_task_wait_multi_pointer (pointers) (next_2)))) (PreH3 : (event_multi_array_valid base pointers )) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  ((pevents) # Ptr  |-> (event_task_wait_multi_pointer (pointers) (next_2)))
  **  (event_task_wait_multi_array_missing base pointers next_2 )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_wait_multi_cursor pevents base next ) ” 
  &&  “ (event_task_wait_multi_value pevent pointers next ) ”
  &&  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks after )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_8 := 
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (index: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_value pevent pointers index )) (PreH2 : (pevent <= 0)) (PreH3 : (0 <= pevent)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
|--
  ((( &( "pevent" ) )) # Ptr  |->_)
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
) \/
(
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (index: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_value pevent pointers index )) (PreH2 : (pevent <= 0)) (PreH3 : (0 <= pevent)) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
|--
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
).

Definition OS_EventTaskWaitMulti_which_implies_wit_8_split_goal_spatial := 
forall (base: Z) (instances: EventTaskWaitMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (index: Z) (pevent: Z) (PreH1 : (event_task_wait_multi_value pevent pointers index )) (PreH2 : (pevent <= 0)) (PreH3 : (0 <= pevent)) ,
  (event_task_wait_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks events )
|--
  (event_multi_array_rep base pointers )
  **  (event_raw_rep sg tasks (event_task_wait_multi_events (sg) (tasks) (entry) (tid) (instances)) )
.

Module Type VC_Correct.


Axiom proof_of_OS_EventTaskWaitMulti_safety_wit_1 : OS_EventTaskWaitMulti_safety_wit_1.
Axiom proof_of_OS_EventTaskWaitMulti_safety_wit_2 : OS_EventTaskWaitMulti_safety_wit_2.
Axiom proof_of_OS_EventTaskWaitMulti_entail_wit_1 : OS_EventTaskWaitMulti_entail_wit_1.
Axiom proof_of_OS_EventTaskWaitMulti_entail_wit_2 : OS_EventTaskWaitMulti_entail_wit_2.
Axiom proof_of_OS_EventTaskWaitMulti_entail_wit_3 : OS_EventTaskWaitMulti_entail_wit_3.
Axiom proof_of_OS_EventTaskWaitMulti_entail_wit_4 : OS_EventTaskWaitMulti_entail_wit_4.
Axiom proof_of_OS_EventTaskWaitMulti_return_wit_1 : OS_EventTaskWaitMulti_return_wit_1.
Axiom proof_of_OS_EventTaskWaitMulti_return_wit_2 : OS_EventTaskWaitMulti_return_wit_2.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_1_pure : OS_EventTaskWaitMulti_partial_solve_wit_1_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_1 : OS_EventTaskWaitMulti_partial_solve_wit_1.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_2 : OS_EventTaskWaitMulti_partial_solve_wit_2.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_3_pure : OS_EventTaskWaitMulti_partial_solve_wit_3_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_3 : OS_EventTaskWaitMulti_partial_solve_wit_3.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_4_pure : OS_EventTaskWaitMulti_partial_solve_wit_4_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_4 : OS_EventTaskWaitMulti_partial_solve_wit_4.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_5_pure : OS_EventTaskWaitMulti_partial_solve_wit_5_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_5 : OS_EventTaskWaitMulti_partial_solve_wit_5.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_6_pure : OS_EventTaskWaitMulti_partial_solve_wit_6_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_6 : OS_EventTaskWaitMulti_partial_solve_wit_6.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_7_pure : OS_EventTaskWaitMulti_partial_solve_wit_7_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_7 : OS_EventTaskWaitMulti_partial_solve_wit_7.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_8_pure : OS_EventTaskWaitMulti_partial_solve_wit_8_pure.
Axiom proof_of_OS_EventTaskWaitMulti_partial_solve_wit_8 : OS_EventTaskWaitMulti_partial_solve_wit_8.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_1 : OS_EventTaskWaitMulti_which_implies_wit_1.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_2 : OS_EventTaskWaitMulti_which_implies_wit_2.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_3 : OS_EventTaskWaitMulti_which_implies_wit_3.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_4 : OS_EventTaskWaitMulti_which_implies_wit_4.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_5 : OS_EventTaskWaitMulti_which_implies_wit_5.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_6 : OS_EventTaskWaitMulti_which_implies_wit_6.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_7 : OS_EventTaskWaitMulti_which_implies_wit_7.
Axiom proof_of_OS_EventTaskWaitMulti_which_implies_wit_8 : OS_EventTaskWaitMulti_which_implies_wit_8.

End VC_Correct.
