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
Require Import Ucos2Verify.VC.code.event.spec.event_task_remove_multi_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_EventTaskRemoveMulti -----*)

Definition OS_EventTaskRemoveMulti_safety_wit_1 := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH2 : (event_task_remove_multi_value pevent pointers index )) (PreH3 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH4 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH9 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH10 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH11 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH12 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH13 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH14 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH15 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH16 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH20 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH21 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH23 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "bitx" ) )) # UChar  |-> bitx)
  **  ((( &( "bity" ) )) # UChar  |-> bity)
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_EventTaskRemoveMulti_entail_wit_1 := 
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "bitx" ) )) # UChar  |->_)
  **  ((( &( "bity" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "bitx" ) )) # UChar  |->_)
  **  ((( &( "bity" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
) \/
(
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  TT && emp 
|--
  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ”
  &&  emp
).

Definition OS_EventTaskRemoveMulti_entail_wit_1_split_goal_1 := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)
.

Definition OS_EventTaskRemoveMulti_entail_wit_1_split_goal_2 := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH2 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))
.

Definition OS_EventTaskRemoveMulti_entail_wit_2 := 
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "bitx" ) )) # UChar  |->_)
  **  ((( &( "bity" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "bitx" ) )) # UChar  |->_)
  **  ((( &( "bity" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
) \/
(
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  TT && emp 
|--
  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ”
  &&  emp
).

Definition OS_EventTaskRemoveMulti_entail_wit_2_split_goal_1 := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)
.

Definition OS_EventTaskRemoveMulti_entail_wit_2_split_goal_2 := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))
.

Definition OS_EventTaskRemoveMulti_entail_wit_3 := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : ((event_task_remove_multi_pointer (pointers) (0)) = (event_task_remove_multi_pointer (pointers) (0)))) (PreH2 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH3 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH4 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH5 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH6 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH7 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH9 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH10 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH12 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (index: Z) ,
  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers index ) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_entail_wit_4_1 := 
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index_2: Z) (events_2: Glob_EventAbstractState) (eid_2: Z) (e_2: OSEventAbstractState) (index_3: Z) (PreH1 : ((Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)) = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_3 )) (PreH3 : (event_task_remove_multi_value pevent pointers index_3 )) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_remove_multi_selected sg events_2 pointers instances index_3 eid_2 e_2 )) (PreH6 : (0 <= (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH7 : ((encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH8 : (0 <= (encode_event_wait_grp ((e_2.(waitList) )) (tasks)))) (PreH9 : ((encode_event_wait_grp ((e_2.(waitList) )) (tasks)) < 256)) (PreH10 : (pevent <> 0)) (PreH11 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH12 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH13 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH14 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH15 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH17 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH24 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH25 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH26 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH31 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH32 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH33 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (y * sizeof(UCHAR)))) # UChar  |-> (Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_3 events_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (Z.land (encode_event_wait_grp ((e_2.(waitList) )) (tasks)) (Z.lnot bity)))
  **  (event_task_remove_multi_event_frame sg tasks events_2 eid_2 e_2 (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (eid: Z)  (e: OSEventAbstractState)  (index: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
) \/
(
forall (pevents_multi_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index_2: Z) (events_2: Glob_EventAbstractState) (eid_2: Z) (e_2: OSEventAbstractState) (index_3: Z) (PreH1 : ((Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)) = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_3 )) (PreH3 : (event_task_remove_multi_value pevent pointers index_3 )) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_remove_multi_selected sg events_2 pointers instances index_3 eid_2 e_2 )) (PreH6 : (0 <= (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH7 : ((encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH8 : (0 <= (encode_event_wait_grp ((e_2.(waitList) )) (tasks)))) (PreH9 : ((encode_event_wait_grp ((e_2.(waitList) )) (tasks)) < 256)) (PreH10 : (pevent <> 0)) (PreH11 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH12 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH13 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH14 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH15 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH17 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH24 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH25 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH26 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH31 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH32 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH33 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (y * sizeof(UCHAR)))) # UChar  |-> (Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_3 events_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_task_remove_multi_event_frame sg tasks events_2 eid_2 e_2 (tcb_y_of_prio ((t.(curPrio) ))) )
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (eid: Z)  (e: OSEventAbstractState)  (index: Z) ,
  “ ((Z.land (encode_event_wait_grp ((e_2.(waitList) )) (tasks)) (Z.lnot bity)) = (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  (frame )
).

Definition OS_EventTaskRemoveMulti_entail_wit_4_2 := 
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index_2: Z) (events_2: Glob_EventAbstractState) (eid_2: Z) (e_2: OSEventAbstractState) (index_3: Z) (PreH1 : ((Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)) <> 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_3 )) (PreH3 : (event_task_remove_multi_value pevent pointers index_3 )) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_remove_multi_selected sg events_2 pointers instances index_3 eid_2 e_2 )) (PreH6 : (0 <= (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH7 : ((encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH8 : (0 <= (encode_event_wait_grp ((e_2.(waitList) )) (tasks)))) (PreH9 : ((encode_event_wait_grp ((e_2.(waitList) )) (tasks)) < 256)) (PreH10 : (pevent <> 0)) (PreH11 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH12 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH13 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH14 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH15 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH17 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH24 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH25 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH26 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH31 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH32 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH33 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (y * sizeof(UCHAR)))) # UChar  |-> (Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_3 events_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e_2.(waitList) )) (tasks)))
  **  (event_task_remove_multi_event_frame sg tasks events_2 eid_2 e_2 (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (eid: Z)  (e: OSEventAbstractState)  (index: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
) \/
(
forall (pevents_multi_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index_2: Z) (events_2: Glob_EventAbstractState) (eid_2: Z) (e_2: OSEventAbstractState) (index_3: Z) (PreH1 : ((Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)) <> 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_3 )) (PreH3 : (event_task_remove_multi_value pevent pointers index_3 )) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_remove_multi_selected sg events_2 pointers instances index_3 eid_2 e_2 )) (PreH6 : (0 <= (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH7 : ((encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH8 : (0 <= (encode_event_wait_grp ((e_2.(waitList) )) (tasks)))) (PreH9 : ((encode_event_wait_grp ((e_2.(waitList) )) (tasks)) < 256)) (PreH10 : (pevent <> 0)) (PreH11 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH12 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH13 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH14 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH15 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH16 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH17 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH22 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH23 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH24 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH25 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH26 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH27 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH28 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH29 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH30 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH31 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH32 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH33 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (y * sizeof(UCHAR)))) # UChar  |-> (Z.land (encode_event_wait_tbl_at_or ((e_2.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) (Z.lnot bitx)))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_3 events_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_task_remove_multi_event_frame sg tasks events_2 eid_2 e_2 (tcb_y_of_prio ((t.(curPrio) ))) )
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (eid: Z)  (e: OSEventAbstractState)  (index: Z) ,
  “ ((encode_event_wait_grp ((e_2.(waitList) )) (tasks)) = (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  (frame )
).

Definition OS_EventTaskRemoveMulti_entail_wit_5 := 
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index_2: Z) (events_2: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (next_2: Z) (next: Z) (after: Glob_EventAbstractState) (next_3: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_3 )) (PreH2 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (next)) pointers next_3 )) (PreH3 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH4 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH5 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 )) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH8 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH9 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH10 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH12 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH13 : (event_task_remove_multi_selected sg events_2 pointers instances index_2 eid e )) (PreH14 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next_3 after )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  EX (events: Glob_EventAbstractState)  (index: Z) ,
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (next)) pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
) \/
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index_2: Z) (events_2: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (next_2: Z) (next: Z) (next_3: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_3 )) (PreH2 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (next)) pointers next_3 )) (PreH3 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH4 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH5 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 )) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH8 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH9 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH10 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH12 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH13 : (event_task_remove_multi_selected sg events_2 pointers instances index_2 eid e )) (PreH14 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  TT && emp 
|--
  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ”
  &&  emp
).

Definition OS_EventTaskRemoveMulti_entail_wit_5_split_goal_1 := 
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index_2: Z) (events_2: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (next_2: Z) (next: Z) (next_3: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_3 )) (PreH2 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (next)) pointers next_3 )) (PreH3 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH4 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH5 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 )) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH8 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH9 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH10 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH12 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH13 : (event_task_remove_multi_selected sg events_2 pointers instances index_2 eid e )) (PreH14 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )
.

Definition OS_EventTaskRemoveMulti_entail_wit_5_split_goal_2 := 
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index_2: Z) (events_2: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (next_2: Z) (next: Z) (next_3: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_3 )) (PreH2 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (next)) pointers next_3 )) (PreH3 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH4 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH5 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 )) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH8 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH9 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH10 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH12 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH13 : (event_task_remove_multi_selected sg events_2 pointers instances index_2 eid e )) (PreH14 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH16 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH18 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )
.

Definition OS_EventTaskRemoveMulti_return_wit_1 := 
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks (event_task_remove_multi_events (entry) (tid) (instances)) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  (event_task_remove_multi_post sg tasks entry tid t pointers instances ptcb_pre pevents_multi_pre )
  **  (frame )
) \/
(
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks (event_task_remove_multi_events (entry) (tid) (instances)) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  (event_task_remove_multi_post sg tasks entry tid t pointers instances ptcb_pre pevents_multi_pre )
  **  (frame )
).

Definition OS_EventTaskRemoveMulti_return_wit_1_split_goal_spatial := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks (event_task_remove_multi_events (entry) (tid) (instances)) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  (event_task_remove_multi_post sg tasks entry tid t pointers instances ptcb_pre pevents_multi_pre )
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_1_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "bitx" ) )) # UChar  |->_)
  **  ((( &( "bity" ) )) # UChar  |->_)
  **  ((( &( "y" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  ((( &( "pevents" ) )) # Ptr  |->_)
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks entry )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_1_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks entry )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_raw_rep sg tasks entry )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_1 := OS_EventTaskRemoveMulti_partial_solve_wit_1_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_1_aux.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_2 := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH2 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH3 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH4 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH5 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH6 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH7 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH8 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_3_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH2 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH9 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> pevents_multi_pre)
  **  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((( &( "bitx" ) )) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((( &( "bity" ) )) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  ((( &( "y" ) )) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ ((event_task_remove_multi_pointer (pointers) (0)) = (event_task_remove_multi_pointer (pointers) (0))) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_3_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH2 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH3 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH4 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH9 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ ((event_task_remove_multi_pointer (pointers) (0)) = (event_task_remove_multi_pointer (pointers) (0))) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_3 := OS_EventTaskRemoveMulti_partial_solve_wit_3_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_3_aux.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_4_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent <> 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "bitx" ) )) # UChar  |-> bitx)
  **  ((( &( "bity" ) )) # UChar  |-> bity)
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
|--
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_4_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent <> 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_4 := OS_EventTaskRemoveMulti_partial_solve_wit_4_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_4_aux.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_5 := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (index_2: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH2 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_remove_multi_selected sg events pointers instances index_2 eid e )) (PreH5 : (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))) (PreH6 : ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256)) (PreH7 : (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks)))) (PreH8 : ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256)) (PreH9 : (pevent <> 0)) (PreH10 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH11 : (event_task_remove_multi_value pevent pointers index )) (PreH12 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH13 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH14 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH16 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH18 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH19 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH20 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH21 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH22 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH23 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH24 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH25 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH26 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH27 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH28 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH29 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH30 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH31 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH32 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_2 events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e.(waitList) )) (tasks)))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index_2 ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index_2 eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ” 
  &&  “ (pevent <> 0) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (y * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_2 events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e.(waitList) )) (tasks)))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_6_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH2 : (event_task_remove_multi_value pevent pointers index )) (PreH3 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH4 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_remove_multi_selected sg events pointers instances index eid e )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "bitx" ) )) # UChar  |-> bitx)
  **  ((( &( "bity" ) )) # UChar  |-> bity)
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
|--
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_6_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH2 : (event_task_remove_multi_value pevent pointers index )) (PreH3 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH4 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH5 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH6 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH7 : (event_task_remove_multi_selected sg events pointers instances index eid e )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_6 := OS_EventTaskRemoveMulti_partial_solve_wit_6_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_6_aux.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_7_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH2 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH3 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH4 : (event_task_remove_multi_value pevent pointers index )) (PreH5 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH6 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH7 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH8 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH9 : (event_task_remove_multi_selected sg events pointers instances index eid e )) (PreH10 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH12 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  ((( &( "pevents" ) )) # Ptr  |-> (pevents + (1 * sizeof(PTR))))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "bitx" ) )) # UChar  |-> bitx)
  **  ((( &( "bity" ) )) # UChar  |-> bity)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
|--
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_7_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH2 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH3 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH4 : (event_task_remove_multi_value pevent pointers index )) (PreH5 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH6 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH7 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH8 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH9 : (event_task_remove_multi_selected sg events pointers instances index eid e )) (PreH10 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH12 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_7 := OS_EventTaskRemoveMulti_partial_solve_wit_7_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_7_aux.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_8_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (next_2: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH3 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 )) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH6 : (event_task_remove_multi_value pevent pointers index )) (PreH7 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH10 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH11 : (event_task_remove_multi_selected sg events pointers instances index eid e )) (PreH12 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH16 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  ((( &( "pevents" ) )) # Ptr  |-> (pevents + (1 * sizeof(PTR))))
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (((pevents + (1 * sizeof(PTR)))) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next )
  **  (event_raw_rep sg tasks after )
  **  ((( &( "pevent" ) )) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next)))
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "bitx" ) )) # UChar  |-> bitx)
  **  ((( &( "bity" ) )) # UChar  |-> bity)
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
|--
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ ((event_task_remove_multi_pointer (pointers) (next)) = (event_task_remove_multi_pointer (pointers) (next))) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_8_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (index: Z) (events: Glob_EventAbstractState) (eid: Z) (e: OSEventAbstractState) (pevents: Z) (pevent: Z) (y: Z) (bitx: Z) (bity: Z) (next_2: Z) (after: Glob_EventAbstractState) (next: Z) (PreH1 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next )) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH3 : (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 )) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH5 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH6 : (event_task_remove_multi_value pevent pointers index )) (PreH7 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH8 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH9 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH10 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH11 : (event_task_remove_multi_selected sg events pointers instances index eid e )) (PreH12 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH14 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH15 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH16 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH17 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (((pevents + (1 * sizeof(PTR)))) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next )
  **  (event_raw_rep sg tasks after )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ ((event_task_remove_multi_pointer (pointers) (next)) = (event_task_remove_multi_pointer (pointers) (next))) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next_2 ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (((pevents + (1 * sizeof(PTR)))) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next )
  **  (event_raw_rep sg tasks after )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_8 := OS_EventTaskRemoveMulti_partial_solve_wit_8_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_8_aux.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_9_pure := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  ((( &( "pevents" ) )) # Ptr  |-> pevents)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  ((( &( "y" ) )) # UChar  |-> y)
  **  ((( &( "bitx" ) )) # UChar  |-> bitx)
  **  ((( &( "bity" ) )) # UChar  |-> bity)
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
  **  ((( &( "ptcb" ) )) # Ptr  |-> ptcb_pre)
  **  ((( &( "pevents_multi" ) )) # Ptr  |-> pevents_multi_pre)
|--
  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (pevent <= 0) ” 
  &&  “ (0 <= pevent) ”
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_9_aux := 
forall (pevents_multi_pre: Z) (ptcb_pre: Z) (frame: Assertion) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (bity: Z) (bitx: Z) (y: Z) (pevent: Z) (pevents: Z) (index: Z) (PreH1 : (pevent = 0)) (PreH2 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH3 : (event_task_remove_multi_value pevent pointers index )) (PreH4 : (y = (tcb_y_of_prio ((t.(curPrio) ))))) (PreH5 : (bitx = (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH6 : (bity = (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH7 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH8 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH9 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH10 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH11 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH12 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH13 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH14 : (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 )) (PreH15 : (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 )) (PreH16 : (event_multi_array_valid pevents_multi_pre pointers )) (PreH17 : (0 <= (tcb_bit_y_of_prio ((t.(curPrio) ))))) (PreH18 : ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256)) (PreH19 : (0 <= (tcb_bit_x_of_prio ((t.(curPrio) ))))) (PreH20 : ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256)) (PreH21 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH22 : (0 <= (tcb_y_of_prio ((t.(curPrio) ))))) (PreH23 : ((tcb_y_of_prio ((t.(curPrio) ))) < 8)) (PreH24 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
|--
  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (pevent <= 0) ” 
  &&  “ (0 <= pevent) ” 
  &&  “ (pevent = 0) ” 
  &&  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (y = (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bitx = (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ (bity = (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ” 
  &&  “ (event_task_remove_multi_value (event_task_remove_multi_pointer (pointers) (0)) pointers 0 ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ” 
  &&  “ (0 <= (tcb_bit_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_y_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (0 <= (tcb_bit_x_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_bit_x_of_prio ((t.(curPrio) ))) < 256) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBY")) # UChar  |-> (tcb_y_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitX")) # UChar  |-> (tcb_bit_x_of_prio ((t.(curPrio) ))))
  **  ((&((ptcb_pre)  # "os_tcb" ->ₛ "OSTCBBitY")) # UChar  |-> (tcb_bit_y_of_prio ((t.(curPrio) ))))
  **  (frame )
.

Definition OS_EventTaskRemoveMulti_partial_solve_wit_9 := OS_EventTaskRemoveMulti_partial_solve_wit_9_pure -> OS_EventTaskRemoveMulti_partial_solve_wit_9_aux.

Definition OS_EventTaskRemoveMulti_which_implies_wit_1 := 
(
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ” 
  &&  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
) \/
(
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ” 
  &&  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_1_split_goal_1 := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ ((tcb_y_of_prio ((t.(curPrio) ))) < 8) ”
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_1_split_goal_2 := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  “ (0 <= (tcb_y_of_prio ((t.(curPrio) )))) ”
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_1_split_goal_spatial := 
forall (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (PreH1 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_raw_rep sg tasks entry )
|--
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances 0 entry )
  **  (event_raw_rep sg tasks entry )
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_2 := 
(
forall (pevents_multi_pre: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep pevents_multi_pre pointers )
|--
  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
  &&  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
) \/
(
forall (pevents_multi_pre: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep pevents_multi_pre pointers )
|--
  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
  &&  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_2_split_goal_1 := 
forall (pevents_multi_pre: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep pevents_multi_pre pointers )
|--
  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_2_split_goal_spatial := 
forall (pevents_multi_pre: Z) (pointers: (@list Z)) ,
  (event_multi_array_rep pevents_multi_pre pointers )
|--
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_3 := 
(
forall (pevents_multi_pre: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_remove_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
|--
  “ (pevent = (event_task_remove_multi_pointer (pointers) (0))) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers 0 ) ”
  &&  (event_multi_array_rep pevents_multi_pre pointers )
) \/
(
forall (pevents_multi_pre: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_remove_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
|--
  “ (event_task_remove_multi_value pevent pointers 0 ) ” 
  &&  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ”
  &&  (event_multi_array_rep pevents_multi_pre pointers )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_3_split_goal_1 := 
forall (pevents_multi_pre: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_remove_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
|--
  “ (event_task_remove_multi_value pevent pointers 0 ) ”
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_3_split_goal_2 := 
forall (pevents_multi_pre: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_remove_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
|--
  “ (event_task_remove_multi_cursor pevents_multi_pre pevents_multi_pre 0 ) ”
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_3_split_goal_spatial := 
forall (pevents_multi_pre: Z) (pointers: (@list Z)) (pevent: Z) (PreH1 : (pevent = (event_task_remove_multi_pointer (pointers) (0)))) (PreH2 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  ((pevents_multi_pre) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (0)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers 0 )
|--
  (event_multi_array_rep pevents_multi_pre pointers )
.

Definition OS_EventTaskRemoveMulti_which_implies_wit_4 := 
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events_2: Glob_EventAbstractState) (index_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH2 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH3 : (pevent <> 0)) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_2 events_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events_2 )
|--
  EX (events: Glob_EventAbstractState)  (eid: Z)  (e: OSEventAbstractState)  (index: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e.(waitList) )) (tasks)))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
) \/
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events_2: Glob_EventAbstractState) (index_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index_2 )) (PreH2 : (event_task_remove_multi_value pevent pointers index_2 )) (PreH3 : (pevent <> 0)) (PreH4 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index_2 events_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events_2 )
|--
  EX (events: Glob_EventAbstractState)  (eid: Z)  (e: OSEventAbstractState)  (index: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre index ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers index ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ” 
  &&  “ (event_task_remove_multi_selected sg events pointers instances index eid e ) ” 
  &&  “ (0 <= (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ” 
  &&  “ ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))) < 256) ” 
  &&  “ (0 <= (encode_event_wait_grp ((e.(waitList) )) (tasks))) ” 
  &&  “ ((encode_event_wait_grp ((e.(waitList) )) (tasks)) < 256) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (encode_event_wait_grp ((e.(waitList) )) (tasks)))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_5 := 
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (e: OSEventAbstractState) (eid: Z) (events: Glob_EventAbstractState) (index: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH2 : (event_task_remove_multi_value pevent pointers index )) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_remove_multi_selected sg events pointers instances index eid e )) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((( &( "pevent" ) )) # Ptr  |->_)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
) \/
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (t: TaskAbstractState) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (e: OSEventAbstractState) (eid: Z) (events: Glob_EventAbstractState) (index: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre index )) (PreH2 : (event_task_remove_multi_value pevent pointers index )) (PreH3 : (event_task_remove_multi_input sg tasks entry tid t pointers instances )) (PreH4 : (event_task_remove_multi_selected sg events pointers instances index eid e )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + ((tcb_y_of_prio ((t.(curPrio) ))) * sizeof(UCHAR)))) # UChar  |-> (event_task_remove_cleared ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((tcb_bit_x_of_prio ((t.(curPrio) ))))))
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> (event_task_remove_group ((encode_event_wait_tbl_at_or ((e.(waitList) )) (tasks) ((tcb_y_of_prio ((t.(curPrio) )))))) ((encode_event_wait_grp ((e.(waitList) )) (tasks))) ((tcb_bit_x_of_prio ((t.(curPrio) )))) ((tcb_bit_y_of_prio ((t.(curPrio) ))))))
  **  (event_task_remove_multi_event_frame sg tasks events eid e (tcb_y_of_prio ((t.(curPrio) ))) )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_remove_multi_cursor (pevents + (1 * sizeof(PTR))) pevents_multi_pre next ) ” 
  &&  “ (event_task_remove_multi_input sg tasks entry tid t pointers instances ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_6 := 
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre next_2 )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre next ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((pevents) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next )
  **  (event_raw_rep sg tasks after )
) \/
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre next_2 )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre next ) ” 
  &&  “ (event_multi_array_valid pevents_multi_pre pointers ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  ((pevents) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next )
  **  (event_raw_rep sg tasks after )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_7 := 
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre next_2 )) (PreH2 : (pevent = (event_task_remove_multi_pointer (pointers) (next_2)))) (PreH3 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  ((pevents) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next_2)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next_2 )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre next ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers next ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
) \/
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (after_2: Glob_EventAbstractState) (next_2: Z) (pevents: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_cursor pevents pevents_multi_pre next_2 )) (PreH2 : (pevent = (event_task_remove_multi_pointer (pointers) (next_2)))) (PreH3 : (event_multi_array_valid pevents_multi_pre pointers )) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next_2 after_2 )
  **  ((pevents) # Ptr  |-> (event_task_remove_multi_pointer (pointers) (next_2)))
  **  (event_task_remove_multi_array_missing pevents_multi_pre pointers next_2 )
  **  (event_raw_rep sg tasks after_2 )
|--
  EX (after: Glob_EventAbstractState)  (next: Z) ,
  “ (event_task_remove_multi_cursor pevents pevents_multi_pre next ) ” 
  &&  “ (event_task_remove_multi_value pevent pointers next ) ”
  &&  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances next after )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks after )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_8 := 
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (index: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_value pevent pointers index )) (PreH2 : (pevent <= 0)) (PreH3 : (0 <= pevent)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent)
  **  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
|--
  ((( &( "pevent" ) )) # Ptr  |->_)
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks (event_task_remove_multi_events (entry) (tid) (instances)) )
) \/
(
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (index: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_value pevent pointers index )) (PreH2 : (pevent <= 0)) (PreH3 : (0 <= pevent)) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
|--
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks (event_task_remove_multi_events (entry) (tid) (instances)) )
).

Definition OS_EventTaskRemoveMulti_which_implies_wit_8_split_goal_spatial := 
forall (pevents_multi_pre: Z) (instances: EventTaskRemoveMultiInstances) (pointers: (@list Z)) (tid: Z) (entry: Glob_EventAbstractState) (tasks: Glob_TaskAbstractState) (sg: StableGlobVars) (events: Glob_EventAbstractState) (index: Z) (pevent: Z) (PreH1 : (event_task_remove_multi_value pevent pointers index )) (PreH2 : (pevent <= 0)) (PreH3 : (0 <= pevent)) ,
  (event_task_remove_multi_loop_assert sg tasks entry tid pointers instances index events )
  **  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks events )
|--
  (event_multi_array_rep pevents_multi_pre pointers )
  **  (event_raw_rep sg tasks (event_task_remove_multi_events (entry) (tid) (instances)) )
.

Module Type VC_Correct.


Axiom proof_of_OS_EventTaskRemoveMulti_safety_wit_1 : OS_EventTaskRemoveMulti_safety_wit_1.
Axiom proof_of_OS_EventTaskRemoveMulti_entail_wit_1 : OS_EventTaskRemoveMulti_entail_wit_1.
Axiom proof_of_OS_EventTaskRemoveMulti_entail_wit_2 : OS_EventTaskRemoveMulti_entail_wit_2.
Axiom proof_of_OS_EventTaskRemoveMulti_entail_wit_3 : OS_EventTaskRemoveMulti_entail_wit_3.
Axiom proof_of_OS_EventTaskRemoveMulti_entail_wit_4_1 : OS_EventTaskRemoveMulti_entail_wit_4_1.
Axiom proof_of_OS_EventTaskRemoveMulti_entail_wit_4_2 : OS_EventTaskRemoveMulti_entail_wit_4_2.
Axiom proof_of_OS_EventTaskRemoveMulti_entail_wit_5 : OS_EventTaskRemoveMulti_entail_wit_5.
Axiom proof_of_OS_EventTaskRemoveMulti_return_wit_1 : OS_EventTaskRemoveMulti_return_wit_1.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_1_pure : OS_EventTaskRemoveMulti_partial_solve_wit_1_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_1 : OS_EventTaskRemoveMulti_partial_solve_wit_1.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_2 : OS_EventTaskRemoveMulti_partial_solve_wit_2.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_3_pure : OS_EventTaskRemoveMulti_partial_solve_wit_3_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_3 : OS_EventTaskRemoveMulti_partial_solve_wit_3.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_4_pure : OS_EventTaskRemoveMulti_partial_solve_wit_4_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_4 : OS_EventTaskRemoveMulti_partial_solve_wit_4.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_5 : OS_EventTaskRemoveMulti_partial_solve_wit_5.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_6_pure : OS_EventTaskRemoveMulti_partial_solve_wit_6_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_6 : OS_EventTaskRemoveMulti_partial_solve_wit_6.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_7_pure : OS_EventTaskRemoveMulti_partial_solve_wit_7_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_7 : OS_EventTaskRemoveMulti_partial_solve_wit_7.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_8_pure : OS_EventTaskRemoveMulti_partial_solve_wit_8_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_8 : OS_EventTaskRemoveMulti_partial_solve_wit_8.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_9_pure : OS_EventTaskRemoveMulti_partial_solve_wit_9_pure.
Axiom proof_of_OS_EventTaskRemoveMulti_partial_solve_wit_9 : OS_EventTaskRemoveMulti_partial_solve_wit_9.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_1 : OS_EventTaskRemoveMulti_which_implies_wit_1.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_2 : OS_EventTaskRemoveMulti_which_implies_wit_2.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_3 : OS_EventTaskRemoveMulti_which_implies_wit_3.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_4 : OS_EventTaskRemoveMulti_which_implies_wit_4.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_5 : OS_EventTaskRemoveMulti_which_implies_wit_5.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_6 : OS_EventTaskRemoveMulti_which_implies_wit_6.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_7 : OS_EventTaskRemoveMulti_which_implies_wit_7.
Axiom proof_of_OS_EventTaskRemoveMulti_which_implies_wit_8 : OS_EventTaskRemoveMulti_which_implies_wit_8.

End VC_Correct.
