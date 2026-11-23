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
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Import Ucos2Verify.lib.ucos2_rules_lib.UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_EventWaitListInit -----*)

Definition OS_EventWaitListInit_safety_wit_1 := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition OS_EventWaitListInit_entail_wit_1 := 
forall (pevent_pre: Z) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") 0 )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ”
  &&  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") 0 )
.

Definition OS_EventWaitListInit_entail_wit_2 := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") (i + 1 ) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ”
  &&  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") (i + 1 ) )
.

Definition OS_EventWaitListInit_return_wit_1 := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i = 8)) (PreH2 : (i >= 8)) (PreH3 : (0 <= i)) (PreH4 : (i <= 8)) ,
  (event_wait_list_init_post &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") )
|--
  (event_wait_list_init_post &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") )
.

Definition OS_EventWaitListInit_partial_solve_wit_1 := 
forall (pevent_pre: Z) ,
  (event_wait_list_init_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") )
|--
  (event_wait_list_init_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventGrp") &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") )
.

Definition OS_EventWaitListInit_partial_solve_wit_2_pure := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ”
.

Definition OS_EventWaitListInit_partial_solve_wit_2_aux := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ”
  &&  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
.

Definition OS_EventWaitListInit_partial_solve_wit_2 := OS_EventWaitListInit_partial_solve_wit_2_pure -> OS_EventWaitListInit_partial_solve_wit_2_aux.

Definition OS_EventWaitListInit_partial_solve_wit_3_pure := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "i" ) )) # UChar  |-> i)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (event_wait_list_init_row_frame &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ”
.

Definition OS_EventWaitListInit_partial_solve_wit_3_aux := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i < 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (event_wait_list_init_row_frame &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
|--
  “ (0 <= i) ” 
  &&  “ (i < 8) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ”
  &&  (((&((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (event_wait_list_init_row_frame &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
.

Definition OS_EventWaitListInit_partial_solve_wit_3 := OS_EventWaitListInit_partial_solve_wit_3_pure -> OS_EventWaitListInit_partial_solve_wit_3_aux.

Definition OS_EventWaitListInit_partial_solve_wit_4_pure := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "i" ) )) # UChar  |-> i)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (i >= 8) ”
.

Definition OS_EventWaitListInit_partial_solve_wit_4_aux := 
forall (pevent_pre: Z) (i: Z) (PreH1 : (i >= 8)) (PreH2 : (0 <= i)) (PreH3 : (i <= 8)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ”
  &&  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent_pre)  # "os_event" ->ₛ "OSEventTbl") i )
.

Definition OS_EventWaitListInit_partial_solve_wit_4 := OS_EventWaitListInit_partial_solve_wit_4_pure -> OS_EventWaitListInit_partial_solve_wit_4_aux.

Definition OS_EventWaitListInit_which_implies_wit_1 := 
(
forall (pevent: Z) ,
  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |->_)
  **  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") 0 )
) \/
(
forall (pevent: Z) ,
  (event_wait_list_init_pre &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
|--
  EX (x: Z) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> x)
  **  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") 0 )
).

Definition OS_EventWaitListInit_which_implies_wit_2 := 
(
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |->_)
  **  (event_wait_list_init_row_frame &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
) \/
(
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  EX (x: Z) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> x)
  **  (event_wait_list_init_row_frame &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
).

Definition OS_EventWaitListInit_which_implies_wit_3 := 
(
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (event_wait_list_init_row_frame &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") (i + 1 ) )
) \/
(
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (event_wait_list_init_row_frame &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") (i + 1 ) )
).

Definition OS_EventWaitListInit_which_implies_wit_3_split_goal_spatial := 
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i < 8)) ,
  (((&((pevent)  # "os_event" ->ₛ "OSEventTbl") + (i * sizeof(UCHAR)))) # UChar  |-> 0)
  **  (event_wait_list_init_row_frame &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") (i + 1 ) )
.

Definition OS_EventWaitListInit_which_implies_wit_4 := 
(
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : (i >= 8)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  “ (i = 8) ”
  &&  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
) \/
(
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : (i >= 8)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
).

Definition OS_EventWaitListInit_which_implies_wit_4_split_goal_spatial := 
forall (i: Z) (pevent: Z) (PreH1 : (0 <= i)) (PreH2 : (i <= 8)) (PreH3 : (i >= 8)) ,
  ((&((pevent)  # "os_event" ->ₛ "OSEventGrp")) # UChar  |-> 0)
  **  (event_wait_list_init_table_prefix &((pevent)  # "os_event" ->ₛ "OSEventTbl") i )
|--
  (event_wait_list_init_post &((pevent)  # "os_event" ->ₛ "OSEventGrp") &((pevent)  # "os_event" ->ₛ "OSEventTbl") )
.

Module Type VC_Correct.


Axiom proof_of_OS_EventWaitListInit_safety_wit_1 : OS_EventWaitListInit_safety_wit_1.
Axiom proof_of_OS_EventWaitListInit_entail_wit_1 : OS_EventWaitListInit_entail_wit_1.
Axiom proof_of_OS_EventWaitListInit_entail_wit_2 : OS_EventWaitListInit_entail_wit_2.
Axiom proof_of_OS_EventWaitListInit_return_wit_1 : OS_EventWaitListInit_return_wit_1.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_1 : OS_EventWaitListInit_partial_solve_wit_1.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_2_pure : OS_EventWaitListInit_partial_solve_wit_2_pure.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_2 : OS_EventWaitListInit_partial_solve_wit_2.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_3_pure : OS_EventWaitListInit_partial_solve_wit_3_pure.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_3 : OS_EventWaitListInit_partial_solve_wit_3.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_4_pure : OS_EventWaitListInit_partial_solve_wit_4_pure.
Axiom proof_of_OS_EventWaitListInit_partial_solve_wit_4 : OS_EventWaitListInit_partial_solve_wit_4.
Axiom proof_of_OS_EventWaitListInit_which_implies_wit_1 : OS_EventWaitListInit_which_implies_wit_1.
Axiom proof_of_OS_EventWaitListInit_which_implies_wit_2 : OS_EventWaitListInit_which_implies_wit_2.
Axiom proof_of_OS_EventWaitListInit_which_implies_wit_3 : OS_EventWaitListInit_which_implies_wit_3.
Axiom proof_of_OS_EventWaitListInit_which_implies_wit_4 : OS_EventWaitListInit_which_implies_wit_4.

End VC_Correct.
