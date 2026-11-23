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
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.event.spec.init_event_list_names_spec.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OS_InitEventList -----*)

Definition OS_InitEventList_safety_wit_1 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) (PreH5 : ((osMaxEvents (sg)) = 10)) (PreH6 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 24)) (PreH9 : ((sizeof( "os_event" ) * 10) = 240)) (PreH10 : (0 <= (g_OSEventTbl (sg)))) (PreH11 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH12 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH13 : (init_event_list_named_table_layout sg )) (PreH14 : (full_features_kernel_profile sg )) ,
  (mem_clr_pre (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitEventList_safety_wit_2 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : ((ix + 1 ) = (ix + 1 ))) (PreH13 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + (ix * 24 ) ))) (PreH14 : ((( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + ((ix + 1 ) * 24 ) ))) (PreH15 : (ix < (10 - 1 ))) (PreH16 : ((osMaxEvents (sg)) = 10)) (PreH17 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH18 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH19 : (sizeof( "os_event" ) = 24)) (PreH20 : (0 <= (g_OSEventTbl (sg)))) (PreH21 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH22 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH23 : (init_event_list_named_table_layout sg )) (PreH24 : (full_features_kernel_profile sg )) (PreH25 : (0 <= ix)) (PreH26 : (ix <= 9)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((( &( "pevent2" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitEventList_safety_wit_3 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (ix = 9)) (PreH11 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + 216 ))) (PreH12 : (ix >= (10 - 1 ))) (PreH13 : ((osMaxEvents (sg)) = 10)) (PreH14 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH15 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH16 : (sizeof( "os_event" ) = 24)) (PreH17 : (0 <= (g_OSEventTbl (sg)))) (PreH18 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH19 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH20 : (init_event_list_named_table_layout sg )) (PreH21 : (full_features_kernel_profile sg )) (PreH22 : (0 <= ix)) (PreH23 : (ix <= 9)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitEventList_safety_wit_4 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (ix = 9)) (PreH11 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + 216 ))) (PreH12 : (ix >= (10 - 1 ))) (PreH13 : ((osMaxEvents (sg)) = 10)) (PreH14 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH15 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH16 : (sizeof( "os_event" ) = 24)) (PreH17 : (0 <= (g_OSEventTbl (sg)))) (PreH18 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH19 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH20 : (init_event_list_named_table_layout sg )) (PreH21 : (full_features_kernel_profile sg )) (PreH22 : (0 <= ix)) (PreH23 : (ix <= 9)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitEventList_safety_wit_5 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) ,
  ((( &( "OSEventFreeList" ) )) # Ptr  |->_)
  **  (init_event_list_named_prefix sg (LitMap (("?"%string))) 10 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |->_)
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OS_InitEventList_entail_wit_1 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) (PreH5 : ((osMaxEvents (sg)) = 10)) (PreH6 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 24)) (PreH9 : ((sizeof( "os_event" ) * 10) = 240)) (PreH10 : (0 <= (g_OSEventTbl (sg)))) (PreH11 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH12 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH13 : (init_event_list_named_table_layout sg )) (PreH14 : (full_features_kernel_profile sg )) ,
  (mem_clr_post (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 9) ”
  &&  (init_event_list_named_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) (PreH5 : ((osMaxEvents (sg)) = 10)) (PreH6 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 24)) (PreH9 : ((sizeof( "os_event" ) * 10) = 240)) (PreH10 : (0 <= (g_OSEventTbl (sg)))) (PreH11 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH12 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH13 : (init_event_list_named_table_layout sg )) (PreH14 : (full_features_kernel_profile sg )) ,
  (mem_clr_post (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_InitEventList_entail_wit_1_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) (PreH5 : ((osMaxEvents (sg)) = 10)) (PreH6 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 24)) (PreH9 : ((sizeof( "os_event" ) * 10) = 240)) (PreH10 : (0 <= (g_OSEventTbl (sg)))) (PreH11 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH12 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH13 : (init_event_list_named_table_layout sg )) (PreH14 : (full_features_kernel_profile sg )) ,
  (mem_clr_post (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) 0 )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_entail_wit_2 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : ((ix + 1 ) = (ix + 1 ))) (PreH13 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + (ix * 24 ) ))) (PreH14 : ((( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + ((ix + 1 ) * 24 ) ))) (PreH15 : (ix < (10 - 1 ))) (PreH16 : ((osMaxEvents (sg)) = 10)) (PreH17 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH18 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH19 : (sizeof( "os_event" ) = 24)) (PreH20 : (0 <= (g_OSEventTbl (sg)))) (PreH21 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH22 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH23 : (init_event_list_named_table_layout sg )) (PreH24 : (full_features_kernel_profile sg )) (PreH25 : (0 <= ix)) (PreH26 : (ix <= 9)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((( &( "pevent2" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 9) ”
  &&  (init_event_list_named_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |->_)
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + (ix * 24 ) ))) (PreH13 : ((( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + ((ix + 1 ) * 24 ) ))) (PreH14 : (ix < (10 - 1 ))) (PreH15 : ((osMaxEvents (sg)) = 10)) (PreH16 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH17 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH18 : (sizeof( "os_event" ) = 24)) (PreH19 : (0 <= (g_OSEventTbl (sg)))) (PreH20 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH21 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH22 : (init_event_list_named_table_layout sg )) (PreH23 : (full_features_kernel_profile sg )) (PreH24 : (0 <= ix)) (PreH25 : (ix <= 9)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_InitEventList_entail_wit_2_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + (ix * 24 ) ))) (PreH13 : ((( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + ((ix + 1 ) * 24 ) ))) (PreH14 : (ix < (10 - 1 ))) (PreH15 : ((osMaxEvents (sg)) = 10)) (PreH16 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH17 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH18 : (sizeof( "os_event" ) = 24)) (PreH19 : (0 <= (g_OSEventTbl (sg)))) (PreH20 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH21 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH22 : (init_event_list_named_table_layout sg )) (PreH23 : (full_features_kernel_profile sg )) (PreH24 : (0 <= ix)) (PreH25 : (ix <= 9)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
  **  (frame )
|--
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_entail_wit_3 := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= (ix + 1 )) ” 
  &&  “ ((ix + 1 ) <= 9) ”
  &&  (init_event_list_named_loop_state sg (LitMap (("?"%string))) (ix + 1 ) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_entail_wit_4 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (ix = 9)) (PreH11 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + 216 ))) (PreH12 : (ix >= (10 - 1 ))) (PreH13 : ((osMaxEvents (sg)) = 10)) (PreH14 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH15 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH16 : (sizeof( "os_event" ) = 24)) (PreH17 : (0 <= (g_OSEventTbl (sg)))) (PreH18 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH19 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH20 : (init_event_list_named_table_layout sg )) (PreH21 : (full_features_kernel_profile sg )) (PreH22 : (0 <= ix)) (PreH23 : (ix <= 9)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ”
  &&  ((( &( "OSEventFreeList" ) )) # Ptr  |->_)
  **  (init_event_list_named_prefix sg (LitMap (("?"%string))) 10 )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |->_)
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (ix = 9)) (PreH11 : ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = ((g_OSEventTbl (sg)) + 216 ))) (PreH12 : (ix >= (10 - 1 ))) (PreH13 : ((osMaxEvents (sg)) = 10)) (PreH14 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH15 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH16 : (sizeof( "os_event" ) = 24)) (PreH17 : (0 <= (g_OSEventTbl (sg)))) (PreH18 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH19 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH20 : (init_event_list_named_table_layout sg )) (PreH21 : (full_features_kernel_profile sg )) (PreH22 : (0 <= ix)) (PreH23 : (ix <= 9)) ,
  (GlobalStrings LitMap )
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&(((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
  **  (frame )
|--
  EX (x: Z) ,
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ”
  &&  ((( &( "OSEventFreeList" ) )) # Ptr  |-> x)
  **  (init_event_list_named_prefix sg (LitMap (("?"%string))) 10 )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_InitEventList_return_wit_1 := 
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) ,
  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))))
  **  (init_event_list_named_prefix sg (LitMap (("?"%string))) 10 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ”
  &&  (init_event_list_named_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
) \/
(
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) ,
  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))))
  **  (init_event_list_named_prefix sg (LitMap (("?"%string))) 10 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (init_event_list_named_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
).

Definition OS_InitEventList_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) ,
  ((( &( "OSEventFreeList" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))))
  **  (init_event_list_named_prefix sg (LitMap (("?"%string))) 10 )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  (init_event_list_named_post sg (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_partial_solve_wit_1_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : ((sizeof( "os_event" ) * 10) = 240)) (PreH6 : (0 <= (g_OSEventTbl (sg)))) (PreH7 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH9 : (init_event_list_named_table_layout sg )) (PreH10 : (full_features_kernel_profile sg )) ,
  ((( &( "pevent2" ) )) # Ptr  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (init_event_list_named_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ”
.

Definition OS_InitEventList_partial_solve_wit_1_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : ((sizeof( "os_event" ) * 10) = 240)) (PreH6 : (0 <= (g_OSEventTbl (sg)))) (PreH7 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH9 : (init_event_list_named_table_layout sg )) (PreH10 : (full_features_kernel_profile sg )) ,
  (init_event_list_named_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ” 
  &&  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ”
  &&  (init_event_list_named_pre sg )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_partial_solve_wit_1 := OS_InitEventList_partial_solve_wit_1_pure -> OS_InitEventList_partial_solve_wit_1_aux.

Definition OS_InitEventList_partial_solve_wit_2_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) (PreH5 : ((osMaxEvents (sg)) = 10)) (PreH6 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 24)) (PreH9 : ((sizeof( "os_event" ) * 10) = 240)) (PreH10 : (0 <= (g_OSEventTbl (sg)))) (PreH11 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH12 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH13 : (init_event_list_named_table_layout sg )) (PreH14 : (full_features_kernel_profile sg )) ,
  (mem_clr_pre (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= (sizeof( "os_event" ) * 10)) ” 
  &&  “ ((sizeof( "os_event" ) * 10) <= 65535) ” 
  &&  “ (0 <= (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" )))) ” 
  &&  “ (((( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) + ((sizeof( "os_event" ) * 10) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OS_InitEventList_partial_solve_wit_2_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) (PreH5 : ((osMaxEvents (sg)) = 10)) (PreH6 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH7 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH8 : (sizeof( "os_event" ) = 24)) (PreH9 : ((sizeof( "os_event" ) * 10) = 240)) (PreH10 : (0 <= (g_OSEventTbl (sg)))) (PreH11 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH12 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH13 : (init_event_list_named_table_layout sg )) (PreH14 : (full_features_kernel_profile sg )) ,
  (mem_clr_pre (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ (0 <= (sizeof( "os_event" ) * 10)) ” 
  &&  “ ((sizeof( "os_event" ) * 10) <= 65535) ” 
  &&  “ (0 <= (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" )))) ” 
  &&  “ (((( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) + ((sizeof( "os_event" ) * 10) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ” 
  &&  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ”
  &&  (mem_clr_pre (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_partial_solve_wit_2 := OS_InitEventList_partial_solve_wit_2_pure -> OS_InitEventList_partial_solve_wit_2_aux.

Definition OS_InitEventList_partial_solve_wit_3_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < (10 - 1 ))) (PreH2 : ((osMaxEvents (sg)) = 10)) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH5 : (sizeof( "os_event" ) = 24)) (PreH6 : (0 <= (g_OSEventTbl (sg)))) (PreH7 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH9 : (init_event_list_named_table_layout sg )) (PreH10 : (full_features_kernel_profile sg )) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 9)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((( &( "pevent2" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))))
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 9) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" )))) ” 
  &&  “ ((( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))) = (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" )))) ”
.

Definition OS_InitEventList_partial_solve_wit_3_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix < (10 - 1 ))) (PreH2 : ((osMaxEvents (sg)) = 10)) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH5 : (sizeof( "os_event" ) = 24)) (PreH6 : (0 <= (g_OSEventTbl (sg)))) (PreH7 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH9 : (init_event_list_named_table_layout sg )) (PreH10 : (full_features_kernel_profile sg )) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 9)) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 9) ” 
  &&  “ ((ix + 1 ) = (ix + 1 )) ” 
  &&  “ ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" )))) ” 
  &&  “ ((( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" ))) = (( &( "OSEventTbl" ) ) + ((ix + 1 ) * sizeof( "os_event" )))) ” 
  &&  “ (ix < (10 - 1 )) ” 
  &&  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 9) ”
  &&  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_partial_solve_wit_3 := OS_InitEventList_partial_solve_wit_3_pure -> OS_InitEventList_partial_solve_wit_3_aux.

Definition OS_InitEventList_partial_solve_wit_4_pure := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= (10 - 1 ))) (PreH2 : ((osMaxEvents (sg)) = 10)) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH5 : (sizeof( "os_event" ) = 24)) (PreH6 : (0 <= (g_OSEventTbl (sg)))) (PreH7 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH9 : (init_event_list_named_table_layout sg )) (PreH10 : (full_features_kernel_profile sg )) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 9)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "pevent1" ) )) # Ptr  |-> (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))
  **  ((( &( "pevent2" ) )) # Ptr  |->_)
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 9) ” 
  &&  “ (ix >= 9) ” 
  &&  “ ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" )))) ”
.

Definition OS_InitEventList_partial_solve_wit_4_aux := 
forall (frame: Assertion) (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (PreH1 : (ix >= (10 - 1 ))) (PreH2 : ((osMaxEvents (sg)) = 10)) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH5 : (sizeof( "os_event" ) = 24)) (PreH6 : (0 <= (g_OSEventTbl (sg)))) (PreH7 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH8 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH9 : (init_event_list_named_table_layout sg )) (PreH10 : (full_features_kernel_profile sg )) (PreH11 : (0 <= ix)) (PreH12 : (ix <= 9)) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 9) ” 
  &&  “ (ix >= 9) ” 
  &&  “ ((( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))) = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" )))) ” 
  &&  “ (ix >= (10 - 1 )) ” 
  &&  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 9) ”
  &&  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
  **  (GlobalStrings LitMap )
  **  (frame )
.

Definition OS_InitEventList_partial_solve_wit_4 := OS_InitEventList_partial_solve_wit_4_pure -> OS_InitEventList_partial_solve_wit_4_aux.

Definition OS_InitEventList_which_implies_wit_1 := 
(
forall (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) ,
  (init_event_list_named_pre sg )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ”
  &&  (mem_clr_pre (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
  **  (((g_OSEventFreeList (sg))) # Ptr  |->_)
) \/
(
forall (sg: StableGlobVars) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : (full_features_kernel_profile sg )) (PreH3 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH4 : ((sizeof( "os_event" ) * 10) = 240)) ,
  (init_event_list_named_pre sg )
|--
  EX (x: Z) ,
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((sizeof( "os_event" ) * 10) = 240) ”
  &&  (((g_OSEventFreeList (sg))) # Ptr  |-> x)
  **  (mem_clr_pre (( &( "OSEventTbl" ) ) + (0 * sizeof( "os_event" ))) (sizeof( "os_event" ) * 10) )
).

Definition OS_InitEventList_which_implies_wit_2 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (pevent1: Z) (pevent2: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : (ix_next = (ix + 1 ))) (PreH13 : (pevent1 = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))) (PreH14 : (pevent2 = (( &( "OSEventTbl" ) ) + (ix_next * sizeof( "os_event" ))))) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 9) ” 
  &&  “ (ix_next = (ix + 1 )) ” 
  &&  “ (pevent1 = ((g_OSEventTbl (sg)) + (ix * 24 ) )) ” 
  &&  “ (pevent2 = ((g_OSEventTbl (sg)) + ((ix + 1 ) * 24 ) )) ”
  &&  ((&((pevent1)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (pevent1: Z) (pevent2: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : (ix_next = (ix + 1 ))) (PreH13 : (pevent1 = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))) (PreH14 : (pevent2 = (( &( "OSEventTbl" ) ) + (ix_next * sizeof( "os_event" ))))) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pevent1)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
).

Definition OS_InitEventList_which_implies_wit_2_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (ix_next: Z) (pevent1: Z) (pevent2: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix < 9)) (PreH12 : (ix_next = (ix + 1 ))) (PreH13 : (pevent1 = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))) (PreH14 : (pevent2 = (( &( "OSEventTbl" ) ) + (ix_next * sizeof( "os_event" ))))) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pevent1)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) ix )
.

Definition OS_InitEventList_which_implies_wit_3 := 
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (pevent1: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 9)) (PreH12 : (ix >= 9)) (PreH13 : (pevent1 = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
|--
  “ ((osMaxEvents (sg)) = 10) ” 
  &&  “ ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) )) ” 
  &&  “ ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) )) ” 
  &&  “ (sizeof( "os_event" ) = 24) ” 
  &&  “ (0 <= (g_OSEventTbl (sg))) ” 
  &&  “ (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX) ” 
  &&  “ (((g_OSEventTbl (sg)) % ( 4 ) ) = 0) ” 
  &&  “ (init_event_list_named_table_layout sg ) ” 
  &&  “ (full_features_kernel_profile sg ) ” 
  &&  “ (ix = 9) ” 
  &&  “ (pevent1 = ((g_OSEventTbl (sg)) + 216 )) ”
  &&  ((&((pevent1)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
) \/
(
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (pevent1: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 9)) (PreH12 : (ix >= 9)) (PreH13 : (pevent1 = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pevent1)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
).

Definition OS_InitEventList_which_implies_wit_3_split_goal_spatial := 
forall (LitMap: (string -> Z)) (sg: StableGlobVars) (ix: Z) (pevent1: Z) (PreH1 : ((osMaxEvents (sg)) = 10)) (PreH2 : ((g_OSEventTbl (sg)) = ( &( "OSEventTbl" ) ))) (PreH3 : ((g_OSEventFreeList (sg)) = ( &( "OSEventFreeList" ) ))) (PreH4 : (sizeof( "os_event" ) = 24)) (PreH5 : (0 <= (g_OSEventTbl (sg)))) (PreH6 : (((g_OSEventTbl (sg)) + 240 ) <= UINT_MAX)) (PreH7 : (((g_OSEventTbl (sg)) % ( 4 ) ) = 0)) (PreH8 : (init_event_list_named_table_layout sg )) (PreH9 : (full_features_kernel_profile sg )) (PreH10 : (0 <= ix)) (PreH11 : (ix <= 9)) (PreH12 : (ix >= 9)) (PreH13 : (pevent1 = (( &( "OSEventTbl" ) ) + (ix * sizeof( "os_event" ))))) ,
  (init_event_list_named_loop_state sg (LitMap (("?"%string))) ix )
|--
  ((&((pevent1)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventPtr")) # Ptr  |-> 0)
  **  ((&((pevent1)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> 0)
  **  (init_event_list_named_loop_residual sg (LitMap (("?"%string))) 9 )
.

Module Type VC_Correct.


Axiom proof_of_OS_InitEventList_safety_wit_1 : OS_InitEventList_safety_wit_1.
Axiom proof_of_OS_InitEventList_safety_wit_2 : OS_InitEventList_safety_wit_2.
Axiom proof_of_OS_InitEventList_safety_wit_3 : OS_InitEventList_safety_wit_3.
Axiom proof_of_OS_InitEventList_safety_wit_4 : OS_InitEventList_safety_wit_4.
Axiom proof_of_OS_InitEventList_safety_wit_5 : OS_InitEventList_safety_wit_5.
Axiom proof_of_OS_InitEventList_entail_wit_1 : OS_InitEventList_entail_wit_1.
Axiom proof_of_OS_InitEventList_entail_wit_2 : OS_InitEventList_entail_wit_2.
Axiom proof_of_OS_InitEventList_entail_wit_3 : OS_InitEventList_entail_wit_3.
Axiom proof_of_OS_InitEventList_entail_wit_4 : OS_InitEventList_entail_wit_4.
Axiom proof_of_OS_InitEventList_return_wit_1 : OS_InitEventList_return_wit_1.
Axiom proof_of_OS_InitEventList_partial_solve_wit_1_pure : OS_InitEventList_partial_solve_wit_1_pure.
Axiom proof_of_OS_InitEventList_partial_solve_wit_1 : OS_InitEventList_partial_solve_wit_1.
Axiom proof_of_OS_InitEventList_partial_solve_wit_2_pure : OS_InitEventList_partial_solve_wit_2_pure.
Axiom proof_of_OS_InitEventList_partial_solve_wit_2 : OS_InitEventList_partial_solve_wit_2.
Axiom proof_of_OS_InitEventList_partial_solve_wit_3_pure : OS_InitEventList_partial_solve_wit_3_pure.
Axiom proof_of_OS_InitEventList_partial_solve_wit_3 : OS_InitEventList_partial_solve_wit_3.
Axiom proof_of_OS_InitEventList_partial_solve_wit_4_pure : OS_InitEventList_partial_solve_wit_4_pure.
Axiom proof_of_OS_InitEventList_partial_solve_wit_4 : OS_InitEventList_partial_solve_wit_4.
Axiom proof_of_OS_InitEventList_which_implies_wit_1 : OS_InitEventList_which_implies_wit_1.
Axiom proof_of_OS_InitEventList_which_implies_wit_2 : OS_InitEventList_which_implies_wit_2.
Axiom proof_of_OS_InitEventList_which_implies_wit_3 : OS_InitEventList_which_implies_wit_3.

End VC_Correct.
