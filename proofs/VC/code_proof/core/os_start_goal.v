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
Require Import Ucos2Verify.VC.code.core.spec.os_start_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSStart -----*)

Definition OSStart_safety_wit_1 := 
forall (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (0 = 1)) (PreH2 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH3 : (os_start_safe env 0 entry X )) (PreH4 : (os_start_startup env entry )) (PreH5 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH6 : (os_start_safe env running entry X )) (PreH7 : (os_start_entry_facts env entry running )) (PreH8 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH9 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH10 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  TT && emp 
|--
  “ False ”
.

Definition OSStart_return_wit_1 := 
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  (os_start_post env entry running X frame )
) \/
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  (os_start_post env entry running X frame )
).

Definition OSStart_return_wit_1_split_goal_spatial := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) <> 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  (os_start_post env entry running X frame )
.

Definition OSStart_partial_solve_wit_1_pure := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH2 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH3 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (os_start_pre env entry running X frame )
|--
  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ”
.

Definition OSStart_partial_solve_wit_1_aux := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH2 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH3 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (os_start_pre env entry running X frame )
|--
  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  (os_start_pre env entry running X frame )
.

Definition OSStart_partial_solve_wit_1 := OSStart_partial_solve_wit_1_pure -> OSStart_partial_solve_wit_1_aux.

Definition OSStart_partial_solve_wit_2_pure := 
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (running = 0) ” 
  &&  “ (running = 0) ”
) \/
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (running = 0) ” 
  &&  “ (running = 0) ”
).

Definition OSStart_partial_solve_wit_2_pure_split_goal_1 := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (running = 0) ”
.

Definition OSStart_partial_solve_wit_2_pure_split_goal_2 := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (running = 0) ”
.

Definition OSStart_partial_solve_wit_2_aux := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH5 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH6 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (running = 0) ” 
  &&  “ (running = 0) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  (os_start_entry_remainder env entry running frame )
.

Definition OSStart_partial_solve_wit_2 := OSStart_partial_solve_wit_2_pure -> OSStart_partial_solve_wit_2_aux.

Definition OSStart_partial_solve_wit_3_pure := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_safe env 0 entry X )) (PreH2 : (os_start_startup env entry )) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (os_start_safe env running entry X )) (PreH5 : (os_start_entry_facts env entry running )) (PreH6 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH7 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH8 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (os_start_old_high (entry)) )
  **  (os_start_sched_frame env entry frame )
|--
  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ”
.

Definition OSStart_partial_solve_wit_3_aux := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_safe env 0 entry X )) (PreH2 : (os_start_startup env entry )) (PreH3 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH4 : (os_start_safe env running entry X )) (PreH5 : (os_start_entry_facts env entry running )) (PreH6 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH7 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH8 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (os_start_old_high (entry)) )
  **  (os_start_sched_frame env entry frame )
|--
  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (os_start_old_high (entry)) )
  **  (os_start_sched_frame env entry frame )
.

Definition OSStart_partial_solve_wit_3 := OSStart_partial_solve_wit_3_pure -> OSStart_partial_solve_wit_3_aux.

Definition OSStart_partial_solve_wit_4_pure := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) )
  **  (os_start_sched_frame env entry frame )
|--
  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
.

Definition OSStart_partial_solve_wit_4_aux := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) )
  **  (os_start_sched_frame env entry frame )
|--
  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) )
  **  (os_start_sched_frame env entry frame )
.

Definition OSStart_partial_solve_wit_4 := OSStart_partial_solve_wit_4_pure -> OSStart_partial_solve_wit_4_aux.

Definition OSStart_partial_solve_wit_5_pure := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
|--
  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
.

Definition OSStart_partial_solve_wit_5_aux := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
|--
  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
.

Definition OSStart_partial_solve_wit_5 := OSStart_partial_solve_wit_5_pure -> OSStart_partial_solve_wit_5_aux.

Definition OSStart_partial_solve_wit_6_pure := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
|--
  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ”
.

Definition OSStart_partial_solve_wit_6_aux := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
|--
  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
.

Definition OSStart_partial_solve_wit_6 := OSStart_partial_solve_wit_6_pure -> OSStart_partial_solve_wit_6_aux.

Definition OSStart_partial_solve_wit_7 := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) (PreH4 : ((unsigned_last_nbits (running) (32)) = 0)) (PreH5 : (os_start_safe env running entry X )) (PreH6 : (os_start_entry_facts env entry running )) (PreH7 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH8 : (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) )) (PreH9 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (os_start_high_pre env (kernel_start_ready_state (entry)) X frame )
|--
  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ” 
  &&  “ ((unsigned_last_nbits (running) (32)) = 0) ” 
  &&  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (( &( "OSRunning" ) ) = (os_start_running_address (env))) ” 
  &&  “ (sched_new_global_addresses (os_start_sg (env)) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ) ” 
  &&  “ (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) ) ”
  &&  (os_start_high_pre env (kernel_start_ready_state (entry)) X frame )
.

Definition OSStart_which_implies_wit_1 := 
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) ,
  (os_start_pre env entry running X frame )
|--
  “ (os_start_safe env running entry X ) ” 
  &&  “ (os_start_entry_facts env entry running ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
) \/
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) ,
  (os_start_pre env entry running X frame )
|--
  “ (os_start_entry_facts env entry running ) ” 
  &&  “ (os_start_safe env running entry X ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
).

Definition OSStart_which_implies_wit_1_split_goal_1 := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) ,
  (os_start_pre env entry running X frame )
|--
  “ (os_start_entry_facts env entry running ) ”
.

Definition OSStart_which_implies_wit_1_split_goal_2 := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) ,
  (os_start_pre env entry running X frame )
|--
  “ (os_start_safe env running entry X ) ”
.

Definition OSStart_which_implies_wit_1_split_goal_spatial := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) ,
  (os_start_pre env entry running X frame )
|--
  ((( &( "OSRunning" ) )) # UChar  |-> running)
  **  (os_start_entry_remainder env entry running frame )
.

Definition OSStart_which_implies_wit_2 := 
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (running = 0)) ,
  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (os_start_safe env 0 entry X ) ” 
  &&  “ (os_start_startup env entry ) ”
  &&  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (os_start_old_high (entry)) )
  **  (os_start_sched_frame env entry frame )
) \/
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (running = 0)) ,
  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (os_start_startup env entry ) ”
  &&  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (os_start_old_high (entry)) )
  **  (os_start_sched_frame env entry frame )
).

Definition OSStart_which_implies_wit_2_split_goal_1 := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (running = 0)) ,
  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  (os_start_entry_remainder env entry running frame )
|--
  “ (os_start_startup env entry ) ”
.

Definition OSStart_which_implies_wit_2_split_goal_spatial := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (running: Z) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (( &( "OSRunning" ) ) = (os_start_running_address (env)))) (PreH2 : (os_start_safe env running entry X )) (PreH3 : (os_start_entry_facts env entry running )) (PreH4 : (running = 0)) ,
  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  (os_start_entry_remainder env entry running frame )
|--
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (os_start_old_high (entry)) )
  **  (os_start_sched_frame env entry frame )
.

Definition OSStart_which_implies_wit_3 := 
(
forall (frame: Assertion) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) )
  **  (os_start_sched_frame env entry frame )
|--
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_start_old_priority (entry)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
) \/
(
forall (frame: Assertion) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) )
  **  (os_start_sched_frame env entry frame )
|--
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_start_old_priority (entry)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
).

Definition OSStart_which_implies_wit_3_split_goal_spatial := 
forall (frame: Assertion) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (sched_new_rep (os_start_sg (env)) (os_start_group (entry)) (os_start_rows (entry)) (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) )
  **  (os_start_sched_frame env entry frame )
|--
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (os_start_old_priority (entry)))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
.

Definition OSStart_which_implies_wit_4 := 
(
forall (frame: Assertion) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
|--
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_old_current (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_old_high_task (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
) \/
(
forall (frame: Assertion) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
|--
  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
).

Definition OSStart_which_implies_wit_4_split_goal_spatial := 
forall (frame: Assertion) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) ,
  (PtrArray.full ( &( "OSTCBPrioTbl" ) ) 64 (os_start_table_values (env) (entry)) )
  **  (os_start_c_remainder env entry frame )
|--
  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
.

Definition OSStart_which_implies_wit_5 := 
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
|--
  (os_start_high_pre env (kernel_start_ready_state (entry)) X frame )
) \/
(
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
|--
  (os_start_high_pre env (kernel_start_ready_state (entry)) X frame )
).

Definition OSStart_which_implies_wit_5_split_goal_spatial := 
forall (frame: Assertion) (X: (OsStartObservation -> (UCOS2_Verify_State -> Prop))) (entry: UCOS2_Verify_State) (env: OsStartEnvironment) (PreH1 : (os_start_global_addresses env ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSTCBCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSRunning" ) ) )) (PreH2 : (os_start_safe env 0 entry X )) (PreH3 : (os_start_startup env entry )) ,
  ((( &( "OSPrioHighRdy" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSPrioCur" ) )) # UChar  |-> (sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))))
  **  ((( &( "OSTCBCur" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  ((( &( "OSTCBHighRdy" ) )) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (((( &( "OSTCBPrioTbl" ) ) + ((sched_new_priority ((os_start_group (entry))) ((os_start_rows (entry)))) * sizeof(PTR)))) # Ptr  |-> (os_start_pointer (env) (entry)))
  **  (os_start_table_remainder env entry frame )
|--
  (os_start_high_pre env (kernel_start_ready_state (entry)) X frame )
.

Module Type VC_Correct.


Axiom proof_of_OSStart_safety_wit_1 : OSStart_safety_wit_1.
Axiom proof_of_OSStart_return_wit_1 : OSStart_return_wit_1.
Axiom proof_of_OSStart_partial_solve_wit_1_pure : OSStart_partial_solve_wit_1_pure.
Axiom proof_of_OSStart_partial_solve_wit_1 : OSStart_partial_solve_wit_1.
Axiom proof_of_OSStart_partial_solve_wit_2_pure : OSStart_partial_solve_wit_2_pure.
Axiom proof_of_OSStart_partial_solve_wit_2 : OSStart_partial_solve_wit_2.
Axiom proof_of_OSStart_partial_solve_wit_3_pure : OSStart_partial_solve_wit_3_pure.
Axiom proof_of_OSStart_partial_solve_wit_3 : OSStart_partial_solve_wit_3.
Axiom proof_of_OSStart_partial_solve_wit_4_pure : OSStart_partial_solve_wit_4_pure.
Axiom proof_of_OSStart_partial_solve_wit_4 : OSStart_partial_solve_wit_4.
Axiom proof_of_OSStart_partial_solve_wit_5_pure : OSStart_partial_solve_wit_5_pure.
Axiom proof_of_OSStart_partial_solve_wit_5 : OSStart_partial_solve_wit_5.
Axiom proof_of_OSStart_partial_solve_wit_6_pure : OSStart_partial_solve_wit_6_pure.
Axiom proof_of_OSStart_partial_solve_wit_6 : OSStart_partial_solve_wit_6.
Axiom proof_of_OSStart_partial_solve_wit_7 : OSStart_partial_solve_wit_7.
Axiom proof_of_OSStart_which_implies_wit_1 : OSStart_which_implies_wit_1.
Axiom proof_of_OSStart_which_implies_wit_2 : OSStart_which_implies_wit_2.
Axiom proof_of_OSStart_which_implies_wit_3 : OSStart_which_implies_wit_3.
Axiom proof_of_OSStart_which_implies_wit_4 : OSStart_which_implies_wit_4.
Axiom proof_of_OSStart_which_implies_wit_5 : OSStart_which_implies_wit_5.

End VC_Correct.
