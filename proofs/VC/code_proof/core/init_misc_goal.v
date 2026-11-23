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
Require Import Ucos2Verify.VC.code.core.spec.init_misc_spec.
Import UCOS2_C_Rules.
Local Open Scope sac.

(*----- Function OS_InitMisc -----*)

Definition OS_InitMisc_return_wit_1 := 
(
forall (R: Assertion) (sg: StableGlobVars) (PreH1 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH2 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH3 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting (sg)))) (PreH4 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr (sg)))) (PreH5 : (( &( "OSRunning" ) ) = (g_OSRunning (sg)))) (PreH6 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr (sg)))) (PreH7 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH8 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun (sg)))) (PreH9 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax (sg)))) (PreH10 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy (sg)))) (PreH11 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID (sg)))) ,
  ((( &( "OSTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> 0)
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> 0)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> 0)
  **  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> 0)
  **  (R )
|--
  (init_misc_zero sg )
  **  (R )
) \/
(
forall (R: Assertion) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH4 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH5 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting (sg)))) (PreH6 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr (sg)))) (PreH7 : (( &( "OSRunning" ) ) = (g_OSRunning (sg)))) (PreH8 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr (sg)))) (PreH9 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH10 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun (sg)))) (PreH11 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax (sg)))) (PreH12 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy (sg)))) (PreH13 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID (sg)))) ,
  ((( &( "OSTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> 0)
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> 0)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> 0)
  **  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> 0)
  **  (R )
|--
  (init_misc_zero sg )
  **  (R )
).

Definition OS_InitMisc_return_wit_1_split_goal_spatial := 
forall (R: Assertion) (sg: StableGlobVars) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : (( &( "OSTime" ) ) = (g_OSTime (sg)))) (PreH4 : (( &( "OSIntNesting" ) ) = (g_OSIntNesting (sg)))) (PreH5 : (( &( "OSLockNesting" ) ) = (g_OSLockNesting (sg)))) (PreH6 : (( &( "OSTaskCtr" ) ) = (g_OSTaskCtr (sg)))) (PreH7 : (( &( "OSRunning" ) ) = (g_OSRunning (sg)))) (PreH8 : (( &( "OSCtxSwCtr" ) ) = (g_OSCtxSwCtr (sg)))) (PreH9 : (( &( "OSIdleCtr" ) ) = (g_OSIdleCtr (sg)))) (PreH10 : (( &( "OSIdleCtrRun" ) ) = (g_OSIdleCtrRun (sg)))) (PreH11 : (( &( "OSIdleCtrMax" ) ) = (g_OSIdleCtrMax (sg)))) (PreH12 : (( &( "OSStatRdy" ) ) = (g_OSStatRdy (sg)))) (PreH13 : (( &( "OSTaskRegNextAvailID" ) ) = (g_OSTaskRegNextAvailID (sg)))) ,
  ((( &( "OSTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> 0)
  **  ((( &( "OSLockNesting" ) )) # UChar  |-> 0)
  **  ((( &( "OSTaskCtr" ) )) # UChar  |-> 0)
  **  ((( &( "OSRunning" ) )) # UChar  |-> 0)
  **  ((( &( "OSCtxSwCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtr" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrRun" ) )) # UInt  |-> 0)
  **  ((( &( "OSIdleCtrMax" ) )) # UInt  |-> 0)
  **  ((( &( "OSStatRdy" ) )) # UChar  |-> 0)
  **  ((( &( "OSTaskRegNextAvailID" ) )) # UChar  |-> 0)
  **  (R )
|--
  (init_misc_zero sg )
  **  (R )
.

Module Type VC_Correct.


Axiom proof_of_OS_InitMisc_return_wit_1 : OS_InitMisc_return_wit_1.

End VC_Correct.
