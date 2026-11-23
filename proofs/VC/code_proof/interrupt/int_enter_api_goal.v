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
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_api_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSIntEnter -----*)

Definition OSIntEnter_return_wit_1 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((os_int_enter_nesting (before)) + 1 ))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_irq_masked mask ) ” 
  &&  “ (os_int_enter_return_safe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((os_int_enter_nesting (before)) + 1 ))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_return_safe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
).

Definition OSIntEnter_return_wit_1_split_goal_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((os_int_enter_nesting (before)) + 1 ))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_return_safe before X ) ”
.

Definition OSIntEnter_return_wit_1_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) < 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> ((os_int_enter_nesting (before)) + 1 ))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
.

Definition OSIntEnter_return_wit_2 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_irq_masked mask ) ” 
  &&  “ (os_int_enter_return_safe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_return_safe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
).

Definition OSIntEnter_return_wit_2_split_goal_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_return_safe before X ) ”
.

Definition OSIntEnter_return_wit_2_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((os_int_enter_nesting (before)) >= 255)) (PreH2 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) = 1)) (PreH3 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (0 <= (os_int_enter_nesting (before)))) (PreH6 : ((os_int_enter_nesting (before)) <= 255)) (PreH7 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH8 : (os_int_enter_irq_masked mask )) (PreH9 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
.

Definition OSIntEnter_return_wit_3 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) <> 1)) (PreH2 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (os_int_enter_nesting (before)))) (PreH5 : ((os_int_enter_nesting (before)) <= 255)) (PreH6 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH7 : (os_int_enter_irq_masked mask )) (PreH8 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_irq_masked mask ) ” 
  &&  “ (os_int_enter_return_safe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) <> 1)) (PreH2 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (os_int_enter_nesting (before)))) (PreH5 : ((os_int_enter_nesting (before)) <= 255)) (PreH6 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH7 : (os_int_enter_irq_masked mask )) (PreH8 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_return_safe before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
).

Definition OSIntEnter_return_wit_3_split_goal_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) <> 1)) (PreH2 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (os_int_enter_nesting (before)))) (PreH5 : ((os_int_enter_nesting (before)) <= 255)) (PreH6 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH7 : (os_int_enter_irq_masked mask )) (PreH8 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  “ (os_int_enter_return_safe before X ) ”
.

Definition OSIntEnter_return_wit_3_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((os_int_enter_running (before))) (32)) <> 1)) (PreH2 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (0 <= (os_int_enter_nesting (before)))) (PreH5 : ((os_int_enter_nesting (before)) <= 255)) (PreH6 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH7 : (os_int_enter_irq_masked mask )) (PreH8 : (os_int_enter_safe before X )) ,
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
  **  (interrupt_platform_running platform invocation origin mask )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg (os_int_enter_state (before)) )
.

Definition OSIntEnter_partial_solve_wit_1_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH2 : (os_int_enter_irq_masked mask )) (PreH3 : (os_int_enter_safe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  “ (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ) ”
.

Definition OSIntEnter_partial_solve_wit_1_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (sg: StableGlobVars) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) (PreH2 : (os_int_enter_irq_masked mask )) (PreH3 : (os_int_enter_safe before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (UCOS2_inv sg before )
|--
  “ (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_int_enter_irq_masked mask ) ” 
  &&  “ (os_int_enter_safe before X ) ”
  &&  (UCOS2_inv sg before )
  **  (interrupt_platform_running platform invocation origin mask )
.

Definition OSIntEnter_partial_solve_wit_1 := OSIntEnter_partial_solve_wit_1_pure -> OSIntEnter_partial_solve_wit_1_aux.

Definition OSIntEnter_which_implies_wit_1 := 
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) ,
  (UCOS2_inv sg before )
|--
  “ (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (0 <= (os_int_enter_nesting (before))) ” 
  &&  “ ((os_int_enter_nesting (before)) <= 255) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
) \/
(
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) ,
  (UCOS2_inv sg before )
|--
  “ ((os_int_enter_nesting (before)) <= 255) ” 
  &&  “ (0 <= (os_int_enter_nesting (before))) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
).

Definition OSIntEnter_which_implies_wit_1_split_goal_1 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) ,
  (UCOS2_inv sg before )
|--
  “ ((os_int_enter_nesting (before)) <= 255) ”
.

Definition OSIntEnter_which_implies_wit_1_split_goal_2 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) ,
  (UCOS2_inv sg before )
|--
  “ (0 <= (os_int_enter_nesting (before))) ”
.

Definition OSIntEnter_which_implies_wit_1_split_goal_3 := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) ,
  (UCOS2_inv sg before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSIntEnter_which_implies_wit_1_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (sg: StableGlobVars) (PreH1 : (os_int_enter_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) )) ,
  (UCOS2_inv sg before )
|--
  ((( &( "OSRunning" ) )) # UChar  |-> (os_int_enter_running (before)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (os_int_enter_nesting (before)))
  **  (os_int_enter_frame sg before )
.

Module Type VC_Correct.


Axiom proof_of_OSIntEnter_return_wit_1 : OSIntEnter_return_wit_1.
Axiom proof_of_OSIntEnter_return_wit_2 : OSIntEnter_return_wit_2.
Axiom proof_of_OSIntEnter_return_wit_3 : OSIntEnter_return_wit_3.
Axiom proof_of_OSIntEnter_partial_solve_wit_1_pure : OSIntEnter_partial_solve_wit_1_pure.
Axiom proof_of_OSIntEnter_partial_solve_wit_1 : OSIntEnter_partial_solve_wit_1.
Axiom proof_of_OSIntEnter_which_implies_wit_1 : OSIntEnter_which_implies_wit_1.

End VC_Correct.
