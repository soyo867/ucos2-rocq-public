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
Require Import Ucos2Verify.VC.code.interrupt.spec.os_init_hook_begin_spec.
Import UCOS2_C_Rules TaskStateDef.
Local Open Scope sac.

(*----- Function OSInitHookBegin -----*)

Definition OSInitHookBegin_safety_wit_1 := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (PreH1 : (0 < base)) (PreH2 : ((base % ( 4 ) ) = 0)) (PreH3 : ((base + 4096 ) <= UINT_MAX)) (PreH4 : ((Zlength (initial)) = 1024)) (PreH5 : (base = ( &( "OS_CPU_ExceptStk" ) ))) ,
  (task_stack_clear_rep base initial 0 )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
  **  ((( &( "pstk" ) )) # Ptr  |->_)
  **  ((( &( "size" ) )) # UInt  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSInitHookBegin_safety_wit_2 := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : ((Zlength (initial)) = 1024)) (PreH2 : (0 < size)) (PreH3 : (size <= 1024)) (PreH4 : ((base + (4 * (1024 - size ) ) ) = (base + (4 * (1024 - size ) ) ))) (PreH5 : (size > 0)) (PreH6 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH7 : (0 < base)) (PreH8 : ((base % ( 4 ) ) = 0)) (PreH9 : ((base + 4096 ) <= UINT_MAX)) (PreH10 : ((Zlength (initial)) = 1024)) (PreH11 : (0 <= size)) (PreH12 : (size <= 1024)) (PreH13 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  ((( &( "size" ) )) # UInt  |-> (size - 1 ))
  **  ((( &( "pstk" ) )) # Ptr  |-> (base + (4 * (1024 - size ) ) ))
  **  (((base + (4 * (1024 - size ) ) )) # UInt  |->_)
  **  (os_init_hook_begin_stack_cell_rest base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSInitHookBegin_entail_wit_1 := 
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (PreH1 : (0 < base)) (PreH2 : ((base % ( 4 ) ) = 0)) (PreH3 : ((base + 4096 ) <= UINT_MAX)) (PreH4 : ((Zlength (initial)) = 1024)) (PreH5 : (base = ( &( "OS_CPU_ExceptStk" ) ))) ,
  (task_stack_clear_rep base initial 0 )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
|--
  “ (base = ( &( "OS_CPU_ExceptStk" ) )) ” 
  &&  “ (0 < base) ” 
  &&  “ ((base % ( 4 ) ) = 0) ” 
  &&  “ ((base + 4096 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 <= 1024) ” 
  &&  “ (1024 <= 1024) ” 
  &&  “ ((( &( "OS_CPU_ExceptStk" ) ) + (0 * sizeof(UINT))) = (base + (4 * (1024 - 1024 ) ) )) ”
  &&  (task_stack_clear_rep base initial (1024 - 1024 ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
) \/
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (PreH1 : (0 < base)) (PreH2 : ((base % ( 4 ) ) = 0)) (PreH3 : ((base + 4096 ) <= UINT_MAX)) (PreH4 : ((Zlength (initial)) = 1024)) (PreH5 : (base = ( &( "OS_CPU_ExceptStk" ) ))) ,
  (task_stack_clear_rep base initial 0 )
  **  (R )
|--
  (task_stack_clear_rep base initial (1024 - 1024 ) )
  **  (R )
).

Definition OSInitHookBegin_entail_wit_1_split_goal_spatial := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (PreH1 : (0 < base)) (PreH2 : ((base % ( 4 ) ) = 0)) (PreH3 : ((base + 4096 ) <= UINT_MAX)) (PreH4 : ((Zlength (initial)) = 1024)) (PreH5 : (base = ( &( "OS_CPU_ExceptStk" ) ))) ,
  (task_stack_clear_rep base initial 0 )
  **  (R )
|--
  (task_stack_clear_rep base initial (1024 - 1024 ) )
  **  (R )
.

Definition OSInitHookBegin_entail_wit_2 := 
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : ((Zlength (initial)) = 1024)) (PreH2 : (0 < size)) (PreH3 : (size <= 1024)) (PreH4 : ((base + (4 * (1024 - size ) ) ) = (base + (4 * (1024 - size ) ) ))) (PreH5 : (size > 0)) (PreH6 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH7 : (0 < base)) (PreH8 : ((base % ( 4 ) ) = 0)) (PreH9 : ((base + 4096 ) <= UINT_MAX)) (PreH10 : ((Zlength (initial)) = 1024)) (PreH11 : (0 <= size)) (PreH12 : (size <= 1024)) (PreH13 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (((base + (4 * (1024 - size ) ) )) # UInt  |-> 0)
  **  (os_init_hook_begin_stack_cell_rest base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
|--
  “ (base = ( &( "OS_CPU_ExceptStk" ) )) ” 
  &&  “ (0 < base) ” 
  &&  “ ((base % ( 4 ) ) = 0) ” 
  &&  “ ((base + 4096 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 <= (size - 1 )) ” 
  &&  “ ((size - 1 ) <= 1024) ” 
  &&  “ (((base + (4 * (1024 - size ) ) ) + (1 * sizeof(UINT))) = (base + (4 * (1024 - (size - 1 ) ) ) )) ”
  &&  (task_stack_clear_rep base initial (1024 - (size - 1 ) ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
) \/
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Zlength (initial)) = 1024)) (PreH4 : (0 < size)) (PreH5 : (size <= 1024)) (PreH6 : (size > 0)) (PreH7 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH8 : (0 < base)) (PreH9 : ((base % ( 4 ) ) = 0)) (PreH10 : ((base + 4096 ) <= UINT_MAX)) (PreH11 : ((Zlength (initial)) = 1024)) (PreH12 : (0 <= size)) (PreH13 : (size <= 1024)) (PreH14 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (((base + (4 * (1024 - size ) ) )) # UInt  |-> 0)
  **  (os_init_hook_begin_stack_cell_rest base initial (1024 - size ) )
  **  (R )
|--
  (task_stack_clear_rep base initial (1024 - (size - 1 ) ) )
  **  (R )
).

Definition OSInitHookBegin_entail_wit_2_split_goal_spatial := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) (PreH3 : ((Zlength (initial)) = 1024)) (PreH4 : (0 < size)) (PreH5 : (size <= 1024)) (PreH6 : (size > 0)) (PreH7 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH8 : (0 < base)) (PreH9 : ((base % ( 4 ) ) = 0)) (PreH10 : ((base + 4096 ) <= UINT_MAX)) (PreH11 : ((Zlength (initial)) = 1024)) (PreH12 : (0 <= size)) (PreH13 : (size <= 1024)) (PreH14 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (((base + (4 * (1024 - size ) ) )) # UInt  |-> 0)
  **  (os_init_hook_begin_stack_cell_rest base initial (1024 - size ) )
  **  (R )
|--
  (task_stack_clear_rep base initial (1024 - (size - 1 ) ) )
  **  (R )
.

Definition OSInitHookBegin_return_wit_1 := 
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (size <= 0)) (PreH3 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH4 : (0 < base)) (PreH5 : ((base % ( 4 ) ) = 0)) (PreH6 : ((base + 4096 ) <= UINT_MAX)) (PreH7 : ((Zlength (initial)) = 1024)) (PreH8 : (0 <= size)) (PreH9 : (size <= 1024)) (PreH10 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (R )
  **  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |-> (Z.land (( &( "OS_CPU_ExceptStk" ) ) + (1024 * sizeof(UINT))) 4294967288))
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |-> retval)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  “ (base = ( &( "OS_CPU_ExceptStk" ) )) ”
  &&  (os_init_hook_begin_post base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) R )
) \/
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (retval = 0)) (PreH4 : (size <= 0)) (PreH5 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH6 : (0 < base)) (PreH7 : ((base % ( 4 ) ) = 0)) (PreH8 : ((base + 4096 ) <= UINT_MAX)) (PreH9 : ((Zlength (initial)) = 1024)) (PreH10 : (0 <= size)) (PreH11 : (size <= 1024)) (PreH12 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (R )
  **  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |-> (Z.land (( &( "OS_CPU_ExceptStk" ) ) + (1024 * sizeof(UINT))) 4294967288))
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |-> retval)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  (os_init_hook_begin_post base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) R )
).

Definition OSInitHookBegin_return_wit_1_split_goal_spatial := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (retval: Z) (PreH1 : (retval <= UINT_MAX)) (PreH2 : (retval >= 0)) (PreH3 : (retval = 0)) (PreH4 : (size <= 0)) (PreH5 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH6 : (0 < base)) (PreH7 : ((base % ( 4 ) ) = 0)) (PreH8 : ((base + 4096 ) <= UINT_MAX)) (PreH9 : ((Zlength (initial)) = 1024)) (PreH10 : (0 <= size)) (PreH11 : (size <= 1024)) (PreH12 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (R )
  **  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |-> (Z.land (( &( "OS_CPU_ExceptStk" ) ) + (1024 * sizeof(UINT))) 4294967288))
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |-> retval)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |-> 0)
|--
  (os_init_hook_begin_post base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) R )
.

Definition OSInitHookBegin_partial_solve_wit_1 := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (PreH1 : (base = ( &( "OS_CPU_ExceptStk" ) ))) ,
  (os_init_hook_begin_pre base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) initial R )
|--
  “ (base = ( &( "OS_CPU_ExceptStk" ) )) ”
  &&  (os_init_hook_begin_pre base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) initial R )
.

Definition OSInitHookBegin_partial_solve_wit_2_pure := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH3 : (0 < base)) (PreH4 : ((base % ( 4 ) ) = 0)) (PreH5 : ((base + 4096 ) <= UINT_MAX)) (PreH6 : ((Zlength (initial)) = 1024)) (PreH7 : (0 <= size)) (PreH8 : (size <= 1024)) (PreH9 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  ((( &( "size" ) )) # UInt  |-> size)
  **  ((( &( "pstk" ) )) # Ptr  |-> pstk)
  **  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
|--
  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 < size) ” 
  &&  “ (size <= 1024) ” 
  &&  “ ((base + (4 * (1024 - size ) ) ) = (base + (4 * (1024 - size ) ) )) ”
.

Definition OSInitHookBegin_partial_solve_wit_2_aux := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : (size > 0)) (PreH2 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH3 : (0 < base)) (PreH4 : ((base % ( 4 ) ) = 0)) (PreH5 : ((base + 4096 ) <= UINT_MAX)) (PreH6 : ((Zlength (initial)) = 1024)) (PreH7 : (0 <= size)) (PreH8 : (size <= 1024)) (PreH9 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  ((( &( "pstk" ) )) # Ptr  |-> pstk)
  **  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
|--
  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 < size) ” 
  &&  “ (size <= 1024) ” 
  &&  “ ((base + (4 * (1024 - size ) ) ) = (base + (4 * (1024 - size ) ) )) ” 
  &&  “ (size > 0) ” 
  &&  “ (base = ( &( "OS_CPU_ExceptStk" ) )) ” 
  &&  “ (0 < base) ” 
  &&  “ ((base % ( 4 ) ) = 0) ” 
  &&  “ ((base + 4096 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= 1024) ” 
  &&  “ (pstk = (base + (4 * (1024 - size ) ) )) ”
  &&  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "pstk" ) )) # Ptr  |-> (base + (4 * (1024 - size ) ) ))
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
.

Definition OSInitHookBegin_partial_solve_wit_2 := OSInitHookBegin_partial_solve_wit_2_pure -> OSInitHookBegin_partial_solve_wit_2_aux.

Definition OSInitHookBegin_partial_solve_wit_3 := 
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) (pstk: Z) (size: Z) (PreH1 : (size <= 0)) (PreH2 : (base = ( &( "OS_CPU_ExceptStk" ) ))) (PreH3 : (0 < base)) (PreH4 : ((base % ( 4 ) ) = 0)) (PreH5 : ((base + 4096 ) <= UINT_MAX)) (PreH6 : ((Zlength (initial)) = 1024)) (PreH7 : (0 <= size)) (PreH8 : (size <= 1024)) (PreH9 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |-> (Z.land (( &( "OS_CPU_ExceptStk" ) ) + (1024 * sizeof(UINT))) 4294967288))
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
|--
  “ (size <= 0) ” 
  &&  “ (base = ( &( "OS_CPU_ExceptStk" ) )) ” 
  &&  “ (0 < base) ” 
  &&  “ ((base % ( 4 ) ) = 0) ” 
  &&  “ ((base + 4096 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 <= size) ” 
  &&  “ (size <= 1024) ” 
  &&  “ (pstk = (base + (4 * (1024 - size ) ) )) ”
  &&  (R )
  **  (task_stack_clear_rep base initial (1024 - size ) )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |-> (Z.land (( &( "OS_CPU_ExceptStk" ) ) + (1024 * sizeof(UINT))) 4294967288))
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
.

Definition OSInitHookBegin_which_implies_wit_1 := 
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) ,
  (os_init_hook_begin_pre base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) initial R )
|--
  “ (0 < base) ” 
  &&  “ ((base % ( 4 ) ) = 0) ” 
  &&  “ ((base + 4096 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (initial)) = 1024) ”
  &&  (task_stack_clear_rep base initial 0 )
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |->_)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |->_)
  **  ((( &( "OSTmrCtr" ) )) # UShort  |->_)
  **  (R )
) \/
(
forall (R: Assertion) (initial: (@list (@option Z))) (base: Z) ,
  (os_init_hook_begin_pre base ( &( "OS_CPU_ExceptStkBase" ) ) ( &( "OS_CPU_ARM_DRegCnt" ) ) ( &( "OSTmrCtr" ) ) initial R )
|--
  EX (x_3: Z)  (x_2: Z)  (x: Z) ,
  “ (0 < base) ” 
  &&  “ ((base % ( 4 ) ) = 0) ” 
  &&  “ ((base + 4096 ) <= UINT_MAX) ” 
  &&  “ ((Zlength (initial)) = 1024) ”
  &&  ((( &( "OSTmrCtr" ) )) # UShort  |-> x_3)
  **  ((( &( "OS_CPU_ARM_DRegCnt" ) )) # UInt  |-> x_2)
  **  ((( &( "OS_CPU_ExceptStkBase" ) )) # Ptr  |-> x)
  **  (task_stack_clear_rep base initial 0 )
  **  (R )
).

Definition OSInitHookBegin_which_implies_wit_2 := 
(
forall (initial: (@list (@option Z))) (base: Z) (size: Z) (pstk: Z) (PreH1 : ((Zlength (initial)) = 1024)) (PreH2 : (0 < size)) (PreH3 : (size <= 1024)) (PreH4 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (task_stack_clear_rep base initial (1024 - size ) )
|--
  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 < size) ” 
  &&  “ (size <= 1024) ” 
  &&  “ (pstk = (base + (4 * (1024 - size ) ) )) ”
  &&  ((pstk) # UInt  |->_)
  **  (os_init_hook_begin_stack_cell_rest base initial (1024 - size ) )
) \/
(
forall (initial: (@list (@option Z))) (base: Z) (size: Z) (pstk: Z) (PreH1 : ((Zlength (initial)) = 1024)) (PreH2 : (0 < size)) (PreH3 : (size <= 1024)) (PreH4 : (pstk = (base + (4 * (1024 - size ) ) ))) ,
  (task_stack_clear_rep base initial (1024 - size ) )
|--
  EX (x: Z) ,
  “ ((Zlength (initial)) = 1024) ” 
  &&  “ (0 < size) ” 
  &&  “ (size <= 1024) ” 
  &&  “ (pstk = (base + (4 * (1024 - size ) ) )) ”
  &&  ((pstk) # UInt  |-> x)
  **  (os_init_hook_begin_stack_cell_rest base initial (1024 - size ) )
).

Module Type VC_Correct.


Axiom proof_of_OSInitHookBegin_safety_wit_1 : OSInitHookBegin_safety_wit_1.
Axiom proof_of_OSInitHookBegin_safety_wit_2 : OSInitHookBegin_safety_wit_2.
Axiom proof_of_OSInitHookBegin_entail_wit_1 : OSInitHookBegin_entail_wit_1.
Axiom proof_of_OSInitHookBegin_entail_wit_2 : OSInitHookBegin_entail_wit_2.
Axiom proof_of_OSInitHookBegin_return_wit_1 : OSInitHookBegin_return_wit_1.
Axiom proof_of_OSInitHookBegin_partial_solve_wit_1 : OSInitHookBegin_partial_solve_wit_1.
Axiom proof_of_OSInitHookBegin_partial_solve_wit_2_pure : OSInitHookBegin_partial_solve_wit_2_pure.
Axiom proof_of_OSInitHookBegin_partial_solve_wit_2 : OSInitHookBegin_partial_solve_wit_2.
Axiom proof_of_OSInitHookBegin_partial_solve_wit_3 : OSInitHookBegin_partial_solve_wit_3.
Axiom proof_of_OSInitHookBegin_which_implies_wit_1 : OSInitHookBegin_which_implies_wit_1.
Axiom proof_of_OSInitHookBegin_which_implies_wit_2 : OSInitHookBegin_which_implies_wit_2.

End VC_Correct.
