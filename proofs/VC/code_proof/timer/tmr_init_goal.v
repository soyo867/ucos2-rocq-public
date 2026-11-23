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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_task_timer_phase_spec.
Import TaskStateDef SchedStateDef UCOS2_C_Rules.
Require Import Ucos2Verify.VC.code.timer.spec.tmr_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.mem_clr_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_api_spec.
Local Open Scope sac.

(*----- Function OSTmr_Init -----*)

Definition OSTmr_Init_safety_wit_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Init_safety_wit_2 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Init_safety_wit_3 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH2 : ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) (PreH3 : (ix < (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ptmr2" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Init_safety_wit_4 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH3 : (ix >= (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Init_safety_wit_5 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH3 : (ix >= (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Init_safety_wit_6 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH2 : (ix = 15)) (PreH3 : (ix >= (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 16)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmr_Init_entail_wit_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) 0 )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 15) ”
  &&  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) 0 )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
.

Definition OSTmr_Init_entail_wit_2 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH2 : ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) (PreH3 : (ix < (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ptmr2" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) (ix + 1 ) )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= (ix + 1 )) ” 
  &&  “ ((ix + 1 ) <= 15) ”
  &&  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) (ix + 1 ) )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
.

Definition OSTmr_Init_return_wit_1 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (tmr_init_post p call X )
  **  (coq_prop (tmr_init_source_binding (p)) )
|--
  (tmr_init_post p call X )
) \/
(
forall (LitMap: (string -> Z)) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (tmr_init_source_binding (p)) )
|--
  TT && emp 
).

Definition OSTmr_Init_return_wit_1_split_goal_spatial := 
forall (LitMap: (string -> Z)) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (tmr_init_source_binding (p)) )
|--
  TT && emp 
.

Definition OSTmr_Init_partial_solve_wit_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (LitMap = (tmr_init_literals (p)))) ,
  (tmr_init_pre p call initial X )
|--
  “ (LitMap = (tmr_init_literals (p))) ”
  &&  (tmr_init_pre p call initial X )
.

Definition OSTmr_Init_partial_solve_wit_2_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= (sizeof( "os_tmr" ) * 16)) ” 
  &&  “ ((sizeof( "os_tmr" ) * 16) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OSTmr_Init_partial_solve_wit_2_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
|--
  “ (0 <= (sizeof( "os_tmr" ) * 16)) ” 
  &&  “ ((sizeof( "os_tmr" ) * 16) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (sizeof( "os_tmr" ) * 16)) ” 
  &&  “ ((sizeof( "os_tmr" ) * 16) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (sizeof( "os_tmr_wheel" ) * 7)) ” 
  &&  “ ((sizeof( "os_tmr_wheel" ) * 7) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ”
  &&  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
.

Definition OSTmr_Init_partial_solve_wit_2 := OSTmr_Init_partial_solve_wit_2_pure -> OSTmr_Init_partial_solve_wit_2_aux.

Definition OSTmr_Init_partial_solve_wit_3_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (0 <= (sizeof( "os_tmr_wheel" ) * 7)) ” 
  &&  “ ((sizeof( "os_tmr_wheel" ) * 7) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OSTmr_Init_partial_solve_wit_3_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
|--
  “ (0 <= (sizeof( "os_tmr_wheel" ) * 7)) ” 
  &&  “ ((sizeof( "os_tmr_wheel" ) * 7) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (sizeof( "os_tmr" ) * 16)) ” 
  &&  “ ((sizeof( "os_tmr" ) * 16) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (sizeof( "os_tmr_wheel" ) * 7)) ” 
  &&  “ ((sizeof( "os_tmr_wheel" ) * 7) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ”
  &&  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
.

Definition OSTmr_Init_partial_solve_wit_3 := OSTmr_Init_partial_solve_wit_3_pure -> OSTmr_Init_partial_solve_wit_3_aux.

Definition OSTmr_Init_partial_solve_wit_4_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |->_)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ix" ) )) # UShort  |->_)
|--
  “ (LitMap = (tmr_init_literals (p))) ”
.

Definition OSTmr_Init_partial_solve_wit_4_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= (sizeof( "os_tmr" ) * 16))) (PreH2 : ((sizeof( "os_tmr" ) * 16) <= 65535)) (PreH3 : (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))) (PreH4 : (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX)) (PreH5 : (0 <= (sizeof( "os_tmr_wheel" ) * 7))) (PreH6 : ((sizeof( "os_tmr_wheel" ) * 7) <= 65535)) (PreH7 : (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))))) (PreH8 : (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX)) (PreH9 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= (sizeof( "os_tmr" ) * 16)) ” 
  &&  “ ((sizeof( "os_tmr" ) * 16) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (sizeof( "os_tmr_wheel" ) * 7)) ” 
  &&  “ ((sizeof( "os_tmr_wheel" ) * 7) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ”
  &&  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_post (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
.

Definition OSTmr_Init_partial_solve_wit_4 := OSTmr_Init_partial_solve_wit_4_pure -> OSTmr_Init_partial_solve_wit_4_aux.

Definition OSTmr_Init_partial_solve_wit_5_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix < (16 - 1 ))) (PreH2 : (LitMap = (tmr_init_literals (p)))) (PreH3 : (0 <= ix)) (PreH4 : (ix <= 15)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ptmr2" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
|--
  “ (0 <= ix) ” 
  &&  “ (ix < 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" )))) ”
.

Definition OSTmr_Init_partial_solve_wit_5_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix < (16 - 1 ))) (PreH2 : (LitMap = (tmr_init_literals (p)))) (PreH3 : (0 <= ix)) (PreH4 : (ix <= 15)) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (0 <= ix) ” 
  &&  “ (ix < 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" )))) ” 
  &&  “ (ix < (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
.

Definition OSTmr_Init_partial_solve_wit_5 := OSTmr_Init_partial_solve_wit_5_pure -> OSTmr_Init_partial_solve_wit_5_aux.

Definition OSTmr_Init_partial_solve_wit_6_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH2 : ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) (PreH3 : (ix < (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ptmr2" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  ((( &( "ix_next" ) )) # UShort  |-> (ix + 1 ))
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" )))) ”
.

Definition OSTmr_Init_partial_solve_wit_6_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH2 : ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) (PreH3 : (ix < (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix < 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" )))) ” 
  &&  “ (ix < (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
.

Definition OSTmr_Init_partial_solve_wit_6 := OSTmr_Init_partial_solve_wit_6_pure -> OSTmr_Init_partial_solve_wit_6_aux.

Definition OSTmr_Init_partial_solve_wit_7_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix >= (16 - 1 ))) (PreH2 : (LitMap = (tmr_init_literals (p)))) (PreH3 : (0 <= ix)) (PreH4 : (ix <= 15)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ” 
  &&  “ (ix >= 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ”
.

Definition OSTmr_Init_partial_solve_wit_7_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix >= (16 - 1 ))) (PreH2 : (LitMap = (tmr_init_literals (p)))) (PreH3 : (0 <= ix)) (PreH4 : (ix <= 15)) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ” 
  &&  “ (ix >= 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
.

Definition OSTmr_Init_partial_solve_wit_7 := OSTmr_Init_partial_solve_wit_7_pure -> OSTmr_Init_partial_solve_wit_7_aux.

Definition OSTmr_Init_partial_solve_wit_8_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH3 : (ix >= (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ” 
  &&  “ (ix >= 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ”
.

Definition OSTmr_Init_partial_solve_wit_8_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH3 : (ix >= (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
|--
  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ” 
  &&  “ (ix >= 15) ” 
  &&  “ ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&(((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
.

Definition OSTmr_Init_partial_solve_wit_8 := OSTmr_Init_partial_solve_wit_8_pure -> OSTmr_Init_partial_solve_wit_8_aux.

Definition OSTmr_Init_partial_solve_wit_9 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : ((( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))) = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH2 : (ix = 15)) (PreH3 : (ix >= (16 - 1 ))) (PreH4 : (LitMap = (tmr_init_literals (p)))) (PreH5 : (0 <= ix)) (PreH6 : (ix <= 15)) ,
  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 16)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
|--
  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 16)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
.

Definition OSTmr_Init_partial_solve_wit_10_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_sem_pre p call (tmr_init_after_pool (p) (initial)) true (tmr_init_sem_continuation (p) (call) (true) (X)) )
  **  (tmr_init_static_resources p )
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (1 = 1) ”
.

Definition OSTmr_Init_partial_solve_wit_10_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_sem_pre p call (tmr_init_after_pool (p) (initial)) true (tmr_init_sem_continuation (p) (call) (true) (X)) )
  **  (tmr_init_static_resources p )
|--
  “ (1 = 1) ” 
  &&  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (tmr_init_sem_pre p call (tmr_init_after_pool (p) (initial)) true (tmr_init_sem_continuation (p) (call) (true) (X)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
.

Definition OSTmr_Init_partial_solve_wit_10 := OSTmr_Init_partial_solve_wit_10_pure -> OSTmr_Init_partial_solve_wit_10_aux.

Definition OSTmr_Init_partial_solve_wit_11 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (returned: OsSchedCallContext) (current: UCOS2_Verify_State) (retval: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (tmr_init_sem_return_facts (p) (call) ((tmr_init_after_pool (p) (initial))) (true) ((tmr_init_sem_continuation (p) (call) (true) (X))) (retval) (returned) (current)) )
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> retval)
  **  (tmr_init_sem_return_frame p returned current true )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
|--
  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (coq_prop (tmr_init_sem_return_facts (p) (call) ((tmr_init_after_pool (p) (initial))) (true) ((tmr_init_sem_continuation (p) (call) (true) (X))) (retval) (returned) (current)) )
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> retval)
  **  (tmr_init_sem_return_frame p returned current true )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
.

Definition OSTmr_Init_partial_solve_wit_12_pure := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (lock_call: OsSchedCallContext) (lock_state: UCOS2_Verify_State) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (tmr_init_sem_pre p lock_call lock_state false (tmr_init_sem_continuation (p) (call) (false) (X)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
  **  ((( &( "ptmr1" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))
  **  ((( &( "ix" ) )) # UShort  |-> ix)
  **  ((( &( "ix_next" ) )) # UShort  |->_)
  **  ((( &( "ptmr2" ) )) # Ptr  |->_)
|--
  “ (0 = 0) ”
.

Definition OSTmr_Init_partial_solve_wit_12_aux := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (lock_call: OsSchedCallContext) (lock_state: UCOS2_Verify_State) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (tmr_init_sem_pre p lock_call lock_state false (tmr_init_sem_continuation (p) (call) (false) (X)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
|--
  “ (0 = 0) ” 
  &&  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (tmr_init_sem_pre p lock_call lock_state false (tmr_init_sem_continuation (p) (call) (false) (X)) )
  **  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
.

Definition OSTmr_Init_partial_solve_wit_12 := OSTmr_Init_partial_solve_wit_12_pure -> OSTmr_Init_partial_solve_wit_12_aux.

Definition OSTmr_Init_partial_solve_wit_13 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (lock_call: OsSchedCallContext) (lock_state: UCOS2_Verify_State) (returned: OsSchedCallContext) (current: UCOS2_Verify_State) (retval: Z) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (tmr_init_sem_return_facts (p) (lock_call) (lock_state) (false) ((tmr_init_sem_continuation (p) (call) (false) (X))) (retval) (returned) (current)) )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> retval)
  **  (tmr_init_sem_return_frame p returned current false )
  **  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_static_resources p )
|--
  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (coq_prop (tmr_init_sem_return_facts (p) (lock_call) (lock_state) (false) ((tmr_init_sem_continuation (p) (call) (false) (X))) (retval) (returned) (current)) )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> retval)
  **  (tmr_init_sem_return_frame p returned current false )
  **  (tmr_init_static_resources p )
  **  (coq_prop (tmr_init_source_binding (p)) )
.

Definition OSTmr_Init_partial_solve_wit_14 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (task_call: OsSchedCallContext) (task_state: UCOS2_Verify_State) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_pre p task_call task_state X )
  **  (coq_prop (tmr_init_source_binding (p)) )
|--
  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (tmr_init_task_pre p task_call task_state X )
  **  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
.

Definition OSTmr_Init_partial_solve_wit_15 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (task_call: OsSchedCallContext) (task_state: UCOS2_Verify_State) (PreH1 : (ix = 15)) (PreH2 : (ix >= (16 - 1 ))) (PreH3 : (LitMap = (tmr_init_literals (p)))) (PreH4 : (0 <= ix)) (PreH5 : (ix <= 15)) ,
  (tmr_init_task_return p task_call task_state X )
  **  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (coq_prop (tmr_init_source_binding (p)) )
|--
  “ (ix = 15) ” 
  &&  “ (ix >= (16 - 1 )) ” 
  &&  “ (LitMap = (tmr_init_literals (p))) ” 
  &&  “ (0 <= ix) ” 
  &&  “ (ix <= 15) ”
  &&  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_return p task_call task_state X )
  **  (coq_prop (tmr_init_source_binding (p)) )
.

Definition OSTmr_Init_which_implies_wit_1 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  “ (0 <= (sizeof( "os_tmr" ) * 16)) ” 
  &&  “ ((sizeof( "os_tmr" ) * 16) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (sizeof( "os_tmr_wheel" ) * 7)) ” 
  &&  “ ((sizeof( "os_tmr_wheel" ) * 7) <= 65535) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ”
  &&  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ” 
  &&  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ” 
  &&  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ”
  &&  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
).

Definition OSTmr_Init_which_implies_wit_1_split_goal_1 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  “ (((( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) + ((sizeof( "os_tmr_wheel" ) * 7) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OSTmr_Init_which_implies_wit_1_split_goal_2 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  “ (0 <= (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" )))) ”
.

Definition OSTmr_Init_which_implies_wit_1_split_goal_3 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  “ (((( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) + ((sizeof( "os_tmr" ) * 16) * sizeof(UCHAR))) <= UINT_MAX) ”
.

Definition OSTmr_Init_which_implies_wit_1_split_goal_4 := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  “ (0 <= (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" )))) ”
.

Definition OSTmr_Init_which_implies_wit_1_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_pre p call initial X )
|--
  (mem_clr_pre (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_pre (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
.

Definition OSTmr_Init_which_implies_wit_2 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_post (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
|--
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) 0 )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_post (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
|--
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) 0 )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
).

Definition OSTmr_Init_which_implies_wit_2_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (LitMap = (tmr_init_literals (p)))) ,
  (mem_clr_post (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))) (sizeof( "os_tmr" ) * 16) )
  **  (mem_clr_post (( &( "OSTmrWheelTbl" ) ) + (0 * sizeof( "os_tmr_wheel" ))) (sizeof( "os_tmr_wheel" ) * 7) )
  **  (tmr_init_globals (tmr_init_sg (p)) 0 0 0 0 0 0 )
  **  (tmr_init_pool_context p call initial X )
|--
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) 0 )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
.

Definition OSTmr_Init_which_implies_wit_3 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (ptmr2: Z) (PreH1 : (0 <= ix)) (PreH2 : (ix < 15)) (PreH3 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH4 : (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" )))) ”
  &&  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (ptmr2: Z) (PreH1 : (0 <= ix)) (PreH2 : (ix < 15)) (PreH3 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH4 : (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
).

Definition OSTmr_Init_which_implies_wit_3_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (ptmr2: Z) (PreH1 : (0 <= ix)) (PreH2 : (ix < 15)) (PreH3 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH4 : (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
.

Definition OSTmr_Init_which_implies_wit_4 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (ptmr2: Z) (PreH1 : (LitMap = (tmr_init_literals (p)))) (PreH2 : (0 <= ix)) (PreH3 : (ix < 15)) (PreH4 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH5 : (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) ,
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> ptmr2)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ” 
  &&  “ (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" )))) ”
  &&  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) (ix + 1 ) )
  **  (tmr_init_pool_literal_residual p call initial X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (ptmr2: Z) (PreH1 : (LitMap = (tmr_init_literals (p)))) (PreH2 : (0 <= ix)) (PreH3 : (ix < 15)) (PreH4 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH5 : (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) ,
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> ptmr2)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) (ix + 1 ) )
  **  (tmr_init_pool_literal_residual p call initial X )
).

Definition OSTmr_Init_which_implies_wit_4_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (ptmr2: Z) (PreH1 : (LitMap = (tmr_init_literals (p)))) (PreH2 : (0 <= ix)) (PreH3 : (ix < 15)) (PreH4 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) (PreH5 : (ptmr2 = (( &( "OSTmrTbl" ) ) + ((ix + 1 ) * sizeof( "os_tmr" ))))) ,
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> ptmr2)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) (ix + 1 ) )
  **  (tmr_init_pool_literal_residual p call initial X )
.

Definition OSTmr_Init_which_implies_wit_5 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (PreH1 : (0 <= ix)) (PreH2 : (ix <= 15)) (PreH3 : (ix >= 15)) (PreH4 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (ix = 15) ” 
  &&  “ (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ”
  &&  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (PreH1 : (0 <= ix)) (PreH2 : (ix <= 15)) (PreH3 : (ix >= 15)) (PreH4 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
).

Definition OSTmr_Init_which_implies_wit_5_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (PreH1 : (0 <= ix)) (PreH2 : (ix <= 15)) (PreH3 : (ix >= 15)) (PreH4 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) ,
  (tmr_init_loop (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> 0)
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (tmr_init_pool_literal_residual p call initial X )
.

Definition OSTmr_Init_which_implies_wit_6 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (PreH1 : (LitMap = (tmr_init_literals (p)))) (PreH2 : (0 <= ix)) (PreH3 : (ix <= 15)) (PreH4 : (ix >= 15)) (PreH5 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) ,
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  “ (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" )))) ”
  &&  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (PreH1 : (LitMap = (tmr_init_literals (p)))) (PreH2 : (0 <= ix)) (PreH3 : (ix <= 15)) (PreH4 : (ix >= 15)) (PreH5 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) ,
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
).

Definition OSTmr_Init_which_implies_wit_6_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (ix: Z) (ptmr1: Z) (PreH1 : (LitMap = (tmr_init_literals (p)))) (PreH2 : (0 <= ix)) (PreH3 : (ix <= 15)) (PreH4 : (ix >= 15)) (PreH5 : (ptmr1 = (( &( "OSTmrTbl" ) ) + (ix * sizeof( "os_tmr" ))))) ,
  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> 100)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrNext")) # Ptr  |-> 0)
  **  ((&((ptmr1)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_init_slot_context (tmr_init_sg (p)) (tmr_init_question (p)) ix )
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (GlobalStrings_missing LitMap (tmr_init_missing_literals (p)) )
  **  (tmr_init_pool_literal_residual p call initial X )
|--
  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
.

Definition OSTmr_Init_which_implies_wit_7 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) ,
  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 16)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
|--
  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_sem_pre p call (tmr_init_after_pool (p) (initial)) true (tmr_init_sem_continuation (p) (call) (true) (X)) )
  **  (tmr_init_static_resources p )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) ,
  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 16)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
|--
  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_sem_pre p call (tmr_init_after_pool (p) (initial)) true (tmr_init_sem_continuation (p) (call) (true) (X)) )
  **  (tmr_init_static_resources p )
).

Definition OSTmr_Init_which_implies_wit_7_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (PreH1 : (0 <= UINT_MAX)) (PreH2 : (0 >= 0)) ,
  (tmr_init_globals_context (tmr_init_sg (p)) (tmr_init_question (p)) )
  **  ((( &( "OSTmrTime" ) )) # UInt  |-> 0)
  **  ((( &( "OSTmrUsed" ) )) # UShort  |-> 0)
  **  ((( &( "OSTmrFree" ) )) # UShort  |-> 16)
  **  ((( &( "OSTmrFreeList" ) )) # Ptr  |-> (( &( "OSTmrTbl" ) ) + (0 * sizeof( "os_tmr" ))))
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> 0)
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> 0)
  **  (tmr_init_pool_context p call initial X )
|--
  (coq_prop (tmr_init_source_binding (p)) )
  **  (tmr_init_sem_pre p call (tmr_init_after_pool (p) (initial)) true (tmr_init_sem_continuation (p) (call) (true) (X)) )
  **  (tmr_init_static_resources p )
.

Definition OSTmr_Init_which_implies_wit_8 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (lock_result: Z) (current: UCOS2_Verify_State) (returned: OsSchedCallContext) ,
  (coq_prop (tmr_init_sem_return_facts (p) (call) ((tmr_init_after_pool (p) (initial))) (true) ((tmr_init_sem_continuation (p) (call) (true) (X))) (lock_result) (returned) (current)) )
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> lock_result)
  **  (tmr_init_sem_return_frame p returned current true )
|--
  EX (lock_state: UCOS2_Verify_State)  (lock_call: OsSchedCallContext) ,
  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (tmr_init_sem_pre p lock_call lock_state false (tmr_init_sem_continuation (p) (call) (false) (X)) )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (initial: UCOS2_Verify_State) (call: OsSchedCallContext) (p: TmrInitContext) (lock_result: Z) (current: UCOS2_Verify_State) (returned: OsSchedCallContext) ,
  (coq_prop (tmr_init_sem_return_facts (p) (call) ((tmr_init_after_pool (p) (initial))) (true) ((tmr_init_sem_continuation (p) (call) (true) (X))) (lock_result) (returned) (current)) )
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> lock_result)
  **  (tmr_init_sem_return_frame p returned current true )
|--
  EX (lock_state: UCOS2_Verify_State)  (lock_call: OsSchedCallContext) ,
  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (tmr_init_sem_pre p lock_call lock_state false (tmr_init_sem_continuation (p) (call) (false) (X)) )
).

Definition OSTmr_Init_which_implies_wit_9 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (call: OsSchedCallContext) (p: TmrInitContext) (lock_call: OsSchedCallContext) (lock_state: UCOS2_Verify_State) (returned: OsSchedCallContext) (current: UCOS2_Verify_State) (signal_result: Z) ,
  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (coq_prop (tmr_init_sem_return_facts (p) (lock_call) (lock_state) (false) ((tmr_init_sem_continuation (p) (call) (false) (X))) (signal_result) (returned) (current)) )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> signal_result)
  **  (tmr_init_sem_return_frame p returned current false )
  **  (tmr_init_static_resources p )
|--
  EX (task_state: UCOS2_Verify_State)  (task_call: OsSchedCallContext) ,
  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_pre p task_call task_state X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (call: OsSchedCallContext) (p: TmrInitContext) (lock_call: OsSchedCallContext) (lock_state: UCOS2_Verify_State) (returned: OsSchedCallContext) (current: UCOS2_Verify_State) (signal_result: Z) ,
  (coq_prop (task_tcb_init_stack_same_call (lock_call) (call)) )
  **  (coq_prop (tmr_init_sem_return_facts (p) (lock_call) (lock_state) (false) ((tmr_init_sem_continuation (p) (call) (false) (X))) (signal_result) (returned) (current)) )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> signal_result)
  **  (tmr_init_sem_return_frame p returned current false )
  **  (tmr_init_static_resources p )
|--
  EX (task_state: UCOS2_Verify_State)  (task_call: OsSchedCallContext) ,
  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_pre p task_call task_state X )
).

Definition OSTmr_Init_which_implies_wit_10 := 
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (call: OsSchedCallContext) (p: TmrInitContext) (task_call: OsSchedCallContext) (task_state: UCOS2_Verify_State) ,
  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_return p task_call task_state X )
|--
  (tmr_init_post p call X )
) \/
(
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (call: OsSchedCallContext) (p: TmrInitContext) (task_call: OsSchedCallContext) (task_state: UCOS2_Verify_State) ,
  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_return p task_call task_state X )
|--
  (tmr_init_post p call X )
).

Definition OSTmr_Init_which_implies_wit_10_split_goal_spatial := 
forall (X: (unit -> (UCOS2_Verify_State -> Prop))) (call: OsSchedCallContext) (p: TmrInitContext) (task_call: OsSchedCallContext) (task_state: UCOS2_Verify_State) ,
  (coq_prop (task_tcb_init_stack_same_call (task_call) (call)) )
  **  (tmr_init_task_return p task_call task_state X )
|--
  (tmr_init_post p call X )
.

Definition OSTmr_InitTask_derive_timer_init_spec_by_phase_spec := 
forall (X_timer_init_spec: (unit -> (UCOS2_Verify_State -> Prop))) (before_timer_init_spec: UCOS2_Verify_State) (call_timer_init_spec: OsSchedCallContext) (p_timer_init_spec: TmrInitContext) ,
  (tmr_init_task_pre p_timer_init_spec call_timer_init_spec before_timer_init_spec X_timer_init_spec )
|--
EX (environment_phase_spec: TaskStackCallEnvironment) (critical_phase_spec: CriticalRegionResources) (saved_local_phase_spec: (Armv7aContinuation -> Assertion)) (sg_phase_spec: StableGlobVars) (entry_phase_spec: Z) (base_phase_spec: Z) (task_return_phase_spec: Z) (mask_phase_spec: Z) (lower_phase_spec: (@list (@option Z))) (old_frame_phase_spec: (@list (@option Z))) (upper_phase_spec: (@list (@option Z))) (call_phase_spec: OsSchedCallContext) (initial_phase_spec: UCOS2_Verify_State) (LitMap_phase_spec: (string -> Z)) (literals_phase_spec: (@list string)) (X_phase_spec: (unit -> (UCOS2_Verify_State -> Prop))) ,
  (“ (entry_phase_spec = ( &( "OSTmr_Task" ) )) ” 
  &&  “ (base_phase_spec = ( &( "OSTmrTaskStk" ) )) ” 
  &&  “ (task_return_phase_spec = ( &( "OS_TaskReturn" ) )) ” 
  &&  “ (task_create_stack_global_addresses sg_phase_spec ( &( "OSIntNesting" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRunning" ) ) ) ” 
  &&  “ (task_tcb_init_global_addresses sg_phase_spec ( &( "OSTCBFreeList" ) ) ( &( "OSTCBList" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ( &( "OSTaskCtr" ) ) ) ” 
  &&  “ (os_sched_global_addresses sg_phase_spec ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (kernel_sched_ready_clients critical_phase_spec ) ” 
  &&  “ (kernel_tcb_stack_field_layout sg_phase_spec ) ” 
  &&  “ (task_create_runtime_call_input (tmr_init_task_create_args (entry_phase_spec) (base_phase_spec)) call_phase_spec initial_phase_spec ) ” 
  &&  “ (tmr_init_task_stopped initial_phase_spec ) ” 
  &&  “ (tmr_init_task_safe environment_phase_spec critical_phase_spec sg_phase_spec entry_phase_spec base_phase_spec task_return_phase_spec lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec initial_phase_spec X_phase_spec ) ”
  &&  (coq_prop (task_name_set_addresses (sg_phase_spec) (( &( "OSTCBPrioTbl" ) )) (( &( "OSTCBCur" ) )) (( &( "OSIntNesting" ) ))) )
  **  (coq_prop (task_name_set_layout (sg_phase_spec)) )
  **  (tmr_init_task_entry environment_phase_spec critical_phase_spec saved_local_phase_spec sg_phase_spec entry_phase_spec base_phase_spec task_return_phase_spec lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec literals_phase_spec initial_phase_spec ))
  **
  (((tmr_init_task_phase_post environment_phase_spec critical_phase_spec saved_local_phase_spec sg_phase_spec entry_phase_spec base_phase_spec task_return_phase_spec lower_phase_spec old_frame_phase_spec upper_phase_spec call_phase_spec mask_phase_spec LitMap_phase_spec literals_phase_spec initial_phase_spec X_phase_spec ))
  -*
  ((tmr_init_task_return p_timer_init_spec call_timer_init_spec before_timer_init_spec X_timer_init_spec )))
.

Definition OSSemCreate_derive_timer_signal_spec_by_source_spec := 
forall (cnt_pre: Z) (K_timer_signal_spec: (Z -> (UCOS2_Verify_State -> Prop))) (before_timer_signal_spec: UCOS2_Verify_State) (call_timer_signal_spec: OsSchedCallContext) (p_timer_signal_spec: TmrInitContext) ,
  “ (cnt_pre = 0) ”
  &&  (tmr_init_sem_pre p_timer_signal_spec call_timer_signal_spec before_timer_signal_spec false K_timer_signal_spec )
|--
EX (environment_source_spec: TaskStackCallEnvironment) (critical_source_spec: CriticalRegionResources) (sg_source_spec: StableGlobVars) (call_source_spec: OsSchedCallContext) (mask_source_spec: Z) (initial_source_spec: UCOS2_Verify_State) (X_source_spec: (Z -> (UCOS2_Verify_State -> Prop))) ,
  ((sem_create_api_call_pre environment_source_spec critical_source_spec sg_source_spec call_source_spec mask_source_spec initial_source_spec cnt_pre X_source_spec ))
  **
  ((EX retval_2,
  (sem_create_api_call_post environment_source_spec critical_source_spec sg_source_spec call_source_spec mask_source_spec retval_2 X_source_spec ))
  -*
  (EX returned current retval,
  (coq_prop (tmr_init_sem_return_facts (p_timer_signal_spec) (call_timer_signal_spec) (before_timer_signal_spec) (false) (K_timer_signal_spec) (retval) (returned) (current)) )
  **  ((( &( "OSTmrSemSignal" ) )) # Ptr  |-> (tmr_init_sem_current_value (false) (current)))
  **  (tmr_init_sem_return_frame p_timer_signal_spec returned current false )))
.

Definition OSSemCreate_derive_timer_lock_spec_by_source_spec := 
forall (cnt_pre: Z) (K_timer_lock_spec: (Z -> (UCOS2_Verify_State -> Prop))) (before_timer_lock_spec: UCOS2_Verify_State) (call_timer_lock_spec: OsSchedCallContext) (p_timer_lock_spec: TmrInitContext) ,
  “ (cnt_pre = 1) ”
  &&  (tmr_init_sem_pre p_timer_lock_spec call_timer_lock_spec before_timer_lock_spec true K_timer_lock_spec )
|--
EX (environment_source_spec: TaskStackCallEnvironment) (critical_source_spec: CriticalRegionResources) (sg_source_spec: StableGlobVars) (call_source_spec: OsSchedCallContext) (mask_source_spec: Z) (initial_source_spec: UCOS2_Verify_State) (X_source_spec: (Z -> (UCOS2_Verify_State -> Prop))) ,
  ((sem_create_api_call_pre environment_source_spec critical_source_spec sg_source_spec call_source_spec mask_source_spec initial_source_spec cnt_pre X_source_spec ))
  **
  ((EX retval_2,
  (sem_create_api_call_post environment_source_spec critical_source_spec sg_source_spec call_source_spec mask_source_spec retval_2 X_source_spec ))
  -*
  (EX returned current retval,
  (coq_prop (tmr_init_sem_return_facts (p_timer_lock_spec) (call_timer_lock_spec) (before_timer_lock_spec) (true) (K_timer_lock_spec) (retval) (returned) (current)) )
  **  ((( &( "OSTmrSem" ) )) # Ptr  |-> (tmr_init_sem_current_value (true) (current)))
  **  (tmr_init_sem_return_frame p_timer_lock_spec returned current true )))
.

Module Type VC_Correct.


Axiom proof_of_OSTmr_Init_safety_wit_1 : OSTmr_Init_safety_wit_1.
Axiom proof_of_OSTmr_Init_safety_wit_2 : OSTmr_Init_safety_wit_2.
Axiom proof_of_OSTmr_Init_safety_wit_3 : OSTmr_Init_safety_wit_3.
Axiom proof_of_OSTmr_Init_safety_wit_4 : OSTmr_Init_safety_wit_4.
Axiom proof_of_OSTmr_Init_safety_wit_5 : OSTmr_Init_safety_wit_5.
Axiom proof_of_OSTmr_Init_safety_wit_6 : OSTmr_Init_safety_wit_6.
Axiom proof_of_OSTmr_Init_entail_wit_1 : OSTmr_Init_entail_wit_1.
Axiom proof_of_OSTmr_Init_entail_wit_2 : OSTmr_Init_entail_wit_2.
Axiom proof_of_OSTmr_Init_return_wit_1 : OSTmr_Init_return_wit_1.
Axiom proof_of_OSTmr_Init_partial_solve_wit_1 : OSTmr_Init_partial_solve_wit_1.
Axiom proof_of_OSTmr_Init_partial_solve_wit_2_pure : OSTmr_Init_partial_solve_wit_2_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_2 : OSTmr_Init_partial_solve_wit_2.
Axiom proof_of_OSTmr_Init_partial_solve_wit_3_pure : OSTmr_Init_partial_solve_wit_3_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_3 : OSTmr_Init_partial_solve_wit_3.
Axiom proof_of_OSTmr_Init_partial_solve_wit_4_pure : OSTmr_Init_partial_solve_wit_4_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_4 : OSTmr_Init_partial_solve_wit_4.
Axiom proof_of_OSTmr_Init_partial_solve_wit_5_pure : OSTmr_Init_partial_solve_wit_5_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_5 : OSTmr_Init_partial_solve_wit_5.
Axiom proof_of_OSTmr_Init_partial_solve_wit_6_pure : OSTmr_Init_partial_solve_wit_6_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_6 : OSTmr_Init_partial_solve_wit_6.
Axiom proof_of_OSTmr_Init_partial_solve_wit_7_pure : OSTmr_Init_partial_solve_wit_7_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_7 : OSTmr_Init_partial_solve_wit_7.
Axiom proof_of_OSTmr_Init_partial_solve_wit_8_pure : OSTmr_Init_partial_solve_wit_8_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_8 : OSTmr_Init_partial_solve_wit_8.
Axiom proof_of_OSTmr_Init_partial_solve_wit_9 : OSTmr_Init_partial_solve_wit_9.
Axiom proof_of_OSTmr_Init_partial_solve_wit_10_pure : OSTmr_Init_partial_solve_wit_10_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_10 : OSTmr_Init_partial_solve_wit_10.
Axiom proof_of_OSTmr_Init_partial_solve_wit_11 : OSTmr_Init_partial_solve_wit_11.
Axiom proof_of_OSTmr_Init_partial_solve_wit_12_pure : OSTmr_Init_partial_solve_wit_12_pure.
Axiom proof_of_OSTmr_Init_partial_solve_wit_12 : OSTmr_Init_partial_solve_wit_12.
Axiom proof_of_OSTmr_Init_partial_solve_wit_13 : OSTmr_Init_partial_solve_wit_13.
Axiom proof_of_OSTmr_Init_partial_solve_wit_14 : OSTmr_Init_partial_solve_wit_14.
Axiom proof_of_OSTmr_Init_partial_solve_wit_15 : OSTmr_Init_partial_solve_wit_15.
Axiom proof_of_OSTmr_Init_which_implies_wit_1 : OSTmr_Init_which_implies_wit_1.
Axiom proof_of_OSTmr_Init_which_implies_wit_2 : OSTmr_Init_which_implies_wit_2.
Axiom proof_of_OSTmr_Init_which_implies_wit_3 : OSTmr_Init_which_implies_wit_3.
Axiom proof_of_OSTmr_Init_which_implies_wit_4 : OSTmr_Init_which_implies_wit_4.
Axiom proof_of_OSTmr_Init_which_implies_wit_5 : OSTmr_Init_which_implies_wit_5.
Axiom proof_of_OSTmr_Init_which_implies_wit_6 : OSTmr_Init_which_implies_wit_6.
Axiom proof_of_OSTmr_Init_which_implies_wit_7 : OSTmr_Init_which_implies_wit_7.
Axiom proof_of_OSTmr_Init_which_implies_wit_8 : OSTmr_Init_which_implies_wit_8.
Axiom proof_of_OSTmr_Init_which_implies_wit_9 : OSTmr_Init_which_implies_wit_9.
Axiom proof_of_OSTmr_Init_which_implies_wit_10 : OSTmr_Init_which_implies_wit_10.
Axiom proof_of_OSTmr_InitTask_derive_timer_init_spec_by_phase_spec : OSTmr_InitTask_derive_timer_init_spec_by_phase_spec.
Axiom proof_of_OSSemCreate_derive_timer_signal_spec_by_source_spec : OSSemCreate_derive_timer_signal_spec_by_source_spec.
Axiom proof_of_OSSemCreate_derive_timer_lock_spec_by_source_spec : OSSemCreate_derive_timer_lock_spec_by_source_spec.

End VC_Correct.
