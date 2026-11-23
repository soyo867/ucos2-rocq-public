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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_create_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmrCreate -----*)

Definition OSTmrCreate_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 131)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (dly_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 <> opt_pre)) (PreH13 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 130)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH3 : (dly_pre = (tmr_create_delay (args)))) (PreH4 : (period_pre = (tmr_create_period (args)))) (PreH5 : (opt_pre = (tmr_create_option (args)))) (PreH6 : (callback_pre = (tmr_create_callback (args)))) (PreH7 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH8 : (pname_pre = (tmr_create_name_argument (args)))) (PreH9 : (tmr_create_output_binding perr_pre perr0 )) (PreH10 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH11 : (2 <> opt_pre)) (PreH12 : (1 <> opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 132)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 139)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 139)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (period_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (dly_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 <> opt_pre)) (PreH25 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 134)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> 134)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (retval <> 0)) (PreH4 : (tmr_create_locked_facts env args before locked )) (PreH5 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH6 : (tmr_create_entry_facts env args before )) (PreH7 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : ((tmr_create_first_error (args) (before)) = None)) (PreH9 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH12 : (period_pre <= UINT_MAX)) (PreH13 : (dly_pre <= UINT_MAX)) (PreH14 : (period_pre >= 0)) (PreH15 : (dly_pre >= 0)) (PreH16 : (period_pre <> 0)) (PreH17 : (tmr_create_entry_facts env args before )) (PreH18 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH19 : (dly_pre = (tmr_create_delay (args)))) (PreH20 : (period_pre = (tmr_create_period (args)))) (PreH21 : (opt_pre = (tmr_create_option (args)))) (PreH22 : (callback_pre = (tmr_create_callback (args)))) (PreH23 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH24 : (pname_pre = (tmr_create_name_argument (args)))) (PreH25 : (tmr_create_output_binding perr_pre perr0 )) (PreH26 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH27 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_11 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (retval <> 0)) (PreH4 : (tmr_create_locked_facts env args before locked )) (PreH5 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH6 : (tmr_create_entry_facts env args before )) (PreH7 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH8 : ((tmr_create_first_error (args) (before)) = None)) (PreH9 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH12 : (period_pre <= UINT_MAX)) (PreH13 : (dly_pre <= UINT_MAX)) (PreH14 : (period_pre >= 0)) (PreH15 : (dly_pre >= 0)) (PreH16 : (dly_pre <> 0)) (PreH17 : (tmr_create_entry_facts env args before )) (PreH18 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH19 : (dly_pre = (tmr_create_delay (args)))) (PreH20 : (period_pre = (tmr_create_period (args)))) (PreH21 : (opt_pre = (tmr_create_option (args)))) (PreH22 : (callback_pre = (tmr_create_callback (args)))) (PreH23 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH24 : (pname_pre = (tmr_create_name_argument (args)))) (PreH25 : (tmr_create_output_binding perr_pre perr0 )) (PreH26 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH27 : (2 <> opt_pre)) (PreH28 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_12 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_safety_wit_13 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrCreate_entail_wit_1_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre <> 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre <= UINT_MAX)) (PreH2 : (dly_pre <= UINT_MAX)) (PreH3 : (period_pre >= 0)) (PreH4 : (dly_pre >= 0)) (PreH5 : (period_pre <> 0)) (PreH6 : (tmr_create_entry_facts env args before )) (PreH7 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH8 : (dly_pre = (tmr_create_delay (args)))) (PreH9 : (period_pre = (tmr_create_period (args)))) (PreH10 : (opt_pre = (tmr_create_option (args)))) (PreH11 : (callback_pre = (tmr_create_callback (args)))) (PreH12 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH13 : (pname_pre = (tmr_create_name_argument (args)))) (PreH14 : (tmr_create_output_binding perr_pre perr0 )) (PreH15 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH16 : (2 = opt_pre)) ,
  TT && emp 
|--
  “ ((tmr_create_argument_error (dly_pre) (period_pre) (2)) = None) ”
  &&  emp
).

Definition OSTmrCreate_entail_wit_1_1_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre <= UINT_MAX)) (PreH2 : (dly_pre <= UINT_MAX)) (PreH3 : (period_pre >= 0)) (PreH4 : (dly_pre >= 0)) (PreH5 : (period_pre <> 0)) (PreH6 : (tmr_create_entry_facts env args before )) (PreH7 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH8 : (dly_pre = (tmr_create_delay (args)))) (PreH9 : (period_pre = (tmr_create_period (args)))) (PreH10 : (opt_pre = (tmr_create_option (args)))) (PreH11 : (callback_pre = (tmr_create_callback (args)))) (PreH12 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH13 : (pname_pre = (tmr_create_name_argument (args)))) (PreH14 : (tmr_create_output_binding perr_pre perr0 )) (PreH15 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH16 : (2 = opt_pre)) ,
  ((tmr_create_argument_error (dly_pre) (period_pre) (2)) = None)
.

Definition OSTmrCreate_entail_wit_1_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (dly_pre <> 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 <> opt_pre)) (PreH13 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre <= UINT_MAX)) (PreH2 : (dly_pre <= UINT_MAX)) (PreH3 : (period_pre >= 0)) (PreH4 : (dly_pre >= 0)) (PreH5 : (dly_pre <> 0)) (PreH6 : (tmr_create_entry_facts env args before )) (PreH7 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH8 : (dly_pre = (tmr_create_delay (args)))) (PreH9 : (period_pre = (tmr_create_period (args)))) (PreH10 : (opt_pre = (tmr_create_option (args)))) (PreH11 : (callback_pre = (tmr_create_callback (args)))) (PreH12 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH13 : (pname_pre = (tmr_create_name_argument (args)))) (PreH14 : (tmr_create_output_binding perr_pre perr0 )) (PreH15 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH16 : (2 <> opt_pre)) (PreH17 : (1 = opt_pre)) ,
  TT && emp 
|--
  “ ((tmr_create_argument_error (dly_pre) (period_pre) (1)) = None) ”
  &&  emp
).

Definition OSTmrCreate_entail_wit_1_2_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre <= UINT_MAX)) (PreH2 : (dly_pre <= UINT_MAX)) (PreH3 : (period_pre >= 0)) (PreH4 : (dly_pre >= 0)) (PreH5 : (dly_pre <> 0)) (PreH6 : (tmr_create_entry_facts env args before )) (PreH7 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH8 : (dly_pre = (tmr_create_delay (args)))) (PreH9 : (period_pre = (tmr_create_period (args)))) (PreH10 : (opt_pre = (tmr_create_option (args)))) (PreH11 : (callback_pre = (tmr_create_callback (args)))) (PreH12 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH13 : (pname_pre = (tmr_create_name_argument (args)))) (PreH14 : (tmr_create_output_binding perr_pre perr0 )) (PreH15 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH16 : (2 <> opt_pre)) (PreH17 : (1 = opt_pre)) ,
  ((tmr_create_argument_error (dly_pre) (period_pre) (1)) = None)
.

Definition OSTmrCreate_entail_wit_2_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  TT && emp 
|--
  “ ((tmr_create_first_error (args) (before)) = None) ”
  &&  emp
).

Definition OSTmrCreate_entail_wit_2_1_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  ((tmr_create_first_error (args) (before)) = None)
.

Definition OSTmrCreate_entail_wit_2_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  TT && emp 
|--
  “ ((tmr_create_first_error (args) (before)) = None) ”
  &&  emp
).

Definition OSTmrCreate_entail_wit_2_2_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  ((tmr_create_first_error (args) (before)) = None)
.

Definition OSTmrCreate_return_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (period_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (period_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (period_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (dly_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 <> opt_pre)) (PreH34 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (dly_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 <> opt_pre)) (PreH34 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (dly_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 <> opt_pre)) (PreH34 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (period_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (period_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (period_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (dly_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 <> opt_pre)) (PreH32 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (dly_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 <> opt_pre)) (PreH32 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (dly_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 <> opt_pre)) (PreH32 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |-> 0)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 retval X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 134)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 134)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 134)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_6 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 134)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 134)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  (os_sched_unlock_post (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 134)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_7 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (period_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_8 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) > 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH4 : (period_pre <= UINT_MAX)) (PreH5 : (dly_pre <= UINT_MAX)) (PreH6 : (period_pre >= 0)) (PreH7 : (dly_pre >= 0)) (PreH8 : (dly_pre <> 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH11 : (dly_pre = (tmr_create_delay (args)))) (PreH12 : (period_pre = (tmr_create_period (args)))) (PreH13 : (opt_pre = (tmr_create_option (args)))) (PreH14 : (callback_pre = (tmr_create_callback (args)))) (PreH15 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH16 : (pname_pre = (tmr_create_name_argument (args)))) (PreH17 : (tmr_create_output_binding perr_pre perr0 )) (PreH18 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH19 : (2 <> opt_pre)) (PreH20 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 139)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_9 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH3 : (dly_pre = (tmr_create_delay (args)))) (PreH4 : (period_pre = (tmr_create_period (args)))) (PreH5 : (opt_pre = (tmr_create_option (args)))) (PreH6 : (callback_pre = (tmr_create_callback (args)))) (PreH7 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH8 : (pname_pre = (tmr_create_name_argument (args)))) (PreH9 : (tmr_create_output_binding perr_pre perr0 )) (PreH10 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH11 : (2 <> opt_pre)) (PreH12 : (1 <> opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 132)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH3 : (dly_pre = (tmr_create_delay (args)))) (PreH4 : (period_pre = (tmr_create_period (args)))) (PreH5 : (opt_pre = (tmr_create_option (args)))) (PreH6 : (callback_pre = (tmr_create_callback (args)))) (PreH7 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH8 : (pname_pre = (tmr_create_name_argument (args)))) (PreH9 : (tmr_create_output_binding perr_pre perr0 )) (PreH10 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH11 : (2 <> opt_pre)) (PreH12 : (1 <> opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 132)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_9_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH3 : (dly_pre = (tmr_create_delay (args)))) (PreH4 : (period_pre = (tmr_create_period (args)))) (PreH5 : (opt_pre = (tmr_create_option (args)))) (PreH6 : (callback_pre = (tmr_create_callback (args)))) (PreH7 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH8 : (pname_pre = (tmr_create_name_argument (args)))) (PreH9 : (tmr_create_output_binding perr_pre perr0 )) (PreH10 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH11 : (2 <> opt_pre)) (PreH12 : (1 <> opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 132)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_10 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (dly_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 <> opt_pre)) (PreH13 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 130)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (dly_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 <> opt_pre)) (PreH13 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 130)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_10_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (dly_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 <> opt_pre)) (PreH13 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 130)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_return_wit_11 := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 131)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 131)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_return_wit_11_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (period_pre = 0)) (PreH2 : (tmr_create_entry_facts env args before )) (PreH3 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH4 : (dly_pre = (tmr_create_delay (args)))) (PreH5 : (period_pre = (tmr_create_period (args)))) (PreH6 : (opt_pre = (tmr_create_option (args)))) (PreH7 : (callback_pre = (tmr_create_callback (args)))) (PreH8 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH9 : (pname_pre = (tmr_create_name_argument (args)))) (PreH10 : (tmr_create_output_binding perr_pre perr0 )) (PreH11 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH12 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |-> 131)
  **  (tmr_create_global_strings env LitMap )
|--
  (tmr_create_api_post env args before perr0 0 X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (dly_pre = (tmr_create_delay (args)))) (PreH2 : (period_pre = (tmr_create_period (args)))) (PreH3 : (opt_pre = (tmr_create_option (args)))) (PreH4 : (callback_pre = (tmr_create_callback (args)))) (PreH5 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH6 : (pname_pre = (tmr_create_name_argument (args)))) (PreH7 : (tmr_create_output_binding perr_pre perr0 )) (PreH8 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) ,
  (tmr_create_api_pre env args before perr_pre X )
  **  (tmr_create_global_strings env LitMap )
|--
  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ”
  &&  (tmr_create_api_pre env args before perr_pre X )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH2 : (period_pre <= UINT_MAX)) (PreH3 : (dly_pre <= UINT_MAX)) (PreH4 : (period_pre >= 0)) (PreH5 : (dly_pre >= 0)) (PreH6 : (dly_pre <> 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH9 : (dly_pre = (tmr_create_delay (args)))) (PreH10 : (period_pre = (tmr_create_period (args)))) (PreH11 : (opt_pre = (tmr_create_option (args)))) (PreH12 : (callback_pre = (tmr_create_callback (args)))) (PreH13 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH14 : (pname_pre = (tmr_create_name_argument (args)))) (PreH15 : (tmr_create_output_binding perr_pre perr0 )) (PreH16 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH17 : (2 <> opt_pre)) (PreH18 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ”
.

Definition OSTmrCreate_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH2 : (period_pre <= UINT_MAX)) (PreH3 : (dly_pre <= UINT_MAX)) (PreH4 : (period_pre >= 0)) (PreH5 : (dly_pre >= 0)) (PreH6 : (dly_pre <> 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH9 : (dly_pre = (tmr_create_delay (args)))) (PreH10 : (period_pre = (tmr_create_period (args)))) (PreH11 : (opt_pre = (tmr_create_option (args)))) (PreH12 : (callback_pre = (tmr_create_callback (args)))) (PreH13 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH14 : (pname_pre = (tmr_create_name_argument (args)))) (PreH15 : (tmr_create_output_binding perr_pre perr0 )) (PreH16 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH17 : (2 <> opt_pre)) (PreH18 : (1 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_2 := OSTmrCreate_partial_solve_wit_2_pure -> OSTmrCreate_partial_solve_wit_2_aux.

Definition OSTmrCreate_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH2 : (period_pre <= UINT_MAX)) (PreH3 : (dly_pre <= UINT_MAX)) (PreH4 : (period_pre >= 0)) (PreH5 : (dly_pre >= 0)) (PreH6 : (period_pre <> 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH9 : (dly_pre = (tmr_create_delay (args)))) (PreH10 : (period_pre = (tmr_create_period (args)))) (PreH11 : (opt_pre = (tmr_create_option (args)))) (PreH12 : (callback_pre = (tmr_create_callback (args)))) (PreH13 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH14 : (pname_pre = (tmr_create_name_argument (args)))) (PreH15 : (tmr_create_output_binding perr_pre perr0 )) (PreH16 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH17 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ”
.

Definition OSTmrCreate_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH2 : (period_pre <= UINT_MAX)) (PreH3 : (dly_pre <= UINT_MAX)) (PreH4 : (period_pre >= 0)) (PreH5 : (dly_pre >= 0)) (PreH6 : (period_pre <> 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH9 : (dly_pre = (tmr_create_delay (args)))) (PreH10 : (period_pre = (tmr_create_period (args)))) (PreH11 : (opt_pre = (tmr_create_option (args)))) (PreH12 : (callback_pre = (tmr_create_callback (args)))) (PreH13 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH14 : (pname_pre = (tmr_create_name_argument (args)))) (PreH15 : (tmr_create_output_binding perr_pre perr0 )) (PreH16 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH17 : (2 = opt_pre)) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_3 := OSTmrCreate_partial_solve_wit_3_pure -> OSTmrCreate_partial_solve_wit_3_aux.

Definition OSTmrCreate_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_first_error (args) (before)) = None)) (PreH2 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH5 : (period_pre <= UINT_MAX)) (PreH6 : (dly_pre <= UINT_MAX)) (PreH7 : (period_pre >= 0)) (PreH8 : (dly_pre >= 0)) (PreH9 : (dly_pre <> 0)) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH12 : (dly_pre = (tmr_create_delay (args)))) (PreH13 : (period_pre = (tmr_create_period (args)))) (PreH14 : (opt_pre = (tmr_create_option (args)))) (PreH15 : (callback_pre = (tmr_create_callback (args)))) (PreH16 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH17 : (pname_pre = (tmr_create_name_argument (args)))) (PreH18 : (tmr_create_output_binding perr_pre perr0 )) (PreH19 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH20 : (2 <> opt_pre)) (PreH21 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ”
.

Definition OSTmrCreate_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_first_error (args) (before)) = None)) (PreH2 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH5 : (period_pre <= UINT_MAX)) (PreH6 : (dly_pre <= UINT_MAX)) (PreH7 : (period_pre >= 0)) (PreH8 : (dly_pre >= 0)) (PreH9 : (dly_pre <> 0)) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH12 : (dly_pre = (tmr_create_delay (args)))) (PreH13 : (period_pre = (tmr_create_period (args)))) (PreH14 : (opt_pre = (tmr_create_option (args)))) (PreH15 : (callback_pre = (tmr_create_callback (args)))) (PreH16 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH17 : (pname_pre = (tmr_create_name_argument (args)))) (PreH18 : (tmr_create_output_binding perr_pre perr0 )) (PreH19 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH20 : (2 <> opt_pre)) (PreH21 : (1 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_4 := OSTmrCreate_partial_solve_wit_4_pure -> OSTmrCreate_partial_solve_wit_4_aux.

Definition OSTmrCreate_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_first_error (args) (before)) = None)) (PreH2 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH5 : (period_pre <= UINT_MAX)) (PreH6 : (dly_pre <= UINT_MAX)) (PreH7 : (period_pre >= 0)) (PreH8 : (dly_pre >= 0)) (PreH9 : (period_pre <> 0)) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH12 : (dly_pre = (tmr_create_delay (args)))) (PreH13 : (period_pre = (tmr_create_period (args)))) (PreH14 : (opt_pre = (tmr_create_option (args)))) (PreH15 : (callback_pre = (tmr_create_callback (args)))) (PreH16 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH17 : (pname_pre = (tmr_create_name_argument (args)))) (PreH18 : (tmr_create_output_binding perr_pre perr0 )) (PreH19 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH20 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ”
.

Definition OSTmrCreate_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : ((tmr_create_first_error (args) (before)) = None)) (PreH2 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH5 : (period_pre <= UINT_MAX)) (PreH6 : (dly_pre <= UINT_MAX)) (PreH7 : (period_pre >= 0)) (PreH8 : (dly_pre >= 0)) (PreH9 : (period_pre <> 0)) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH12 : (dly_pre = (tmr_create_delay (args)))) (PreH13 : (period_pre = (tmr_create_period (args)))) (PreH14 : (opt_pre = (tmr_create_option (args)))) (PreH15 : (callback_pre = (tmr_create_callback (args)))) (PreH16 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH17 : (pname_pre = (tmr_create_name_argument (args)))) (PreH18 : (tmr_create_output_binding perr_pre perr0 )) (PreH19 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH20 : (2 = opt_pre)) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_5 := OSTmrCreate_partial_solve_wit_5_pure -> OSTmrCreate_partial_solve_wit_5_aux.

Definition OSTmrCreate_partial_solve_wit_6_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (period_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 = opt_pre)) ,
  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (period_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 = opt_pre)) ,
  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_6 := OSTmrCreate_partial_solve_wit_6_pure -> OSTmrCreate_partial_solve_wit_6_aux.

Definition OSTmrCreate_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (dly_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 <> opt_pre)) (PreH23 : (1 = opt_pre)) ,
  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (dly_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 <> opt_pre)) (PreH23 : (1 = opt_pre)) ,
  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_7 := OSTmrCreate_partial_solve_wit_7_pure -> OSTmrCreate_partial_solve_wit_7_aux.

Definition OSTmrCreate_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (dly_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 <> opt_pre)) (PreH23 : (1 = opt_pre)) ,
  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ”
.

Definition OSTmrCreate_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (dly_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 <> opt_pre)) (PreH23 : (1 = opt_pre)) ,
  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_8 := OSTmrCreate_partial_solve_wit_8_pure -> OSTmrCreate_partial_solve_wit_8_aux.

Definition OSTmrCreate_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (period_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 = opt_pre)) ,
  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ”
.

Definition OSTmrCreate_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((tmr_create_first_error (args) (before)) = None)) (PreH4 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH7 : (period_pre <= UINT_MAX)) (PreH8 : (dly_pre <= UINT_MAX)) (PreH9 : (period_pre >= 0)) (PreH10 : (dly_pre >= 0)) (PreH11 : (period_pre <> 0)) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH14 : (dly_pre = (tmr_create_delay (args)))) (PreH15 : (period_pre = (tmr_create_period (args)))) (PreH16 : (opt_pre = (tmr_create_option (args)))) (PreH17 : (callback_pre = (tmr_create_callback (args)))) (PreH18 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH19 : (pname_pre = (tmr_create_name_argument (args)))) (PreH20 : (tmr_create_output_binding perr_pre perr0 )) (PreH21 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH22 : (2 = opt_pre)) ,
  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_9 := OSTmrCreate_partial_solve_wit_9_pure -> OSTmrCreate_partial_solve_wit_9_aux.

Definition OSTmrCreate_partial_solve_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (period_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 = opt_pre)) ,
  (tmr_alloc_low_pre head next prev used free )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_alloc_low_pre head next prev used free )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_11 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (dly_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 <> opt_pre)) (PreH25 : (1 = opt_pre)) ,
  (tmr_alloc_low_pre head next prev used free )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_alloc_low_pre head next prev used free )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (dly_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 <> opt_pre)) (PreH25 : (1 = opt_pre)) ,
  (tmr_alloc_low_post head next prev used free retval )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ”
.

Definition OSTmrCreate_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (dly_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 <> opt_pre)) (PreH25 : (1 = opt_pre)) ,
  (tmr_alloc_low_post head next prev used free retval )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_alloc_low_post head next prev used free retval )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_12 := OSTmrCreate_partial_solve_wit_12_pure -> OSTmrCreate_partial_solve_wit_12_aux.

Definition OSTmrCreate_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (period_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 = opt_pre)) ,
  (tmr_alloc_low_post head next prev used free retval )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ”
.

Definition OSTmrCreate_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH3 : (tmr_create_entry_facts env args before )) (PreH4 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH5 : ((tmr_create_first_error (args) (before)) = None)) (PreH6 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH9 : (period_pre <= UINT_MAX)) (PreH10 : (dly_pre <= UINT_MAX)) (PreH11 : (period_pre >= 0)) (PreH12 : (dly_pre >= 0)) (PreH13 : (period_pre <> 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH16 : (dly_pre = (tmr_create_delay (args)))) (PreH17 : (period_pre = (tmr_create_period (args)))) (PreH18 : (opt_pre = (tmr_create_option (args)))) (PreH19 : (callback_pre = (tmr_create_callback (args)))) (PreH20 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH21 : (pname_pre = (tmr_create_name_argument (args)))) (PreH22 : (tmr_create_output_binding perr_pre perr0 )) (PreH23 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH24 : (2 = opt_pre)) ,
  (tmr_alloc_low_post head next prev used free retval )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_alloc_low_post head next prev used free retval )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_13 := OSTmrCreate_partial_solve_wit_13_pure -> OSTmrCreate_partial_solve_wit_13_aux.

Definition OSTmrCreate_partial_solve_wit_14_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_pointer_null retval ) ” 
  &&  “ (tmr_create_pointer_null 0 ) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_pointer_null 0 ) ” 
  &&  “ (tmr_create_pointer_null 0 ) ”
).

Definition OSTmrCreate_partial_solve_wit_14_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_pointer_null 0 ) ”
.

Definition OSTmrCreate_partial_solve_wit_14_pure_split_goal_2 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_pointer_null 0 ) ”
.

Definition OSTmrCreate_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_pointer_null retval ) ” 
  &&  “ (tmr_create_pointer_null 0 ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_14 := OSTmrCreate_partial_solve_wit_14_pure -> OSTmrCreate_partial_solve_wit_14_aux.

Definition OSTmrCreate_partial_solve_wit_15_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_pointer_null retval ) ” 
  &&  “ (tmr_create_pointer_null 0 ) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_pointer_null 0 ) ” 
  &&  “ (tmr_create_pointer_null 0 ) ”
).

Definition OSTmrCreate_partial_solve_wit_15_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_pointer_null 0 ) ”
.

Definition OSTmrCreate_partial_solve_wit_15_pure_split_goal_2 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_pointer_null 0 ) ”
.

Definition OSTmrCreate_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval = 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_pointer_null retval ) ” 
  &&  “ (tmr_create_pointer_null 0 ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_15 := OSTmrCreate_partial_solve_wit_15_pure -> OSTmrCreate_partial_solve_wit_15_aux.

Definition OSTmrCreate_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_pointer_null retval ) ” 
  &&  “ (tmr_create_prefix env args before TmrCreateExhausted locked ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_16 := OSTmrCreate_partial_solve_wit_16_pure -> OSTmrCreate_partial_solve_wit_16_aux.

Definition OSTmrCreate_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (tmr_create_pointer_null retval )) (PreH2 : (tmr_create_prefix env args before TmrCreateExhausted locked )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (retval = 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_pointer_null retval ) ” 
  &&  “ (tmr_create_prefix env args before TmrCreateExhausted locked ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (retval = 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_17 := OSTmrCreate_partial_solve_wit_17_pure -> OSTmrCreate_partial_solve_wit_17_aux.

Definition OSTmrCreate_partial_solve_wit_18_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (retval <> 0) ”
.

Definition OSTmrCreate_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (dly_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 <> opt_pre)) (PreH26 : (1 = opt_pre)) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_18 := OSTmrCreate_partial_solve_wit_18_pure -> OSTmrCreate_partial_solve_wit_18_aux.

Definition OSTmrCreate_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (retval <> 0) ”
.

Definition OSTmrCreate_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (PreH1 : (retval <> 0)) (PreH2 : (tmr_create_locked_facts env args before locked )) (PreH3 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH4 : (tmr_create_entry_facts env args before )) (PreH5 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH6 : ((tmr_create_first_error (args) (before)) = None)) (PreH7 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_create_entry_facts env args before )) (PreH9 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH10 : (period_pre <= UINT_MAX)) (PreH11 : (dly_pre <= UINT_MAX)) (PreH12 : (period_pre >= 0)) (PreH13 : (dly_pre >= 0)) (PreH14 : (period_pre <> 0)) (PreH15 : (tmr_create_entry_facts env args before )) (PreH16 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH17 : (dly_pre = (tmr_create_delay (args)))) (PreH18 : (period_pre = (tmr_create_period (args)))) (PreH19 : (opt_pre = (tmr_create_option (args)))) (PreH20 : (callback_pre = (tmr_create_callback (args)))) (PreH21 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH22 : (pname_pre = (tmr_create_name_argument (args)))) (PreH23 : (tmr_create_output_binding perr_pre perr0 )) (PreH24 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH25 : (2 = opt_pre)) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) retval )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_19 := OSTmrCreate_partial_solve_wit_19_pure -> OSTmrCreate_partial_solve_wit_19_aux.

Definition OSTmrCreate_partial_solve_wit_20_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (retval <> 0)) (PreH3 : (tmr_create_locked_facts env args before locked )) (PreH4 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((tmr_create_first_error (args) (before)) = None)) (PreH8 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH11 : (period_pre <= UINT_MAX)) (PreH12 : (dly_pre <= UINT_MAX)) (PreH13 : (period_pre >= 0)) (PreH14 : (dly_pre >= 0)) (PreH15 : (dly_pre <> 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH18 : (dly_pre = (tmr_create_delay (args)))) (PreH19 : (period_pre = (tmr_create_period (args)))) (PreH20 : (opt_pre = (tmr_create_option (args)))) (PreH21 : (callback_pre = (tmr_create_callback (args)))) (PreH22 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH23 : (pname_pre = (tmr_create_name_argument (args)))) (PreH24 : (tmr_create_output_binding perr_pre perr0 )) (PreH25 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH26 : (2 <> opt_pre)) (PreH27 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (timer_private_rep (tmr_create_globals (env)) i private )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ”
.

Definition OSTmrCreate_partial_solve_wit_20_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (retval <> 0)) (PreH3 : (tmr_create_locked_facts env args before locked )) (PreH4 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((tmr_create_first_error (args) (before)) = None)) (PreH8 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH11 : (period_pre <= UINT_MAX)) (PreH12 : (dly_pre <= UINT_MAX)) (PreH13 : (period_pre >= 0)) (PreH14 : (dly_pre >= 0)) (PreH15 : (dly_pre <> 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH18 : (dly_pre = (tmr_create_delay (args)))) (PreH19 : (period_pre = (tmr_create_period (args)))) (PreH20 : (opt_pre = (tmr_create_option (args)))) (PreH21 : (callback_pre = (tmr_create_callback (args)))) (PreH22 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH23 : (pname_pre = (tmr_create_name_argument (args)))) (PreH24 : (tmr_create_output_binding perr_pre perr0 )) (PreH25 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH26 : (2 <> opt_pre)) (PreH27 : (1 = opt_pre)) ,
  (timer_inv (tmr_create_globals (env)) allocated )
  **  (timer_private_rep (tmr_create_globals (env)) i private )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (timer_private_rep (tmr_create_globals (env)) i private )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_20 := OSTmrCreate_partial_solve_wit_20_pure -> OSTmrCreate_partial_solve_wit_20_aux.

Definition OSTmrCreate_partial_solve_wit_21_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (retval <> 0)) (PreH3 : (tmr_create_locked_facts env args before locked )) (PreH4 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((tmr_create_first_error (args) (before)) = None)) (PreH8 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH11 : (period_pre <= UINT_MAX)) (PreH12 : (dly_pre <= UINT_MAX)) (PreH13 : (period_pre >= 0)) (PreH14 : (dly_pre >= 0)) (PreH15 : (period_pre <> 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH18 : (dly_pre = (tmr_create_delay (args)))) (PreH19 : (period_pre = (tmr_create_period (args)))) (PreH20 : (opt_pre = (tmr_create_option (args)))) (PreH21 : (callback_pre = (tmr_create_callback (args)))) (PreH22 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH23 : (pname_pre = (tmr_create_name_argument (args)))) (PreH24 : (tmr_create_output_binding perr_pre perr0 )) (PreH25 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH26 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (timer_private_rep (tmr_create_globals (env)) i private )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ”
.

Definition OSTmrCreate_partial_solve_wit_21_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (retval <> 0)) (PreH3 : (tmr_create_locked_facts env args before locked )) (PreH4 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH5 : (tmr_create_entry_facts env args before )) (PreH6 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((tmr_create_first_error (args) (before)) = None)) (PreH8 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH11 : (period_pre <= UINT_MAX)) (PreH12 : (dly_pre <= UINT_MAX)) (PreH13 : (period_pre >= 0)) (PreH14 : (dly_pre >= 0)) (PreH15 : (period_pre <> 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH18 : (dly_pre = (tmr_create_delay (args)))) (PreH19 : (period_pre = (tmr_create_period (args)))) (PreH20 : (opt_pre = (tmr_create_option (args)))) (PreH21 : (callback_pre = (tmr_create_callback (args)))) (PreH22 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH23 : (pname_pre = (tmr_create_name_argument (args)))) (PreH24 : (tmr_create_output_binding perr_pre perr0 )) (PreH25 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH26 : (2 = opt_pre)) ,
  (timer_inv (tmr_create_globals (env)) allocated )
  **  (timer_private_rep (tmr_create_globals (env)) i private )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (timer_private_rep (tmr_create_globals (env)) i private )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_21 := OSTmrCreate_partial_solve_wit_21_pure -> OSTmrCreate_partial_solve_wit_21_aux.

Definition OSTmrCreate_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre = 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ ((tmr_create_name_argument (args)) = 0) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ”
.

Definition OSTmrCreate_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre = 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ ((tmr_create_name_argument (args)) = 0) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_22 := OSTmrCreate_partial_solve_wit_22_pure -> OSTmrCreate_partial_solve_wit_22_aux.

Definition OSTmrCreate_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre = 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ ((tmr_create_name_argument (args)) = 0) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ”
.

Definition OSTmrCreate_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre = 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ ((tmr_create_name_argument (args)) = 0) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_23 := OSTmrCreate_partial_solve_wit_23_pure -> OSTmrCreate_partial_solve_wit_23_aux.

Definition OSTmrCreate_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ”
.

Definition OSTmrCreate_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_24 := OSTmrCreate_partial_solve_wit_24_pure -> OSTmrCreate_partial_solve_wit_24_aux.

Definition OSTmrCreate_partial_solve_wit_25_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ”
.

Definition OSTmrCreate_partial_solve_wit_25_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_25 := OSTmrCreate_partial_solve_wit_25_pure -> OSTmrCreate_partial_solve_wit_25_aux.

Definition OSTmrCreate_partial_solve_wit_26_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (pname_pre = (tmr_create_chosen_name (args))) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (pname_pre = (tmr_create_chosen_name (args))) ”
).

Definition OSTmrCreate_partial_solve_wit_26_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (pname_pre = (tmr_create_chosen_name (args))) ”
.

Definition OSTmrCreate_partial_solve_wit_26_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (dly_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 <> opt_pre)) (PreH29 : (1 = opt_pre)) ,
  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (pname_pre = (tmr_create_chosen_name (args))) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_create_delay (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_create_period (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_create_option (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (tmr_create_callback (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (tmr_create_callback_arg (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_create_chosen_name (args)))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_26 := OSTmrCreate_partial_solve_wit_26_pure -> OSTmrCreate_partial_solve_wit_26_aux.

Definition OSTmrCreate_partial_solve_wit_27_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (pname_pre = (tmr_create_chosen_name (args))) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (pname_pre = (tmr_create_chosen_name (args))) ”
).

Definition OSTmrCreate_partial_solve_wit_27_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (pname_pre = (tmr_create_chosen_name (args))) ”
.

Definition OSTmrCreate_partial_solve_wit_27_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (PreH1 : (pname_pre <> 0)) (PreH2 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH3 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH4 : (retval <> 0)) (PreH5 : (tmr_create_locked_facts env args before locked )) (PreH6 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH7 : (tmr_create_entry_facts env args before )) (PreH8 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((tmr_create_first_error (args) (before)) = None)) (PreH10 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH11 : (tmr_create_entry_facts env args before )) (PreH12 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH13 : (period_pre <= UINT_MAX)) (PreH14 : (dly_pre <= UINT_MAX)) (PreH15 : (period_pre >= 0)) (PreH16 : (dly_pre >= 0)) (PreH17 : (period_pre <> 0)) (PreH18 : (tmr_create_entry_facts env args before )) (PreH19 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH20 : (dly_pre = (tmr_create_delay (args)))) (PreH21 : (period_pre = (tmr_create_period (args)))) (PreH22 : (opt_pre = (tmr_create_option (args)))) (PreH23 : (callback_pre = (tmr_create_callback (args)))) (PreH24 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH25 : (pname_pre = (tmr_create_name_argument (args)))) (PreH26 : (tmr_create_output_binding perr_pre perr0 )) (PreH27 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH28 : (2 = opt_pre)) ,
  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> pname_pre)
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (pname_pre = (tmr_create_chosen_name (args))) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_create_delay (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_create_period (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_create_option (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (tmr_create_callback (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (tmr_create_callback_arg (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_create_chosen_name (args)))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_27 := OSTmrCreate_partial_solve_wit_27_pure -> OSTmrCreate_partial_solve_wit_27_aux.

Definition OSTmrCreate_partial_solve_wit_28_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ”
).

Definition OSTmrCreate_partial_solve_wit_28_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ”
.

Definition OSTmrCreate_partial_solve_wit_28_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (dly_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 <> opt_pre)) (PreH31 : (1 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_create_delay (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_create_period (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_create_option (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (tmr_create_callback (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (tmr_create_callback_arg (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_create_chosen_name (args)))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_28 := OSTmrCreate_partial_solve_wit_28_pure -> OSTmrCreate_partial_solve_wit_28_aux.

Definition OSTmrCreate_partial_solve_wit_29_pure := 
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ”
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ”
).

Definition OSTmrCreate_partial_solve_wit_29_pure_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ”
.

Definition OSTmrCreate_partial_solve_wit_29_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH3 : (pname_pre = 0)) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (retval <> 0)) (PreH7 : (tmr_create_locked_facts env args before locked )) (PreH8 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH9 : (tmr_create_entry_facts env args before )) (PreH10 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((tmr_create_first_error (args) (before)) = None)) (PreH12 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_create_entry_facts env args before )) (PreH14 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH15 : (period_pre <= UINT_MAX)) (PreH16 : (dly_pre <= UINT_MAX)) (PreH17 : (period_pre >= 0)) (PreH18 : (dly_pre >= 0)) (PreH19 : (period_pre <> 0)) (PreH20 : (tmr_create_entry_facts env args before )) (PreH21 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH22 : (dly_pre = (tmr_create_delay (args)))) (PreH23 : (period_pre = (tmr_create_period (args)))) (PreH24 : (opt_pre = (tmr_create_option (args)))) (PreH25 : (callback_pre = (tmr_create_callback (args)))) (PreH26 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH27 : (pname_pre = (tmr_create_name_argument (args)))) (PreH28 : (tmr_create_output_binding perr_pre perr0 )) (PreH29 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH30 : (2 = opt_pre)) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> dly_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> period_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> opt_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> callback_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> callback_arg_pre)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> ((LitMap (("?"%string))) + (0 * sizeof(CHAR))))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (((LitMap (("?"%string))) + (0 * sizeof(CHAR))) = (tmr_create_chosen_name (args))) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  ((&((retval)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_create_delay (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_create_period (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_create_option (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (tmr_create_callback (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (tmr_create_callback_arg (args)))
  **  ((&((retval)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_create_chosen_name (args)))
  **  (tmr_create_retained_fields retval (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_29 := OSTmrCreate_partial_solve_wit_29_pure -> OSTmrCreate_partial_solve_wit_29_aux.

Definition OSTmrCreate_partial_solve_wit_30_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (period_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_30_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (period_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 = opt_pre)) ,
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_30 := OSTmrCreate_partial_solve_wit_30_pure -> OSTmrCreate_partial_solve_wit_30_aux.

Definition OSTmrCreate_partial_solve_wit_31_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (dly_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 <> opt_pre)) (PreH34 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_31_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (literal_rest: Assertion) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH5 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) (PreH6 : (pname_pre = 0)) (PreH7 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH8 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH9 : (retval <> 0)) (PreH10 : (tmr_create_locked_facts env args before locked )) (PreH11 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH12 : (tmr_create_entry_facts env args before )) (PreH13 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH14 : ((tmr_create_first_error (args) (before)) = None)) (PreH15 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_create_entry_facts env args before )) (PreH17 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH18 : (period_pre <= UINT_MAX)) (PreH19 : (dly_pre <= UINT_MAX)) (PreH20 : (period_pre >= 0)) (PreH21 : (dly_pre >= 0)) (PreH22 : (dly_pre <> 0)) (PreH23 : (tmr_create_entry_facts env args before )) (PreH24 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH25 : (dly_pre = (tmr_create_delay (args)))) (PreH26 : (period_pre = (tmr_create_period (args)))) (PreH27 : (opt_pre = (tmr_create_option (args)))) (PreH28 : (callback_pre = (tmr_create_callback (args)))) (PreH29 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH30 : (pname_pre = (tmr_create_name_argument (args)))) (PreH31 : (tmr_create_output_binding perr_pre perr0 )) (PreH32 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH33 : (2 <> opt_pre)) (PreH34 : (1 = opt_pre)) ,
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ” 
  &&  “ (pname_pre = 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  (tmr_create_global_strings env LitMap )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrCreate_partial_solve_wit_31 := OSTmrCreate_partial_solve_wit_31_pure -> OSTmrCreate_partial_solve_wit_31_aux.

Definition OSTmrCreate_partial_solve_wit_32_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (period_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_32_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (period_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 = opt_pre)) ,
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (period_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 = opt_pre) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_32 := OSTmrCreate_partial_solve_wit_32_pure -> OSTmrCreate_partial_solve_wit_32_aux.

Definition OSTmrCreate_partial_solve_wit_33_pure := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (dly_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 <> opt_pre)) (PreH32 : (1 = opt_pre)) ,
  ((( &( "ptmr" ) )) # Ptr  |-> retval)
  **  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
  **  ((( &( "dly" ) )) # UInt  |-> dly_pre)
  **  ((( &( "period" ) )) # UInt  |-> period_pre)
  **  ((( &( "opt" ) )) # UChar  |-> opt_pre)
  **  ((( &( "callback" ) )) # Ptr  |-> callback_pre)
  **  ((( &( "callback_arg" ) )) # Ptr  |-> callback_arg_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_partial_solve_wit_33_aux := 
forall (perr_pre: Z) (pname_pre: Z) (callback_arg_pre: Z) (callback_pre: Z) (opt_pre: Z) (period_pre: Z) (dly_pre: Z) (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (LitMap: (string -> Z)) (perr0: Z) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (retval: Z) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (completion: UCOS2_Verify_State) (PreH1 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH2 : (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion )) (PreH3 : (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : (pname_pre <> 0)) (PreH5 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH6 : (tmr_create_allocated_facts env args before locked retval i private allocated )) (PreH7 : (retval <> 0)) (PreH8 : (tmr_create_locked_facts env args before locked )) (PreH9 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) (PreH10 : (tmr_create_entry_facts env args before )) (PreH11 : (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH12 : ((tmr_create_first_error (args) (before)) = None)) (PreH13 : ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0)) (PreH14 : (tmr_create_entry_facts env args before )) (PreH15 : ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None)) (PreH16 : (period_pre <= UINT_MAX)) (PreH17 : (dly_pre <= UINT_MAX)) (PreH18 : (period_pre >= 0)) (PreH19 : (dly_pre >= 0)) (PreH20 : (dly_pre <> 0)) (PreH21 : (tmr_create_entry_facts env args before )) (PreH22 : (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X )) (PreH23 : (dly_pre = (tmr_create_delay (args)))) (PreH24 : (period_pre = (tmr_create_period (args)))) (PreH25 : (opt_pre = (tmr_create_option (args)))) (PreH26 : (callback_pre = (tmr_create_callback (args)))) (PreH27 : (callback_arg_pre = (tmr_create_callback_arg (args)))) (PreH28 : (pname_pre = (tmr_create_name_argument (args)))) (PreH29 : (tmr_create_output_binding perr_pre perr0 )) (PreH30 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) (PreH31 : (2 <> opt_pre)) (PreH32 : (1 = opt_pre)) ,
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (tmr_create_allocated_facts env args before locked retval i private allocated ) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_create_first_error (args) (before)) = None) ” 
  &&  “ ((unsigned_last_nbits ((tmr_create_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ ((tmr_create_argument_error ((tmr_create_delay (args))) ((tmr_create_period (args))) ((tmr_create_option (args)))) = None) ” 
  &&  “ (period_pre <= UINT_MAX) ” 
  &&  “ (dly_pre <= UINT_MAX) ” 
  &&  “ (period_pre >= 0) ” 
  &&  “ (dly_pre >= 0) ” 
  &&  “ (dly_pre <> 0) ” 
  &&  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ” 
  &&  “ (dly_pre = (tmr_create_delay (args))) ” 
  &&  “ (period_pre = (tmr_create_period (args))) ” 
  &&  “ (opt_pre = (tmr_create_option (args))) ” 
  &&  “ (callback_pre = (tmr_create_callback (args))) ” 
  &&  “ (callback_arg_pre = (tmr_create_callback_arg (args))) ” 
  &&  “ (pname_pre = (tmr_create_name_argument (args))) ” 
  &&  “ (tmr_create_output_binding perr_pre perr0 ) ” 
  &&  “ ((tmr_create_default_name (args)) = (LitMap (("?"%string)))) ” 
  &&  “ (2 <> opt_pre) ” 
  &&  “ (1 = opt_pre) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
  **  ((perr_pre) # UChar  |->_)
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_partial_solve_wit_33 := OSTmrCreate_partial_solve_wit_33_pure -> OSTmrCreate_partial_solve_wit_33_aux.

Definition OSTmrCreate_which_implies_wit_1 := 
(
forall (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (perr: Z) ,
  (tmr_create_api_pre env args before perr X )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ”
  &&  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  ((perr) # UChar  |->_)
) \/
(
forall (X: (TmrCreateOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (perr: Z) ,
  (tmr_create_api_pre env args before perr X )
|--
  EX (x: Z) ,
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (safeExec (tmr_create_at_state (before)) (tmr_create_program (env) (args)) X ) ”
  &&  ((perr) # UChar  |-> x)
  **  (tmr_create_return_frame env (tmr_create_caller (env)) before )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
).

Definition OSTmrCreate_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
|--
  “ (tmr_create_entry_facts env args before ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
).

Definition OSTmrCreate_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  (tmr_create_return_frame env (tmr_create_caller (env)) before )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
.

Definition OSTmrCreate_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
|--
  “ (tmr_create_entry_facts env args before ) ” 
  &&  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
|--
  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
).

Definition OSTmrCreate_which_implies_wit_3_split_goal_1 := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
|--
  “ (os_sched_lock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrCreate_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_create_nesting (before)))
  **  (tmr_create_observation_rest env before )
|--
  (os_sched_lock_pre (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
.

Definition OSTmrCreate_which_implies_wit_4 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : ((tmr_create_first_error (args) (before)) = None)) ,
  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
|--
  EX (head: Z)  (next: Z)  (prev: Z)  (used: Z)  (free: Z)  (alloc_frame: Assertion)  (locked: UCOS2_Verify_State) ,
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ”
  &&  (tmr_alloc_low_pre head next prev used free )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (PreH1 : (tmr_create_entry_facts env args before )) (PreH2 : ((tmr_create_first_error (args) (before)) = None)) ,
  (os_sched_lock_post (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (os_sched_call_invocation ((tmr_create_caller (env)))) (os_sched_call_origin ((tmr_create_caller (env)))) (tmr_create_mask (env)) before )
  **  (os_sched_context_resources (tmr_create_external (env)) (tmr_create_caller (env)) )
  **  (unmap_table_rep (tmr_create_globals (env)) )
|--
  EX (head: Z)  (next: Z)  (prev: Z)  (used: Z)  (free: Z)  (alloc_frame: Assertion)  (locked: UCOS2_Verify_State) ,
  “ (tmr_create_locked_facts env args before locked ) ” 
  &&  “ (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame ) ”
  &&  (tmr_alloc_low_pre head next prev used free )
  **  (alloc_frame )
  **  (tmr_create_kernel_frame env locked )
).

Definition OSTmrCreate_which_implies_wit_5 := 
(
forall (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (ptmr: Z) (PreH1 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) ,
  (tmr_alloc_low_post head next prev used free ptmr )
  **  (alloc_frame )
|--
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
) \/
(
forall (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (ptmr: Z) (PreH1 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) ,
  (tmr_alloc_low_post head next prev used free ptmr )
  **  (alloc_frame )
|--
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
).

Definition OSTmrCreate_which_implies_wit_5_split_goal_spatial := 
forall (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (head: Z) (next: Z) (prev: Z) (used: Z) (free: Z) (alloc_frame: Assertion) (ptmr: Z) (PreH1 : (tmr_create_alloc_consequence (tmr_create_globals (env)) (tmr_create_timers (locked)) head next prev used free alloc_frame )) ,
  (tmr_alloc_low_post head next prev used free ptmr )
  **  (alloc_frame )
|--
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
.

Definition OSTmrCreate_which_implies_wit_6 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_pointer_null ptmr )) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
  **  (tmr_create_kernel_frame env locked )
|--
  “ (tmr_create_pointer_null ptmr ) ” 
  &&  “ (tmr_create_prefix env args before TmrCreateExhausted locked ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_pointer_null ptmr )) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
  **  (tmr_create_kernel_frame env locked )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_create_prefix env args before TmrCreateExhausted locked ) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
).

Definition OSTmrCreate_which_implies_wit_6_split_goal_1 := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_pointer_null ptmr )) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
  **  (tmr_create_kernel_frame env locked )
|--
  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrCreate_which_implies_wit_6_split_goal_2 := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_pointer_null ptmr )) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
  **  (tmr_create_kernel_frame env locked )
|--
  “ (tmr_create_prefix env args before TmrCreateExhausted locked ) ”
.

Definition OSTmrCreate_which_implies_wit_6_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (tmr_create_pointer_null ptmr )) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
  **  (tmr_create_kernel_frame env locked )
|--
  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) locked )
.

Definition OSTmrCreate_which_implies_wit_7 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (ptmr <> 0)) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
|--
  EX (i: Z)  (private: TimerPrivateAllocation)  (allocated: GlobTimerState) ,
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ”
  &&  (timer_inv (tmr_create_globals (env)) allocated )
  **  (timer_private_rep (tmr_create_globals (env)) i private )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_create_locked_facts env args before locked )) (PreH2 : (ptmr <> 0)) ,
  (tmr_alloc_configured_result (tmr_create_globals (env)) (tmr_create_timers (locked)) ptmr )
|--
  EX (i: Z)  (private: TimerPrivateAllocation)  (allocated: GlobTimerState) ,
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ”
  &&  (timer_inv (tmr_create_globals (env)) allocated )
  **  (timer_private_rep (tmr_create_globals (env)) i private )
).

Definition OSTmrCreate_which_implies_wit_8 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) ,
  (timer_private_rep (tmr_create_globals (env)) i private )
|--
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (timerImageState ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (timerImageDelay ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (timerImagePeriod ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (timerImageOption ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (timerImageCallback ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (timerImageArg ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields ptmr (timerPrivateImage (private)) )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) ,
  (timer_private_rep (tmr_create_globals (env)) i private )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (timerImageState ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (timerImageDelay ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (timerImagePeriod ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (timerImageOption ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (timerImageCallback ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (timerImageArg ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields ptmr (timerPrivateImage (private)) )
).

Definition OSTmrCreate_which_implies_wit_8_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) ,
  (timer_private_rep (tmr_create_globals (env)) i private )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (timerImageState ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (timerImageDelay ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (timerImagePeriod ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (timerImageOption ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (timerImageCallback ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (timerImageArg ((timerPrivateImage (private)))))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (timerImageName ((timerPrivateImage (private)))))
  **  (tmr_create_retained_fields ptmr (timerPrivateImage (private)) )
.

Definition OSTmrCreate_which_implies_wit_9 := 
(
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) (PreH2 : ((tmr_create_name_argument (args)) = 0)) (PreH3 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
|--
  EX (literal_rest: Assertion) ,
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ”
  &&  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
) \/
(
forall (LitMap: (string -> Z)) (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) (PreH2 : ((tmr_create_name_argument (args)) = 0)) (PreH3 : ((tmr_create_default_name (args)) = (LitMap (("?"%string))))) ,
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
|--
  EX (literal_rest: Assertion) ,
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ” 
  &&  “ (tmr_create_literal_rejoin env locked LitMap literal_rest ) ”
  &&  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
).

Definition OSTmrCreate_which_implies_wit_10 := 
(
forall (LitMap: (string -> Z)) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (literal_rest: Assertion) (PreH1 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) ,
  (store_stringLit (LitMap (("?"%string))) ("?"%string) )
  **  (literal_rest )
  **  (GlobalStrings_missing LitMap (cons (("?"%string)) ((@nil string))) )
|--
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
) \/
(
forall (LitMap: (string -> Z)) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (literal_rest: Assertion) (PreH1 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) ,
  (GlobalStrings LitMap )
  **  (literal_rest )
|--
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
).

Definition OSTmrCreate_which_implies_wit_10_split_goal_spatial := 
forall (LitMap: (string -> Z)) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (literal_rest: Assertion) (PreH1 : (tmr_create_literal_rejoin env locked LitMap literal_rest )) ,
  (GlobalStrings LitMap )
  **  (literal_rest )
|--
  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
  **  (tmr_create_global_strings env LitMap )
.

Definition OSTmrCreate_which_implies_wit_11 := 
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_create_delay (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_create_period (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_create_option (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (tmr_create_callback (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (tmr_create_callback_arg (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_create_chosen_name (args)))
  **  (tmr_create_retained_fields ptmr (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
|--
  EX (completion: UCOS2_Verify_State) ,
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ” 
  &&  “ (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
) \/
(
forall (before: UCOS2_Verify_State) (args: TmrCreateArguments) (env: TmrCreateEnvironment) (locked: UCOS2_Verify_State) (i: Z) (private: TimerPrivateAllocation) (allocated: GlobTimerState) (ptmr: Z) (PreH1 : ((tmr_create_period (args)) <= UINT_MAX)) (PreH2 : ((tmr_create_delay (args)) <= UINT_MAX)) (PreH3 : ((tmr_create_period (args)) >= 0)) (PreH4 : ((tmr_create_delay (args)) >= 0)) (PreH5 : (tmr_create_allocated_facts env args before locked ptmr i private allocated )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> 1)
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrDly")) # UInt  |-> (tmr_create_delay (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrPeriod")) # UInt  |-> (tmr_create_period (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrOpt")) # UChar  |-> (tmr_create_option (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallback")) # Ptr  |-> (tmr_create_callback (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrCallbackArg")) # Ptr  |-> (tmr_create_callback_arg (args)))
  **  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_create_chosen_name (args)))
  **  (tmr_create_retained_fields ptmr (timerPrivateImage (private)) )
  **  (timer_inv (tmr_create_globals (env)) allocated )
  **  (tmr_create_kernel_frame env locked )
  **  (tmr_create_name_storage (tmr_create_name_plan (env)) )
|--
  EX (completion: UCOS2_Verify_State) ,
  “ (tmr_create_allocated_facts env args before locked ptmr i private allocated ) ” 
  &&  “ (tmr_create_prefix env args before (TmrCreateStored (i) (private)) completion ) ” 
  &&  “ (os_sched_unlock_global_addresses (tmr_create_globals (env)) ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre (tmr_create_external (env)) (tmr_create_platform (env)) (tmr_create_critical (env)) (tmr_create_globals (env)) (tmr_create_caller (env)) (tmr_create_mask (env)) completion )
  **  (tmr_create_result_storage env args (TmrCreateStored (i) (private)) )
).

Module Type VC_Correct.


Axiom proof_of_OSTmrCreate_safety_wit_1 : OSTmrCreate_safety_wit_1.
Axiom proof_of_OSTmrCreate_safety_wit_2 : OSTmrCreate_safety_wit_2.
Axiom proof_of_OSTmrCreate_safety_wit_3 : OSTmrCreate_safety_wit_3.
Axiom proof_of_OSTmrCreate_safety_wit_4 : OSTmrCreate_safety_wit_4.
Axiom proof_of_OSTmrCreate_safety_wit_5 : OSTmrCreate_safety_wit_5.
Axiom proof_of_OSTmrCreate_safety_wit_6 : OSTmrCreate_safety_wit_6.
Axiom proof_of_OSTmrCreate_safety_wit_7 : OSTmrCreate_safety_wit_7.
Axiom proof_of_OSTmrCreate_safety_wit_8 : OSTmrCreate_safety_wit_8.
Axiom proof_of_OSTmrCreate_safety_wit_9 : OSTmrCreate_safety_wit_9.
Axiom proof_of_OSTmrCreate_safety_wit_10 : OSTmrCreate_safety_wit_10.
Axiom proof_of_OSTmrCreate_safety_wit_11 : OSTmrCreate_safety_wit_11.
Axiom proof_of_OSTmrCreate_safety_wit_12 : OSTmrCreate_safety_wit_12.
Axiom proof_of_OSTmrCreate_safety_wit_13 : OSTmrCreate_safety_wit_13.
Axiom proof_of_OSTmrCreate_entail_wit_1_1 : OSTmrCreate_entail_wit_1_1.
Axiom proof_of_OSTmrCreate_entail_wit_1_2 : OSTmrCreate_entail_wit_1_2.
Axiom proof_of_OSTmrCreate_entail_wit_2_1 : OSTmrCreate_entail_wit_2_1.
Axiom proof_of_OSTmrCreate_entail_wit_2_2 : OSTmrCreate_entail_wit_2_2.
Axiom proof_of_OSTmrCreate_return_wit_1 : OSTmrCreate_return_wit_1.
Axiom proof_of_OSTmrCreate_return_wit_2 : OSTmrCreate_return_wit_2.
Axiom proof_of_OSTmrCreate_return_wit_3 : OSTmrCreate_return_wit_3.
Axiom proof_of_OSTmrCreate_return_wit_4 : OSTmrCreate_return_wit_4.
Axiom proof_of_OSTmrCreate_return_wit_5 : OSTmrCreate_return_wit_5.
Axiom proof_of_OSTmrCreate_return_wit_6 : OSTmrCreate_return_wit_6.
Axiom proof_of_OSTmrCreate_return_wit_7 : OSTmrCreate_return_wit_7.
Axiom proof_of_OSTmrCreate_return_wit_8 : OSTmrCreate_return_wit_8.
Axiom proof_of_OSTmrCreate_return_wit_9 : OSTmrCreate_return_wit_9.
Axiom proof_of_OSTmrCreate_return_wit_10 : OSTmrCreate_return_wit_10.
Axiom proof_of_OSTmrCreate_return_wit_11 : OSTmrCreate_return_wit_11.
Axiom proof_of_OSTmrCreate_partial_solve_wit_1 : OSTmrCreate_partial_solve_wit_1.
Axiom proof_of_OSTmrCreate_partial_solve_wit_2_pure : OSTmrCreate_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_2 : OSTmrCreate_partial_solve_wit_2.
Axiom proof_of_OSTmrCreate_partial_solve_wit_3_pure : OSTmrCreate_partial_solve_wit_3_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_3 : OSTmrCreate_partial_solve_wit_3.
Axiom proof_of_OSTmrCreate_partial_solve_wit_4_pure : OSTmrCreate_partial_solve_wit_4_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_4 : OSTmrCreate_partial_solve_wit_4.
Axiom proof_of_OSTmrCreate_partial_solve_wit_5_pure : OSTmrCreate_partial_solve_wit_5_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_5 : OSTmrCreate_partial_solve_wit_5.
Axiom proof_of_OSTmrCreate_partial_solve_wit_6_pure : OSTmrCreate_partial_solve_wit_6_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_6 : OSTmrCreate_partial_solve_wit_6.
Axiom proof_of_OSTmrCreate_partial_solve_wit_7_pure : OSTmrCreate_partial_solve_wit_7_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_7 : OSTmrCreate_partial_solve_wit_7.
Axiom proof_of_OSTmrCreate_partial_solve_wit_8_pure : OSTmrCreate_partial_solve_wit_8_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_8 : OSTmrCreate_partial_solve_wit_8.
Axiom proof_of_OSTmrCreate_partial_solve_wit_9_pure : OSTmrCreate_partial_solve_wit_9_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_9 : OSTmrCreate_partial_solve_wit_9.
Axiom proof_of_OSTmrCreate_partial_solve_wit_10 : OSTmrCreate_partial_solve_wit_10.
Axiom proof_of_OSTmrCreate_partial_solve_wit_11 : OSTmrCreate_partial_solve_wit_11.
Axiom proof_of_OSTmrCreate_partial_solve_wit_12_pure : OSTmrCreate_partial_solve_wit_12_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_12 : OSTmrCreate_partial_solve_wit_12.
Axiom proof_of_OSTmrCreate_partial_solve_wit_13_pure : OSTmrCreate_partial_solve_wit_13_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_13 : OSTmrCreate_partial_solve_wit_13.
Axiom proof_of_OSTmrCreate_partial_solve_wit_14_pure : OSTmrCreate_partial_solve_wit_14_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_14 : OSTmrCreate_partial_solve_wit_14.
Axiom proof_of_OSTmrCreate_partial_solve_wit_15_pure : OSTmrCreate_partial_solve_wit_15_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_15 : OSTmrCreate_partial_solve_wit_15.
Axiom proof_of_OSTmrCreate_partial_solve_wit_16_pure : OSTmrCreate_partial_solve_wit_16_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_16 : OSTmrCreate_partial_solve_wit_16.
Axiom proof_of_OSTmrCreate_partial_solve_wit_17_pure : OSTmrCreate_partial_solve_wit_17_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_17 : OSTmrCreate_partial_solve_wit_17.
Axiom proof_of_OSTmrCreate_partial_solve_wit_18_pure : OSTmrCreate_partial_solve_wit_18_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_18 : OSTmrCreate_partial_solve_wit_18.
Axiom proof_of_OSTmrCreate_partial_solve_wit_19_pure : OSTmrCreate_partial_solve_wit_19_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_19 : OSTmrCreate_partial_solve_wit_19.
Axiom proof_of_OSTmrCreate_partial_solve_wit_20_pure : OSTmrCreate_partial_solve_wit_20_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_20 : OSTmrCreate_partial_solve_wit_20.
Axiom proof_of_OSTmrCreate_partial_solve_wit_21_pure : OSTmrCreate_partial_solve_wit_21_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_21 : OSTmrCreate_partial_solve_wit_21.
Axiom proof_of_OSTmrCreate_partial_solve_wit_22_pure : OSTmrCreate_partial_solve_wit_22_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_22 : OSTmrCreate_partial_solve_wit_22.
Axiom proof_of_OSTmrCreate_partial_solve_wit_23_pure : OSTmrCreate_partial_solve_wit_23_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_23 : OSTmrCreate_partial_solve_wit_23.
Axiom proof_of_OSTmrCreate_partial_solve_wit_24_pure : OSTmrCreate_partial_solve_wit_24_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_24 : OSTmrCreate_partial_solve_wit_24.
Axiom proof_of_OSTmrCreate_partial_solve_wit_25_pure : OSTmrCreate_partial_solve_wit_25_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_25 : OSTmrCreate_partial_solve_wit_25.
Axiom proof_of_OSTmrCreate_partial_solve_wit_26_pure : OSTmrCreate_partial_solve_wit_26_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_26 : OSTmrCreate_partial_solve_wit_26.
Axiom proof_of_OSTmrCreate_partial_solve_wit_27_pure : OSTmrCreate_partial_solve_wit_27_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_27 : OSTmrCreate_partial_solve_wit_27.
Axiom proof_of_OSTmrCreate_partial_solve_wit_28_pure : OSTmrCreate_partial_solve_wit_28_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_28 : OSTmrCreate_partial_solve_wit_28.
Axiom proof_of_OSTmrCreate_partial_solve_wit_29_pure : OSTmrCreate_partial_solve_wit_29_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_29 : OSTmrCreate_partial_solve_wit_29.
Axiom proof_of_OSTmrCreate_partial_solve_wit_30_pure : OSTmrCreate_partial_solve_wit_30_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_30 : OSTmrCreate_partial_solve_wit_30.
Axiom proof_of_OSTmrCreate_partial_solve_wit_31_pure : OSTmrCreate_partial_solve_wit_31_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_31 : OSTmrCreate_partial_solve_wit_31.
Axiom proof_of_OSTmrCreate_partial_solve_wit_32_pure : OSTmrCreate_partial_solve_wit_32_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_32 : OSTmrCreate_partial_solve_wit_32.
Axiom proof_of_OSTmrCreate_partial_solve_wit_33_pure : OSTmrCreate_partial_solve_wit_33_pure.
Axiom proof_of_OSTmrCreate_partial_solve_wit_33 : OSTmrCreate_partial_solve_wit_33.
Axiom proof_of_OSTmrCreate_which_implies_wit_1 : OSTmrCreate_which_implies_wit_1.
Axiom proof_of_OSTmrCreate_which_implies_wit_2 : OSTmrCreate_which_implies_wit_2.
Axiom proof_of_OSTmrCreate_which_implies_wit_3 : OSTmrCreate_which_implies_wit_3.
Axiom proof_of_OSTmrCreate_which_implies_wit_4 : OSTmrCreate_which_implies_wit_4.
Axiom proof_of_OSTmrCreate_which_implies_wit_5 : OSTmrCreate_which_implies_wit_5.
Axiom proof_of_OSTmrCreate_which_implies_wit_6 : OSTmrCreate_which_implies_wit_6.
Axiom proof_of_OSTmrCreate_which_implies_wit_7 : OSTmrCreate_which_implies_wit_7.
Axiom proof_of_OSTmrCreate_which_implies_wit_8 : OSTmrCreate_which_implies_wit_8.
Axiom proof_of_OSTmrCreate_which_implies_wit_9 : OSTmrCreate_which_implies_wit_9.
Axiom proof_of_OSTmrCreate_which_implies_wit_10 : OSTmrCreate_which_implies_wit_10.
Axiom proof_of_OSTmrCreate_which_implies_wit_11 : OSTmrCreate_which_implies_wit_11.

End VC_Correct.
