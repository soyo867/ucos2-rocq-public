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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_del_spec.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Import UCOS2_C_Rules.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad MonadNotation.
Local Open Scope monad_scope.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmrDel -----*)

Definition OSTmrDel_safety_wit_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 = ptmr_pre)) (PreH2 : (perr0 = perr_pre)) (PreH3 : (perr0 <> 0)) (PreH4 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH5 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH6 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrDel_return_wit_1 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 <> (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 <> (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 <> (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_2 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_3 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_4 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 <> (tmr_del_image_state (current_image)))) (PreH27 : (2 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 <> (tmr_del_image_state (current_image)))) (PreH27 : (2 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 <> (tmr_del_image_state (current_image)))) (PreH27 : (2 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_5 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH4 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH5 : (tmr_unlink_layout )) (PreH6 : (tmr_unlink_profile sg )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH9 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH10 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH11 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH12 : (UCOS2_state_inv sg locked )) (PreH13 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH14 : (tmr_del_locked_image locked i current_image )) (PreH15 : (tmr_del_checks_passed ptmr0 image before )) (PreH16 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH17 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH18 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH19 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH20 : (valid_stable_glob_vars sg )) (PreH21 : (tmr_del_c_bindings sg ptmr0 )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (ptmr0 = ptmr_pre)) (PreH26 : (perr0 = perr_pre)) (PreH27 : (perr0 <> 0)) (PreH28 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH29 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH30 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH31 : (3 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH4 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH5 : (tmr_unlink_layout )) (PreH6 : (tmr_unlink_profile sg )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH9 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH10 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH11 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH12 : (UCOS2_state_inv sg locked )) (PreH13 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH14 : (tmr_del_locked_image locked i current_image )) (PreH15 : (tmr_del_checks_passed ptmr0 image before )) (PreH16 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH17 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH18 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH19 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH20 : (valid_stable_glob_vars sg )) (PreH21 : (tmr_del_c_bindings sg ptmr0 )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (ptmr0 = ptmr_pre)) (PreH26 : (perr0 = perr_pre)) (PreH27 : (perr0 <> 0)) (PreH28 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH29 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH30 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH31 : (3 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH4 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH5 : (tmr_unlink_layout )) (PreH6 : (tmr_unlink_profile sg )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH9 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH10 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH11 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH12 : (UCOS2_state_inv sg locked )) (PreH13 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH14 : (tmr_del_locked_image locked i current_image )) (PreH15 : (tmr_del_checks_passed ptmr0 image before )) (PreH16 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH17 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH18 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH19 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH20 : (valid_stable_glob_vars sg )) (PreH21 : (tmr_del_c_bindings sg ptmr0 )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (ptmr0 = ptmr_pre)) (PreH26 : (perr0 = perr_pre)) (PreH27 : (perr0 <> 0)) (PreH28 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH29 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH30 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH31 : (3 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_post external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 0)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 1 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_6 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) > 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 139)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) > 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 139)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) > 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 139)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_7 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) <> 100)) (PreH2 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH3 : (valid_stable_glob_vars sg )) (PreH4 : (tmr_del_c_bindings sg ptmr0 )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH7 : (ptmr_pre <> 0)) (PreH8 : (ptmr0 = ptmr_pre)) (PreH9 : (perr0 = perr_pre)) (PreH10 : (perr0 <> 0)) (PreH11 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH12 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH13 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) <> 100)) (PreH2 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH3 : (valid_stable_glob_vars sg )) (PreH4 : (tmr_del_c_bindings sg ptmr0 )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH7 : (ptmr_pre <> 0)) (PreH8 : (ptmr0 = ptmr_pre)) (PreH9 : (perr0 = perr_pre)) (PreH10 : (perr0 <> 0)) (PreH11 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH12 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH13 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) <> 100)) (PreH2 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH3 : (valid_stable_glob_vars sg )) (PreH4 : (tmr_del_c_bindings sg ptmr0 )) (PreH5 : (UCOS2_state_inv sg before )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH7 : (ptmr_pre <> 0)) (PreH8 : (ptmr0 = ptmr_pre)) (PreH9 : (perr0 = perr_pre)) (PreH10 : (perr0 <> 0)) (PreH11 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH12 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH13 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_return_wit_8 := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr0 = ptmr_pre)) (PreH3 : (perr0 = perr_pre)) (PreH4 : (perr0 <> 0)) (PreH5 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH6 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH7 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((perr_pre) # UChar  |-> 138)
  **  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr0 = ptmr_pre)) (PreH3 : (perr0 = perr_pre)) (PreH4 : (perr0 <> 0)) (PreH5 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH6 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH7 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((perr_pre) # UChar  |-> 138)
  **  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (ptmr0 = ptmr_pre)) (PreH3 : (perr0 = perr_pre)) (PreH4 : (perr0 <> 0)) (PreH5 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH6 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH7 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((perr_pre) # UChar  |-> 138)
  **  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  (tmr_del_api_post external platform critical sg context mask before ptmr0 (LitMap (("?"%string))) perr0 0 X )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr0 = ptmr_pre)) (PreH3 : (perr0 = perr_pre)) (PreH4 : (perr0 <> 0)) (PreH5 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH6 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH7 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
  **  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (ptmr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ”
.

Definition OSTmrDel_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (ptmr0 = ptmr_pre)) (PreH3 : (perr0 = perr_pre)) (PreH4 : (perr0 <> 0)) (PreH5 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH6 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH7 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((perr_pre) # UChar  |-> perr_in)
  **  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (ptmr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ”
  &&  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_1 := OSTmrDel_partial_solve_wit_1_pure -> OSTmrDel_partial_solve_wit_1_aux.

Definition OSTmrDel_partial_solve_wit_2 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH2 : (valid_stable_glob_vars sg )) (PreH3 : (tmr_del_c_bindings sg ptmr0 )) (PreH4 : (UCOS2_state_inv sg before )) (PreH5 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (ptmr0 = ptmr_pre)) (PreH8 : (perr0 = perr_pre)) (PreH9 : (perr0 <> 0)) (PreH10 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH11 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH12 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (ptmr0 <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_del_int_nesting (before)) <= 0) ” 
  &&  “ ((tmr_del_image_type (image)) = 100) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((tmr_del_image_type (image)) = 100) ” 
  &&  “ ((tmr_del_int_nesting (before)) <= 0) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
).

Definition OSTmrDel_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((tmr_del_image_type (image)) = 100) ”
.

Definition OSTmrDel_partial_solve_wit_3_pure_split_goal_2 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ ((tmr_del_int_nesting (before)) <= 0) ”
.

Definition OSTmrDel_partial_solve_wit_3_pure_split_goal_3 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH2 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH3 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH4 : (valid_stable_glob_vars sg )) (PreH5 : (tmr_del_c_bindings sg ptmr0 )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH8 : (ptmr_pre <> 0)) (PreH9 : (ptmr0 = ptmr_pre)) (PreH10 : (perr0 = perr_pre)) (PreH11 : (perr0 <> 0)) (PreH12 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH13 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH14 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (ptmr0 <> 0) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((tmr_del_int_nesting (before)) <= 0) ” 
  &&  “ ((tmr_del_image_type (image)) = 100) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (tmr_del_observation_residual sg before i image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_3 := OSTmrDel_partial_solve_wit_3_pure -> OSTmrDel_partial_solve_wit_3_aux.

Definition OSTmrDel_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_del_checks_passed ptmr0 image before )) (PreH2 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH4 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH5 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH6 : (valid_stable_glob_vars sg )) (PreH7 : (tmr_del_c_bindings sg ptmr0 )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr0 = ptmr_pre)) (PreH12 : (perr0 = perr_pre)) (PreH13 : (perr0 <> 0)) (PreH14 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH15 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH16 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_del_checks_passed ptmr0 image before )) (PreH2 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH4 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH5 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH6 : (valid_stable_glob_vars sg )) (PreH7 : (tmr_del_c_bindings sg ptmr0 )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr0 = ptmr_pre)) (PreH12 : (perr0 = perr_pre)) (PreH13 : (perr0 <> 0)) (PreH14 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH15 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH16 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_4 := OSTmrDel_partial_solve_wit_4_pure -> OSTmrDel_partial_solve_wit_4_aux.

Definition OSTmrDel_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_del_checks_passed ptmr0 image before )) (PreH2 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH4 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH5 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH6 : (valid_stable_glob_vars sg )) (PreH7 : (tmr_del_c_bindings sg ptmr0 )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr0 = ptmr_pre)) (PreH12 : (perr0 = perr_pre)) (PreH13 : (perr0 <> 0)) (PreH14 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH15 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH16 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ”
.

Definition OSTmrDel_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (tmr_del_checks_passed ptmr0 image before )) (PreH2 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH4 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH5 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH6 : (valid_stable_glob_vars sg )) (PreH7 : (tmr_del_c_bindings sg ptmr0 )) (PreH8 : (UCOS2_state_inv sg before )) (PreH9 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (ptmr0 = ptmr_pre)) (PreH12 : (perr0 = perr_pre)) (PreH13 : (perr0 <> 0)) (PreH14 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH15 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH16 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ”
  &&  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_5 := OSTmrDel_partial_solve_wit_5_pure -> OSTmrDel_partial_solve_wit_5_aux.

Definition OSTmrDel_partial_solve_wit_6 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ ((tmr_del_image_state (current_image)) = 3) ”
.

Definition OSTmrDel_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ ((tmr_del_image_state (current_image)) = 3) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_7 := OSTmrDel_partial_solve_wit_7_pure -> OSTmrDel_partial_solve_wit_7_aux.

Definition OSTmrDel_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_unlink_layout )) (PreH2 : (tmr_unlink_profile sg )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH5 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH8 : (UCOS2_state_inv sg locked )) (PreH9 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH10 : (tmr_del_locked_image locked i current_image )) (PreH11 : (tmr_del_checks_passed ptmr0 image before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH14 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH15 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH16 : (valid_stable_glob_vars sg )) (PreH17 : (tmr_del_c_bindings sg ptmr0 )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr0 = ptmr_pre)) (PreH22 : (perr0 = perr_pre)) (PreH23 : (perr0 <> 0)) (PreH24 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH25 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH26 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH27 : (3 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (ptmr0 = (timer_pool_addr (sg) (i))) ”
.

Definition OSTmrDel_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_unlink_layout )) (PreH2 : (tmr_unlink_profile sg )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH5 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH8 : (UCOS2_state_inv sg locked )) (PreH9 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH10 : (tmr_del_locked_image locked i current_image )) (PreH11 : (tmr_del_checks_passed ptmr0 image before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH14 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH15 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH16 : (valid_stable_glob_vars sg )) (PreH17 : (tmr_del_c_bindings sg ptmr0 )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr0 = ptmr_pre)) (PreH22 : (perr0 = perr_pre)) (PreH23 : (perr0 <> 0)) (PreH24 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH25 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH26 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH27 : (3 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> ptmr0)
  **  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_8 := OSTmrDel_partial_solve_wit_8_pure -> OSTmrDel_partial_solve_wit_8_aux.

Definition OSTmrDel_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_unlink_layout )) (PreH2 : (tmr_unlink_profile sg )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH5 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH8 : (UCOS2_state_inv sg locked )) (PreH9 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH10 : (tmr_del_locked_image locked i current_image )) (PreH11 : (tmr_del_checks_passed ptmr0 image before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH14 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH15 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH16 : (valid_stable_glob_vars sg )) (PreH17 : (tmr_del_c_bindings sg ptmr0 )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr0 = ptmr_pre)) (PreH22 : (perr0 = perr_pre)) (PreH23 : (perr0 <> 0)) (PreH24 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH25 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH26 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH27 : (3 = (tmr_del_image_state (current_image)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> (timer_pool_addr (sg) (i)))
  **  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ ((timer_pool_addr (sg) (i)) = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ”
.

Definition OSTmrDel_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_unlink_layout )) (PreH2 : (tmr_unlink_profile sg )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH5 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH8 : (UCOS2_state_inv sg locked )) (PreH9 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH10 : (tmr_del_locked_image locked i current_image )) (PreH11 : (tmr_del_checks_passed ptmr0 image before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH14 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH15 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH16 : (valid_stable_glob_vars sg )) (PreH17 : (tmr_del_c_bindings sg ptmr0 )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr0 = ptmr_pre)) (PreH22 : (perr0 = perr_pre)) (PreH23 : (perr0 <> 0)) (PreH24 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH25 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH26 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH27 : (3 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ ((timer_pool_addr (sg) (i)) = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_9 := OSTmrDel_partial_solve_wit_9_pure -> OSTmrDel_partial_solve_wit_9_aux.

Definition OSTmrDel_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_unlink_layout )) (PreH2 : (tmr_unlink_profile sg )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH5 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH8 : (UCOS2_state_inv sg locked )) (PreH9 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH10 : (tmr_del_locked_image locked i current_image )) (PreH11 : (tmr_del_checks_passed ptmr0 image before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH14 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH15 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH16 : (valid_stable_glob_vars sg )) (PreH17 : (tmr_del_c_bindings sg ptmr0 )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr0 = ptmr_pre)) (PreH22 : (perr0 = perr_pre)) (PreH23 : (perr0 <> 0)) (PreH24 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH25 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH26 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH27 : (3 = (tmr_del_image_state (current_image)))) ,
  (tmr_unlink_configured_post sg (tmr_del_timer_state (locked)) i )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> (timer_pool_addr (sg) (i)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ”
.

Definition OSTmrDel_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_unlink_layout )) (PreH2 : (tmr_unlink_profile sg )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH5 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH6 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH7 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH8 : (UCOS2_state_inv sg locked )) (PreH9 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH10 : (tmr_del_locked_image locked i current_image )) (PreH11 : (tmr_del_checks_passed ptmr0 image before )) (PreH12 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH14 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH15 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH16 : (valid_stable_glob_vars sg )) (PreH17 : (tmr_del_c_bindings sg ptmr0 )) (PreH18 : (UCOS2_state_inv sg before )) (PreH19 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH20 : (ptmr_pre <> 0)) (PreH21 : (ptmr0 = ptmr_pre)) (PreH22 : (perr0 = perr_pre)) (PreH23 : (perr0 <> 0)) (PreH24 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH25 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH26 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH27 : (3 = (tmr_del_image_state (current_image)))) ,
  (tmr_unlink_configured_post sg (tmr_del_timer_state (locked)) i )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  (tmr_unlink_configured_post sg (tmr_del_timer_state (locked)) i )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_10 := OSTmrDel_partial_solve_wit_10_pure -> OSTmrDel_partial_solve_wit_10_aux.

Definition OSTmrDel_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH2 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH3 : (tmr_unlink_layout )) (PreH4 : (tmr_unlink_profile sg )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH7 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH8 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH9 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH12 : (tmr_del_locked_image locked i current_image )) (PreH13 : (tmr_del_checks_passed ptmr0 image before )) (PreH14 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH16 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH17 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH18 : (valid_stable_glob_vars sg )) (PreH19 : (tmr_del_c_bindings sg ptmr0 )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH22 : (ptmr_pre <> 0)) (PreH23 : (ptmr0 = ptmr_pre)) (PreH24 : (perr0 = perr_pre)) (PreH25 : (perr0 <> 0)) (PreH26 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH27 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH28 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH29 : (3 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg s )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> (timer_pool_addr (sg) (i)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ”
.

Definition OSTmrDel_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH2 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH3 : (tmr_unlink_layout )) (PreH4 : (tmr_unlink_profile sg )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH7 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH8 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH9 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH12 : (tmr_del_locked_image locked i current_image )) (PreH13 : (tmr_del_checks_passed ptmr0 image before )) (PreH14 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH16 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH17 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH18 : (valid_stable_glob_vars sg )) (PreH19 : (tmr_del_c_bindings sg ptmr0 )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH22 : (ptmr_pre <> 0)) (PreH23 : (ptmr0 = ptmr_pre)) (PreH24 : (perr0 = perr_pre)) (PreH25 : (perr0 <> 0)) (PreH26 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH27 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH28 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH29 : (3 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg s )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ” 
  &&  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  (timer_inv sg s )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_11 := OSTmrDel_partial_solve_wit_11_pure -> OSTmrDel_partial_solve_wit_11_aux.

Definition OSTmrDel_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH2 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH3 : (tmr_unlink_layout )) (PreH4 : (tmr_unlink_profile sg )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH7 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH8 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH9 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH12 : (tmr_del_locked_image locked i current_image )) (PreH13 : (tmr_del_checks_passed ptmr0 image before )) (PreH14 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH16 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH17 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH18 : (valid_stable_glob_vars sg )) (PreH19 : (tmr_del_c_bindings sg ptmr0 )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH22 : (ptmr_pre <> 0)) (PreH23 : (ptmr0 = ptmr_pre)) (PreH24 : (perr0 = perr_pre)) (PreH25 : (perr0 <> 0)) (PreH26 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH27 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH28 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH29 : (3 = (tmr_del_image_state (current_image)))) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> (timer_pool_addr (sg) (i)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ”
.

Definition OSTmrDel_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH2 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH3 : (tmr_unlink_layout )) (PreH4 : (tmr_unlink_profile sg )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH7 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH8 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH9 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH10 : (UCOS2_state_inv sg locked )) (PreH11 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH12 : (tmr_del_locked_image locked i current_image )) (PreH13 : (tmr_del_checks_passed ptmr0 image before )) (PreH14 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH16 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH17 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH18 : (valid_stable_glob_vars sg )) (PreH19 : (tmr_del_c_bindings sg ptmr0 )) (PreH20 : (UCOS2_state_inv sg before )) (PreH21 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH22 : (ptmr_pre <> 0)) (PreH23 : (ptmr0 = ptmr_pre)) (PreH24 : (perr0 = perr_pre)) (PreH25 : (perr0 <> 0)) (PreH26 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH27 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH28 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH29 : (3 = (tmr_del_image_state (current_image)))) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_12 := OSTmrDel_partial_solve_wit_12_pure -> OSTmrDel_partial_solve_wit_12_aux.

Definition OSTmrDel_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH4 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH5 : (tmr_unlink_layout )) (PreH6 : (tmr_unlink_profile sg )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH9 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH10 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH11 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH12 : (UCOS2_state_inv sg locked )) (PreH13 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH14 : (tmr_del_locked_image locked i current_image )) (PreH15 : (tmr_del_checks_passed ptmr0 image before )) (PreH16 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH17 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH18 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH19 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH20 : (valid_stable_glob_vars sg )) (PreH21 : (tmr_del_c_bindings sg ptmr0 )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (ptmr0 = ptmr_pre)) (PreH26 : (perr0 = perr_pre)) (PreH27 : (perr0 <> 0)) (PreH28 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH29 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH30 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH31 : (3 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> (timer_pool_addr (sg) (i)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (s: GlobTimerState) (old: TimerImage) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) )) (PreH4 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH5 : (tmr_unlink_layout )) (PreH6 : (tmr_unlink_profile sg )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) (PreH9 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH10 : (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg)))) (PreH11 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH12 : (UCOS2_state_inv sg locked )) (PreH13 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH14 : (tmr_del_locked_image locked i current_image )) (PreH15 : (tmr_del_checks_passed ptmr0 image before )) (PreH16 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH17 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH18 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH19 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH20 : (valid_stable_glob_vars sg )) (PreH21 : (tmr_del_c_bindings sg ptmr0 )) (PreH22 : (UCOS2_state_inv sg before )) (PreH23 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (ptmr0 = ptmr_pre)) (PreH26 : (perr0 = perr_pre)) (PreH27 : (perr0 <> 0)) (PreH28 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH29 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH30 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH31 : (3 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 = (tmr_del_image_state (current_image))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_13 := OSTmrDel_partial_solve_wit_13_pure -> OSTmrDel_partial_solve_wit_13_aux.

Definition OSTmrDel_partial_solve_wit_14_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_image_stopped current_image ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_image_stopped current_image ) ”
).

Definition OSTmrDel_partial_solve_wit_14_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_image_stopped current_image ) ”
.

Definition OSTmrDel_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_image_stopped current_image ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 = (tmr_del_image_state (current_image))) ”
  &&  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_14 := OSTmrDel_partial_solve_wit_14_pure -> OSTmrDel_partial_solve_wit_14_aux.

Definition OSTmrDel_partial_solve_wit_15_pure := 
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_image_stopped current_image ) ”
) \/
(
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_image_stopped current_image ) ”
).

Definition OSTmrDel_partial_solve_wit_15_pure_split_goal_1 := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_image_stopped current_image ) ”
.

Definition OSTmrDel_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_image_stopped current_image ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 = (tmr_del_image_state (current_image))) ”
  &&  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_15 := OSTmrDel_partial_solve_wit_15_pure -> OSTmrDel_partial_solve_wit_15_aux.

Definition OSTmrDel_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr_pre ) ”
.

Definition OSTmrDel_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr_pre ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 = (tmr_del_image_state (current_image))) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_16 := OSTmrDel_partial_solve_wit_16_pure -> OSTmrDel_partial_solve_wit_16_aux.

Definition OSTmrDel_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr_pre ) ”
.

Definition OSTmrDel_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 = (tmr_del_image_state (current_image)))) ,
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr_pre ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 = (tmr_del_image_state (current_image))) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_17 := OSTmrDel_partial_solve_wit_17_pure -> OSTmrDel_partial_solve_wit_17_aux.

Definition OSTmrDel_partial_solve_wit_18_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 = (tmr_del_image_state (current_image)))) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ”
.

Definition OSTmrDel_partial_solve_wit_18_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 = (tmr_del_image_state (current_image)))) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 = (tmr_del_image_state (current_image))) ”
  &&  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_18 := OSTmrDel_partial_solve_wit_18_pure -> OSTmrDel_partial_solve_wit_18_aux.

Definition OSTmrDel_partial_solve_wit_19_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 = (tmr_del_image_state (current_image)))) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ”
.

Definition OSTmrDel_partial_solve_wit_19_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH2 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 = (tmr_del_image_state (current_image)))) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (GlobalStrings LitMap )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 = (tmr_del_image_state (current_image))) ”
  &&  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_19 := OSTmrDel_partial_solve_wit_19_pure -> OSTmrDel_partial_solve_wit_19_aux.

Definition OSTmrDel_partial_solve_wit_20_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_20_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 = (tmr_del_image_state (current_image))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_20 := OSTmrDel_partial_solve_wit_20_pure -> OSTmrDel_partial_solve_wit_20_aux.

Definition OSTmrDel_partial_solve_wit_21_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 <> (tmr_del_image_state (current_image)))) (PreH27 : (2 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_21_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 )) (PreH4 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH5 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH6 : (UCOS2_state_inv sg locked )) (PreH7 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH8 : (tmr_del_locked_image locked i current_image )) (PreH9 : (tmr_del_checks_passed ptmr0 image before )) (PreH10 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH11 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH12 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH13 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH14 : (valid_stable_glob_vars sg )) (PreH15 : (tmr_del_c_bindings sg ptmr0 )) (PreH16 : (UCOS2_state_inv sg before )) (PreH17 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (ptmr0 = ptmr_pre)) (PreH20 : (perr0 = perr_pre)) (PreH21 : (perr0 <> 0)) (PreH22 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH23 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH24 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH25 : (3 <> (tmr_del_image_state (current_image)))) (PreH26 : (1 <> (tmr_del_image_state (current_image)))) (PreH27 : (2 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 = (tmr_del_image_state (current_image))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_21 := OSTmrDel_partial_solve_wit_21_pure -> OSTmrDel_partial_solve_wit_21_aux.

Definition OSTmrDel_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 <> (tmr_del_image_state (current_image)))) (PreH24 : (0 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ ((tmr_del_image_state (current_image)) = 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ”
.

Definition OSTmrDel_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 <> (tmr_del_image_state (current_image)))) (PreH24 : (0 = (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ ((tmr_del_image_state (current_image)) = 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (0 = (tmr_del_image_state (current_image))) ”
  &&  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_22 := OSTmrDel_partial_solve_wit_22_pure -> OSTmrDel_partial_solve_wit_22_aux.

Definition OSTmrDel_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 = (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (0 = (tmr_del_image_state (current_image))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_23 := OSTmrDel_partial_solve_wit_23_pure -> OSTmrDel_partial_solve_wit_23_aux.

Definition OSTmrDel_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 <> (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result )) (PreH2 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH3 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH6 : (tmr_del_locked_image locked i current_image )) (PreH7 : (tmr_del_checks_passed ptmr0 image before )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH10 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH11 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH12 : (valid_stable_glob_vars sg )) (PreH13 : (tmr_del_c_bindings sg ptmr0 )) (PreH14 : (UCOS2_state_inv sg before )) (PreH15 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH16 : (ptmr_pre <> 0)) (PreH17 : (ptmr0 = ptmr_pre)) (PreH18 : (perr0 = perr_pre)) (PreH19 : (perr0 <> 0)) (PreH20 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH21 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH22 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH23 : (3 <> (tmr_del_image_state (current_image)))) (PreH24 : (1 <> (tmr_del_image_state (current_image)))) (PreH25 : (2 <> (tmr_del_image_state (current_image)))) (PreH26 : (0 <> (tmr_del_image_state (current_image)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (0 <> (tmr_del_image_state (current_image))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_24 := OSTmrDel_partial_solve_wit_24_pure -> OSTmrDel_partial_solve_wit_24_aux.

Definition OSTmrDel_partial_solve_wit_25_pure := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 <> (tmr_del_image_state (current_image)))) (PreH24 : (0 <> (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 0) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 1) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 2) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 3) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ”
.

Definition OSTmrDel_partial_solve_wit_25_aux := 
forall (perr_pre: Z) (ptmr_pre: Z) (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (X: (TmrDelOutput -> (UCOS2_Verify_State -> Prop))) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH2 : (UCOS2_state_inv sg locked )) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (tmr_del_locked_image locked i current_image )) (PreH5 : (tmr_del_checks_passed ptmr0 image before )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0)) (PreH8 : ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100)) (PreH9 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH10 : (valid_stable_glob_vars sg )) (PreH11 : (tmr_del_c_bindings sg ptmr0 )) (PreH12 : (UCOS2_state_inv sg before )) (PreH13 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH14 : (ptmr_pre <> 0)) (PreH15 : (ptmr0 = ptmr_pre)) (PreH16 : (perr0 = perr_pre)) (PreH17 : (perr0 <> 0)) (PreH18 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH19 : (tmr_del_observation_case sg before ptmr0 i image )) (PreH20 : (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X )) (PreH21 : (3 <> (tmr_del_image_state (current_image)))) (PreH22 : (1 <> (tmr_del_image_state (current_image)))) (PreH23 : (2 <> (tmr_del_image_state (current_image)))) (PreH24 : (0 <> (tmr_del_image_state (current_image)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 0) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 1) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 2) ” 
  &&  “ ((tmr_del_image_state (current_image)) <> 3) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ” 
  &&  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_int_nesting (before))) (32)) <= 0) ” 
  &&  “ ((unsigned_last_nbits ((tmr_del_image_type (image))) (32)) = 100) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (ptmr0 = ptmr_pre) ” 
  &&  “ (perr0 = perr_pre) ” 
  &&  “ (perr0 <> 0) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_observation_case sg before ptmr0 i image ) ” 
  &&  “ (safeExec (tmr_del_at_state (before)) (tmr_del_call_program (external) (critical) (sg) (context) (ptmr0) ((LitMap (("?"%string))))) X ) ” 
  &&  “ (3 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (1 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (2 <> (tmr_del_image_state (current_image))) ” 
  &&  “ (0 <> (tmr_del_image_state (current_image))) ”
  &&  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
  **  ((perr_pre) # UChar  |-> perr_in)
.

Definition OSTmrDel_partial_solve_wit_25 := OSTmrDel_partial_solve_wit_25_pure -> OSTmrDel_partial_solve_wit_25_aux.

Definition OSTmrDel_which_implies_wit_1 := 
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_observation_binding sg before ptmr0 i image ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
) \/
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (tmr_del_c_bindings sg ptmr0 ) ” 
  &&  “ (valid_stable_glob_vars sg ) ” 
  &&  “ (tmr_del_observation_binding sg before ptmr0 i image ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_which_implies_wit_1_split_goal_1 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSTmrDel_which_implies_wit_1_split_goal_2 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_c_bindings sg ptmr0 ) ”
.

Definition OSTmrDel_which_implies_wit_1_split_goal_3 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (valid_stable_glob_vars sg ) ”
.

Definition OSTmrDel_which_implies_wit_1_split_goal_4 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_observation_binding sg before ptmr0 i image ) ”
.

Definition OSTmrDel_which_implies_wit_1_split_goal_spatial := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (perr_in: Z) (perr0: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr0 <> 0)) (PreH2 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) (PreH3 : (tmr_del_observation_case sg before ptmr0 i image )) ,
  (tmr_del_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before ptmr0 perr0 perr_in )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (GlobalStrings LitMap )
|--
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
  **  (tmr_del_observation_residual sg before i image )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_which_implies_wit_2 := 
(
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH2 : (tmr_del_c_bindings sg ptmr0 )) (PreH3 : (ptmr0 <> 0)) (PreH4 : ((tmr_del_image_type (image)) = 100)) (PreH5 : ((tmr_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (tmr_del_observation_residual sg before i image )
|--
  “ (tmr_del_checks_passed ptmr0 image before ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
) \/
(
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH2 : (tmr_del_c_bindings sg ptmr0 )) (PreH3 : (ptmr0 <> 0)) (PreH4 : ((tmr_del_image_type (image)) = 100)) (PreH5 : ((tmr_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (tmr_del_observation_residual sg before i image )
|--
  “ (tmr_del_checks_passed ptmr0 image before ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
).

Definition OSTmrDel_which_implies_wit_2_split_goal_1 := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH2 : (tmr_del_c_bindings sg ptmr0 )) (PreH3 : (ptmr0 <> 0)) (PreH4 : ((tmr_del_image_type (image)) = 100)) (PreH5 : ((tmr_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (tmr_del_observation_residual sg before i image )
|--
  “ (tmr_del_checks_passed ptmr0 image before ) ”
.

Definition OSTmrDel_which_implies_wit_2_split_goal_spatial := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (tmr_del_observation_binding sg before ptmr0 i image )) (PreH2 : (tmr_del_c_bindings sg ptmr0 )) (PreH3 : (ptmr0 <> 0)) (PreH4 : ((tmr_del_image_type (image)) = 100)) (PreH5 : ((tmr_del_int_nesting (before)) <= 0)) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH7 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (image)))
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (tmr_del_int_nesting (before)))
  **  (tmr_del_observation_residual sg before i image )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
.

Definition OSTmrDel_which_implies_wit_3 := 
(
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (tmr_del_c_bindings sg ptmr0 )) (PreH3 : (tmr_del_checks_passed ptmr0 image before )) (PreH4 : (tmr_del_observation_binding sg before ptmr0 i image )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
|--
  EX (current_image: TimerImage)  (locked: UCOS2_Verify_State) ,
  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
) \/
(
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (valid_stable_glob_vars sg )) (PreH2 : (tmr_del_c_bindings sg ptmr0 )) (PreH3 : (tmr_del_checks_passed ptmr0 image before )) (PreH4 : (tmr_del_observation_binding sg before ptmr0 i image )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
|--
  EX (current_image: TimerImage)  (locked: UCOS2_Verify_State) ,
  “ (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked ) ” 
  &&  “ (UCOS2_state_inv sg locked ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_del_locked_image locked i current_image ) ”
  &&  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
).

Definition OSTmrDel_which_implies_wit_4 := 
(
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (tmr_unlink_layout ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (timer_api_initialized (tmr_del_timer_state (locked)) ) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
) \/
(
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ” 
  &&  “ (ptmr0 = (timer_pool_addr (sg) (i))) ” 
  &&  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ” 
  &&  “ (tmr_unlink_profile sg ) ” 
  &&  “ (tmr_unlink_layout ) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
).

Definition OSTmrDel_which_implies_wit_4_split_goal_1 := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (( &( "OSTmrWheelTbl" ) ) = (g_OSTmrWheelTbl (sg))) ”
.

Definition OSTmrDel_which_implies_wit_4_split_goal_2 := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (ptmr0 = (timer_pool_addr (sg) (i))) ”
.

Definition OSTmrDel_which_implies_wit_4_split_goal_3 := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (tmr_unlink_running (tmr_del_timer_state (locked)) i ) ”
.

Definition OSTmrDel_which_implies_wit_4_split_goal_4 := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (tmr_unlink_profile sg ) ”
.

Definition OSTmrDel_which_implies_wit_4_split_goal_5 := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  “ (tmr_unlink_layout ) ”
.

Definition OSTmrDel_which_implies_wit_4_split_goal_spatial := 
forall (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 3)) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
|--
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
.

Definition OSTmrDel_which_implies_wit_5 := 
forall (i: Z) (ptmr0: Z) (sg: StableGlobVars) (PreH1 : (ptmr0 = (timer_pool_addr (sg) (i)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr0)
|--
  ((( &( "ptmr" ) )) # Ptr  |-> (timer_pool_addr (sg) (i)))
.

Definition OSTmrDel_which_implies_wit_6 := 
(
forall (LitMap: (string -> Z)) (i: Z) (ptmr0: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) ,
  (tmr_unlink_configured_post sg (tmr_del_timer_state (locked)) i )
  **  (GlobalStrings LitMap )
|--
  EX (s: GlobTimerState)  (old: TimerImage) ,
  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ”
  &&  (timer_inv sg s )
  **  (GlobalStrings LitMap )
) \/
(
forall (LitMap: (string -> Z)) (i: Z) (ptmr0: Z) (sg: StableGlobVars) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (ptmr0 = (timer_pool_addr (sg) (i)))) (PreH3 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH4 : (UCOS2_state_inv sg locked )) (PreH5 : (tmr_unlink_running (tmr_del_timer_state (locked)) i )) ,
  (tmr_unlink_configured_post sg (tmr_del_timer_state (locked)) i )
  **  (GlobalStrings LitMap )
|--
  EX (s: GlobTimerState)  (old: TimerImage) ,
  “ (tmr_del_free_input sg s i old (timer_pool_addr (sg) (i)) ) ” 
  &&  “ (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) ) ”
  &&  (timer_inv sg s )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_which_implies_wit_7 := 
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TimerImage) (s: GlobTimerState) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
) \/
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TimerImage) (s: GlobTimerState) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
).

Definition OSTmrDel_which_implies_wit_7_split_goal_1 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TimerImage) (s: GlobTimerState) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_which_implies_wit_7_split_goal_2 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TimerImage) (s: GlobTimerState) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) tmr_del_success_result ) ”
.

Definition OSTmrDel_which_implies_wit_7_split_goal_spatial := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (old: TimerImage) (s: GlobTimerState) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked s i old (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg s i old (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) (s) (i) (old) ((LitMap (("?"%string))))) )
.

Definition OSTmrDel_which_implies_wit_8 := 
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : (tmr_del_image_stopped current_image )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ” 
  &&  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
) \/
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : (tmr_del_image_stopped current_image )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ” 
  &&  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ”
  &&  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
).

Definition OSTmrDel_which_implies_wit_8_split_goal_1 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : (tmr_del_image_stopped current_image )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) ) ”
.

Definition OSTmrDel_which_implies_wit_8_split_goal_2 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : (tmr_del_image_stopped current_image )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
|--
  “ (tmr_del_free_input sg (tmr_del_timer_state (locked)) i current_image ptmr0 ) ”
.

Definition OSTmrDel_which_implies_wit_8_split_goal_spatial := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : (tmr_del_image_stopped current_image )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (GlobalStrings LitMap )
|--
  (timer_inv sg (tmr_del_timer_state (locked)) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (GlobalStrings LitMap )
.

Definition OSTmrDel_which_implies_wit_9 := 
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
) \/
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
).

Definition OSTmrDel_which_implies_wit_9_split_goal_1 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_which_implies_wit_9_split_goal_2 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) tmr_del_success_result ) ”
.

Definition OSTmrDel_which_implies_wit_9_split_goal_spatial := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_release_step sg locked (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )) (PreH6 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  (tmr_free_valid_post sg (tmr_del_timer_state (locked)) i current_image (LitMap (("?"%string))) )
  **  (UCOS2_raw_rep_missing_timer sg locked )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  (os_sched_unlock_pre external platform critical sg context mask (tmr_del_release_state (sg) (locked) ((tmr_del_timer_state (locked))) (i) (current_image) ((LitMap (("?"%string))))) )
.

Definition OSTmrDel_which_implies_wit_10 := 
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 0)) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
) \/
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 0)) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
).

Definition OSTmrDel_which_implies_wit_10_split_goal_1 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 0)) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_which_implies_wit_10_split_goal_2 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 0)) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_inactive_result ) ”
.

Definition OSTmrDel_which_implies_wit_10_split_goal_spatial := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) = 0)) (PreH7 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
.

Definition OSTmrDel_which_implies_wit_11 := 
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) <> 0)) (PreH7 : ((tmr_del_image_state (current_image)) <> 1)) (PreH8 : ((tmr_del_image_state (current_image)) <> 2)) (PreH9 : ((tmr_del_image_state (current_image)) <> 3)) (PreH10 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
) \/
(
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) <> 0)) (PreH7 : ((tmr_del_image_state (current_image)) <> 1)) (PreH8 : ((tmr_del_image_state (current_image)) <> 2)) (PreH9 : ((tmr_del_image_state (current_image)) <> 3)) (PreH10 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
).

Definition OSTmrDel_which_implies_wit_11_split_goal_1 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) <> 0)) (PreH7 : ((tmr_del_image_state (current_image)) <> 1)) (PreH8 : ((tmr_del_image_state (current_image)) <> 2)) (PreH9 : ((tmr_del_image_state (current_image)) <> 3)) (PreH10 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrDel_which_implies_wit_11_split_goal_2 := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) <> 0)) (PreH7 : ((tmr_del_image_state (current_image)) <> 1)) (PreH8 : ((tmr_del_image_state (current_image)) <> 2)) (PreH9 : ((tmr_del_image_state (current_image)) <> 3)) (PreH10 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  “ (tmr_del_result_prop critical sg (os_sched_call_invocation (context)) ptmr0 (LitMap (("?"%string))) before locked tmr_del_invalid_state_result ) ”
.

Definition OSTmrDel_which_implies_wit_11_split_goal_spatial := 
forall (LitMap: (string -> Z)) (image: TimerImage) (i: Z) (ptmr0: Z) (before: UCOS2_Verify_State) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (current_image: TimerImage) (locked: UCOS2_Verify_State) (PreH1 : (tmr_del_c_bindings sg ptmr0 )) (PreH2 : (tmr_del_call_history critical sg (os_sched_call_invocation (context)) before ptmr0 i image locked )) (PreH3 : (UCOS2_state_inv sg locked )) (PreH4 : (timer_api_initialized (tmr_del_timer_state (locked)) )) (PreH5 : (tmr_del_locked_image locked i current_image )) (PreH6 : ((tmr_del_image_state (current_image)) <> 0)) (PreH7 : ((tmr_del_image_state (current_image)) <> 1)) (PreH8 : ((tmr_del_image_state (current_image)) <> 2)) (PreH9 : ((tmr_del_image_state (current_image)) <> 3)) (PreH10 : (tmr_del_scheduler_acquire_safety external critical sg context before ptmr0 (LitMap (("?"%string))) )) ,
  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_del_image_type (current_image)))
  **  ((&((ptmr0)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_del_image_state (current_image)))
  **  (tmr_del_locked_observation_residual sg locked i current_image )
  **  (interrupt_platform_running platform (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask )
  **  (os_sched_context_resources external context )
  **  (unmap_table_rep sg )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
.

Module Type VC_Correct.


Axiom proof_of_OSTmrDel_safety_wit_1 : OSTmrDel_safety_wit_1.
Axiom proof_of_OSTmrDel_return_wit_1 : OSTmrDel_return_wit_1.
Axiom proof_of_OSTmrDel_return_wit_2 : OSTmrDel_return_wit_2.
Axiom proof_of_OSTmrDel_return_wit_3 : OSTmrDel_return_wit_3.
Axiom proof_of_OSTmrDel_return_wit_4 : OSTmrDel_return_wit_4.
Axiom proof_of_OSTmrDel_return_wit_5 : OSTmrDel_return_wit_5.
Axiom proof_of_OSTmrDel_return_wit_6 : OSTmrDel_return_wit_6.
Axiom proof_of_OSTmrDel_return_wit_7 : OSTmrDel_return_wit_7.
Axiom proof_of_OSTmrDel_return_wit_8 : OSTmrDel_return_wit_8.
Axiom proof_of_OSTmrDel_partial_solve_wit_1_pure : OSTmrDel_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_1 : OSTmrDel_partial_solve_wit_1.
Axiom proof_of_OSTmrDel_partial_solve_wit_2 : OSTmrDel_partial_solve_wit_2.
Axiom proof_of_OSTmrDel_partial_solve_wit_3_pure : OSTmrDel_partial_solve_wit_3_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_3 : OSTmrDel_partial_solve_wit_3.
Axiom proof_of_OSTmrDel_partial_solve_wit_4_pure : OSTmrDel_partial_solve_wit_4_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_4 : OSTmrDel_partial_solve_wit_4.
Axiom proof_of_OSTmrDel_partial_solve_wit_5_pure : OSTmrDel_partial_solve_wit_5_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_5 : OSTmrDel_partial_solve_wit_5.
Axiom proof_of_OSTmrDel_partial_solve_wit_6 : OSTmrDel_partial_solve_wit_6.
Axiom proof_of_OSTmrDel_partial_solve_wit_7_pure : OSTmrDel_partial_solve_wit_7_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_7 : OSTmrDel_partial_solve_wit_7.
Axiom proof_of_OSTmrDel_partial_solve_wit_8_pure : OSTmrDel_partial_solve_wit_8_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_8 : OSTmrDel_partial_solve_wit_8.
Axiom proof_of_OSTmrDel_partial_solve_wit_9_pure : OSTmrDel_partial_solve_wit_9_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_9 : OSTmrDel_partial_solve_wit_9.
Axiom proof_of_OSTmrDel_partial_solve_wit_10_pure : OSTmrDel_partial_solve_wit_10_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_10 : OSTmrDel_partial_solve_wit_10.
Axiom proof_of_OSTmrDel_partial_solve_wit_11_pure : OSTmrDel_partial_solve_wit_11_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_11 : OSTmrDel_partial_solve_wit_11.
Axiom proof_of_OSTmrDel_partial_solve_wit_12_pure : OSTmrDel_partial_solve_wit_12_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_12 : OSTmrDel_partial_solve_wit_12.
Axiom proof_of_OSTmrDel_partial_solve_wit_13_pure : OSTmrDel_partial_solve_wit_13_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_13 : OSTmrDel_partial_solve_wit_13.
Axiom proof_of_OSTmrDel_partial_solve_wit_14_pure : OSTmrDel_partial_solve_wit_14_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_14 : OSTmrDel_partial_solve_wit_14.
Axiom proof_of_OSTmrDel_partial_solve_wit_15_pure : OSTmrDel_partial_solve_wit_15_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_15 : OSTmrDel_partial_solve_wit_15.
Axiom proof_of_OSTmrDel_partial_solve_wit_16_pure : OSTmrDel_partial_solve_wit_16_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_16 : OSTmrDel_partial_solve_wit_16.
Axiom proof_of_OSTmrDel_partial_solve_wit_17_pure : OSTmrDel_partial_solve_wit_17_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_17 : OSTmrDel_partial_solve_wit_17.
Axiom proof_of_OSTmrDel_partial_solve_wit_18_pure : OSTmrDel_partial_solve_wit_18_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_18 : OSTmrDel_partial_solve_wit_18.
Axiom proof_of_OSTmrDel_partial_solve_wit_19_pure : OSTmrDel_partial_solve_wit_19_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_19 : OSTmrDel_partial_solve_wit_19.
Axiom proof_of_OSTmrDel_partial_solve_wit_20_pure : OSTmrDel_partial_solve_wit_20_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_20 : OSTmrDel_partial_solve_wit_20.
Axiom proof_of_OSTmrDel_partial_solve_wit_21_pure : OSTmrDel_partial_solve_wit_21_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_21 : OSTmrDel_partial_solve_wit_21.
Axiom proof_of_OSTmrDel_partial_solve_wit_22_pure : OSTmrDel_partial_solve_wit_22_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_22 : OSTmrDel_partial_solve_wit_22.
Axiom proof_of_OSTmrDel_partial_solve_wit_23_pure : OSTmrDel_partial_solve_wit_23_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_23 : OSTmrDel_partial_solve_wit_23.
Axiom proof_of_OSTmrDel_partial_solve_wit_24_pure : OSTmrDel_partial_solve_wit_24_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_24 : OSTmrDel_partial_solve_wit_24.
Axiom proof_of_OSTmrDel_partial_solve_wit_25_pure : OSTmrDel_partial_solve_wit_25_pure.
Axiom proof_of_OSTmrDel_partial_solve_wit_25 : OSTmrDel_partial_solve_wit_25.
Axiom proof_of_OSTmrDel_which_implies_wit_1 : OSTmrDel_which_implies_wit_1.
Axiom proof_of_OSTmrDel_which_implies_wit_2 : OSTmrDel_which_implies_wit_2.
Axiom proof_of_OSTmrDel_which_implies_wit_3 : OSTmrDel_which_implies_wit_3.
Axiom proof_of_OSTmrDel_which_implies_wit_4 : OSTmrDel_which_implies_wit_4.
Axiom proof_of_OSTmrDel_which_implies_wit_5 : OSTmrDel_which_implies_wit_5.
Axiom proof_of_OSTmrDel_which_implies_wit_6 : OSTmrDel_which_implies_wit_6.
Axiom proof_of_OSTmrDel_which_implies_wit_7 : OSTmrDel_which_implies_wit_7.
Axiom proof_of_OSTmrDel_which_implies_wit_8 : OSTmrDel_which_implies_wit_8.
Axiom proof_of_OSTmrDel_which_implies_wit_9 : OSTmrDel_which_implies_wit_9.
Axiom proof_of_OSTmrDel_which_implies_wit_10 : OSTmrDel_which_implies_wit_10.
Axiom proof_of_OSTmrDel_which_implies_wit_11 : OSTmrDel_which_implies_wit_11.

End VC_Correct.
