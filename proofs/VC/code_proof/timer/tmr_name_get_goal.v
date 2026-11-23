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
Require Import Ucos2Verify.VC.code.timer.spec.tmr_name_get_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSTmrNameGet -----*)

Definition OSTmrNameGet_safety_wit_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = p)) (PreH2 : (pdest_pre = dest)) (PreH3 : (perr_pre = error_addr)) (PreH4 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH6 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrNameGet_safety_wit_2 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pdest_pre <> 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (pdest_pre = dest)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSTmrNameGet_entail_wit_1_1 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_post (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) chars retval (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (retval = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "pdest" ) )) # Ptr  |-> dest)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_post (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) chars retval (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (retval = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
).

Definition OSTmrNameGet_entail_wit_1_2 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH40 : (1 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_post (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) chars retval (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (retval = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "pdest" ) )) # Ptr  |-> dest)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH40 : (1 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_post (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) chars retval (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (retval = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
).

Definition OSTmrNameGet_entail_wit_1_3 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH40 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH41 : (2 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_post (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) chars retval (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (retval = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "pdest" ) )) # Ptr  |-> dest)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (retval: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH40 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH41 : (2 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_post (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) chars retval (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((perr_pre) # UChar  |->_)
|--
  EX (x: Z) ,
  “ (perr_pre = error_addr) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (retval = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  ((error_addr) # UChar  |-> x)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
).

Definition OSTmrNameGet_return_wit_1 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH38 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH38 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
).

Definition OSTmrNameGet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH38 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 141)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
.

Definition OSTmrNameGet_return_wit_2 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : ((tmr_name_get_type (view) (before)) = 100)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH20 : (p <> 0)) (PreH21 : (dest <> 0)) (PreH22 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (pdest_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (pdest_pre = dest)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH30 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH32 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH33 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH34 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH35 : (0 = (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : ((tmr_name_get_type (view) (before)) = 100)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH20 : (p <> 0)) (PreH21 : (dest <> 0)) (PreH22 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (pdest_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (pdest_pre = dest)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH30 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH32 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH33 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH34 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH35 : (0 = (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
).

Definition OSTmrNameGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : ((tmr_name_get_type (view) (before)) = 100)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH20 : (p <> 0)) (PreH21 : (dest <> 0)) (PreH22 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (pdest_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (pdest_pre = dest)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH30 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH32 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH33 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH34 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH35 : (0 = (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 135)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
.

Definition OSTmrNameGet_return_wit_3 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |-> 0)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old len X )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |-> 0)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old len X )
).

Definition OSTmrNameGet_return_wit_3_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  (os_sched_unlock_post external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |-> 0)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old len X )
.

Definition OSTmrNameGet_return_wit_4 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) > 0)) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : ((tmr_name_get_type (view) (before)) = 100)) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (dest <> 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (pdest_pre <> 0)) (PreH17 : (ptmr_pre = p)) (PreH18 : (pdest_pre = dest)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 17)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) > 0)) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : ((tmr_name_get_type (view) (before)) = 100)) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (dest <> 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (pdest_pre <> 0)) (PreH17 : (ptmr_pre = p)) (PreH18 : (pdest_pre = dest)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 17)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
).

Definition OSTmrNameGet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) > 0)) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : ((tmr_name_get_type (view) (before)) = 100)) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (dest <> 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (pdest_pre <> 0)) (PreH17 : (ptmr_pre = p)) (PreH18 : (pdest_pre = dest)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 17)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
.

Definition OSTmrNameGet_return_wit_5 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) <> 100)) (PreH4 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (pdest_pre <> 0)) (PreH12 : (ptmr_pre = p)) (PreH13 : (pdest_pre = dest)) (PreH14 : (perr_pre = error_addr)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) <> 100)) (PreH4 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (pdest_pre <> 0)) (PreH12 : (ptmr_pre = p)) (PreH13 : (pdest_pre = dest)) (PreH14 : (perr_pre = error_addr)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
).

Definition OSTmrNameGet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) <> 100)) (PreH4 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (pdest_pre <> 0)) (PreH12 : (ptmr_pre = p)) (PreH13 : (pdest_pre = dest)) (PreH14 : (perr_pre = error_addr)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 137)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
.

Definition OSTmrNameGet_return_wit_6 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (pdest_pre <> 0)) (PreH3 : (ptmr_pre = p)) (PreH4 : (pdest_pre = dest)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 138)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (pdest_pre <> 0)) (PreH3 : (ptmr_pre = p)) (PreH4 : (pdest_pre = dest)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 138)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
).

Definition OSTmrNameGet_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre = 0)) (PreH2 : (pdest_pre <> 0)) (PreH3 : (ptmr_pre = p)) (PreH4 : (pdest_pre = dest)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 138)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
.

Definition OSTmrNameGet_return_wit_7 := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pdest_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (pdest_pre = dest)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 136)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pdest_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (pdest_pre = dest)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 136)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
).

Definition OSTmrNameGet_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (pdest_pre = 0)) (PreH2 : (ptmr_pre = p)) (PreH3 : (pdest_pre = dest)) (PreH4 : (perr_pre = error_addr)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH7 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |-> 136)
|--
  (tmr_name_get_post external platform critical sg context mask view p dest error_addr before old 0 X )
.

Definition OSTmrNameGet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (pdest_pre <> 0)) (PreH3 : (ptmr_pre = p)) (PreH4 : (pdest_pre = dest)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (ptmr_pre <> 0)) (PreH2 : (pdest_pre <> 0)) (PreH3 : (ptmr_pre = p)) (PreH4 : (pdest_pre = dest)) (PreH5 : (perr_pre = error_addr)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_1 := OSTmrNameGet_partial_solve_wit_1_pure -> OSTmrNameGet_partial_solve_wit_1_aux.

Definition OSTmrNameGet_partial_solve_wit_2_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_type (view) (before)) <> 100) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_type (view) (before)) <> 100) ”
).

Definition OSTmrNameGet_partial_solve_wit_2_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_type (view) (before)) <> 100) ”
.

Definition OSTmrNameGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_type (view) (before)) <> 100) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) <> 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_2 := OSTmrNameGet_partial_solve_wit_2_pure -> OSTmrNameGet_partial_solve_wit_2_aux.

Definition OSTmrNameGet_partial_solve_wit_3_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_type (view) (before)) = 100) ”
).

Definition OSTmrNameGet_partial_solve_wit_3_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_type (view) (before)) = 100) ”
.

Definition OSTmrNameGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH2 : (p <> 0)) (PreH3 : (dest <> 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (ptmr_pre <> 0)) (PreH7 : (pdest_pre <> 0)) (PreH8 : (ptmr_pre = p)) (PreH9 : (pdest_pre = dest)) (PreH10 : (perr_pre = error_addr)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH13 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_3 := OSTmrNameGet_partial_solve_wit_3_pure -> OSTmrNameGet_partial_solve_wit_3_aux.

Definition OSTmrNameGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (pdest_pre <> 0)) (PreH12 : (ptmr_pre = p)) (PreH13 : (pdest_pre = dest)) (PreH14 : (perr_pre = error_addr)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH5 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (ptmr_pre <> 0)) (PreH11 : (pdest_pre <> 0)) (PreH12 : (ptmr_pre = p)) (PreH13 : (pdest_pre = dest)) (PreH14 : (perr_pre = error_addr)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH17 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_4 := OSTmrNameGet_partial_solve_wit_4_pure -> OSTmrNameGet_partial_solve_wit_4_aux.

Definition OSTmrNameGet_partial_solve_wit_5_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((task_name_get_nesting (before)) > 0) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_get_nesting (before)) > 0) ”
).

Definition OSTmrNameGet_partial_solve_wit_5_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_get_nesting (before)) > 0) ”
.

Definition OSTmrNameGet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((task_name_get_nesting (before)) > 0) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_5 := OSTmrNameGet_partial_solve_wit_5_pure -> OSTmrNameGet_partial_solve_wit_5_aux.

Definition OSTmrNameGet_partial_solve_wit_6_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_get_nesting (before)) = 0) ”
).

Definition OSTmrNameGet_partial_solve_wit_6_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_get_nesting (before)) = 0) ”
.

Definition OSTmrNameGet_partial_solve_wit_6_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (p <> 0)) (PreH5 : (dest <> 0)) (PreH6 : ((tmr_name_get_type (view) (before)) = 100)) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (ptmr_pre <> 0)) (PreH14 : (pdest_pre <> 0)) (PreH15 : (ptmr_pre = p)) (PreH16 : (pdest_pre = dest)) (PreH17 : (perr_pre = error_addr)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH20 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_6 := OSTmrNameGet_partial_solve_wit_6_pure -> OSTmrNameGet_partial_solve_wit_6_aux.

Definition OSTmrNameGet_partial_solve_wit_7_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : ((tmr_name_get_type (view) (before)) = 100)) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (dest <> 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (pdest_pre <> 0)) (PreH17 : (ptmr_pre = p)) (PreH18 : (pdest_pre = dest)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ”
.

Definition OSTmrNameGet_partial_solve_wit_7_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (p <> 0)) (PreH7 : (dest <> 0)) (PreH8 : ((tmr_name_get_type (view) (before)) = 100)) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH11 : (p <> 0)) (PreH12 : (dest <> 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (ptmr_pre <> 0)) (PreH16 : (pdest_pre <> 0)) (PreH17 : (ptmr_pre = p)) (PreH18 : (pdest_pre = dest)) (PreH19 : (perr_pre = error_addr)) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH22 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_7 := OSTmrNameGet_partial_solve_wit_7_pure -> OSTmrNameGet_partial_solve_wit_7_aux.

Definition OSTmrNameGet_partial_solve_wit_8_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : ((tmr_name_get_type (view) (before)) = 100)) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH14 : (p <> 0)) (PreH15 : (dest <> 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (pdest_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (pdest_pre = dest)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_8_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : ((tmr_name_get_type (view) (before)) = 100)) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH14 : (p <> 0)) (PreH15 : (dest <> 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (pdest_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (pdest_pre = dest)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_8 := OSTmrNameGet_partial_solve_wit_8_pure -> OSTmrNameGet_partial_solve_wit_8_aux.

Definition OSTmrNameGet_partial_solve_wit_9_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : ((tmr_name_get_type (view) (before)) = 100)) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH14 : (p <> 0)) (PreH15 : (dest <> 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (pdest_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (pdest_pre = dest)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ”
.

Definition OSTmrNameGet_partial_solve_wit_9_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH7 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (p <> 0)) (PreH10 : (dest <> 0)) (PreH11 : ((tmr_name_get_type (view) (before)) = 100)) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH14 : (p <> 0)) (PreH15 : (dest <> 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (ptmr_pre <> 0)) (PreH19 : (pdest_pre <> 0)) (PreH20 : (ptmr_pre = p)) (PreH21 : (pdest_pre = dest)) (PreH22 : (perr_pre = error_addr)) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH25 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_9 := OSTmrNameGet_partial_solve_wit_9_pure -> OSTmrNameGet_partial_solve_wit_9_aux.

Definition OSTmrNameGet_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : ((task_name_get_nesting (before)) = 0)) (PreH3 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH4 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH5 : ((task_name_get_nesting (before)) = 0)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (p <> 0)) (PreH11 : (dest <> 0)) (PreH12 : ((tmr_name_get_type (view) (before)) = 100)) (PreH13 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (ptmr_pre <> 0)) (PreH20 : (pdest_pre <> 0)) (PreH21 : (ptmr_pre = p)) (PreH22 : (pdest_pre = dest)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
  **  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : ((task_name_get_nesting (before)) = 0)) (PreH3 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH4 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH5 : ((task_name_get_nesting (before)) = 0)) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH10 : (p <> 0)) (PreH11 : (dest <> 0)) (PreH12 : ((tmr_name_get_type (view) (before)) = 100)) (PreH13 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH14 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : (ptmr_pre <> 0)) (PreH20 : (pdest_pre <> 0)) (PreH21 : (ptmr_pre = p)) (PreH22 : (pdest_pre = dest)) (PreH23 : (perr_pre = error_addr)) (PreH24 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH25 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH26 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) ,
  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ”
  &&  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_10 := OSTmrNameGet_partial_solve_wit_10_pure -> OSTmrNameGet_partial_solve_wit_10_aux.

Definition OSTmrNameGet_partial_solve_wit_11_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful (2)) = true) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (2)) = true) ” 
  &&  “ ((tmr_name_get_successful (2)) = true) ”
).

Definition OSTmrNameGet_partial_solve_wit_11_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (2)) = true) ”
.

Definition OSTmrNameGet_partial_solve_wit_11_pure_split_goal_2 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (2)) = true) ”
.

Definition OSTmrNameGet_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful (2)) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_11 := OSTmrNameGet_partial_solve_wit_11_pure -> OSTmrNameGet_partial_solve_wit_11_aux.

Definition OSTmrNameGet_partial_solve_wit_12_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful (1)) = true) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (1)) = true) ” 
  &&  “ ((tmr_name_get_successful (1)) = true) ”
).

Definition OSTmrNameGet_partial_solve_wit_12_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (1)) = true) ”
.

Definition OSTmrNameGet_partial_solve_wit_12_pure_split_goal_2 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (1)) = true) ”
.

Definition OSTmrNameGet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful (1)) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_12 := OSTmrNameGet_partial_solve_wit_12_pure -> OSTmrNameGet_partial_solve_wit_12_aux.

Definition OSTmrNameGet_partial_solve_wit_13_pure := 
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful (3)) = true) ”
) \/
(
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (3)) = true) ” 
  &&  “ ((tmr_name_get_successful (3)) = true) ”
).

Definition OSTmrNameGet_partial_solve_wit_13_pure_split_goal_1 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (3)) = true) ”
.

Definition OSTmrNameGet_partial_solve_wit_13_pure_split_goal_2 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful (3)) = true) ”
.

Definition OSTmrNameGet_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful (3)) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_13 := OSTmrNameGet_partial_solve_wit_13_pure -> OSTmrNameGet_partial_solve_wit_13_aux.

Definition OSTmrNameGet_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (old = (Some (previous)))) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ”
.

Definition OSTmrNameGet_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (old = (Some (previous)))) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_14 := OSTmrNameGet_partial_solve_wit_14_pure -> OSTmrNameGet_partial_solve_wit_14_aux.

Definition OSTmrNameGet_partial_solve_wit_15_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (old = (Some (previous)))) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ”
.

Definition OSTmrNameGet_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (old = (Some (previous)))) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_15 := OSTmrNameGet_partial_solve_wit_15_pure -> OSTmrNameGet_partial_solve_wit_15_aux.

Definition OSTmrNameGet_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (old = (Some (previous)))) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ”
.

Definition OSTmrNameGet_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (old = (Some (previous)))) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_16 := OSTmrNameGet_partial_solve_wit_16_pure -> OSTmrNameGet_partial_solve_wit_16_aux.

Definition OSTmrNameGet_partial_solve_wit_17 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 = (tmr_name_get_state (view) (locked))) ”
  &&  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_18 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH40 : (1 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 = (tmr_name_get_state (view) (locked))) ”
  &&  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_19 := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (previous: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH8 : (old = (Some (previous)))) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars ))) (PreH11 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH12 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH13 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH14 : ((task_name_get_nesting (before)) = 0)) (PreH15 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH16 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH17 : ((task_name_get_nesting (before)) = 0)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH20 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : (p <> 0)) (PreH23 : (dest <> 0)) (PreH24 : ((tmr_name_get_type (view) (before)) = 100)) (PreH25 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH26 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH27 : (p <> 0)) (PreH28 : (dest <> 0)) (PreH29 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH30 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH31 : (ptmr_pre <> 0)) (PreH32 : (pdest_pre <> 0)) (PreH33 : (ptmr_pre = p)) (PreH34 : (pdest_pre = dest)) (PreH35 : (perr_pre = error_addr)) (PreH36 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH37 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH38 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH39 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH40 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH41 : (2 = (tmr_name_get_state (view) (locked)))) ,
  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 = (tmr_name_get_state (view) (locked))) ”
  &&  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
  **  ((pdest_pre) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_20_pure := 
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  ((( &( "len" ) )) # UChar  |-> len)
  **  ((( &( "pdest" ) )) # Ptr  |-> dest)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ”
.

Definition OSTmrNameGet_partial_solve_wit_20_aux := 
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH4 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH5 : (tmr_name_get_name_readable view locked chars )) (PreH6 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_20 := OSTmrNameGet_partial_solve_wit_20_pure -> OSTmrNameGet_partial_solve_wit_20_aux.

Definition OSTmrNameGet_partial_solve_wit_21_pure := 
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> p)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((( &( "len" ) )) # UChar  |-> len)
  **  ((( &( "pdest" ) )) # Ptr  |-> dest)
  **  ((( &( "perr" ) )) # Ptr  |-> error_addr)
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_21_aux := 
forall (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (len: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH8 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH9 : (tmr_name_get_name_readable view locked chars )) (PreH10 : (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((p)  # "os_tmr" ->ₛ "OSTmrType") &((p)  # "os_tmr" ->ₛ "OSTmrName") &((p)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (len = (task_name_get_length ((tmr_name_get_name (view) (locked))) (chars))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((dest) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  ((error_addr) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_21 := OSTmrNameGet_partial_solve_wit_21_pure -> OSTmrNameGet_partial_solve_wit_21_aux.

Definition OSTmrNameGet_partial_solve_wit_22_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH32 : (0 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_state (view) (locked)) = 0) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_22_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH32 : (0 = (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_state (view) (locked)) = 0) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (0 = (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_22 := OSTmrNameGet_partial_solve_wit_22_pure -> OSTmrNameGet_partial_solve_wit_22_aux.

Definition OSTmrNameGet_partial_solve_wit_23_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : ((tmr_name_get_type (view) (before)) = 100)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH20 : (p <> 0)) (PreH21 : (dest <> 0)) (PreH22 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (pdest_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (pdest_pre = dest)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH30 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH32 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH33 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH34 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH35 : (0 = (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_23_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH4 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH5 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH6 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH9 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH13 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : (p <> 0)) (PreH16 : (dest <> 0)) (PreH17 : ((tmr_name_get_type (view) (before)) = 100)) (PreH18 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH19 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH20 : (p <> 0)) (PreH21 : (dest <> 0)) (PreH22 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH23 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH24 : (ptmr_pre <> 0)) (PreH25 : (pdest_pre <> 0)) (PreH26 : (ptmr_pre = p)) (PreH27 : (pdest_pre = dest)) (PreH28 : (perr_pre = error_addr)) (PreH29 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH30 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH31 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH32 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH33 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH34 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH35 : (0 = (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) = 0) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (0 = (tmr_name_get_state (view) (locked))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_23 := OSTmrNameGet_partial_solve_wit_23_pure -> OSTmrNameGet_partial_solve_wit_23_aux.

Definition OSTmrNameGet_partial_solve_wit_24_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH38 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_24_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH7 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH10 : ((task_name_get_nesting (before)) = 0)) (PreH11 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH12 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH13 : ((task_name_get_nesting (before)) = 0)) (PreH14 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH15 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH16 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH17 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH18 : (p <> 0)) (PreH19 : (dest <> 0)) (PreH20 : ((tmr_name_get_type (view) (before)) = 100)) (PreH21 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH22 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH23 : (p <> 0)) (PreH24 : (dest <> 0)) (PreH25 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (ptmr_pre <> 0)) (PreH28 : (pdest_pre <> 0)) (PreH29 : (ptmr_pre = p)) (PreH30 : (pdest_pre = dest)) (PreH31 : (perr_pre = error_addr)) (PreH32 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH33 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH34 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH35 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH36 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH37 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH38 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 0) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 1) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 2) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 3) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (0 <> (tmr_name_get_state (view) (locked))) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_24 := OSTmrNameGet_partial_solve_wit_24_pure -> OSTmrNameGet_partial_solve_wit_24_aux.

Definition OSTmrNameGet_partial_solve_wit_25_pure := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH32 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  ((( &( "ptmr" ) )) # Ptr  |-> ptmr_pre)
  **  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pdest" ) )) # Ptr  |-> pdest_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_state (view) (locked)) <> 0) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 1) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 2) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 3) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
.

Definition OSTmrNameGet_partial_solve_wit_25_aux := 
forall (perr_pre: Z) (pdest_pre: Z) (ptmr_pre: Z) (X: TmrNameGetPost) (old: (@option Z)) (error_addr: Z) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH4 : ((task_name_get_nesting (before)) = 0)) (PreH5 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH6 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) (PreH7 : ((task_name_get_nesting (before)) = 0)) (PreH8 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH9 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH10 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH11 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH12 : (p <> 0)) (PreH13 : (dest <> 0)) (PreH14 : ((tmr_name_get_type (view) (before)) = 100)) (PreH15 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH16 : ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100)) (PreH17 : (p <> 0)) (PreH18 : (dest <> 0)) (PreH19 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH20 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH21 : (ptmr_pre <> 0)) (PreH22 : (pdest_pre <> 0)) (PreH23 : (ptmr_pre = p)) (PreH24 : (pdest_pre = dest)) (PreH25 : (perr_pre = error_addr)) (PreH26 : (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH27 : (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) )) (PreH28 : (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) )) (PreH29 : (3 <> (tmr_name_get_state (view) (locked)))) (PreH30 : (1 <> (tmr_name_get_state (view) (locked)))) (PreH31 : (2 <> (tmr_name_get_state (view) (locked)))) (PreH32 : (0 <> (tmr_name_get_state (view) (locked)))) ,
  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
|--
  “ ((tmr_name_get_state (view) (locked)) <> 0) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 1) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 2) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 3) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((unsigned_last_nbits ((tmr_name_get_type (view) (before))) (32)) = 100) ” 
  &&  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (ptmr_pre <> 0) ” 
  &&  “ (pdest_pre <> 0) ” 
  &&  “ (ptmr_pre = p) ” 
  &&  “ (pdest_pre = dest) ” 
  &&  “ (perr_pre = error_addr) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (os_sched_unlock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ( &( "OSPrioHighRdy" ) ) ( &( "OSPrioCur" ) ) ( &( "OSTCBHighRdy" ) ) ( &( "OSTCBPrioTbl" ) ) ( &( "OSCtxSwCtr" ) ) ( &( "OSUnMapTbl" ) ) ( &( "OSRdyGrp" ) ) ( &( "OSRdyTbl" ) ) ) ” 
  &&  “ (os_sched_lock_global_addresses sg ( &( "OSRunning" ) ) ( &( "OSIntNesting" ) ) ( &( "OSLockNesting" ) ) ) ” 
  &&  “ (3 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (1 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (2 <> (tmr_name_get_state (view) (locked))) ” 
  &&  “ (0 <> (tmr_name_get_state (view) (locked))) ”
  &&  ((&((ptmr_pre)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest_pre old )
  **  ((perr_pre) # UChar  |->_)
.

Definition OSTmrNameGet_partial_solve_wit_25 := OSTmrNameGet_partial_solve_wit_25_pure -> OSTmrNameGet_partial_solve_wit_25_aux.

Definition OSTmrNameGet_which_implies_wit_1 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
).

Definition OSTmrNameGet_which_implies_wit_1_split_goal_1 := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ”
.

Definition OSTmrNameGet_which_implies_wit_1_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
.

Definition OSTmrNameGet_which_implies_wit_2 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) <> 100)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) <> 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) <> 100)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
).

Definition OSTmrNameGet_which_implies_wit_2_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) <> 100)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
.

Definition OSTmrNameGet_which_implies_wit_3 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
|--
  “ (p <> 0) ” 
  &&  “ (dest <> 0) ” 
  &&  “ ((tmr_name_get_type (view) (before)) = 100) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
).

Definition OSTmrNameGet_which_implies_wit_3_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH5 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrType")) # UChar  |-> (tmr_name_get_type (view) (before)))
  **  (tmr_name_get_type_rest external platform critical sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
.

Definition OSTmrNameGet_which_implies_wit_4 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ”
  &&  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
).

Definition OSTmrNameGet_which_implies_wit_4_split_goal_1 := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ”
.

Definition OSTmrNameGet_which_implies_wit_4_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
.

Definition OSTmrNameGet_which_implies_wit_5 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : ((task_name_get_nesting (before)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
|--
  “ ((task_name_get_nesting (before)) > 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : ((task_name_get_nesting (before)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
).

Definition OSTmrNameGet_which_implies_wit_5_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : ((task_name_get_nesting (before)) > 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
.

Definition OSTmrNameGet_which_implies_wit_6 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
|--
  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
).

Definition OSTmrNameGet_which_implies_wit_6_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (ptmr: Z) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (tmr_name_get_int_rest external platform sg context mask view p dest before )
|--
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
.

Definition OSTmrNameGet_which_implies_wit_7 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : ((task_name_get_nesting (before)) = 0)) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ ((task_name_get_nesting (before)) = 0) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ” 
  &&  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : ((task_name_get_nesting (before)) = 0)) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ” 
  &&  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ”
  &&  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
).

Definition OSTmrNameGet_which_implies_wit_7_split_goal_1 := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : ((task_name_get_nesting (before)) = 0)) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ ((tmr_name_get_early_error (view) (p) (dest) (before)) = None) ”
.

Definition OSTmrNameGet_which_implies_wit_7_split_goal_2 := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : ((task_name_get_nesting (before)) = 0)) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  “ (tmr_name_get_entry_facts external critical sg context view p dest before old X ) ”
.

Definition OSTmrNameGet_which_implies_wit_7_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : (p <> 0)) (PreH2 : (dest <> 0)) (PreH3 : ((tmr_name_get_type (view) (before)) = 100)) (PreH4 : ((task_name_get_nesting (before)) = 0)) ,
  (tmr_name_get_pre external platform critical sg context mask view p dest before old X )
|--
  (os_sched_lock_pre platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
.

Definition OSTmrNameGet_which_implies_wit_8 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
|--
  EX (locked: UCOS2_Verify_State) ,
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ”
  &&  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (PreH1 : ((task_name_get_nesting (before)) = 0)) (PreH2 : (tmr_name_get_entry_facts external critical sg context view p dest before old X )) (PreH3 : ((tmr_name_get_early_error (view) (p) (dest) (before)) = None)) ,
  (os_sched_lock_post platform critical sg (os_sched_call_invocation (context)) (os_sched_call_origin (context)) mask before )
  **  (tmr_name_get_continuation external sg context )
  **  (tmr_name_get_private view p dest before )
|--
  EX (locked: UCOS2_Verify_State) ,
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ”
  &&  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
).

Definition OSTmrNameGet_which_implies_wit_9 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
).

Definition OSTmrNameGet_which_implies_wit_9_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  (tmr_name_get_locked external platform critical sg context mask view p dest before locked )
|--
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
.

Definition OSTmrNameGet_which_implies_wit_10 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (pdest: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest old )
|--
  EX (chars: (@list Z))  (previous: Z) ,
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest) # Ptr  |-> previous)
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (pdest: Z) (PreH1 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
  **  (task_name_get_output_cell pdest old )
|--
  EX (chars: (@list Z))  (previous: Z) ,
  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ” 
  &&  “ (((tmr_name_get_name (view) (locked)) <> 0) -> (readable_name (tmr_name_get_names (view) (locked)) (tmr_name_get_name (view) (locked)) chars )) ”
  &&  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
  **  ((pdest) # Ptr  |-> previous)
).

Definition OSTmrNameGet_which_implies_wit_11 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ”
  &&  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
|--
  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
).

Definition OSTmrNameGet_which_implies_wit_11_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrName")) # Ptr  |-> (tmr_name_get_name (view) (locked)))
  **  (tmr_name_get_name_rest external platform critical sg context mask view p dest before locked )
|--
  (tmr_name_get_strlen_pre (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_name (view) (locked)) (tmr_name_get_names (view) (locked)) chars (tmr_name_get_strlen_frame (external) (platform) (critical) (sg) (context) (mask) (view) (p) (locked) (chars)) )
.

Definition OSTmrNameGet_which_implies_wit_12 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) ,
  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
|--
  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ” 
  &&  “ ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true) ” 
  &&  “ (tmr_name_get_name_readable view locked chars ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) ,
  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
).

Definition OSTmrNameGet_which_implies_wit_12_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (chars: (@list Z)) (ptmr: Z) (PreH1 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH2 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) (PreH3 : ((tmr_name_get_successful ((tmr_name_get_state (view) (locked)))) = true)) (PreH4 : (tmr_name_get_name_readable view locked chars )) ,
  (task_name_get_name_bytes (tmr_name_get_name (view) (locked)) chars )
  **  (tmr_name_get_strlen_frame external platform critical sg context mask view p locked chars )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
.

Definition OSTmrNameGet_which_implies_wit_13 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
|--
  “ ((tmr_name_get_state (view) (locked)) = 0) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
).

Definition OSTmrNameGet_which_implies_wit_13_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : ((tmr_name_get_state (view) (locked)) = 0)) (PreH2 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH3 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
.

Definition OSTmrNameGet_which_implies_wit_14 := 
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
|--
  “ ((tmr_name_get_state (view) (locked)) <> 0) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 1) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 2) ” 
  &&  “ ((tmr_name_get_state (view) (locked)) <> 3) ” 
  &&  “ (tmr_name_get_lock_facts external critical sg context view p dest before old X locked ) ” 
  &&  “ (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) ) ”
  &&  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
) \/
(
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
).

Definition OSTmrNameGet_which_implies_wit_14_split_goal_spatial := 
forall (X: TmrNameGetPost) (old: (@option Z)) (dest: Z) (p: Z) (before: UCOS2_Verify_State) (view: TmrNameGetView) (mask: Z) (context: OsSchedCallContext) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (external: OsSchedExternalResources) (locked: UCOS2_Verify_State) (ptmr: Z) (PreH1 : ((tmr_name_get_state (view) (locked)) <> 0)) (PreH2 : ((tmr_name_get_state (view) (locked)) <> 1)) (PreH3 : ((tmr_name_get_state (view) (locked)) <> 2)) (PreH4 : ((tmr_name_get_state (view) (locked)) <> 3)) (PreH5 : (tmr_name_get_lock_facts external critical sg context view p dest before old X locked )) (PreH6 : (tmr_name_get_layout sg p &((ptmr)  # "os_tmr" ->ₛ "OSTmrType") &((ptmr)  # "os_tmr" ->ₛ "OSTmrName") &((ptmr)  # "os_tmr" ->ₛ "OSTmrState") ( &( "OSIntNesting" ) ) )) ,
  ((&((ptmr)  # "os_tmr" ->ₛ "OSTmrState")) # UChar  |-> (tmr_name_get_state (view) (locked)))
  **  (tmr_name_get_state_rest external platform critical sg context mask view p dest before locked )
|--
  (os_sched_unlock_pre external platform critical sg context mask locked )
  **  (tmr_name_get_private view p dest before )
.

Module Type VC_Correct.


Axiom proof_of_OSTmrNameGet_safety_wit_1 : OSTmrNameGet_safety_wit_1.
Axiom proof_of_OSTmrNameGet_safety_wit_2 : OSTmrNameGet_safety_wit_2.
Axiom proof_of_OSTmrNameGet_entail_wit_1_1 : OSTmrNameGet_entail_wit_1_1.
Axiom proof_of_OSTmrNameGet_entail_wit_1_2 : OSTmrNameGet_entail_wit_1_2.
Axiom proof_of_OSTmrNameGet_entail_wit_1_3 : OSTmrNameGet_entail_wit_1_3.
Axiom proof_of_OSTmrNameGet_return_wit_1 : OSTmrNameGet_return_wit_1.
Axiom proof_of_OSTmrNameGet_return_wit_2 : OSTmrNameGet_return_wit_2.
Axiom proof_of_OSTmrNameGet_return_wit_3 : OSTmrNameGet_return_wit_3.
Axiom proof_of_OSTmrNameGet_return_wit_4 : OSTmrNameGet_return_wit_4.
Axiom proof_of_OSTmrNameGet_return_wit_5 : OSTmrNameGet_return_wit_5.
Axiom proof_of_OSTmrNameGet_return_wit_6 : OSTmrNameGet_return_wit_6.
Axiom proof_of_OSTmrNameGet_return_wit_7 : OSTmrNameGet_return_wit_7.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_1_pure : OSTmrNameGet_partial_solve_wit_1_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_1 : OSTmrNameGet_partial_solve_wit_1.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_2_pure : OSTmrNameGet_partial_solve_wit_2_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_2 : OSTmrNameGet_partial_solve_wit_2.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_3_pure : OSTmrNameGet_partial_solve_wit_3_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_3 : OSTmrNameGet_partial_solve_wit_3.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_4_pure : OSTmrNameGet_partial_solve_wit_4_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_4 : OSTmrNameGet_partial_solve_wit_4.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_5_pure : OSTmrNameGet_partial_solve_wit_5_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_5 : OSTmrNameGet_partial_solve_wit_5.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_6_pure : OSTmrNameGet_partial_solve_wit_6_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_6 : OSTmrNameGet_partial_solve_wit_6.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_7_pure : OSTmrNameGet_partial_solve_wit_7_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_7 : OSTmrNameGet_partial_solve_wit_7.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_8_pure : OSTmrNameGet_partial_solve_wit_8_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_8 : OSTmrNameGet_partial_solve_wit_8.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_9_pure : OSTmrNameGet_partial_solve_wit_9_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_9 : OSTmrNameGet_partial_solve_wit_9.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_10_pure : OSTmrNameGet_partial_solve_wit_10_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_10 : OSTmrNameGet_partial_solve_wit_10.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_11_pure : OSTmrNameGet_partial_solve_wit_11_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_11 : OSTmrNameGet_partial_solve_wit_11.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_12_pure : OSTmrNameGet_partial_solve_wit_12_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_12 : OSTmrNameGet_partial_solve_wit_12.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_13_pure : OSTmrNameGet_partial_solve_wit_13_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_13 : OSTmrNameGet_partial_solve_wit_13.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_14_pure : OSTmrNameGet_partial_solve_wit_14_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_14 : OSTmrNameGet_partial_solve_wit_14.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_15_pure : OSTmrNameGet_partial_solve_wit_15_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_15 : OSTmrNameGet_partial_solve_wit_15.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_16_pure : OSTmrNameGet_partial_solve_wit_16_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_16 : OSTmrNameGet_partial_solve_wit_16.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_17 : OSTmrNameGet_partial_solve_wit_17.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_18 : OSTmrNameGet_partial_solve_wit_18.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_19 : OSTmrNameGet_partial_solve_wit_19.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_20_pure : OSTmrNameGet_partial_solve_wit_20_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_20 : OSTmrNameGet_partial_solve_wit_20.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_21_pure : OSTmrNameGet_partial_solve_wit_21_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_21 : OSTmrNameGet_partial_solve_wit_21.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_22_pure : OSTmrNameGet_partial_solve_wit_22_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_22 : OSTmrNameGet_partial_solve_wit_22.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_23_pure : OSTmrNameGet_partial_solve_wit_23_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_23 : OSTmrNameGet_partial_solve_wit_23.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_24_pure : OSTmrNameGet_partial_solve_wit_24_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_24 : OSTmrNameGet_partial_solve_wit_24.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_25_pure : OSTmrNameGet_partial_solve_wit_25_pure.
Axiom proof_of_OSTmrNameGet_partial_solve_wit_25 : OSTmrNameGet_partial_solve_wit_25.
Axiom proof_of_OSTmrNameGet_which_implies_wit_1 : OSTmrNameGet_which_implies_wit_1.
Axiom proof_of_OSTmrNameGet_which_implies_wit_2 : OSTmrNameGet_which_implies_wit_2.
Axiom proof_of_OSTmrNameGet_which_implies_wit_3 : OSTmrNameGet_which_implies_wit_3.
Axiom proof_of_OSTmrNameGet_which_implies_wit_4 : OSTmrNameGet_which_implies_wit_4.
Axiom proof_of_OSTmrNameGet_which_implies_wit_5 : OSTmrNameGet_which_implies_wit_5.
Axiom proof_of_OSTmrNameGet_which_implies_wit_6 : OSTmrNameGet_which_implies_wit_6.
Axiom proof_of_OSTmrNameGet_which_implies_wit_7 : OSTmrNameGet_which_implies_wit_7.
Axiom proof_of_OSTmrNameGet_which_implies_wit_8 : OSTmrNameGet_which_implies_wit_8.
Axiom proof_of_OSTmrNameGet_which_implies_wit_9 : OSTmrNameGet_which_implies_wit_9.
Axiom proof_of_OSTmrNameGet_which_implies_wit_10 : OSTmrNameGet_which_implies_wit_10.
Axiom proof_of_OSTmrNameGet_which_implies_wit_11 : OSTmrNameGet_which_implies_wit_11.
Axiom proof_of_OSTmrNameGet_which_implies_wit_12 : OSTmrNameGet_which_implies_wit_12.
Axiom proof_of_OSTmrNameGet_which_implies_wit_13 : OSTmrNameGet_which_implies_wit_13.
Axiom proof_of_OSTmrNameGet_which_implies_wit_14 : OSTmrNameGet_which_implies_wit_14.

End VC_Correct.
