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
Require Import Ucos2Verify.VC.code.memory.spec.mem_name_get_spec.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Import Monad MonadNotation UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSMemNameGet -----*)

Definition OSMemNameGet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH2 : (pmem_pre = pe)) (PreH3 : (pname_pre = pn)) (PreH4 : (perr_pre = err)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameGet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre <> 0)) (PreH2 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = pn)) (PreH5 : (perr_pre = err)) (PreH6 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH7 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameGet_safety_wit_3 := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH3 : (old = (Some (previous)))) (PreH4 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH5 : (pe <> 0)) (PreH6 : (pn <> 0)) (PreH7 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH8 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH9 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((pn) # Ptr  |-> previous)
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((err) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameGet_safety_wit_4 := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH4 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH10 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH11 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH12 : (pe <> 0)) (PreH13 : (pn <> 0)) (PreH14 : (old = (Some (previous)))) (PreH15 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH16 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH17 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH18 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |->_)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSMemNameGet_entail_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = pn)) (PreH12 : (perr_pre = err)) (PreH13 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH14 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = pn)) (PreH12 : (perr_pre = err)) (PreH13 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH14 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  TT && emp 
|--
  “ ((mem_name_get_early_error (pmem_pre) (pname_pre) ((task_name_get_nesting (before)))) = None) ”
  &&  emp
).

Definition OSMemNameGet_entail_wit_1_split_goal_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = pn)) (PreH12 : (perr_pre = err)) (PreH13 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH14 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((mem_name_get_early_error (pmem_pre) (pname_pre) ((task_name_get_nesting (before)))) = None)
.

Definition OSMemNameGet_entail_wit_2 := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (entry: UCOS2_Verify_State) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask retval before entry )) (PreH2 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH3 : (old = (Some (previous)))) (PreH4 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH5 : (pe <> 0)) (PreH6 : (pn <> 0)) (PreH7 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH8 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH9 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (critical_region_masked platform critical sg invocation origin retval entry )
  **  (UCOS2_inv sg entry )
  **  ((pn) # Ptr  |-> previous)
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |->_)
|--
  EX (acquired: UCOS2_Verify_State) ,
  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask retval before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin retval acquired )
  **  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((pn) # Ptr  |-> previous)
  **  ((err) # UChar  |->_)
.

Definition OSMemNameGet_return_wit_1 := 
(
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH4 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH10 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH11 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH12 : (pe <> 0)) (PreH13 : (pn <> 0)) (PreH14 : (old = (Some (previous)))) (PreH15 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH16 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH17 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH18 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |-> 0)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old retval X )
) \/
(
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH4 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH10 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH11 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH12 : (pe <> 0)) (PreH13 : (pn <> 0)) (PreH14 : (old = (Some (previous)))) (PreH15 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH16 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH17 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH18 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |-> 0)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old retval X )
).

Definition OSMemNameGet_return_wit_1_split_goal_spatial := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH4 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH10 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH11 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH12 : (pe <> 0)) (PreH13 : (pn <> 0)) (PreH14 : (old = (Some (previous)))) (PreH15 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH16 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH17 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH18 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_query_restore_post platform critical sg invocation origin cpu_sr acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |-> 0)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old retval X )
.

Definition OSMemNameGet_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = pn)) (PreH12 : (perr_pre = err)) (PreH13 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH14 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 17)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = pn)) (PreH12 : (perr_pre = err)) (PreH13 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH14 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 17)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
).

Definition OSMemNameGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (0 <= (task_name_get_nesting (before)))) (PreH3 : ((task_name_get_nesting (before)) < 256)) (PreH4 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH5 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH6 : (UCOS2_state_inv sg before )) (PreH7 : (pname_pre <> 0)) (PreH8 : (pmem_pre <> 0)) (PreH9 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH10 : (pmem_pre = pe)) (PreH11 : (pname_pre = pn)) (PreH12 : (perr_pre = err)) (PreH13 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH14 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 17)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
.

Definition OSMemNameGet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH4 : (pmem_pre = pe)) (PreH5 : (pname_pre = pn)) (PreH6 : (perr_pre = err)) (PreH7 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 12)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH4 : (pmem_pre = pe)) (PreH5 : (pname_pre = pn)) (PreH6 : (perr_pre = err)) (PreH7 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 12)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
).

Definition OSMemNameGet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH4 : (pmem_pre = pe)) (PreH5 : (pname_pre = pn)) (PreH6 : (perr_pre = err)) (PreH7 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 12)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
.

Definition OSMemNameGet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = pn)) (PreH5 : (perr_pre = err)) (PreH6 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH7 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 96)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = pn)) (PreH5 : (perr_pre = err)) (PreH6 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH7 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 96)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
).

Definition OSMemNameGet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = 0)) (PreH2 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH3 : (pmem_pre = pe)) (PreH4 : (pname_pre = pn)) (PreH5 : (perr_pre = err)) (PreH6 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH7 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |-> 96)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  (mem_name_get_post platform critical sg invocation origin mask before pe pn err view raw raw_chars old 0 X )
.

Definition OSMemNameGet_partial_solve_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pmem_pre = pe)) (PreH2 : (pname_pre = pn)) (PreH3 : (perr_pre = err)) (PreH4 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH5 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (mem_name_get_pre platform critical sg invocation origin mask before pe pn err view raw raw_chars old )
|--
  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = pn) ” 
  &&  “ (perr_pre = err) ” 
  &&  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (mem_name_get_pre platform critical sg invocation origin mask before pe pn err view raw raw_chars old )
.

Definition OSMemNameGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH4 : (pmem_pre = pe)) (PreH5 : (pname_pre = pn)) (PreH6 : (perr_pre = err)) (PreH7 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ”
.

Definition OSMemNameGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pname_pre <> 0)) (PreH2 : (pmem_pre <> 0)) (PreH3 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH4 : (pmem_pre = pe)) (PreH5 : (pname_pre = pn)) (PreH6 : (perr_pre = err)) (PreH7 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH8 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = pn) ” 
  &&  “ (perr_pre = err) ” 
  &&  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
.

Definition OSMemNameGet_partial_solve_wit_2 := OSMemNameGet_partial_solve_wit_2_pure -> OSMemNameGet_partial_solve_wit_2_aux.

Definition OSMemNameGet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pmem_pre <> 0)) (PreH6 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH7 : (pmem_pre = pe)) (PreH8 : (pname_pre = pn)) (PreH9 : (perr_pre = err)) (PreH10 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH11 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMemNameGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0)) (PreH2 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pmem_pre <> 0)) (PreH6 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH7 : (pmem_pre = pe)) (PreH8 : (pname_pre = pn)) (PreH9 : (perr_pre = err)) (PreH10 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH11 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) > 0) ” 
  &&  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = pn) ” 
  &&  “ (perr_pre = err) ” 
  &&  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
.

Definition OSMemNameGet_partial_solve_wit_3 := OSMemNameGet_partial_solve_wit_3_pure -> OSMemNameGet_partial_solve_wit_3_aux.

Definition OSMemNameGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pmem_pre <> 0)) (PreH6 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH7 : (pmem_pre = pe)) (PreH8 : (pname_pre = pn)) (PreH9 : (perr_pre = err)) (PreH10 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH11 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pmem" ) )) # Ptr  |-> pmem_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMemNameGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pmem_pre: Z) (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0)) (PreH2 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH3 : (UCOS2_state_inv sg before )) (PreH4 : (pname_pre <> 0)) (PreH5 : (pmem_pre <> 0)) (PreH6 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH7 : (pmem_pre = pe)) (PreH8 : (pname_pre = pn)) (PreH9 : (perr_pre = err)) (PreH10 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH11 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ ((unsigned_last_nbits ((task_name_get_nesting (before))) (32)) <= 0) ” 
  &&  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pmem_pre <> 0) ” 
  &&  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ (pmem_pre = pe) ” 
  &&  “ (pname_pre = pn) ” 
  &&  “ (perr_pre = err) ” 
  &&  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
.

Definition OSMemNameGet_partial_solve_wit_4 := OSMemNameGet_partial_solve_wit_4_pure -> OSMemNameGet_partial_solve_wit_4_aux.

Definition OSMemNameGet_partial_solve_wit_5_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pn <> 0)) (PreH3 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH4 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH5 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
|--
  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ”
.

Definition OSMemNameGet_partial_solve_wit_5_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (pe <> 0)) (PreH2 : (pn <> 0)) (PreH3 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH4 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH5 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
.

Definition OSMemNameGet_partial_solve_wit_5 := OSMemNameGet_partial_solve_wit_5_pure -> OSMemNameGet_partial_solve_wit_5_aux.

Definition OSMemNameGet_partial_solve_wit_6 := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (PreH1 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH2 : (old = (Some (previous)))) (PreH3 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH4 : (pe <> 0)) (PreH5 : (pn <> 0)) (PreH6 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH7 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH8 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((pn) # Ptr  |-> previous)
  **  (mem_name_get_source sg pe view raw_chars )
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
|--
  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((pn) # Ptr  |-> previous)
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |->_)
.

Definition OSMemNameGet_partial_solve_wit_7_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (pn <> 0)) (PreH3 : (old = (Some (previous)))) (PreH4 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH6 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH7 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((pn) # Ptr  |-> previous)
  **  ((err) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ”
.

Definition OSMemNameGet_partial_solve_wit_7_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (PreH1 : (pe <> 0)) (PreH2 : (pn <> 0)) (PreH3 : (old = (Some (previous)))) (PreH4 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH5 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH6 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH7 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((pn) # Ptr  |-> previous)
  **  ((err) # UChar  |->_)
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> previous)
  **  ((err) # UChar  |->_)
.

Definition OSMemNameGet_partial_solve_wit_7 := OSMemNameGet_partial_solve_wit_7_pure -> OSMemNameGet_partial_solve_wit_7_aux.

Definition OSMemNameGet_partial_solve_wit_8_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH3 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH4 : (pe <> 0)) (PreH5 : (pn <> 0)) (PreH6 : (old = (Some (previous)))) (PreH7 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH9 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH10 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
.

Definition OSMemNameGet_partial_solve_wit_8_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH3 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH4 : (pe <> 0)) (PreH5 : (pn <> 0)) (PreH6 : (old = (Some (previous)))) (PreH7 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH8 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH9 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH10 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
|--
  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
.

Definition OSMemNameGet_partial_solve_wit_8 := OSMemNameGet_partial_solve_wit_8_pure -> OSMemNameGet_partial_solve_wit_8_aux.

Definition OSMemNameGet_partial_solve_wit_9_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH4 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (pe <> 0)) (PreH7 : (pn <> 0)) (PreH8 : (old = (Some (previous)))) (PreH9 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH10 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH11 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH12 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
.

Definition OSMemNameGet_partial_solve_wit_9_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH4 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (pe <> 0)) (PreH7 : (pn <> 0)) (PreH8 : (old = (Some (previous)))) (PreH9 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH10 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH11 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH12 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
.

Definition OSMemNameGet_partial_solve_wit_9 := OSMemNameGet_partial_solve_wit_9_pure -> OSMemNameGet_partial_solve_wit_9_aux.

Definition OSMemNameGet_partial_solve_wit_10 := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH4 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (pe <> 0)) (PreH10 : (pn <> 0)) (PreH11 : (old = (Some (previous)))) (PreH12 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH13 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH14 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH15 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((err) # UChar  |->_)
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
  **  (task_name_get_name_bytes (memImageName (image)) chars )
  **  ((pn) # Ptr  |-> (memImageName (image)))
.

Definition OSMemNameGet_partial_solve_wit_11_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH4 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (pe <> 0)) (PreH10 : (pn <> 0)) (PreH11 : (old = (Some (previous)))) (PreH12 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH13 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH14 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH15 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
  **  (task_name_get_name_bytes (memImageName (image)) chars )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((( &( "len" ) )) # UChar  |->_)
|--
  “ ((memImageName (image)) = (memImageName (image))) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ”
.

Definition OSMemNameGet_partial_solve_wit_11_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH4 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (pe <> 0)) (PreH10 : (pn <> 0)) (PreH11 : (old = (Some (previous)))) (PreH12 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH13 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH14 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH15 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
  **  (task_name_get_name_bytes (memImageName (image)) chars )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  “ ((memImageName (image)) = (memImageName (image))) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
  **  ((pn) # Ptr  |-> (memImageName (image)))
.

Definition OSMemNameGet_partial_solve_wit_11 := OSMemNameGet_partial_solve_wit_11_pure -> OSMemNameGet_partial_solve_wit_11_aux.

Definition OSMemNameGet_partial_solve_wit_12 := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH2 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH3 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH4 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH5 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH6 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH7 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH8 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH9 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH10 : (pe <> 0)) (PreH11 : (pn <> 0)) (PreH12 : (old = (Some (previous)))) (PreH13 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH14 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH15 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH16 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  “ (retval = (task_name_get_length ((memImageName (image))) (chars))) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
  **  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
.

Definition OSMemNameGet_partial_solve_wit_13_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH2 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH3 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH4 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH5 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH6 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH7 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH8 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH9 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH10 : (pe <> 0)) (PreH11 : (pn <> 0)) (PreH12 : (old = (Some (previous)))) (PreH13 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH14 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH15 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH16 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
  **  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
.

Definition OSMemNameGet_partial_solve_wit_13_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH2 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH3 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH4 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH5 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH6 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH7 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH8 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH9 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH10 : (pe <> 0)) (PreH11 : (pn <> 0)) (PreH12 : (old = (Some (previous)))) (PreH13 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH14 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH15 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH16 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
  **  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (retval = (task_name_get_length ((memImageName (image))) (chars))) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
.

Definition OSMemNameGet_partial_solve_wit_13 := OSMemNameGet_partial_solve_wit_13_pure -> OSMemNameGet_partial_solve_wit_13_aux.

Definition OSMemNameGet_partial_solve_wit_14_pure := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH4 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH10 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH11 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH12 : (pe <> 0)) (PreH13 : (pn <> 0)) (PreH14 : (old = (Some (previous)))) (PreH15 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH16 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH17 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH18 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> cpu_sr)
  **  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((( &( "pmem" ) )) # Ptr  |-> pe)
  **  ((( &( "pname" ) )) # Ptr  |-> pn)
  **  ((( &( "perr" ) )) # Ptr  |-> err)
  **  ((pn) # Ptr  |-> (memImageName (image)))
  **  ((( &( "len" ) )) # UChar  |-> retval)
|--
  “ (cpu_sr = cpu_sr) ”
.

Definition OSMemNameGet_partial_solve_wit_14_aux := 
forall (X: (MemNameGetObservation -> (UCOS2_Verify_State -> Prop))) (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (previous: Z) (cpu_sr: Z) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (retval: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH3 : (retval = (task_name_get_length ((memImageName (image))) (chars)))) (PreH4 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH5 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH6 : (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars )) (PreH7 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH8 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH9 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH10 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH11 : (mem_name_get_selected view raw raw_chars acquired image chars )) (PreH12 : (pe <> 0)) (PreH13 : (pn <> 0)) (PreH14 : (old = (Some (previous)))) (PreH15 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) (PreH16 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH17 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH18 : (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
|--
  “ (cpu_sr = cpu_sr) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (retval = (task_name_get_length ((memImageName (image))) (chars))) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (pe <> 0) ” 
  &&  “ (pn <> 0) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ” 
  &&  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_safe critical sg invocation pe pn view raw raw_chars before X ) ”
  &&  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
  **  ((err) # UChar  |->_)
  **  (mem_name_get_strlen_carrier (memImageName (image)) )
  **  ((pn) # Ptr  |-> (memImageName (image)))
.

Definition OSMemNameGet_partial_solve_wit_14 := OSMemNameGet_partial_solve_wit_14_pure -> OSMemNameGet_partial_solve_wit_14_aux.

Definition OSMemNameGet_which_implies_wit_1 := 
(
forall (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (mem_name_get_pre platform critical sg invocation origin mask before pe pn err view raw raw_chars old )
|--
  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
  **  ((err) # UChar  |->_)
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
) \/
(
forall (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (err: Z) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) ,
  (mem_name_get_pre platform critical sg invocation origin mask before pe pn err view raw raw_chars old )
|--
  EX (x: Z) ,
  “ (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old ) ”
  &&  ((err) # UChar  |-> x)
  **  (mutex_query_closed platform critical sg invocation origin mask before )
  **  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
).

Definition OSMemNameGet_which_implies_wit_2 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
).

Definition OSMemNameGet_which_implies_wit_2_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  “ (UCOS2_state_inv sg before ) ”
.

Definition OSMemNameGet_which_implies_wit_2_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) ,
  (mutex_query_closed platform critical sg invocation origin mask before )
|--
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
.

Definition OSMemNameGet_which_implies_wit_3 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSMemNameGet_which_implies_wit_3_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ”
.

Definition OSMemNameGet_which_implies_wit_3_split_goal_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (0 <= (task_name_get_nesting (before))) ”
.

Definition OSMemNameGet_which_implies_wit_3_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMemNameGet_which_implies_wit_4 := 
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) ) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ” 
  &&  “ ((task_name_get_nesting (before)) < 256) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
) \/
(
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ” 
  &&  “ (0 <= (task_name_get_nesting (before))) ”
  &&  (mutex_query_closed platform critical sg invocation origin mask before )
).

Definition OSMemNameGet_which_implies_wit_4_split_goal_1 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ ((task_name_get_nesting (before)) < 256) ”
.

Definition OSMemNameGet_which_implies_wit_4_split_goal_2 := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  “ (0 <= (task_name_get_nesting (before))) ”
.

Definition OSMemNameGet_which_implies_wit_4_split_goal_spatial := 
forall (before: UCOS2_Verify_State) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (PreH1 : (mem_name_get_addresses sg ( &( "OSIntNesting" ) ) )) (PreH2 : (UCOS2_state_inv sg before )) ,
  (interrupt_platform_running platform invocation origin mask )
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> (task_name_get_nesting (before)))
  **  (task_name_get_nesting_frame sg before )
|--
  (mutex_query_closed platform critical sg invocation origin mask before )
.

Definition OSMemNameGet_which_implies_wit_5 := 
(
forall (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH2 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) ,
  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  EX (previous: Z) ,
  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ”
  &&  ((pn) # Ptr  |-> previous)
  **  (mem_name_get_source sg pe view raw_chars )
) \/
(
forall (old: (@option Z)) (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pn: Z) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (PreH1 : (mem_name_get_access critical sg invocation pe pn view raw raw_chars before old )) (PreH2 : ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None)) ,
  (task_name_get_output_cell pn old )
  **  (mem_name_get_guarded_source sg pe pn view raw_chars before )
|--
  EX (previous: Z) ,
  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (old = (Some (previous))) ” 
  &&  “ ((mem_name_get_early_error (pe) (pn) ((task_name_get_nesting (before)))) = None) ”
  &&  ((pn) # Ptr  |-> previous)
  **  (mem_name_get_source sg pe view raw_chars )
).

Definition OSMemNameGet_which_implies_wit_6 := 
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
|--
  EX (image: MemoryControlImage)  (chars: (@list Z)) ,
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
  &&  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
) \/
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
|--
  EX (image: MemoryControlImage)  (chars: (@list Z)) ,
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
  &&  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
).

Definition OSMemNameGet_which_implies_wit_7 := 
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
|--
  “ (mem_name_get_admission critical sg invocation pe view raw raw_chars before ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
  &&  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
) \/
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
|--
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
).

Definition OSMemNameGet_which_implies_wit_7_split_goal_spatial := 
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (PreH1 : (mem_name_get_admission critical sg invocation pe view raw raw_chars before )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  ((&((pe)  # "os_mem" ->ₛ "OSMemName")) # Ptr  |-> (memImageName (image)))
  **  (mem_name_get_control_residual sg pe view acquired image )
  **  (mem_name_get_raw_bytes view raw_chars )
|--
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
.

Definition OSMemNameGet_which_implies_wit_8 := 
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ” 
  &&  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ”
  &&  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
) \/
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
|--
  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ”
  &&  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
).

Definition OSMemNameGet_which_implies_wit_8_split_goal_1 := 
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
|--
  “ (task_name_get_readable (mem_name_get_names (view) (raw) (acquired)) (memImageName (image)) chars ) ”
.

Definition OSMemNameGet_which_implies_wit_8_split_goal_spatial := 
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
|--
  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
.

Definition OSMemNameGet_which_implies_wit_9 := 
(
forall (view: MemQueryView) (err: Z) (pe: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) ,
  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
|--
  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
) \/
(
forall (view: MemQueryView) (err: Z) (pe: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) ,
  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
|--
  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
).

Definition OSMemNameGet_which_implies_wit_9_split_goal_spatial := 
forall (view: MemQueryView) (err: Z) (pe: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) ,
  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
|--
  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
.

Definition OSMemNameGet_which_implies_wit_10 := 
(
forall (view: MemQueryView) (err: Z) (pe: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) ,
  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
|--
  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
  **  ((err) # UChar  |->_)
) \/
(
forall (view: MemQueryView) (err: Z) (pe: Z) (origin: TaskInvocationOrigin) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (platform: InterruptPlatformResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) ,
  (mem_name_get_call_frame platform critical sg invocation origin cpu_sr pe err view acquired (memImageName (image)) chars )
|--
  EX (x: Z) ,
  ((err) # UChar  |-> x)
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
  **  (critical_region_masked platform critical sg invocation origin cpu_sr acquired )
).

Definition OSMemNameGet_which_implies_wit_11 := 
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
|--
  “ (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired ) ” 
  &&  “ (mem_name_get_selected view raw raw_chars acquired image chars ) ”
  &&  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
) \/
(
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
|--
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
).

Definition OSMemNameGet_which_implies_wit_11_split_goal_spatial := 
forall (raw_chars: (@list Z)) (raw: NameResourceState) (view: MemQueryView) (pe: Z) (before: UCOS2_Verify_State) (mask: Z) (invocation: nat) (sg: StableGlobVars) (critical: CriticalRegionResources) (acquired: UCOS2_Verify_State) (image: MemoryControlImage) (chars: (@list Z)) (cpu_sr: Z) (PreH1 : (mem_query_acquire_facts critical sg invocation mask cpu_sr before acquired )) (PreH2 : (mem_name_get_selected view raw raw_chars acquired image chars )) ,
  (task_name_get_name_bytes (memImageName (image)) chars )
  **  (mem_name_get_string_residual sg pe view acquired (memImageName (image)) chars )
|--
  (UCOS2_inv sg acquired )
  **  (mem_name_get_source sg pe view raw_chars )
.

Definition OS_StrLen_derive_mem_name_get_spec_by_source_spec := 
forall (psrc_pre: Z) (frame_mem_name_get_spec: Assertion) (chars_mem_name_get_spec: (@list Z)) (names_mem_name_get_spec: NameResourceState) (entry_mem_name_get_spec: Z) ,
  “ (psrc_pre = entry_mem_name_get_spec) ” 
  &&  “ (task_name_get_readable names_mem_name_get_spec entry_mem_name_get_spec chars_mem_name_get_spec ) ”
  &&  (task_name_get_name_bytes entry_mem_name_get_spec chars_mem_name_get_spec )
  **  (frame_mem_name_get_spec )
|--
EX (entry_source_spec: Z) (base_source_spec: Z) (names_source_spec: NameResourceState) (chars_source_spec: (@list Z)) (frame_source_spec: Assertion) ,
  ((“ (psrc_pre = entry_source_spec) ” 
  &&  “ (psrc_pre <> 0) ” 
  &&  “ (psrc_pre = base_source_spec) ”
  &&  (coq_prop (readable_name (names_source_spec) (psrc_pre) (chars_source_spec)) )
  **  (os_strlen_bytes psrc_pre chars_source_spec )
  **  (frame_source_spec ))
  ||
  (“ (psrc_pre = entry_source_spec) ” 
  &&  “ (psrc_pre = 0) ”
  &&  (frame_source_spec )))
  **
  (((EX retval_2,
  “ (entry_source_spec = 0) ” 
  &&  “ (retval_2 = 0) ”
  &&  (frame_source_spec ))
  ||
  (EX retval_2,
  “ (entry_source_spec <> 0) ” 
  &&  “ (entry_source_spec = base_source_spec) ”
  &&  (coq_prop (os_strlen_result (chars_source_spec) (retval_2)) )
  **  (os_strlen_bytes entry_source_spec chars_source_spec )
  **  (frame_source_spec )))
  -*
  (EX retval,
  “ (retval = (task_name_get_length (entry_mem_name_get_spec) (chars_mem_name_get_spec))) ”
  &&  (task_name_get_name_bytes entry_mem_name_get_spec chars_mem_name_get_spec )
  **  (frame_mem_name_get_spec )
  **  (mem_name_get_strlen_carrier entry_mem_name_get_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSMemNameGet_safety_wit_1 : OSMemNameGet_safety_wit_1.
Axiom proof_of_OSMemNameGet_safety_wit_2 : OSMemNameGet_safety_wit_2.
Axiom proof_of_OSMemNameGet_safety_wit_3 : OSMemNameGet_safety_wit_3.
Axiom proof_of_OSMemNameGet_safety_wit_4 : OSMemNameGet_safety_wit_4.
Axiom proof_of_OSMemNameGet_entail_wit_1 : OSMemNameGet_entail_wit_1.
Axiom proof_of_OSMemNameGet_entail_wit_2 : OSMemNameGet_entail_wit_2.
Axiom proof_of_OSMemNameGet_return_wit_1 : OSMemNameGet_return_wit_1.
Axiom proof_of_OSMemNameGet_return_wit_2 : OSMemNameGet_return_wit_2.
Axiom proof_of_OSMemNameGet_return_wit_3 : OSMemNameGet_return_wit_3.
Axiom proof_of_OSMemNameGet_return_wit_4 : OSMemNameGet_return_wit_4.
Axiom proof_of_OSMemNameGet_partial_solve_wit_1 : OSMemNameGet_partial_solve_wit_1.
Axiom proof_of_OSMemNameGet_partial_solve_wit_2_pure : OSMemNameGet_partial_solve_wit_2_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_2 : OSMemNameGet_partial_solve_wit_2.
Axiom proof_of_OSMemNameGet_partial_solve_wit_3_pure : OSMemNameGet_partial_solve_wit_3_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_3 : OSMemNameGet_partial_solve_wit_3.
Axiom proof_of_OSMemNameGet_partial_solve_wit_4_pure : OSMemNameGet_partial_solve_wit_4_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_4 : OSMemNameGet_partial_solve_wit_4.
Axiom proof_of_OSMemNameGet_partial_solve_wit_5_pure : OSMemNameGet_partial_solve_wit_5_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_5 : OSMemNameGet_partial_solve_wit_5.
Axiom proof_of_OSMemNameGet_partial_solve_wit_6 : OSMemNameGet_partial_solve_wit_6.
Axiom proof_of_OSMemNameGet_partial_solve_wit_7_pure : OSMemNameGet_partial_solve_wit_7_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_7 : OSMemNameGet_partial_solve_wit_7.
Axiom proof_of_OSMemNameGet_partial_solve_wit_8_pure : OSMemNameGet_partial_solve_wit_8_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_8 : OSMemNameGet_partial_solve_wit_8.
Axiom proof_of_OSMemNameGet_partial_solve_wit_9_pure : OSMemNameGet_partial_solve_wit_9_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_9 : OSMemNameGet_partial_solve_wit_9.
Axiom proof_of_OSMemNameGet_partial_solve_wit_10 : OSMemNameGet_partial_solve_wit_10.
Axiom proof_of_OSMemNameGet_partial_solve_wit_11_pure : OSMemNameGet_partial_solve_wit_11_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_11 : OSMemNameGet_partial_solve_wit_11.
Axiom proof_of_OSMemNameGet_partial_solve_wit_12 : OSMemNameGet_partial_solve_wit_12.
Axiom proof_of_OSMemNameGet_partial_solve_wit_13_pure : OSMemNameGet_partial_solve_wit_13_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_13 : OSMemNameGet_partial_solve_wit_13.
Axiom proof_of_OSMemNameGet_partial_solve_wit_14_pure : OSMemNameGet_partial_solve_wit_14_pure.
Axiom proof_of_OSMemNameGet_partial_solve_wit_14 : OSMemNameGet_partial_solve_wit_14.
Axiom proof_of_OSMemNameGet_which_implies_wit_1 : OSMemNameGet_which_implies_wit_1.
Axiom proof_of_OSMemNameGet_which_implies_wit_2 : OSMemNameGet_which_implies_wit_2.
Axiom proof_of_OSMemNameGet_which_implies_wit_3 : OSMemNameGet_which_implies_wit_3.
Axiom proof_of_OSMemNameGet_which_implies_wit_4 : OSMemNameGet_which_implies_wit_4.
Axiom proof_of_OSMemNameGet_which_implies_wit_5 : OSMemNameGet_which_implies_wit_5.
Axiom proof_of_OSMemNameGet_which_implies_wit_6 : OSMemNameGet_which_implies_wit_6.
Axiom proof_of_OSMemNameGet_which_implies_wit_7 : OSMemNameGet_which_implies_wit_7.
Axiom proof_of_OSMemNameGet_which_implies_wit_8 : OSMemNameGet_which_implies_wit_8.
Axiom proof_of_OSMemNameGet_which_implies_wit_9 : OSMemNameGet_which_implies_wit_9.
Axiom proof_of_OSMemNameGet_which_implies_wit_10 : OSMemNameGet_which_implies_wit_10.
Axiom proof_of_OSMemNameGet_which_implies_wit_11 : OSMemNameGet_which_implies_wit_11.
Axiom proof_of_OS_StrLen_derive_mem_name_get_spec_by_source_spec : OS_StrLen_derive_mem_name_get_spec_by_source_spec.

End VC_Correct.
