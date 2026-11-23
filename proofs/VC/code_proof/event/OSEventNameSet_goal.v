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
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.event.spec.event_name_set_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSEventNameSet -----*)

Definition OSEventNameSet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (perr_pre <> 0)) (PreH2 : (0 <= nesting)) (PreH3 : (nesting <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_safety_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameSet_return_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 <> type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((perr_pre) # UChar  |-> 1)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 <> type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (1)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 <> type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (1)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting > 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  ((perr_pre) # UChar  |-> 18)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting > 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (18)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting > 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (18)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (perr_pre <> 0)) (PreH4 : (0 <= nesting)) (PreH5 : (nesting <= 255)) ,
  ((perr_pre) # UChar  |-> 12)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (perr_pre <> 0)) (PreH4 : (0 <= nesting)) (PreH5 : (nesting <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (12)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (perr_pre <> 0)) (PreH4 : (0 <= nesting)) (PreH5 : (nesting <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (12)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  ((perr_pre) # UChar  |-> 4)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (4)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (4)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_6 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_7 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_return_wit_8 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  EX (error: Z) ,
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (error)) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
).

Definition OSEventNameSet_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (frame )
|--
  (coq_prop (event_name_set_observation (pevent_pre) (pname_pre) (nesting) (type_byte) (0)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte (event_name_set_final_name (pevent_pre) (pname_pre) (nesting) (type_byte) (name_old)) )
.

Definition OSEventNameSet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting <= 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ”
.

Definition OSEventNameSet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting <= 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ”
  &&  (event_name_set_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_1 := OSEventNameSet_partial_solve_wit_1_pure -> OSEventNameSet_partial_solve_wit_1_aux.

Definition OSEventNameSet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameSet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 <> type_byte) ” 
  &&  “ (1 <> type_byte) ” 
  &&  “ (2 = type_byte) ”
  &&  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_2 := OSEventNameSet_partial_solve_wit_2_pure -> OSEventNameSet_partial_solve_wit_2_aux.

Definition OSEventNameSet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameSet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 <> type_byte) ” 
  &&  “ (1 = type_byte) ”
  &&  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_3 := OSEventNameSet_partial_solve_wit_3_pure -> OSEventNameSet_partial_solve_wit_3_aux.

Definition OSEventNameSet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameSet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 = type_byte) ”
  &&  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_4 := OSEventNameSet_partial_solve_wit_4_pure -> OSEventNameSet_partial_solve_wit_4_aux.

Definition OSEventNameSet_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameSet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 = type_byte) ”
  &&  (event_name_set_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_5 := OSEventNameSet_partial_solve_wit_5_pure -> OSEventNameSet_partial_solve_wit_5_aux.

Definition OSEventNameSet_partial_solve_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 = type_byte) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 = type_byte) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 <> type_byte) ” 
  &&  “ (1 = type_byte) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 <> type_byte) ” 
  &&  “ (1 <> type_byte) ” 
  &&  “ (2 = type_byte) ”
  &&  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ”
.

Definition OSEventNameSet_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 = type_byte) ”
  &&  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_10 := OSEventNameSet_partial_solve_wit_10_pure -> OSEventNameSet_partial_solve_wit_10_aux.

Definition OSEventNameSet_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ”
.

Definition OSEventNameSet_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 = type_byte) ”
  &&  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_11 := OSEventNameSet_partial_solve_wit_11_pure -> OSEventNameSet_partial_solve_wit_11_aux.

Definition OSEventNameSet_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ”
.

Definition OSEventNameSet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 <> type_byte) ” 
  &&  “ (1 = type_byte) ”
  &&  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_12 := OSEventNameSet_partial_solve_wit_12_pure -> OSEventNameSet_partial_solve_wit_12_aux.

Definition OSEventNameSet_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ”
.

Definition OSEventNameSet_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (type_byte: Z) (nesting: Z) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (retval = retval) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (pevent_pre <> 0) ” 
  &&  “ (perr_pre <> 0) ” 
  &&  “ (0 <= nesting) ” 
  &&  “ (nesting <= 255) ” 
  &&  “ (3 <> type_byte) ” 
  &&  “ (4 <> type_byte) ” 
  &&  “ (1 <> type_byte) ” 
  &&  “ (2 = type_byte) ”
  &&  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameSet_partial_solve_wit_13 := OSEventNameSet_partial_solve_wit_13_pure -> OSEventNameSet_partial_solve_wit_13_aux.

Definition OSEventNameSet_which_implies_wit_1 := 
(
forall (name_old: Z) (type_byte: Z) (nesting: Z) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) ,
  (event_name_set_access pevent pname &((pevent)  # "os_event" ->ₛ "OSEventType") &((pevent)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  “ (pevent <> 0) ” 
  &&  “ (pname <> 0) ” 
  &&  “ (nesting <= 0) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
) \/
(
forall (name_old: Z) (type_byte: Z) (nesting: Z) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) ,
  (event_name_set_access pevent pname &((pevent)  # "os_event" ->ₛ "OSEventType") &((pevent)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
).

Definition OSEventNameSet_which_implies_wit_1_split_goal_spatial := 
forall (name_old: Z) (type_byte: Z) (nesting: Z) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) ,
  (event_name_set_access pevent pname &((pevent)  # "os_event" ->ₛ "OSEventType") &((pevent)  # "os_event" ->ₛ "OSEventName") nesting type_byte name_old )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_set_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
.

Definition OSEventNameSet_which_implies_wit_2 := 
(
forall (name_old: Z) (type_byte: Z) (pevent: Z) (PreH1 : (1 <= type_byte)) (PreH2 : (type_byte <= 4)) ,
  (event_name_set_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
|--
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
) \/
(
forall (name_old: Z) (type_byte: Z) (pevent: Z) (PreH1 : (1 <= type_byte)) (PreH2 : (type_byte <= 4)) ,
  (event_name_set_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
|--
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
).

Definition OSEventNameSet_which_implies_wit_2_split_goal_spatial := 
forall (name_old: Z) (type_byte: Z) (pevent: Z) (PreH1 : (1 <= type_byte)) (PreH2 : (type_byte <= 4)) ,
  (event_name_set_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") type_byte name_old )
|--
  (coq_prop (event_name_type_supported (type_byte)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name_old)
.

Module Type VC_Correct.


Axiom proof_of_OSEventNameSet_safety_wit_1 : OSEventNameSet_safety_wit_1.
Axiom proof_of_OSEventNameSet_safety_wit_2 : OSEventNameSet_safety_wit_2.
Axiom proof_of_OSEventNameSet_safety_wit_3 : OSEventNameSet_safety_wit_3.
Axiom proof_of_OSEventNameSet_safety_wit_4 : OSEventNameSet_safety_wit_4.
Axiom proof_of_OSEventNameSet_safety_wit_5 : OSEventNameSet_safety_wit_5.
Axiom proof_of_OSEventNameSet_safety_wit_6 : OSEventNameSet_safety_wit_6.
Axiom proof_of_OSEventNameSet_safety_wit_7 : OSEventNameSet_safety_wit_7.
Axiom proof_of_OSEventNameSet_safety_wit_8 : OSEventNameSet_safety_wit_8.
Axiom proof_of_OSEventNameSet_safety_wit_9 : OSEventNameSet_safety_wit_9.
Axiom proof_of_OSEventNameSet_safety_wit_10 : OSEventNameSet_safety_wit_10.
Axiom proof_of_OSEventNameSet_return_wit_1 : OSEventNameSet_return_wit_1.
Axiom proof_of_OSEventNameSet_return_wit_2 : OSEventNameSet_return_wit_2.
Axiom proof_of_OSEventNameSet_return_wit_3 : OSEventNameSet_return_wit_3.
Axiom proof_of_OSEventNameSet_return_wit_4 : OSEventNameSet_return_wit_4.
Axiom proof_of_OSEventNameSet_return_wit_5 : OSEventNameSet_return_wit_5.
Axiom proof_of_OSEventNameSet_return_wit_6 : OSEventNameSet_return_wit_6.
Axiom proof_of_OSEventNameSet_return_wit_7 : OSEventNameSet_return_wit_7.
Axiom proof_of_OSEventNameSet_return_wit_8 : OSEventNameSet_return_wit_8.
Axiom proof_of_OSEventNameSet_partial_solve_wit_1_pure : OSEventNameSet_partial_solve_wit_1_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_1 : OSEventNameSet_partial_solve_wit_1.
Axiom proof_of_OSEventNameSet_partial_solve_wit_2_pure : OSEventNameSet_partial_solve_wit_2_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_2 : OSEventNameSet_partial_solve_wit_2.
Axiom proof_of_OSEventNameSet_partial_solve_wit_3_pure : OSEventNameSet_partial_solve_wit_3_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_3 : OSEventNameSet_partial_solve_wit_3.
Axiom proof_of_OSEventNameSet_partial_solve_wit_4_pure : OSEventNameSet_partial_solve_wit_4_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_4 : OSEventNameSet_partial_solve_wit_4.
Axiom proof_of_OSEventNameSet_partial_solve_wit_5_pure : OSEventNameSet_partial_solve_wit_5_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_5 : OSEventNameSet_partial_solve_wit_5.
Axiom proof_of_OSEventNameSet_partial_solve_wit_6 : OSEventNameSet_partial_solve_wit_6.
Axiom proof_of_OSEventNameSet_partial_solve_wit_7 : OSEventNameSet_partial_solve_wit_7.
Axiom proof_of_OSEventNameSet_partial_solve_wit_8 : OSEventNameSet_partial_solve_wit_8.
Axiom proof_of_OSEventNameSet_partial_solve_wit_9 : OSEventNameSet_partial_solve_wit_9.
Axiom proof_of_OSEventNameSet_partial_solve_wit_10_pure : OSEventNameSet_partial_solve_wit_10_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_10 : OSEventNameSet_partial_solve_wit_10.
Axiom proof_of_OSEventNameSet_partial_solve_wit_11_pure : OSEventNameSet_partial_solve_wit_11_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_11 : OSEventNameSet_partial_solve_wit_11.
Axiom proof_of_OSEventNameSet_partial_solve_wit_12_pure : OSEventNameSet_partial_solve_wit_12_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_12 : OSEventNameSet_partial_solve_wit_12.
Axiom proof_of_OSEventNameSet_partial_solve_wit_13_pure : OSEventNameSet_partial_solve_wit_13_pure.
Axiom proof_of_OSEventNameSet_partial_solve_wit_13 : OSEventNameSet_partial_solve_wit_13.
Axiom proof_of_OSEventNameSet_which_implies_wit_1 : OSEventNameSet_which_implies_wit_1.
Axiom proof_of_OSEventNameSet_which_implies_wit_2 : OSEventNameSet_which_implies_wit_2.

End VC_Correct.
