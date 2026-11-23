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
Require Import Ucos2Verify.VC.code.event.spec.event_name_get_call_spec.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope sac.

(*----- Function OSEventNameGet -----*)

Definition OSEventNameGet_safety_wit_1 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (perr_pre <> 0)) (PreH2 : (0 <= nesting)) (PreH3 : (nesting <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_2 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_3 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_4 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_5 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_safety_wit_10 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition OSEventNameGet_return_wit_1 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_1_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_2 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_2_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_3 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_3_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_4 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> 0)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_4_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (interrupt_platform_running platform invocation origin mask )
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (0) (retval) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_5 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 <> type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> 1)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 <> type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (1) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_5_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 <> type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (1) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_6 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting > 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> 17)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting > 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (17) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_6_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting > 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (17) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_7 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (perr_pre <> 0)) (PreH4 : (0 <= nesting)) (PreH5 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> 12)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (perr_pre <> 0)) (PreH4 : (0 <= nesting)) (PreH5 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (12) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_7_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pname_pre = 0)) (PreH2 : (pevent_pre <> 0)) (PreH3 : (perr_pre <> 0)) (PreH4 : (0 <= nesting)) (PreH5 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (12) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_return_wit_8 := 
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> 4)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  EX (error: Z) ,
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (error) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  ((perr_pre) # UChar  |-> error)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
) \/
(
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (4) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
).

Definition OSEventNameGet_return_wit_8_split_goal_spatial := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre = 0)) (PreH2 : (perr_pre <> 0)) (PreH3 : (0 <= nesting)) (PreH4 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  (coq_prop (event_name_get_observation (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars) (4) (0) ((event_name_get_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name)))) )
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte (event_name_get_final_output (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (output_old)) chars )
.

Definition OSEventNameGet_partial_solve_wit_1_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting <= 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ”
.

Definition OSEventNameGet_partial_solve_wit_1_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (nesting <= 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (pevent_pre <> 0)) (PreH4 : (perr_pre <> 0)) (PreH5 : (0 <= nesting)) (PreH6 : (nesting <= 255)) ,
  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
  **  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
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
  &&  (event_name_get_access pevent_pre pname_pre &((pevent_pre)  # "os_event" ->ₛ "OSEventType") &((pevent_pre)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_1 := OSEventNameGet_partial_solve_wit_1_pure -> OSEventNameGet_partial_solve_wit_1_aux.

Definition OSEventNameGet_partial_solve_wit_2_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameGet_partial_solve_wit_2_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
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
  &&  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_2 := OSEventNameGet_partial_solve_wit_2_pure -> OSEventNameGet_partial_solve_wit_2_aux.

Definition OSEventNameGet_partial_solve_wit_3_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameGet_partial_solve_wit_3_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
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
  &&  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_3 := OSEventNameGet_partial_solve_wit_3_pure -> OSEventNameGet_partial_solve_wit_3_aux.

Definition OSEventNameGet_partial_solve_wit_4_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameGet_partial_solve_wit_4_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
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
  &&  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_4 := OSEventNameGet_partial_solve_wit_4_pure -> OSEventNameGet_partial_solve_wit_4_aux.

Definition OSEventNameGet_partial_solve_wit_5_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((( &( "cpu_sr" ) )) # UInt  |-> 0)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
  &&  “ (type_byte <= 4) ”
.

Definition OSEventNameGet_partial_solve_wit_5_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
|--
  “ (pevent_pre <> 0) ” 
  &&  “ (pname_pre <> 0) ” 
  &&  “ (nesting <= 0) ” 
  &&  “ (1 <= type_byte) ” 
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
  &&  (coq_prop (event_name_get_request (names) (pevent_pre) (pname_pre) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent_pre)  # "os_event" ->ₛ "OSEventName") pname_pre name type_byte output_old chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (interrupt_platform_running platform invocation origin mask )
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_5 := OSEventNameGet_partial_solve_wit_5_pure -> OSEventNameGet_partial_solve_wit_5_aux.

Definition OSEventNameGet_partial_solve_wit_6 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
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
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_7 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
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
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_8 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
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
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_9 := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
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
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
.

Definition OSEventNameGet_partial_solve_wit_10_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ”
.

Definition OSEventNameGet_partial_solve_wit_10_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ” 
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
  &&  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_10 := OSEventNameGet_partial_solve_wit_10_pure -> OSEventNameGet_partial_solve_wit_10_aux.

Definition OSEventNameGet_partial_solve_wit_11_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ”
.

Definition OSEventNameGet_partial_solve_wit_11_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ” 
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
  &&  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_11 := OSEventNameGet_partial_solve_wit_11_pure -> OSEventNameGet_partial_solve_wit_11_aux.

Definition OSEventNameGet_partial_solve_wit_12_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ”
.

Definition OSEventNameGet_partial_solve_wit_12_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ” 
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
  &&  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_12 := OSEventNameGet_partial_solve_wit_12_pure -> OSEventNameGet_partial_solve_wit_12_aux.

Definition OSEventNameGet_partial_solve_wit_13_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |->_)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ”
.

Definition OSEventNameGet_partial_solve_wit_13_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  (event_name_get_name_bytes name chars )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
  **  (frame )
|--
  “ (name = name) ” 
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
  &&  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_13 := OSEventNameGet_partial_solve_wit_13_pure -> OSEventNameGet_partial_solve_wit_13_aux.

Definition OSEventNameGet_partial_solve_wit_14_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (retval = retval) ”
.

Definition OSEventNameGet_partial_solve_wit_14_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
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
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_14 := OSEventNameGet_partial_solve_wit_14_pure -> OSEventNameGet_partial_solve_wit_14_aux.

Definition OSEventNameGet_partial_solve_wit_15_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (retval = retval) ”
.

Definition OSEventNameGet_partial_solve_wit_15_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
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
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_15 := OSEventNameGet_partial_solve_wit_15_pure -> OSEventNameGet_partial_solve_wit_15_aux.

Definition OSEventNameGet_partial_solve_wit_16_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (retval = retval) ”
.

Definition OSEventNameGet_partial_solve_wit_16_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
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
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_16 := OSEventNameGet_partial_solve_wit_16_pure -> OSEventNameGet_partial_solve_wit_16_aux.

Definition OSEventNameGet_partial_solve_wit_17_pure := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((( &( "pevent" ) )) # Ptr  |-> pevent_pre)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((( &( "pname" ) )) # Ptr  |-> pname_pre)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((( &( "cpu_sr" ) )) # UInt  |-> retval)
  **  ((( &( "len" ) )) # UChar  |-> retval_2)
  **  ((( &( "perr" ) )) # Ptr  |-> perr_pre)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
|--
  “ (retval = retval) ”
.

Definition OSEventNameGet_partial_solve_wit_17_aux := 
forall (perr_pre: Z) (pname_pre: Z) (pevent_pre: Z) (error_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (frame: Assertion) (mask: Z) (origin: TaskInvocationOrigin) (invocation: nat) (platform: InterruptPlatformResources) (retval: Z) (retval_2: Z) (PreH1 : (pevent_pre <> 0)) (PreH2 : (pname_pre <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (nesting <= 0)) (PreH5 : (pname_pre <> 0)) (PreH6 : (pevent_pre <> 0)) (PreH7 : (perr_pre <> 0)) (PreH8 : (0 <= nesting)) (PreH9 : (nesting <= 255)) (PreH10 : (3 <> type_byte)) (PreH11 : (4 <> type_byte)) (PreH12 : (1 <> type_byte)) (PreH13 : (2 = type_byte)) ,
  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  (coq_prop (interrupt_saved_value (mask) (retval)) )
  **  (interrupt_platform_running platform invocation origin 192 )
  **  (interrupt_platform_saved platform (save_token (retval) (invocation) (origin)) )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
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
  **  (coq_prop (event_name_get_result (names) (name) (chars) (retval_2)) )
  **  (event_name_get_name_bytes name chars )
  **  (frame )
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname_pre) # Ptr  |-> name)
  **  ((&((pevent_pre)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  ((perr_pre) # UChar  |-> error_old)
  **  ((( &( "OSIntNesting" ) )) # UChar  |-> nesting)
.

Definition OSEventNameGet_partial_solve_wit_17 := OSEventNameGet_partial_solve_wit_17_pure -> OSEventNameGet_partial_solve_wit_17_aux.

Definition OSEventNameGet_which_implies_wit_1 := 
(
forall (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) ,
  (event_name_get_access pevent pname &((pevent)  # "os_event" ->ₛ "OSEventType") &((pevent)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  “ (pevent <> 0) ” 
  &&  “ (pname <> 0) ” 
  &&  “ (nesting <= 0) ”
  &&  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") pname name type_byte output_old chars )
) \/
(
forall (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) ,
  (event_name_get_access pevent pname &((pevent)  # "os_event" ->ₛ "OSEventType") &((pevent)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") pname name type_byte output_old chars )
).

Definition OSEventNameGet_which_implies_wit_1_split_goal_spatial := 
forall (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) ,
  (event_name_get_access pevent pname &((pevent)  # "os_event" ->ₛ "OSEventType") &((pevent)  # "os_event" ->ₛ "OSEventName") name nesting type_byte output_old chars )
|--
  ((&((pevent)  # "os_event" ->ₛ "OSEventType")) # UChar  |-> type_byte)
  **  (event_name_get_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") pname name type_byte output_old chars )
.

Definition OSEventNameGet_which_implies_wit_2 := 
(
forall (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (1 <= type_byte)) (PreH5 : (type_byte <= 4)) ,
  (coq_prop (event_name_get_request (names) (pevent) (pname) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") pname name type_byte output_old chars )
|--
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
) \/
(
forall (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (1 <= type_byte)) (PreH5 : (type_byte <= 4)) ,
  (coq_prop (event_name_get_request (names) (pevent) (pname) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") pname name type_byte output_old chars )
|--
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
).

Definition OSEventNameGet_which_implies_wit_2_split_goal_spatial := 
forall (output_old: Z) (name: Z) (type_byte: Z) (nesting: Z) (chars: (@list Z)) (names: NameResourceState) (pevent: Z) (pname: Z) (PreH1 : (pevent <> 0)) (PreH2 : (pname <> 0)) (PreH3 : (nesting <= 0)) (PreH4 : (1 <= type_byte)) (PreH5 : (type_byte <= 4)) ,
  (coq_prop (event_name_get_request (names) (pevent) (pname) (nesting) (type_byte) (name) (chars)) )
  **  (event_name_get_after_type &((pevent)  # "os_event" ->ₛ "OSEventName") pname name type_byte output_old chars )
|--
  (coq_prop (event_name_get_readable (names) (name) (chars)) )
  **  ((&((pevent)  # "os_event" ->ₛ "OSEventName")) # Ptr  |-> name)
  **  ((pname) # Ptr  |-> output_old)
  **  (event_name_get_name_bytes name chars )
.

Definition OS_StrLen_derive_name_get_spec_by_source_spec := 
forall (psrc_pre: Z) (frame_name_get_spec: Assertion) (chars_name_get_spec: (@list Z)) (names_name_get_spec: NameResourceState) (entry_name_get_spec: Z) ,
  “ (psrc_pre = entry_name_get_spec) ”
  &&  (coq_prop (event_name_get_readable (names_name_get_spec) (psrc_pre) (chars_name_get_spec)) )
  **  (event_name_get_name_bytes psrc_pre chars_name_get_spec )
  **  (frame_name_get_spec )
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
  (coq_prop (event_name_get_result (names_name_get_spec) (entry_name_get_spec) (chars_name_get_spec) (retval)) )
  **  (event_name_get_name_bytes entry_name_get_spec chars_name_get_spec )
  **  (frame_name_get_spec )))
.

Module Type VC_Correct.


Axiom proof_of_OSEventNameGet_safety_wit_1 : OSEventNameGet_safety_wit_1.
Axiom proof_of_OSEventNameGet_safety_wit_2 : OSEventNameGet_safety_wit_2.
Axiom proof_of_OSEventNameGet_safety_wit_3 : OSEventNameGet_safety_wit_3.
Axiom proof_of_OSEventNameGet_safety_wit_4 : OSEventNameGet_safety_wit_4.
Axiom proof_of_OSEventNameGet_safety_wit_5 : OSEventNameGet_safety_wit_5.
Axiom proof_of_OSEventNameGet_safety_wit_6 : OSEventNameGet_safety_wit_6.
Axiom proof_of_OSEventNameGet_safety_wit_7 : OSEventNameGet_safety_wit_7.
Axiom proof_of_OSEventNameGet_safety_wit_8 : OSEventNameGet_safety_wit_8.
Axiom proof_of_OSEventNameGet_safety_wit_9 : OSEventNameGet_safety_wit_9.
Axiom proof_of_OSEventNameGet_safety_wit_10 : OSEventNameGet_safety_wit_10.
Axiom proof_of_OSEventNameGet_return_wit_1 : OSEventNameGet_return_wit_1.
Axiom proof_of_OSEventNameGet_return_wit_2 : OSEventNameGet_return_wit_2.
Axiom proof_of_OSEventNameGet_return_wit_3 : OSEventNameGet_return_wit_3.
Axiom proof_of_OSEventNameGet_return_wit_4 : OSEventNameGet_return_wit_4.
Axiom proof_of_OSEventNameGet_return_wit_5 : OSEventNameGet_return_wit_5.
Axiom proof_of_OSEventNameGet_return_wit_6 : OSEventNameGet_return_wit_6.
Axiom proof_of_OSEventNameGet_return_wit_7 : OSEventNameGet_return_wit_7.
Axiom proof_of_OSEventNameGet_return_wit_8 : OSEventNameGet_return_wit_8.
Axiom proof_of_OSEventNameGet_partial_solve_wit_1_pure : OSEventNameGet_partial_solve_wit_1_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_1 : OSEventNameGet_partial_solve_wit_1.
Axiom proof_of_OSEventNameGet_partial_solve_wit_2_pure : OSEventNameGet_partial_solve_wit_2_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_2 : OSEventNameGet_partial_solve_wit_2.
Axiom proof_of_OSEventNameGet_partial_solve_wit_3_pure : OSEventNameGet_partial_solve_wit_3_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_3 : OSEventNameGet_partial_solve_wit_3.
Axiom proof_of_OSEventNameGet_partial_solve_wit_4_pure : OSEventNameGet_partial_solve_wit_4_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_4 : OSEventNameGet_partial_solve_wit_4.
Axiom proof_of_OSEventNameGet_partial_solve_wit_5_pure : OSEventNameGet_partial_solve_wit_5_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_5 : OSEventNameGet_partial_solve_wit_5.
Axiom proof_of_OSEventNameGet_partial_solve_wit_6 : OSEventNameGet_partial_solve_wit_6.
Axiom proof_of_OSEventNameGet_partial_solve_wit_7 : OSEventNameGet_partial_solve_wit_7.
Axiom proof_of_OSEventNameGet_partial_solve_wit_8 : OSEventNameGet_partial_solve_wit_8.
Axiom proof_of_OSEventNameGet_partial_solve_wit_9 : OSEventNameGet_partial_solve_wit_9.
Axiom proof_of_OSEventNameGet_partial_solve_wit_10_pure : OSEventNameGet_partial_solve_wit_10_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_10 : OSEventNameGet_partial_solve_wit_10.
Axiom proof_of_OSEventNameGet_partial_solve_wit_11_pure : OSEventNameGet_partial_solve_wit_11_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_11 : OSEventNameGet_partial_solve_wit_11.
Axiom proof_of_OSEventNameGet_partial_solve_wit_12_pure : OSEventNameGet_partial_solve_wit_12_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_12 : OSEventNameGet_partial_solve_wit_12.
Axiom proof_of_OSEventNameGet_partial_solve_wit_13_pure : OSEventNameGet_partial_solve_wit_13_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_13 : OSEventNameGet_partial_solve_wit_13.
Axiom proof_of_OSEventNameGet_partial_solve_wit_14_pure : OSEventNameGet_partial_solve_wit_14_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_14 : OSEventNameGet_partial_solve_wit_14.
Axiom proof_of_OSEventNameGet_partial_solve_wit_15_pure : OSEventNameGet_partial_solve_wit_15_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_15 : OSEventNameGet_partial_solve_wit_15.
Axiom proof_of_OSEventNameGet_partial_solve_wit_16_pure : OSEventNameGet_partial_solve_wit_16_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_16 : OSEventNameGet_partial_solve_wit_16.
Axiom proof_of_OSEventNameGet_partial_solve_wit_17_pure : OSEventNameGet_partial_solve_wit_17_pure.
Axiom proof_of_OSEventNameGet_partial_solve_wit_17 : OSEventNameGet_partial_solve_wit_17.
Axiom proof_of_OSEventNameGet_which_implies_wit_1 : OSEventNameGet_which_implies_wit_1.
Axiom proof_of_OSEventNameGet_which_implies_wit_2 : OSEventNameGet_which_implies_wit_2.
Axiom proof_of_OS_StrLen_derive_name_get_spec_by_source_spec : OS_StrLen_derive_name_get_spec_by_source_spec.

End VC_Correct.
