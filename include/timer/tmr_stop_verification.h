#ifndef TMR_STOP_VERIFICATION_H
#define TMR_STOP_VERIFICATION_H

/* Declaration recipe for the pinned V2.93.01, 32-bit little-endian input.
 * Insert the common annotation declarations after the original types/globals.
 * Attach the three named contracts below at the ORIGINAL prototype sites:
 * ucos_ii.h: OSSchedLock/OSSchedUnlock; os_tmr.c: static OSTmr_Unlink.
 * Their declarations replace those sites; this file supplies no C body,
 * typedef, layout, callback cast, or replacement ABI. OS_TMR_CALLBACK remains
 * the original void (*)(void *, void *).
 *
 * This is a candidate to be consumed at the original declaration sites.
 * The callee contracts are explicit product lifts of existing contracts.
 * Their canonical obligations reuse the complete kernel-callee witnesses
 * through slice/lift. The public declaration below must also be attached
 * to the actual single-function carrier and consumed by canonical QCP.
 */

#include "verification_stdlib.h"
/*@ Import Coq From SimpleC.CoreLang Require Import CTypes */
/*@ Import Coq Import SimpleCtypeNotations */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_unlink_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.timer_callback_semantics */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.timer_callee_lift_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_stop_fields_spec */
/*@ Import Coq Require Import Ucos2Verify.VC.code.timer.spec.tmr_stop_call_resources_spec */
/* Base specs export legacy assertion names. Select the callback model again
 * after all spec imports; the fixed source prelude also selects it earlier. */
/*@ Import Coq Import TimerCallback_C_Rules TimerCallback_C_Rules.Rules */
/*@ Import Coq Local Open Scope Z_scope */
/*@ Import Coq Local Open Scope sac */

/* Application is bound by each caller's With {Application}; AppRep is an
 * ordinary ghost argument of type Application -> Assertion. Neither is a
 * global opaque constant. Types/functions below are existing Coq declarations.
 */
/*@ Extern Coq
    (TmrStopState :: * => *) (TmrStopEffects :: * => *)
    (TmrStopCallApplication :: * => *)
    (TmrStopReturn :: *) (tmr_stop_output :: *) (TmrStopField :: *)
    (StableGlobVars :: *) (UCOS2_Verify_State :: *) (GlobTimerState :: *)
    (TimerImage :: *) (InterruptPlatformResources :: *)
    (CriticalRegionResources :: *) (OsSchedExternalResources :: *)
    (OsSchedCallContext :: *) (TaskInvocationOrigin :: *)
    (nat :: *) (bool :: *) (unit :: *) (prod :: * => * => *)
    (program :: * => * => *) */
/*@ Extern Coq
    (true : bool) (false : bool) (tt : unit)
    (pair : {A} {B} -> A -> B -> prod A B)
    (eq : {A} -> A -> A -> Prop)
    (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
    (bind : {Sigma} {A} {B} -> program Sigma A -> (A -> program Sigma B) -> program Sigma B)
    (ret : {Sigma} {A} -> A -> program Sigma A) */
/* MonadErr also has a program notation. These names denote ONLY StateRel. */
/*@ Printing Coq Name program := StateRelMonad.M */
/*@ Printing Coq Name bind := StateRelMonad.bind */
/*@ Printing Coq Name ret := StateRelMonad.ret */
/*@ Printing Strategy Name program := StateRelMonad.M */
/*@ Printing Strategy Name bind := StateRelMonad.bind */
/*@ Printing Strategy Name ret := StateRelMonad.ret */

/*@ Extern Coq
    (tmr_stop_kernel : {Application} -> TmrStopState Application -> UCOS2_Verify_State)
    (tmr_stop_error : {Application} -> TmrStopState Application -> Z)
    (tmr_stop_application : {Application} -> TmrStopState Application -> Application)
    (tmr_stop_set_error : {Application} -> Z -> TmrStopState Application -> TmrStopState Application)
    (tmr_stop_set_kernel : {Application} -> UCOS2_Verify_State -> TmrStopState Application -> TmrStopState Application)
    (tmr_stop_return_value : TmrStopReturn -> Z)
    (tmr_stop_return_error : TmrStopReturn -> Z)
    (tmr_stop_return_context : TmrStopReturn -> OsSchedCallContext)
    (tmr_stop_return_output : TmrStopReturn -> tmr_stop_output)
    (tmr_stop_lock_application : {Application} -> TmrStopEffects Application -> OsSchedCallContext -> TmrStopState Application -> TmrStopState Application -> Prop)
    (tmr_stop_unlock_application : {Application} -> TmrStopEffects Application -> OsSchedCallContext -> TmrStopState Application -> OsSchedCallContext -> TmrStopState Application -> Prop)
    (tmr_stop_callback : {Application} -> TmrStopEffects Application -> Z -> Z -> Z -> OsSchedCallContext -> program (TmrStopState Application) OsSchedCallContext)
    (tmr_stop_store_error_program : {Application} -> Z -> program (TmrStopState Application) unit)
    (tmr_stop_finish_program : {Application} -> Z -> OsSchedCallContext -> program (TmrStopState Application) TmrStopReturn)
    (tmr_stop_lock_program : {Application} -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> OsSchedCallContext -> program (TmrStopState Application) unit)
    (tmr_stop_unlock_program : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> OsSchedCallContext -> program (TmrStopState Application) OsSchedCallContext)
    (tmr_stop_unlink_program : {Application} -> StableGlobVars -> Z -> program (TmrStopState Application) unit)
    (tmr_stop_type_program : {Application} -> bool -> Z -> (TmrStopState Application -> Z) -> program (TmrStopState Application) Z)
    (tmr_stop_state_program : {Application} -> bool -> Z -> (TmrStopState Application -> Z) -> program (TmrStopState Application) Z)
    (tmr_stop_api_program : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> program (TmrStopState Application) tmr_stop_output)
    (tmr_stop_api_pre : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> (tmr_stop_output -> TmrStopState Application -> Prop) -> Prop)
*/

/* Section parameters are pruned by Coq: context_rep has no Application or
 * AppRep; client_rep has only AppRep/perr; unlock_ready has no platform/mask.
 * For pre/post, the Z arguments after effects are mask, perr; after pooled
 * they are pointer, index, opt, argument, followed by raw_type/raw_state.
 */
/*@ Extern Coq
    (tmr_stop_context_rep : OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> OsSchedCallContext -> UCOS2_Verify_State -> Assertion)
    (tmr_stop_client_rep : {Application} -> (Application -> Assertion) -> Z -> TmrStopState Application -> Assertion)
    (tmr_stop_owned : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_unlock_ready : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> TmrStopState Application -> Prop)
    (tmr_stop_pre : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> (tmr_stop_output -> TmrStopState Application -> Prop) -> Assertion)
    (tmr_stop_post : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Z -> (tmr_stop_output -> TmrStopState Application -> Prop) -> Assertion)
    (tmr_stop_callback_pre : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> prod Z Z -> Assertion)
    (tmr_stop_callback_post : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> prod Z Z -> unit -> Assertion)
    (tmr_stop_callback_capability : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
*/

/* Existing field views use the actual alias-arrow addresses. The fields
 * layout proposition is an input/ABI obligation, never an added axiom.
 */
/*@ Extern Coq
    (StopTypeField : TmrStopField) (StopStateField : TmrStopField)
    (StopCallbackField : TmrStopField) (StopArgumentField : TmrStopField)
    (tmr_stop_fields_layout : Prop)
    (tmr_stop_field_cell : Z -> TimerImage -> TmrStopField -> Assertion)
    (tmr_stop_owned_field_view : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Z -> TimerImage -> TmrStopField -> Assertion)
    (tmr_stop_unlink_frame : {Application} -> OsSchedExternalResources -> InterruptPlatformResources -> StableGlobVars -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_raw_rep : Z -> Z -> Z -> Z -> Assertion)
    (tmr_stop_raw_state_rep : Z -> Z -> Z -> Z -> Assertion)
    (TimerState : UCOS2_Verify_State -> GlobTimerState)
    (replace_TimerS : GlobTimerState -> UCOS2_Verify_State -> UCOS2_Verify_State)
    (os_sched_call_invocation : OsSchedCallContext -> nat)
    (os_sched_call_origin : OsSchedCallContext -> TaskInvocationOrigin)
    (os_sched_lock_ints : UCOS2_Verify_State -> Z)
    (g_OSIntNesting : StableGlobVars -> Z)
    (g_OSTmrWheelTbl : StableGlobVars -> Z)
    (UCOS2_state_inv : StableGlobVars -> UCOS2_Verify_State -> Prop)
    (timer_api_initialized : GlobTimerState -> Prop)
    (timer_pool_addr : StableGlobVars -> Z -> Z)
    (tmr_unlink_layout : Prop) (tmr_unlink_profile : StableGlobVars -> Prop)
    (tmr_unlink_running : GlobTimerState -> Z -> Prop)
*/

/* Only the printed assertion names below are rebound to their proved
 * product wrappers. Pure source relations/safety keep their old meaning.
 */
/*@ Extern Coq
    (os_sched_lock_global_addresses : StableGlobVars -> Z -> Z -> Z -> Prop)
    (os_sched_unlock_global_addresses : StableGlobVars -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Prop)
    (os_sched_unlock_acquire_safety : OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (os_sched_lock_call_relation : CriticalRegionResources -> StableGlobVars -> nat -> UCOS2_Verify_State -> UCOS2_Verify_State -> UCOS2_Verify_State -> Prop)
    (os_sched_unlock_call_relation : OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> UCOS2_Verify_State -> OsSchedCallContext -> UCOS2_Verify_State -> Prop)
    (os_sched_lock_program_pre : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Assertion)
    (os_sched_lock_program_post : InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> nat -> TaskInvocationOrigin -> Z -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Assertion)
    (os_sched_unlock_program_pre : OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Assertion)
    (os_sched_unlock_program_post : OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> OsSchedCallContext -> Z -> UCOS2_Verify_State -> (UCOS2_Verify_State -> Prop) -> Assertion)
    (os_sched_context_resources : OsSchedExternalResources -> OsSchedCallContext -> Assertion)
    (unmap_table_rep : StableGlobVars -> Assertion)
    (timer_inv : StableGlobVars -> GlobTimerState -> Assertion)
    (tmr_unlink_configured_post : StableGlobVars -> GlobTimerState -> Z -> Assertion)
    (tmr_unlink_raw_pre : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion -> Assertion)
    (tmr_unlink_raw_post : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Assertion -> Assertion)
*/
/*@ Printing Coq Name os_sched_lock_program_pre := TimerCalleeLift.os_sched_lock_program_pre */
/*@ Printing Coq Name os_sched_lock_program_post := TimerCalleeLift.os_sched_lock_program_post */
/*@ Printing Coq Name os_sched_unlock_program_pre := TimerCalleeLift.os_sched_unlock_program_pre */
/*@ Printing Coq Name os_sched_unlock_program_post := TimerCalleeLift.os_sched_unlock_program_post */
/*@ Printing Coq Name os_sched_context_resources := TimerCalleeLift.os_sched_context_resources */
/*@ Printing Coq Name unmap_table_rep := TimerCalleeLift.unmap_table_rep */
/*@ Printing Coq Name timer_inv := TimerCalleeLift.timer_inv */
/*@ Printing Coq Name tmr_unlink_configured_post := TimerCalleeLift.tmr_unlink_configured_post */
/*@ Printing Coq Name tmr_unlink_raw_pre := TimerCalleeLift.tmr_unlink_raw_pre */
/*@ Printing Coq Name tmr_unlink_raw_post := TimerCalleeLift.tmr_unlink_raw_post */

/* Concrete call interface. The CallApplication wrapper contains the real
 * raw Type/State byte observations and the residual client state. Its
 * representation includes those cells only when pooled=false. The one
 * output byte remains in entry_owned/client_rep and may equal callback_arg.
 */
/*@ Extern Coq
    (tmr_stop_call_type_byte : {Client} -> TmrStopCallApplication Client -> Z)
    (tmr_stop_call_state_byte : {Client} -> TmrStopCallApplication Client -> Z)
    (tmr_stop_call_client : {Client} -> TmrStopCallApplication Client -> Client)
    (tmr_stop_call_application_rep : {Client} -> (Client -> Assertion) -> bool -> Z -> Z -> TmrStopCallApplication Client -> Assertion)
    (tmr_stop_call_raw_type : {Client} -> TmrStopState (TmrStopCallApplication Client) -> Z)
    (tmr_stop_call_raw_state : {Client} -> TmrStopState (TmrStopCallApplication Client) -> Z)
    (tmr_stop_call_effects : {Application} -> (Z -> Z -> Z -> OsSchedCallContext -> program (TmrStopState Application) OsSchedCallContext) -> TmrStopEffects Application)
    (tmr_stop_entry_client_rep : {Application} -> (Application -> Assertion) -> Z -> TmrStopState Application -> Assertion)
    (tmr_stop_entry_owned : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_pooled_binding : StableGlobVars -> Z -> Z -> GlobTimerState -> Prop)
    (tmr_stop_call_entry_field_view : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Z -> TimerImage -> TmrStopField -> Assertion)
    (tmr_stop_call_lock_pre : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_lock_post : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_unlock_pre : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_unlock_post : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_callback_instance_pre : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> (Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop) -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> prod Z Z -> Assertion)
    (tmr_stop_call_callback_capability : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> (Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop) -> Z -> Z -> Z -> Assertion)
    (tmr_stop_call_callback_capabilities : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> (Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop) -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_callback_resources : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> (Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop) -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_callback_domain : {Application} -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Prop)
    (tmr_stop_call_requirements : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Prop)
    (tmr_stop_call_input_binding : {Client} -> StableGlobVars -> Z -> bool -> Z -> Z -> TmrStopState (TmrStopCallApplication Client) -> Prop)
    (tmr_stop_call_pre : {Client} -> (Client -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> (Z -> Z -> Z -> OsSchedCallContext -> program (TmrStopState (TmrStopCallApplication Client)) OsSchedCallContext) -> Z -> Z -> Z -> bool -> Z -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState (TmrStopCallApplication Client) -> (tmr_stop_output -> TmrStopState (TmrStopCallApplication Client) -> Prop) -> Assertion)
    (tmr_stop_call_post : {Client} -> (Client -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> (Z -> Z -> Z -> OsSchedCallContext -> program (TmrStopState (TmrStopCallApplication Client)) OsSchedCallContext) -> Z -> Z -> Z -> bool -> Z -> Z -> Z -> Z -> OsSchedCallContext -> TmrStopState (TmrStopCallApplication Client) -> Z -> (tmr_stop_output -> TmrStopState (TmrStopCallApplication Client) -> Prop) -> Assertion)
    (tmr_stop_call_read_cell : Z -> TmrStopField -> Z -> Assertion)
    (tmr_stop_call_kernel_any : UCOS2_Verify_State -> Prop)
    (tmr_stop_call_stopped_status : Z -> Prop)
    (tmr_stop_call_lock_step : {Application} -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> OsSchedCallContext -> TmrStopState Application -> TmrStopState Application -> Prop)
    (tmr_stop_call_unlink_step : {Application} -> StableGlobVars -> Z -> TmrStopState Application -> TmrStopState Application -> Prop)
    (tmr_stop_call_unlock_step : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> OsSchedCallContext -> TmrStopState Application -> OsSchedCallContext -> TmrStopState Application -> Prop)
    (tmr_stop_call_field_read : {Application} -> bool -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> TmrStopField -> TmrStopState Application -> Z -> Prop)
    (tmr_stop_call_read_rest : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> Z -> bool -> OsSchedCallContext -> TmrStopState Application -> Z -> TmrStopField -> Z -> Assertion)
    (tmr_stop_call_output_frame : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_unlink_client_frame : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> StableGlobVars -> Z -> Z -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_call_source_facts : {Application} -> OsSchedExternalResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> (tmr_stop_output -> TmrStopState Application -> Prop) -> Prop)
    (tmr_stop_call_state_prefix : {Application} -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Z -> TmrStopState Application -> Prop)
    (tmr_stop_call_callback_prefix : {Application} -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Z -> Z -> Z -> TmrStopState Application -> Prop)
    (tmr_stop_call_running_prefix : {Application} -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> OsSchedCallContext -> TmrStopState Application -> Prop)
    (tmr_stop_call_running_ready : {Application} -> (Application -> Assertion) -> OsSchedExternalResources -> InterruptPlatformResources -> CriticalRegionResources -> StableGlobVars -> TmrStopEffects Application -> Z -> Z -> bool -> Z -> Z -> Z -> Z -> (TmrStopState Application -> Z) -> (TmrStopState Application -> Z) -> OsSchedCallContext -> TmrStopState Application -> Assertion)
    (tmr_stop_interrupt_rest : OsSchedExternalResources -> InterruptPlatformResources -> StableGlobVars -> Z -> OsSchedCallContext -> UCOS2_Verify_State -> Assertion)
*/

/* Insert at the existing OSSchedLock declaration. The client/output and
 * context stack resources are the caller's disjoint frame. Xk is the
 * EXISTING kernel continuation, not the public Stop continuation X.
 */
void OSSchedLock(void)
/*@ timer_stop_lock_spec
    With (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
         (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin)
         (mask : Z) (before : UCOS2_Verify_State) (Xk : UCOS2_Verify_State -> Prop)
    Require os_sched_lock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting) &&
            os_sched_lock_program_pre(platform, critical, sg, invocation, origin, mask, before, Xk)
    Ensure os_sched_lock_program_post(platform, critical, sg, invocation, origin, mask, before, Xk)
*/;

/* Insert at the existing OSSchedUnlock declaration. program_pre contains
 * the real os_sched_unlock_acquire_safety(external,critical,sg,context,before).
 * Its scheduled branch acquires its own state and returns its actual context.
 */
void OSSchedUnlock(void)
/*@ timer_stop_unlock_spec
    With (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
         (critical : CriticalRegionResources) (sg : StableGlobVars)
         (context : OsSchedCallContext) (mask : Z) (before : UCOS2_Verify_State)
         (Xk : UCOS2_Verify_State -> Prop)
    Require os_sched_unlock_global_addresses(sg, &OSRunning, &OSIntNesting, &OSLockNesting,
              &OSPrioHighRdy, &OSPrioCur, &OSTCBHighRdy, OSTCBPrioTbl,
              &OSCtxSwCtr, OSUnMapTbl, &OSRdyGrp, OSRdyTbl) &&
            os_sched_unlock_program_pre(external, platform, critical, sg, context, mask, before, Xk)
    Ensure os_sched_unlock_program_post(external, platform, critical, sg, context, mask, before, Xk)
*/;

/* Insert at the existing static OSTmr_Unlink declaration. This is the
 * existing configured contract used by OSTmrStart's environment; its
 * configured <= raw refinement must also be transported to the new rules.
 * R may depend on Gamma. It excludes the whole Timer representation that
 * this call changes. The raw_pre/raw_post wrappers above slice R explicitly.
 */
static void OSTmr_Unlink(OS_TMR *ptmr)
/*@ timer_stop_unlink_configured_spec
    With (sg : StableGlobVars) (s : GlobTimerState) (i : Z) (R : Assertion)
    Require tmr_unlink_layout && tmr_unlink_profile(sg) &&
            timer_api_initialized(s) && tmr_unlink_running(s, i) &&
            ptmr == timer_pool_addr(sg, i) && OSTmrWheelTbl == g_OSTmrWheelTbl(sg) &&
            timer_inv(sg, s) * R
    Ensure tmr_unlink_configured_post(sg, s, i) * R
*/;

/* The public OSTmrStop contract belongs on the actual single-function
 * carrier. Its complete annotation template is retained in
 * source-bridge-integration.md; no extra target prototype is emitted here.
 */

#endif
