Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Export Ucos2Verify.VC.code.event.spec.event_delete_spec.

Import UCOS2_C_Rules.

(** OSSemDel, V2.93.01 os_sem.c:185--282.  The shared prefix and body
    are bound to the actual SEM type/mask.  Count is zeroed on recycling;
    the source does not release application resources represented by a
    counted semaphore.  Return/perr, trace and any requested scheduler
    continuation are composed after Restore, outside the masked body. *)
Definition sem_delete_context_error (type_byte int_nesting : Z) : option OSErrCode :=
  event_delete_context_error (encode_event_type OS_EVENT_TYPE_SEM) type_byte int_nesting.

Definition sem_delete_critical (sg : StableGlobVars) (eid : EventID) (opt : Z)
  : program UCOS2_Verify_State (addr * (OSErrCode * bool)) :=
  event_delete_critical sg eid PendSem opt.
