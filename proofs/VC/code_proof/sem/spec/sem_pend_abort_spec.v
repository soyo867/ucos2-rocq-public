Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Export Ucos2Verify.VC.code.event.spec.event_pend_abort_spec.

Import UCOS2_C_Rules.

(** OSSemPendAbort, V2.93.01 os_sem.c:439--493.  Reuses the shared
    ordered prefix and counted critical loop, with the real SEM type/mask.
    The semaphore count is preserved; an aborted suspended waiter is not
    thereby promised to become runnable.  This does not migrate an old
    C/manual proof or claim the post-Restore scheduler call has returned. *)
Definition sem_pend_abort_type_error (type_byte : Z) : option OSErrCode :=
  event_pend_abort_type_error (encode_event_type OS_EVENT_TYPE_SEM) type_byte.

Definition sem_pend_abort_critical (sg : StableGlobVars) (eid : EventID) (opt : Z)
  : program UCOS2_Verify_State (Z * (OSErrCode * bool)) :=
  event_pend_abort_critical sg eid PendSem opt.
