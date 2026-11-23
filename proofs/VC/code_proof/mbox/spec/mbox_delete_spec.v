Require Import Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event.
Require Export Ucos2Verify.VC.code.event.spec.event_delete_spec.

Import UCOS2_C_Rules.

(** OSMboxDel, V2.93.01 os_mbox.c:179--279.  Unlike Queue there is no
    QCB/buffer release; unlike Mutex there is no owner/PCP restoration.
    Deletion overwrites the stored message pointer but does not free its
    target.  Abort writes NULL/PendAbort into each actual selected TCB,
    preserving suspension and the later invocation-return obligation. *)
Definition mbox_delete_context_error (type_byte int_nesting : Z) : option OSErrCode :=
  event_delete_context_error (encode_event_type OS_EVENT_TYPE_MBOX) type_byte int_nesting.

Definition mbox_delete_critical (sg : StableGlobVars) (eid : EventID) (opt : Z)
  : program UCOS2_Verify_State (addr * (OSErrCode * bool)) :=
  event_delete_critical sg eid PendMbox opt.
