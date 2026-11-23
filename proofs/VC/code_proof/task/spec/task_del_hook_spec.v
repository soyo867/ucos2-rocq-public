Require Export Ucos2Verify.lib.ucos2_rules_lib.

(** V2.93.01 ARMv7-A deletion wrapper, with both CPU/App hooks enabled.
    The real C call to the selected App_TaskDelHook consumes and returns
    the same UCOS2 caller resource frame.  Its C callee must be delivered
    with the matching source instance; this is not a platform assumption. *)
