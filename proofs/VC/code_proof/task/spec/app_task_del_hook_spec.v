Require Export Ucos2Verify.lib.ucos2_rules_lib.

(** Selected V2.93.01 application deletion hook: [(void)ptcb].
    Its C proof preserves the caller's actual resource frame.  A custom
    application hook requires its own source and effect proof. *)
