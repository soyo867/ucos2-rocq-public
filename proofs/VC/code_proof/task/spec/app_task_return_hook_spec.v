Require Export Ucos2Verify.lib.ucos2_rules_lib.

(** Selected V2.93.01 application return hook: [(void)ptcb].
    The C contract preserves an arbitrary caller resource assertion in the
    existing UCOS2_C_Rules instance.  The pointer is not dereferenced, so no
    non-null or live-TCB premise is required.  Custom hooks need their own
    source and effect proof. *)
