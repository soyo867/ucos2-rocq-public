Require Export Ucos2Verify.lib.ucos2_rules_lib.

(** OS_Dummy, V2.93.01, is an empty internal C function called by TaskDel.
    Its local C contract preserves the caller's exact separated resources.
    This does not replace the Restore/Save interval's interference protocol. *)
