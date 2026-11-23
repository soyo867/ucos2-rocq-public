Require Export Ucos2Verify.lib.ucos2_rules_lib.

(** OSDebugInit's selected V2.93.01 body only forms addresses of the
    declared debug/config objects (including OSTmrTbl[0] and
    OSTmrWheelTbl[0]) through one local const-void pointer and then returns
    the caller frame unchanged.  The local pointer is not exported and no
    object bytes are loaded or written; the caller owns any required global
    layout. *)
