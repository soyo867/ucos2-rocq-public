Require Import Coq.ZArith.ZArith.
Require Import Ucos2Verify.lib.stable_glob_vars.
Local Open Scope Z_scope.

(** The selected profile contains four 24-byte QCBs. OS_MemClr increments
    its byte cursor after the last write, so the one-past pointer must be
    representable. This pure source-layout condition supplies no ownership;
    queue_init_pre supplies all table/root cells and derives the lower bound.
    No linked-image address is selected by this generic internal contract. *)
Definition q_init_table_endpoint_in_range (sg : StableGlobVars) : Prop :=
  sg.(g_OSQTbl) + 96 <= 4294967295.
