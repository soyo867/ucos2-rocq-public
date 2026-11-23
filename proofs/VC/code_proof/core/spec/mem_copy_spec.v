Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.

Import UCOS2_C_Rules.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Exact byte-copy contract in the caller's existing assertion instance.
    The separated writable destination may initially contain arbitrary bytes;
    [UCharArray.full_to_undef_full] weakens initialized storage without dropping
    ownership.  At length zero both arrays have their genuine empty meaning,
    including at address zero.  No ownership of objects named by copied bytes
    is acquired, and no OS global state or typed-layout invariant is assumed. *)
Definition mem_copy_pre (dest src n : Z) (bytes : list Z) : Assertion :=
  UCharArray.undef_full dest n ** UCharArray.full src n bytes.

Definition mem_copy_post (dest src n : Z) (bytes : list Z) : Assertion :=
  UCharArray.full dest n bytes ** UCharArray.full src n bytes.
