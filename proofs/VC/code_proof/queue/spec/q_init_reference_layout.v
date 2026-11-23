Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Local Open Scope Z_scope.

(** User-selected layout-only reference ELF, not a bootable kernel/BSP proof.
    The inspected ARM32 little-endian ELF places the 96-byte OSQTbl and
    four-byte OSQFreeList at these addresses in the official Zynq-7000
    example DDR region. These are address bindings, not heap ownership.
    Other layouts continue to use the unchanged parameterized model. *)
Definition q_init_zynq7_reference_layout (sg : StableGlobVars) : Prop :=
  sg.(g_OSQTbl) = 0x3e000dac /\ sg.(g_OSQFreeList) = 0x3e000da8.

Lemma q_init_zynq7_reference_table_endpoint : forall sg,
  q_init_zynq7_reference_layout sg ->
  0 <= sg.(g_OSQTbl) /\ sg.(g_OSQTbl) + 96 <= 4294967295.
Proof.
  intros sg [Htable Hfree]; rewrite Htable; lia.
Qed.
