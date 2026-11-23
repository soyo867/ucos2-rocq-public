Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_inactive_program_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_spec.
Require Import Ucos2Verify.VC.code.flag.spec.flag_pend_selected_c_source_spec.
Import UCOS2_C_Rules TaskStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Final public-input adapter. The program module has no dependency on the
    selected callee module; this wrapper fixes the original selected source. *)
Module FlagPendInactiveSelectedInput.

Definition flag_pend_selected_owned_input environment critical boundary local sg caller call mask
  i pgrp requested mode delay perr before
  (X : Z -> Z -> UCOS2_Verify_State -> Prop) (frame : Assertion) : Assertion :=
  FlagPendInactiveFirstProgram.flag_pend_owned_input environment critical boundary local sg
    (SelectedEventSources.flag_pend_selected_linked_sources environment critical sg) caller call mask
    i pgrp requested mode delay perr before X frame.

Lemma flag_pend_selected_owned_input_open :
  forall environment critical boundary local sg caller call mask
    i pgrp requested mode delay perr before X frame,
  flag_pend_selected_owned_input environment critical boundary local sg caller call mask
    i pgrp requested mode delay perr before X frame |--
  coq_prop (FlagPendInactiveFirstProgram.flag_pend_public_entry environment critical sg caller call mask
    i pgrp requested mode delay before X) &&
    (PendPhaseCandidate.flag_pend_caller_world environment local sg caller mask before **
      (perr # UChar |->_) ** frame).
Proof.
  intros; apply FlagPendInactiveFirstProgram.flag_pend_owned_input_open.
Qed.

End FlagPendInactiveSelectedInput.

