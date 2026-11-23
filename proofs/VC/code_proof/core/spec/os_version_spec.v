Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Local Open Scope Z_scope.

(* The original selected header defines OS_VERSION as 29300u.  The query
   neither reads nor changes the abstract state, independently of its type. *)
Definition os_version_program {S : Type} : program S Z :=
  StateRelMonad.ret 29300.

Definition os_version_safe {S : Type}
    (s : S) (X : Z -> S -> Prop) : Prop :=
  safeExec (eq s) (@os_version_program S) X.

Definition os_version_safe_return {S : Type}
    (s : S) (result : Z) (X : Z -> S -> Prop) : Prop :=
  safeExec (eq s) (StateRelMonad.ret result) X.

Lemma os_version_program_result :
  forall (S : Type) (s : S) result s',
    os_version_program s result s' <-> result = 29300 /\ s' = s.
Proof.
  intros S s result s'.
  unfold os_version_program, StateRelMonad.ret.
  intuition congruence.
Qed.

Lemma os_version_safe_return_same_state :
  forall (S : Type) (s : S) (X : Z -> S -> Prop),
    os_version_safe s X -> os_version_safe_return s 29300 X.
Proof.
  intros S s X Hsafe. exact Hsafe.
Qed.

Lemma os_version_uint16_range : 0 <= 29300 <= 65535.
Proof. lia. Qed.
