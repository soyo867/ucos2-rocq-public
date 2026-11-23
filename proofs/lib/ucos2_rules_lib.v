Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.SL Require Import ConAssertion CriticalSTS.
From SimpleC.SL Require Export IntLib ArrayLib StoreAux MapLib StringLib.
From compcert.lib Require Import Integers.
Require Import Logic.LogicGenerator.demo932.Interface.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Export StateRelBasic safeexec_lib.
Import Monad.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Local Open Scope string.

(* ================================================================== *)
(* Phase 2 Task 2.0:critical-STS 与 UCOS2_C_Rules 模块基础设施          *)
(* ================================================================== *)

(* C 层 critical_STS:StableGlobVars × UCOS2_Verify_State,transition 只要求 sg 不变 *)
Definition UCOS2_CS_C : critical_STS := {|
  critical_STS_state := StableGlobVars * UCOS2_Verify_State;
  critical_STS_transition := fun s1 s2 => fst s1 = fst s2
|}.

(* 抽象层 critical_STS:UCOS2_Verify_State,transition 为相等(暂时) *)
Definition UCOS2_CS_Abs : critical_STS := {|
  critical_STS_state := UCOS2_Verify_State;
  critical_STS_transition := fun _ _ => True
|}.

(* C 层 STS 包装 *)
Module C_STS_UCOS2 <: critical_STS_def.
  Definition c_sts: critical_STS := UCOS2_CS_C.
End C_STS_UCOS2.

(* QCP 2.1 makes the STS and C-layout arguments explicit.  Keep the concrete
   critical state above, then instantiate each signature layer once. *)
Module S_STS_UCOS2 <: critical_STS_to_STS_def C_STS_UCOS2.
  Include critical_STS_to_STS_def C_STS_UCOS2.
End S_STS_UCOS2.

Module UCOS2_Base_Rules
  <: ConAssertion.CSL S_STS_UCOS2 <: SeparationLogicSig.
  Include S_STS_UCOS2.
  Include ConAssertion.CSL.
  Include DerivedPredSig Arch32 LittleEndian.
  Include StoreLibSig Arch32 LittleEndian.
  Include ArrayLibSig Arch32 LittleEndian.
  Include MapLibSig Arch32 LittleEndian.
  Include StringLibSig Arch32 LittleEndian.
End UCOS2_Base_Rules.

Module UCOS2_Critical_Rules
  <: CriticalCSL C_STS_UCOS2 S_STS_UCOS2 UCOS2_Base_Rules
                 Arch32 LittleEndian UCOS2_Base_Rules.
  Include CriticalCSL C_STS_UCOS2 S_STS_UCOS2 UCOS2_Base_Rules
                      Arch32 LittleEndian UCOS2_Base_Rules.
End UCOS2_Critical_Rules.

Module UCOS2_C_Rules <: SeparationLogicSig.
  Include UCOS2_Base_Rules.
  Include UCOS2_Critical_Rules.
End UCOS2_C_Rules.

(* 抽象层 STS 包装(用于 LastSeen / RTrans_Abs 等) *)
Module C_STS_UCOS2_Abs <: critical_STS_def.
  Definition c_sts: critical_STS := UCOS2_CS_Abs.
End C_STS_UCOS2_Abs.

Module STS_UCOS2_Abs <: critical_STS_to_STS_def C_STS_UCOS2_Abs.
  Include critical_STS_to_STS_def C_STS_UCOS2_Abs.
End STS_UCOS2_Abs.

Export UCOS2_C_Rules.

Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 1 留待 Phase 2 落实的核心定义                                 *)
(* ================================================================== *)

Definition InsideCritical (p : StableGlobVars) (l : UCOS2_Verify_State) : Assertion :=
  UCOS2_C_Rules.InsideCritical (p, l).

Definition OutsideCritical (p : StableGlobVars) (l : UCOS2_Verify_State) : Assertion :=
  UCOS2_C_Rules.OutsideCritical (p, l).

Definition RTrans_C (p1 : StableGlobVars) (l1 : UCOS2_Verify_State)
                    (p2 : StableGlobVars) (l2 : UCOS2_Verify_State) : Prop :=
  UCOS2_C_Rules.RTrans (p1, l1) (p2, l2).

Definition GTrans_C (p1 : StableGlobVars) (l1 : UCOS2_Verify_State)
                    (p2 : StableGlobVars) (l2 : UCOS2_Verify_State) : Prop :=
  UCOS2_C_Rules.GTrans (p1, l1) (p2, l2).

Definition RTrans_Abs (l1 l2 : UCOS2_Verify_State) : Prop :=
  STS_UCOS2_Abs.RTrans l1 l2.

Definition GTrans_Abs (l1 l2 : UCOS2_Verify_State) : Prop :=
  STS_UCOS2_Abs.GTrans l1 l2.

Definition crit_rel_no_os_state_change
  (ls_in ls_out : UCOS2_Verify_State) : Prop :=
  ls_out = ls_in.

Definition crit_rel_event_only
  (ls_in ls_out : UCOS2_Verify_State) : Prop :=
  ls_out =
    replace_EventS ls_out.(EventState) ls_in.

Definition crit_rel_task_event
  (ls_in ls_out : UCOS2_Verify_State) : Prop :=
  ls_out =
    replace_EventS ls_out.(EventState)
      (replace_TskS ls_out.(TskState) ls_in).

Definition crit_rel_task_event_sched
  (ls_in ls_out : UCOS2_Verify_State) : Prop :=
  ls_out =
    replace_SchedS ls_out.(SchedState)
      (replace_EventS ls_out.(EventState)
        (replace_TskS ls_out.(TskState) ls_in)).

Definition crit_rel_intr_only
  (ls_in ls_out : UCOS2_Verify_State) : Prop :=
  ls_out =
    replace_IntrS ls_out.(IntrState) ls_in.

Definition atomic_cmd {A} (c : program UCOS2_Verify_State A)
  : program (UCOS2_Verify_State -> Prop) A :=
  fun X1 a X2 =>
    exists l1 l2, X1 l1 /\ c l1 a l2 /\
    X2 == (RTrans_Abs l2).

Definition LastSeen (s : UCOS2_Verify_State) : (UCOS2_Verify_State -> Prop) -> Prop :=
  fun B => RTrans_Abs s == B.
