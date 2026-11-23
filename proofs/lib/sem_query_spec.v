Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import String.
Require Import AUXLib.ListLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.event.
Require Export Ucos2Verify.lib.event_wait.
Require Export Ucos2Verify.lib.ucos2_verify_inv.

Import ListNotations.
Import EventStateDef.
Import UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string.
Local Open Scope sac_scope.

(** Source-faithful L5 semantics for OSSemQuery.  All four observable arms
    preserve the kernel state; the null checks are intentionally ordered
    before event-address validity and the event-type lookup. *)
Definition OSSemQuery_sem
  (sg : StableGlobVars) (pevent p_sem_data : addr)
  : program UCOS2_Verify_State Z :=
  fun ls0 ret ls1 =>
    (pevent = 0 /\ ret = 4 /\ ls1 = ls0) \/
    (pevent <> 0 /\ p_sem_data = 0 /\ ret = 9 /\ ls1 = ls0) \/
    (pevent <> 0 /\ p_sem_data <> 0 /\
     exists eid,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       unsigned_last_nbits
         (event_slot_type_value ls0.(EventState) eid) 32 <> 3 /\
       ret = 1 /\ ls1 = ls0) \/
    (pevent <> 0 /\ p_sem_data <> 0 /\
     exists eid e cnt event_ptr grp tbl,
       valid_event_id sg eid /\
       pevent = event_addr sg eid /\
       event_snapshot_of_prop
         sg ls0.(TskState) ls0.(EventState) eid e
         3 cnt event_ptr grp tbl /\
       task_event_reference_closure ls0.(TskState) ls0.(EventState) /\
       Zlength tbl = 8 /\ ret = 0 /\ ls1 = ls0).

(** Ordinary-Prop view used by the C public postcondition. *)
Definition sem_query_public_post_prop
  (sg : StableGlobVars) (pevent p_sem_data : addr)
  (ls0 : UCOS2_Verify_State) (ret : Z) (ls1 : UCOS2_Verify_State) : Prop :=
  OSSemQuery_sem sg pevent p_sem_data ls0 ret ls1.

(** Exact return observer for the safeExec thread. *)
Definition observe_sem_query_result
  (ret : Z) : program (UCOS2_Verify_State -> Prop) Z :=
  StateRelMonad.ret ret.

(** Ordered public return semantics of the selected uC/OS-II profile.
    [slot_type] is deliberately ignored by the two earlier null checks. *)
Definition OSSemQuery_return_code
  (pevent p_sem_data slot_type ret : Z) : Prop :=
  ret =
    if Z.eqb pevent 0 then 4
    else if Z.eqb p_sem_data 0 then 9
    else if Z.eqb (unsigned_last_nbits slot_type 32) 3 then 0
    else 1.

(** Exact success observation of the entry event.  This reuses the event
    module's canonical snapshot instead of introducing a parallel semaphore
    state. *)
Definition OSSemQuery_success_observation_of
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (e : OSEventAbstractState)
  (cnt grp : Z) (tbl : list Z) : Prop :=
  task_event_reference_closure entry.(TskState) entry.(EventState) /\
  exists event_ptr,
    event_snapshot_of_prop
      sg entry.(TskState) entry.(EventState) eid e
      3 cnt event_ptr grp tbl /\
    Zlength tbl = 8.

(** Query-output ABI bridge in the exact arrow-field vocabulary emitted by
    QCP.  No guessed byte offsets are part of the semantic contract. *)
Definition OSSemQuery_output_layout_prop
  (base cnt_addr tbl_addr grp_addr : addr) : Prop :=
  cnt_addr = (&(((base)) # "os_sem_data" ->ₛ "OSCnt")) /\
  tbl_addr = (&(((base)) # "os_sem_data" ->ₛ "OSEventTbl")) /\
  grp_addr = (&(((base)) # "os_sem_data" ->ₛ "OSEventGrp")).

(** Projection bridges used when the event is focused for read-only copy. *)
Definition OSSemQuery_event_type_value (e : OSEventAbstractState) : Z :=
  encode_event_type e.(eventType).

Definition OSSemQuery_event_ptr_value
  (sg : StableGlobVars) (e : OSEventAbstractState) : Z :=
  verification_slice_encode_event_ptr_value sg e.

Definition OSSemQuery_event_cnt_value (e : OSEventAbstractState) : Z :=
  encode_event_cnt_value e.

Lemma OSSemQuery_success_observation_cnt :
  forall sg entry eid e cnt grp tbl,
    OSSemQuery_success_observation_of sg entry eid e cnt grp tbl ->
    cnt = OSSemQuery_event_cnt_value e.
Proof.
  intros sg entry eid e cnt grp tbl [_ [event_ptr [Hsnapshot _]]].
  unfold event_snapshot_of_prop in Hsnapshot.
  destruct Hsnapshot as [_ [_ [Hcnt _]]].
  exact Hcnt.
Qed.

Lemma OSSemQuery_return_code_pevent_null :
  forall pevent p_sem_data slot_type,
    pevent = 0 ->
    OSSemQuery_return_code pevent p_sem_data slot_type 4.
Proof.
  intros pevent p_sem_data slot_type ->.
  reflexivity.
Qed.

Lemma OSSemQuery_return_code_pdata_null :
  forall pevent slot_type,
    pevent <> 0 ->
    OSSemQuery_return_code pevent 0 slot_type 9.
Proof.
  intros pevent slot_type Hpevent.
  unfold OSSemQuery_return_code.
  destruct (Z.eqb_spec pevent 0) as [Heq | Hneq].
  - contradiction.
  - reflexivity.
Qed.

Lemma OSSemQuery_return_code_event_type :
  forall pevent p_sem_data slot_type,
    pevent <> 0 -> p_sem_data <> 0 ->
    unsigned_last_nbits slot_type 32 <> 3 ->
    OSSemQuery_return_code pevent p_sem_data slot_type 1.
Proof.
  intros pevent p_sem_data slot_type Hpevent Hpdata Htype.
  unfold OSSemQuery_return_code.
  destruct (Z.eqb_spec pevent 0) as [Heq | Hneq].
  - contradiction.
  - destruct (Z.eqb_spec p_sem_data 0) as [Heq | Hneq_data].
    + contradiction.
    + destruct (Z.eqb_spec (unsigned_last_nbits slot_type 32) 3)
        as [Heq | Hneq_type].
      * contradiction.
      * reflexivity.
Qed.

Lemma OSSemQuery_return_code_success :
  forall pevent p_sem_data,
    pevent <> 0 -> p_sem_data <> 0 ->
    OSSemQuery_return_code pevent p_sem_data 3 0.
Proof.
  intros pevent p_sem_data Hpevent Hpdata.
  unfold OSSemQuery_return_code.
  destruct (Z.eqb_spec pevent 0) as [Heq | Hneq].
  - contradiction.
  - destruct (Z.eqb_spec p_sem_data 0) as [Heq | Hneq_data].
    + contradiction.
    + reflexivity.
Qed.

Lemma atomic_cmd_same_state_continuation__event_snapshot_return :
  forall (A R : Type) (c : program UCOS2_Verify_State A) ls a
    (k : A -> program (UCOS2_Verify_State -> Prop) R) X,
    c ls a ls ->
    safeExec (LastSeen ls) (StateRelMonad.bind (atomic_cmd c) k) X ->
    safeExec (LastSeen ls) (k a) X.
Proof.
  intros A R c ls a k X Hstep [B [Hseen Hsafe]].
  exists B; split; [exact Hseen |].
  unfold safe, StateRelHoare.weakestpre in *.
  intros r B' Hk.
  apply (Hsafe r B').
  exists a, B; split; [|exact Hk].
  exists ls, ls; split.
  - apply (proj1 (Hseen ls)).
    exact I.
  - split; [exact Hstep |].
    exact (fun s => conj (proj2 (Hseen s)) (proj1 (Hseen s))).
Qed.
