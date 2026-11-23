Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Strings.String Coq.micromega.Lia.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.event Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.VC.code.sem.spec.sem_query_call_spec.

Import UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** The observation is the count, group and eight bytes actually copied by
    this call. It does not claim that the queried object is unchanged when
    Restore returns. Caller-owned output memory is retained separately. *)
Record SemQuerySnapshot := {
  sem_query_count : Z;
  sem_query_group : Z;
  sem_query_table : list Z
}.

Definition sem_query_source_api_read (eid : EventID)
  : program UCOS2_Verify_State SemQuerySnapshot :=
  fun entry copied unchanged =>
    exists current,
      mutex_query_copy_snapshot entry eid current copied.(sem_query_count)
        copied.(sem_query_group) copied.(sem_query_table) /\
      current.(eventType) = OS_EVENT_TYPE_SEM /\ unchanged = entry.

(** Ordered source checks, acquisition, protected read, and actual Restore
    interval. No post-invariant, handle-lifetime or progress guard is added. *)
Definition sem_query_source_api_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (eid : EventID) (pe pd : addr)
  : program UCOS2_Verify_State (Z * option SemQuerySnapshot) :=
  if Z.eqb pe 0 then StateRelMonad.ret (4, None)
  else if Z.eqb pd 0 then StateRelMonad.ret (9, None)
  else StateRelMonad.bind (get' (fun s => s)) (fun before =>
    if Z.eqb (event_slot_type_value before.(EventState) eid) 3 then
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.bind (sem_query_source_api_read eid) (fun snapshot =>
          StateRelMonad.bind (update (critical_region_interval critical sg invocation))
            (fun _ => StateRelMonad.ret (0, Some snapshot))))
    else StateRelMonad.ret (1, None)).

Definition sem_query_source_api_safe critical sg invocation eid pe pd before
  (X : Z -> option SemQuerySnapshot -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (sem_query_source_api_program critical sg invocation eid pe pd)
    (fun result after => X (fst result) (snd result) after).

Lemma sem_query_source_api_null_event_return : forall critical sg invocation eid pd before,
  sem_query_source_api_program critical sg invocation eid 0 pd before (4, None) before.
Proof. intros; unfold sem_query_source_api_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma sem_query_source_api_null_data_return : forall critical sg invocation eid pe before,
  pe <> 0 -> sem_query_source_api_program critical sg invocation eid pe 0 before (9, None) before.
Proof.
  intros; unfold sem_query_source_api_program; rewrite (proj2 (Z.eqb_neq _ _) H).
  unfold StateRelMonad.ret; cbn; auto.
Qed.

Lemma sem_query_source_api_wrong_type_return : forall critical sg invocation eid pe pd before,
  pe <> 0 -> pd <> 0 -> event_slot_type_value before.(EventState) eid <> 3 ->
  sem_query_source_api_program critical sg invocation eid pe pd before (1, None) before.
Proof.
  intros critical sg invocation eid pe pd before Hpe Hpd Htype.
  unfold sem_query_source_api_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe),
    (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, get', get.
  exists before, before; split; [split; reflexivity|].
  rewrite (proj2 (Z.eqb_neq _ _) Htype); split; reflexivity.
Qed.

Lemma sem_query_source_api_success :
  forall critical sg invocation eid pe pd before entry after snapshot,
  pe <> 0 -> pd <> 0 -> event_slot_type_value before.(EventState) eid = 3 ->
  critical_region_interval critical sg invocation before entry ->
  sem_query_source_api_read eid entry snapshot entry ->
  critical_region_interval critical sg invocation entry after ->
  sem_query_source_api_program critical sg invocation eid pe pd before (0, Some snapshot) after.
Proof.
  intros critical sg invocation eid pe pd before entry after snapshot
    Hpe Hpd Htype Hacquire Hread Hrestore.
  unfold sem_query_source_api_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe),
    (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, get', get.
  exists before, before; split; [split; reflexivity|].
  rewrite Htype; cbn.
  exists tt, entry; split; [exact Hacquire|].
  exists snapshot, entry; split; [exact Hread|].
  exists tt, after; split; [exact Hrestore|].
  split; reflexivity.
Qed.

Lemma sem_query_source_api_acquire_type :
  forall critical sg invocation eid mask saved before entry observed current,
  sem_query_acquire_facts critical sg invocation eid mask saved before entry observed current ->
  event_slot_type_value before.(EventState) eid = 3.
Proof.
  intros critical sg invocation eid mask saved before entry observed current
    [_ [_ [_ [Hlookup [_ [Htype _]]]]]].
  unfold event_slot_type_value, mutex_query_lookup in *.
  rewrite Hlookup, Htype; reflexivity.
Qed.

Lemma sem_query_source_api_safe_return :
  forall critical sg invocation eid pe pd before after code snapshot X,
  sem_query_source_api_program critical sg invocation eid pe pd before (code, snapshot) after ->
  sem_query_source_api_safe critical sg invocation eid pe pd before X ->
  safeExec (eq after) (StateRelMonad.ret (code, snapshot))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation eid pe pd before after code snapshot X Hprogram Hsafe.
  unfold sem_query_source_api_safe in Hsafe.
  eapply (highstependret_derive
    (sem_query_source_api_program critical sg invocation eid pe pd) (eq before)
    (code, snapshot) (fun _ => eq after)); [|exact Hsafe].
  intros state Hstate; subst state; exists after; split; assumption || reflexivity.
Qed.

Lemma sem_query_source_api_program_result_iff :
  forall critical sg invocation eid pe pd before result after,
  sem_query_source_api_program critical sg invocation eid pe pd before result after <->
  if Z.eqb pe 0 then result = (4, None) /\ before = after
  else if Z.eqb pd 0 then result = (9, None) /\ before = after
  else if Z.eqb (event_slot_type_value before.(EventState) eid) 3 then
    exists entry snapshot,
      critical_region_interval critical sg invocation before entry /\
      sem_query_source_api_read eid entry snapshot entry /\
      critical_region_interval critical sg invocation entry after /\
      result = (0, Some snapshot)
  else result = (1, None) /\ before = after.
Proof.
  intros critical sg invocation eid pe pd before result after.
  unfold sem_query_source_api_program; destruct (Z.eqb pe 0); [reflexivity|].
  destruct (Z.eqb pd 0); [reflexivity|].
  unfold StateRelMonad.bind, get', get, update, StateRelMonad.ret.
  split.
  - intros [observed [state [[-> <-] Hbranch]]].
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3); [|exact Hbranch].
    destruct Hbranch as [u [entry [Hentry [snapshot [released [Hread
      [v [returned [Hreturn [Hresult Hafter]]]]]]]]]].
    pose proof Hread as [current [_ [_ ->]]].
    subst after; exists entry, snapshot; auto.
  - intro Hbranch; exists before, before; split; [split; reflexivity|].
    destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3); [|exact Hbranch].
    destruct Hbranch as [entry [snapshot [Hentry [Hread [Hreturn Hresult]]]]].
    exists tt, entry; split; [exact Hentry|].
    exists snapshot, entry; split; [exact Hread|].
    exists tt, after; split; [exact Hreturn|]; split; [exact Hresult|reflexivity].
Qed.

(** Reflexive intervals witness a mathematical normal endpoint for the
    original live/free domain. This is not a platform termination theorem. *)
Lemma sem_query_source_api_program_has_result :
  forall critical sg invocation eid pe pd before observed,
  sem_query_call_input critical sg invocation pe pd before eid observed ->
  exists result, sem_query_source_api_program critical sg invocation eid pe pd before result before.
Proof.
  intros critical sg invocation eid pe pd before observed Hinput.
  destruct (Z.eq_dec pe 0) as [->|Hpe].
  - exists (4, None); apply sem_query_source_api_null_event_return.
  - destruct (Z.eq_dec pd 0) as [->|Hpd].
    + exists (9, None); apply sem_query_source_api_null_data_return; exact Hpe.
    + destruct (Z.eq_dec (event_slot_type_value before.(EventState) eid) 3) as [Htype|Htype].
      * destruct (sem_query_call_input_live critical sg invocation pe pd before eid observed
          Hinput Hpe Hpd) as [_ [_ [Hslot _]]].
        destruct (sem_query_public_slot_is_sem before eid observed Hslot Htype) as [Hlookup Hsem].
        exists (0, Some {| sem_query_count := encode_event_cnt_value observed;
          sem_query_group := encode_event_wait_grp observed.(waitList) before.(TskState);
          sem_query_table := encode_event_wait_tbl_values observed before.(TskState) |}).
        eapply sem_query_source_api_success; try eassumption; try constructor.
        exists observed; split; [|auto].
        unfold mutex_query_copy_snapshot; cbn; auto.
      * exists (1, None); apply sem_query_source_api_wrong_type_return; assumption.
Qed.

Lemma sem_query_source_api_preserves_validity :
  forall critical sg invocation eid pe pd before result after,
  UCOS2_state_inv sg before ->
  sem_query_source_api_program critical sg invocation eid pe pd before result after ->
  UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation eid pe pd before result after Hvalid Hprogram.
  apply sem_query_source_api_program_result_iff in Hprogram.
  destruct (Z.eqb pe 0); [destruct Hprogram as [_ <-]; exact Hvalid|].
  destruct (Z.eqb pd 0); [destruct Hprogram as [_ <-]; exact Hvalid|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 3);
    [|destruct Hprogram as [_ <-]; exact Hvalid].
  destruct Hprogram as [entry [snapshot [Hentry [_ [Hrestore _]]]]].
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hentry Hvalid)) as Hentry_valid.
  exact (proj1 (critical_region_interval_transports_resources
    critical sg invocation entry after Hrestore Hentry_valid)).
Qed.

Definition sem_query_source_api_restore_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask saved : Z)
  (entry : UCOS2_Verify_State) : Assertion :=
  coq_prop (interrupt_saved_value mask saved /\ UCOS2_state_inv sg entry) &&
  (critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg entry).

Definition sem_query_source_api_output (pd : addr)
  (snapshot : option SemQuerySnapshot) : Assertion :=
  match snapshot with
  | None => emp
  | Some copied => sem_query_output_fields pd copied.(sem_query_count) copied.(sem_query_group) **
      store_osprio_array (&(pd # "os_sem_data" ->ₛ "OSEventTbl")) copied.(sem_query_table)
  end.

Definition sem_query_source_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (eid : EventID) (pe pd code : Z)
  (X : Z -> option SemQuerySnapshot -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX snapshot after,
    coq_prop (sem_query_source_api_program critical sg invocation eid pe pd before (code, snapshot) after /\
      safeExec (eq after) (StateRelMonad.ret (code, snapshot))
        (fun result state => X (fst result) (snd result) state)) **
    (mutex_query_closed platform critical sg invocation origin mask after **
     sem_query_source_api_output pd snapshot).
