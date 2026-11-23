Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Import UCOS2_C_Rules.

Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope sac_scope.

(* ================================================================== *)
(* Phase 2 Task 2.5:TickAbstractState 不变式                           *)
(* ================================================================== *)
(* TickAbstractState 已在 ucos2_verify_state_def.v 中定义               *)

Definition verification_slice_tick_in_range (s : TickAbstractState) : Prop :=
  0 <= s.(ostime).

Definition store_tick_state (sg : StableGlobVars) (s : TickAbstractState) : Assertion :=
  sg.(g_OSTime) # UInt |-> s.(ostime).

Definition verification_slice_tick_inv (sg : StableGlobVars) (s : TickAbstractState) : Assertion :=
  coq_prop (verification_slice_tick_in_range s) && store_tick_state sg s.

(** Native OSTimeTick updates OSTime modulo the 32-bit unsigned range even
    when stepping is waiting or OSRunning is false.  The user tick hook
    has its own effect boundary; no unused history counter is stored. *)
Definition tick_counter_advance (s : TickAbstractState) : TickAbstractState :=
  {| ostime := (s.(ostime) + 1) mod 4294967296;
     tickStepState := s.(tickStepState) |}.

Definition tick_step_decision (state : Z) : bool * Z :=
  if Z.eqb state 0 then (true, 0)
  else if Z.eqb state 1 then (false, 1)
  else if Z.eqb state 2 then (true, 1)
  else (true, 0).

Definition tick_step_advance (running : bool)
  (s : TickAbstractState) : bool * TickAbstractState :=
  let counted := tick_counter_advance s in
  if running then
    let '(process, next_step) := tick_step_decision s.(tickStepState) in
    (process, {| ostime := counted.(ostime);
                 tickStepState := next_step |})
  else (false, counted).

Lemma tick_counter_unsigned : forall s,
  0 <= (tick_counter_advance s).(ostime) < 4294967296.
Proof. intros; simpl; apply Z.mod_pos_bound; lia. Qed.

Lemma tick_wait_counts_without_task_processing : forall s,
  s.(tickStepState) = 1 ->
  fst (tick_step_advance true s) = false /\
  (snd (tick_step_advance true s)).(ostime) =
    (s.(ostime) + 1) mod 4294967296.
Proof. intros s H; unfold tick_step_advance; rewrite H; simpl; auto. Qed.

Definition tick_task_update (t : TaskAbstractState) : TaskAbstractState :=
  if Z.eqb t.(dly) 0 then t else
  let delay := t.(dly) - 1 in
  let expired := Z.eqb delay 0 in
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr);
     tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom);
     tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt);
     tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode);
     tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName);
     tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr);
     tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart);
     tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42);
     tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr); curPrio := t.(curPrio);
     stat := if expired then task_status_after_timeout t.(stat) else t.(stat);
     statPend := if expired then
       snd (task_status_timeout (encode_task_status t.(stat))) else t.(statPend);
     dly := delay; eventPtr := t.(eventPtr); eventMultiWaitEvents := t.(eventMultiWaitEvents);
     eventMultiRdy := t.(eventMultiRdy); msg := t.(msg);
     nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma tick_task_preserves_non_timeout_fields : forall t,
  let post := tick_task_update t in
  post.(taskID) = t.(taskID) /\
  post.(taskGeneration) = t.(taskGeneration) /\
  post.(curPrio) = t.(curPrio) /\
  post.(tcbStkPtr) = t.(tcbStkPtr) /\
  post.(tcbExtPtr) = t.(tcbExtPtr) /\
  post.(tcbStkBottom) = t.(tcbStkBottom) /\
  post.(tcbStkSize) = t.(tcbStkSize) /\
  post.(tcbOpt) = t.(tcbOpt) /\
  post.(tcbPublicId) = t.(tcbPublicId) /\
  post.(tcbFlagNode) = t.(tcbFlagNode) /\
  post.(tcbFlagsRdy) = t.(tcbFlagsRdy) /\
  post.(tcbTaskName) = t.(tcbTaskName) /\
  post.(tcbReg0) = t.(tcbReg0) /\
  post.(tcbPadding42) = t.(tcbPadding42) /\
  post.(tcbPadding43) = t.(tcbPadding43) /\
  post.(tcbEventMultiPtr) = t.(tcbEventMultiPtr) /\
  post.(eventPtr) = t.(eventPtr) /\
  post.(eventMultiWaitEvents) = t.(eventMultiWaitEvents) /\
  post.(eventMultiRdy) = t.(eventMultiRdy) /\
  post.(msg) = t.(msg) /\ post.(nextTCB) = t.(nextTCB) /\
  post.(prevTCB) = t.(prevTCB) /\ post.(delReq) = t.(delReq).
Proof.
  intro t; cbv zeta; unfold tick_task_update.
  destruct (Z.eqb t.(dly) 0); repeat split; reflexivity.
Qed.

Lemma tick_task_delay_bounded : forall t,
  0 <= t.(dly) < 4294967296 ->
  0 <= (tick_task_update t).(dly) < 4294967296.
Proof.
  intros t H; unfold tick_task_update.
  destruct (Z.eqb (dly t) 0) eqn:Hz; [exact H|].
  apply Z.eqb_neq in Hz; simpl; lia.
Qed.

Lemma tick_task_preserves_reserved_bits_clear : forall multi t,
  task_status_reserved_bits_clear multi t.(stat) ->
  task_status_reserved_bits_clear multi (tick_task_update t).(stat).
Proof.
  intros multi t Hclear; unfold tick_task_update.
  destruct (Z.eqb t.(dly) 0); [exact Hclear|].
  destruct (Z.eqb (t.(dly) - 1) 0); [|exact Hclear].
  apply task_status_after_timeout_preserves_reserved_bits; exact Hclear.
Qed.

Lemma tick_task_one_tick_timeout : forall t pty,
  t.(dly) = 1 -> (task_non_suspension_bits t.(stat)) = task_pend_mask pty -> pty <> PendMulti ->
  (tick_task_update t).(dly) = 0 /\
  (task_non_suspension_bits (tick_task_update t).(stat)) = 0 /\
  (tick_task_update t).(statPend) = PendTimeout /\
  (tick_task_update t).(eventPtr) = t.(eventPtr).
Proof.
  intros t pty Hd Hp Hkind; unfold tick_task_update; rewrite Hd.
  destruct (task_status_after_timeout_single_kind t.(stat) pty Hp Hkind) as [Hclear Hresult].
  change (0 = 0 /\ task_non_suspension_bits (task_status_after_timeout t.(stat)) = 0 /\
    snd (task_status_timeout (encode_task_status t.(stat))) = PendTimeout /\ t.(eventPtr) = t.(eventPtr)).
  repeat split; assumption || reflexivity.
Qed.

Lemma tick_preserves_linked_phase : forall t pty,
  task_linked_wait_phase t pty ->
  task_linked_wait_phase (tick_task_update t) pty.
Proof.
  intros t pty Hphase; unfold tick_task_update.
  destruct (Z.eqb (dly t) 0) eqn:Hz; [exact Hphase|].
  destruct (Z.eqb (dly t - 1) 0) eqn:Hlast.
  - apply Z.eqb_eq in Hlast.
    destruct Hphase as [Hp | [_ [_ Hd]]].
    + unfold task_linked_wait_phase; cbn [stat statPend dly].
      rewrite (task_status_single_of_mask t.(stat) (Some pty) Hp).
      destruct pty; destruct (task_is_suspended t.(stat));
        try (left; reflexivity); right; repeat split; reflexivity || lia.
    + subst; rewrite Hd in Hz; discriminate.
  - unfold task_linked_wait_phase in *; simpl.
    destruct Hphase as [Hp | [_ [_ Hd]]]; [left; exact Hp|].
    rewrite Hd in Hz; discriminate.
Qed.

(** Match the source's decrement, conditional status clear and result
    store.  Event/Flag registrations remain linked until their cleanup. *)
Lemma tick_task_update_image_eq : forall sg t,
  0 < t.(dly) < 4294967296 ->
  task_tcb64_image sg (tick_task_update t) =
    let decremented := tcb_write (task_tcb64_image sg t) TCBDly (Some (t.(dly) - 1)) in
    if Z.eqb (t.(dly) - 1) 0 then
      tcb_expire_status_image decremented (encode_task_status t.(stat))
    else decremented.
Proof.
  intros sg t Hd; unfold tick_task_update.
  destruct (Z.eqb t.(dly) 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia|].
  destruct (Z.eqb (t.(dly) - 1) 0).
  - apply functional_extensionality; intro field.
    unfold tcb_expire_status_image.
    destruct (task_status_has_pending (encode_task_status t.(stat))) eqn:Hpending;
      destruct field; try reflexivity;
      cbn [task_tcb64_image stat statPend tcb_write field_storage.field_update TCBField_eq_dec];
      unfold task.encode_task_status in *;
      rewrite ?task_status_after_timeout_encoding;
      unfold task_status_timeout; rewrite ?Hpending; reflexivity.
  - apply functional_extensionality; intros []; reflexivity.
Qed.

Lemma tick_task_update_layout_image_eq : forall sg t,
  0 < t.(dly) < 4294967296 ->
  task_layout_image sg (tick_task_update t) =
    let decremented := tcb_layout_update_common
      (fun image => tcb_write image TCBDly (Some (t.(dly) - 1)))
      (task_layout_image sg t) in
    if Z.eqb (t.(dly) - 1) 0 then
      tcb_multi_timeout_image decremented (encode_task_status t.(stat))
    else decremented.
Proof.
  intros sg t Hd.
  pose proof (tick_task_update_image_eq sg t Hd) as Hcommon.
  unfold tick_task_update in Hcommon |- *.
  destruct (Z.eqb t.(dly) 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia|].
  destruct (Z.eqb (t.(dly) - 1) 0);
    apply functional_extensionality; intros [field| | | | | | |]; try reflexivity.
  all: pose proof (f_equal (fun image => image field) Hcommon) as Hfield;
    destruct field; try exact Hfield; try reflexivity;
    unfold tcb_multi_timeout_image, tcb_expire_status_image in *;
    destruct (task_status_has_pending (encode_task_status t.(stat))) in Hfield |- *;
    exact Hfield || reflexivity.
Qed.

(** Expiration changes the canonical Task, not just an independent raw
    image.  The input-array pointer and Event registrations remain linked;
    the caller's continuation owns their later removal. *)
Lemma tick_task_one_tick_multi_timeout : forall sg t array,
  t.(dly) = 1 -> task_multi_registered_fields (task_layout_image sg t) array ->
  task_multi_expired_fields (task_layout_image sg (tick_task_update t)) array.
Proof.
  intros sg t array Hd Hregistered.
  rewrite tick_task_update_layout_image_eq by (rewrite Hd; lia).
  rewrite Hd; cbn [Z.sub Z.eqb].
  apply tcb_multi_timeout_expired_fields.
  - destruct Hregistered as [Ha [Hp [Hr [Hs [bits [Hb Hbits]]]]]].
    split; [exact Ha|]; split; [exact Hp|]; split; [exact Hr|]; split; [exact Hs|].
    exists bits; split; [exact Hb|exact Hbits].
  - reflexivity.
  - reflexivity.
Qed.

(** One OSTimeTick loop body's masked update (os_core.c:990--1014).
    [t] is the actual cursor lookup at this iteration, not an entry snapshot.
    The outer running/step/idle tests, tick/trace hooks, cursor read and
    Restore are separate source phases.  In particular a delay of zero does
    not insert a task merely because its status now says RDY.  On expiration
    the source tests only SUSPEND, even when MULTI remains set. *)
Definition tick_task_step (sg : StableGlobVars) (tid : TaskID)
  (t : TaskAbstractState) (s : UCOS2_Verify_State) : UCOS2_Verify_State :=
  if Z.eqb t.(dly) 0 then s else
  let new := tick_task_update t in
  replace_TskS (glob_task_set_usedtask s.(TskState) tid new)
    (if Z.eqb new.(dly) 0 then
       replace_SchedS (sched_wake_by_status sg s.(TskState) s.(SchedState)
         tid (encode_task_status new.(stat))) s
     else s).

Lemma tick_task_zero_delay_eq : forall t,
  t.(dly) = 0 -> tick_task_update t = t.
Proof. intros t H; unfold tick_task_update; rewrite H; reflexivity. Qed.

Lemma tick_task_step_zero_delay_eq : forall sg tid t s,
  t.(dly) = 0 -> tick_task_step sg tid t s = s.
Proof. intros sg tid t s H; unfold tick_task_step; rewrite H; reflexivity. Qed.

Lemma tick_task_step_task_state_eq : forall sg tid t s,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  (tick_task_step sg tid t s).(TskState) =
    glob_task_set_usedtask s.(TskState) tid (tick_task_update t).
Proof.
  intros sg tid t s Ht; unfold tick_task_step.
  destruct (Z.eqb t.(dly) 0) eqn:Hdelay.
  - apply Z.eqb_eq in Hdelay; rewrite tick_task_zero_delay_eq by exact Hdelay.
    unfold glob_task_set_usedtask.
    destruct s.(TskState); simpl in *; f_equal.
    apply functional_extensionality; intro slot; destruct (Z.eqb slot tid) eqn:E;
      [apply Z.eqb_eq in E; subst slot; exact Ht|reflexivity].
  - destruct (Z.eqb (tick_task_update t).(dly) 0); reflexivity.
Qed.

Lemma tick_task_update_preserves_in_range : forall sg tasks tid t,
  task_in_range sg tasks -> tasks.(inUsedTaskStates) tid = Some t ->
  task_in_range sg (glob_task_set_usedtask tasks tid (tick_task_update t)).
Proof.
  intros sg tasks tid t Htasks Ht; eapply task_update_preserves_in_range;
    [exact Htasks|exact Ht| | | | |];
    unfold tick_task_update; destruct (Z.eqb t.(dly) 0); reflexivity.
Qed.

Lemma tick_task_step_preserves_task_in_range : forall sg tid t s,
  task_in_range sg s.(TskState) -> s.(TskState).(inUsedTaskStates) tid = Some t ->
  task_in_range sg (tick_task_step sg tid t s).(TskState).
Proof.
  intros; rewrite tick_task_step_task_state_eq by exact H0.
  apply tick_task_update_preserves_in_range; assumption.
Qed.

Lemma tick_task_step_other_task_eq : forall sg tid t s slot,
  slot <> tid ->
  (tick_task_step sg tid t s).(TskState).(inUsedTaskStates) slot =
    s.(TskState).(inUsedTaskStates) slot.
Proof.
  intros sg tid t s slot Hne; unfold tick_task_step.
  destruct (Z.eqb t.(dly) 0); [reflexivity|].
  destruct (Z.eqb (tick_task_update t).(dly) 0); simpl;
    rewrite (proj2 (Z.eqb_neq _ _) Hne); reflexivity.
Qed.

Lemma tick_task_step_non_task_sched_state_eq : forall sg tid t s,
  let post := tick_task_step sg tid t s in
  replace_TskS s.(TskState) (replace_SchedS s.(SchedState) post) = s.
Proof.
  intros sg tid t s; cbn zeta; unfold tick_task_step.
  destruct (Z.eqb t.(dly) 0); [destruct s; reflexivity|].
  destruct (Z.eqb (tick_task_update t).(dly) 0); destruct s; reflexivity.
Qed.

Definition tick_inv (sg : StableGlobVars) (s : TickAbstractState) : Assertion :=
  coq_prop (0 <= s.(ostime) < 4294967296 /\
            0 <= s.(tickStepState) < 256) &&
  (store_tick_state sg s **
   sg.(g_OSTickStepState) # UChar |-> s.(tickStepState)).
