Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.ucos2_spatial.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.

Import UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The documented caller supplies the current masked execution resource.
    [mask] is the IRQ/FIQ projection, not a saved CPU word.  IRQ must be
    masked; either FIQ setting is retained.  This API neither acquires nor
    restores the mask, and does not establish the platform implementation. *)
Definition os_int_enter_irq_masked (mask : Z) : Prop :=
  Z.land mask 192 = mask /\ Z.testbit mask 7 = true.

Definition os_int_enter_running (s : UCOS2_Verify_State) : Z :=
  if s.(SchedState).(isRunning) then 1 else 0.

Definition os_int_enter_nesting (s : UCOS2_Verify_State) : Z :=
  s.(IntrState).(intNesting).

Definition os_int_enter_global_addresses
  (sg : StableGlobVars) (running nesting : Z) : Prop :=
  running = sg.(g_OSRunning) /\ nesting = sg.(g_OSIntNesting).

(** Ordered source observation followed by the existing source-exact
    saturating counter transformer.  The update relation is mathematical:
    its saturated identity endpoint is not an additional concrete store.
    Trace is disabled in the selected profile. *)
Definition os_int_enter_program : program UCOS2_Verify_State unit :=
  bind (get' (fun s => s.(SchedState).(isRunning)))
    (fun running =>
       if running then
         bind (update' (fun s =>
           replace_IntrS (interrupt_enter_state true s.(IntrState)) s))
           (fun _ => ret tt)
       else ret tt).

Lemma os_int_enter_program_result_iff : forall before result after,
  os_int_enter_program before result after <->
  result = tt /\ after = os_int_enter_state before.
Proof.
  intros before result after.
  unfold os_int_enter_program, os_int_enter_state.
  unfold_monad.
  unfold get', get, update', update.
  split.
  - intros (running & observed & [Hrunning Hobserved] & Hstep).
    subst running observed.
    destruct (isRunning (SchedState before)) eqn:Hrun.
    + destruct Hstep as (u & changed & Hchanged & [Hresult Hafter]).
      split; [exact Hresult|].
      rewrite <- Hafter.
      change (changed = replace_IntrS
        (interrupt_enter_state true (IntrState before)) before) in Hchanged.
      rewrite Hchanged.
      destruct before; reflexivity.
    + destruct Hstep as [Hresult Hafter]; subst after.
      split; [exact Hresult |]. destruct before; reflexivity.
  - intros [Hresult Hafter]; subst result after.
    exists (isRunning (SchedState before)), before.
    split; [split; reflexivity |].
    destruct (isRunning (SchedState before)) eqn:Hrun.
    + exists tt, (replace_IntrS (interrupt_enter_state true (IntrState before)) before).
      repeat split; reflexivity.
    + split; [reflexivity |]. destruct before; reflexivity.
Qed.

Lemma os_int_enter_program_has_result : forall before,
  os_int_enter_program before tt (os_int_enter_state before).
Proof. intro; apply os_int_enter_program_result_iff; split; reflexivity. Qed.

Definition os_int_enter_safe (before : UCOS2_Verify_State)
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) os_int_enter_program X.

Definition os_int_enter_return_safe (before : UCOS2_Verify_State)
  (X : unit -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq (os_int_enter_state before)) (ret tt) X.

Lemma os_int_enter_safe_return : forall before X,
  os_int_enter_safe before X -> os_int_enter_return_safe before X.
Proof.
  intros before X Hsafe.
  eapply (highstependret_derive os_int_enter_program (eq before) tt
    (fun _ => eq (os_int_enter_state before))).
  - intros observed Hobserved; subst observed.
    exists (os_int_enter_state before); split.
    + apply os_int_enter_program_has_result.
    + reflexivity.
  - exact Hsafe.
Qed.

(** The residual contains the untouched lock counter, the scheduler minus
    its running byte, and all other kernel modules.  In particular no
    duplicate running/nesting ownership and no validity premise is hidden
    inside the structural residual. *)
Definition os_int_enter_frame (sg : StableGlobVars)
  (before : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSLockNesting) # UChar |-> before.(IntrState).(lockNesting) **
  sched_raw_rep_without_running sg before.(TskState) before.(SchedState) **
  UCOS2_raw_rep_missing_two sg before SchedModule InterruptModule.

Lemma os_int_enter_inv_split : forall sg before,
  UCOS2_inv sg before |--
  coq_prop (UCOS2_state_inv sg before) &&
  (sg.(g_OSRunning) # UChar |-> os_int_enter_running before **
   sg.(g_OSIntNesting) # UChar |-> os_int_enter_nesting before **
   os_int_enter_frame sg before).
Proof.
  intros sg before.
  rewrite (UCOS2_inv_split_two sg before SchedModule InterruptModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  rewrite sched_raw_rep_split_running.
  unfold interrupt_inv, store_int_state, os_int_enter_frame,
    os_int_enter_running, os_int_enter_nesting.
  entailer!.
Qed.

Lemma os_int_enter_inv_merge : forall sg before,
  UCOS2_state_inv sg before ->
  sg.(g_OSRunning) # UChar |-> os_int_enter_running before **
  sg.(g_OSIntNesting) # UChar |-> os_int_enter_nesting (os_int_enter_state before) **
  os_int_enter_frame sg before |-- UCOS2_inv sg (os_int_enter_state before).
Proof.
  intros sg before Hvalid.
  unfold os_int_enter_frame, os_int_enter_running, os_int_enter_nesting.
  pose proof (os_int_enter_merge_inv sg before Hvalid) as Hmerge.
  unfold UCOS2_raw_rep_missing_interrupt in Hmerge.
  rewrite (UCOS2_raw_rep_missing_module_split_module sg before
    InterruptModule SchedModule ltac:(discriminate)) in Hmerge.
  rewrite UCOS2_raw_rep_missing_two_comm_eq in Hmerge.
  cbn [UCOS2_module_rep] in Hmerge.
  rewrite sched_raw_rep_split_running in Hmerge.
  unfold store_int_state in Hmerge.
  assert (Hlock : lockNesting (interrupt_enter_state
    (isRunning (SchedState before)) (IntrState before)) =
    lockNesting (IntrState before)).
  { unfold interrupt_enter_state.
    destruct (isRunning (SchedState before)); [destruct (intNesting (IntrState before) <? 255)|];
      reflexivity. }
  rewrite Hlock in Hmerge.
  change (sg.(g_OSRunning) # UChar |-> (if before.(SchedState).(isRunning) then 1 else 0) **
    sg.(g_OSIntNesting) # UChar |->
      (interrupt_enter_state before.(SchedState).(isRunning) before.(IntrState)).(intNesting) **
    (sg.(g_OSLockNesting) # UChar |-> before.(IntrState).(lockNesting) **
     sched_raw_rep_without_running sg before.(TskState) before.(SchedState) **
     UCOS2_raw_rep_missing_two sg before SchedModule InterruptModule) |--
       UCOS2_inv sg (os_int_enter_state before)).
  rewrite <- Hmerge; entailer!.
Qed.
