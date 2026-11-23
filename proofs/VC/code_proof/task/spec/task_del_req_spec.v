Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import String.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSTaskDelReq changes this real byte only. In particular it neither
    deletes a task nor releases any Mutex, stack or waiting registration. *)
Definition task_set_delete_request (t : TaskAbstractState) (requested : bool)
  : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := t.(tcbTaskName); tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr); tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart); tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42); tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend);
     dly := t.(dly); eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := requested |}.

Lemma task_set_delete_request_same : forall t,
  task_set_delete_request t t.(delReq) = t.
Proof. intros []; reflexivity. Qed.

Lemma task_set_delete_request_last : forall t first last,
  task_set_delete_request (task_set_delete_request t first) last =
  task_set_delete_request t last.
Proof. reflexivity. Qed.

Lemma task_set_delete_request_layout_image_eq : forall sg t requested,
  task_layout_image sg (task_set_delete_request t requested) =
  tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBDelReq)
    (Some (encode_task_delete_request requested)).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |];
    [destruct field| | | | | | |]; reflexivity.
Qed.

Definition task_del_req_state (s : UCOS2_Verify_State) tid old : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_usedtask s.(TskState) tid
    (task_set_delete_request old true)) s.

Definition task_del_req_current (s : UCOS2_Verify_State) tid t : Prop :=
  s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some t.

Definition task_del_req_target (s : UCOS2_Verify_State) prio tid t : Prop :=
  s.(TskState).(prioTbl) prio = PTTask tid /\ s.(TskState).(inUsedTaskStates) tid = Some t.

(** The source dereferences OSTCBCur only on SELF. This is call-acquisition
    safety, not an ISR guard, ready premise, or a promise that arbitrary
    environment steps leave OSTCBCur unchanged. It has the same form as
    os_int_exit_acquire_safety, with the actual byte-read consumer here. *)
Definition task_del_req_admission (critical : CriticalRegionResources)
  sg invocation prio before : Prop :=
  prio = 255 -> forall acquired,
    critical_region_interval critical sg invocation before acquired ->
    exists tid t, task_del_req_current acquired tid t.

(** Six ordered observations. PTTask is looked up by the acquired table,
    with no equality between the queried priority and the task's curPrio. *)
Inductive task_del_req_step (prio : Z) (before : UCOS2_Verify_State)
  : Z -> UCOS2_Verify_State -> Prop :=
| TaskDelReqIdle : prio = 63 -> task_del_req_step prio before 62 before
| TaskDelReqInvalid : 64 <= prio < 255 -> task_del_req_step prio before 42 before
| TaskDelReqSelf : forall tid t,
    prio = 255 -> task_del_req_current before tid t ->
    task_del_req_step prio before (encode_task_delete_request t.(delReq)) before
| TaskDelReqFree : 0 <= prio < 63 -> before.(TskState).(prioTbl) prio = PTFree ->
    task_del_req_step prio before 67 before
| TaskDelReqReserved : 0 <= prio < 63 -> before.(TskState).(prioTbl) prio = PTReserved ->
    task_del_req_step prio before 61 before
| TaskDelReqSet : forall tid t,
    0 <= prio < 63 -> before.(TskState).(prioTbl) prio = PTTask tid ->
    before.(TskState).(inUsedTaskStates) tid = Some t ->
    task_del_req_step prio before 0 (task_del_req_state before tid t).

(** Keep the linearization endpoint separate from a later returned world.
    In particular SELF's byte and the successful store refer to acquired,
    not to an arbitrary state after Restore has enabled interrupts. *)
Definition task_del_req_result critical sg invocation prio before result current : Prop :=
  ((prio = 63 \/ 64 <= prio < 255) /\
    task_del_req_step prio before result before /\ current = before) \/
  ((prio = 255 \/ 0 <= prio < 63) /\
    exists acquired released,
      critical_region_interval critical sg invocation before acquired /\
      task_del_req_step prio acquired result released /\
      critical_region_interval critical sg invocation released current).

(** The protected computation reads the acquired current task for SELF, or
    reads the acquired priority-table entry and writes only its request byte.
    [get] is partial exactly where the C dereference has no allocated TCB;
    the existing invariant/admission establish readability at those sites. *)
Definition task_del_req_protected_program (prio : Z)
  : program UCOS2_Verify_State Z :=
  if Z.eqb prio 255 then
    StateRelMonad.bind
      (get (fun s t => exists tid, task_del_req_current s tid t))
      (fun t => StateRelMonad.ret (encode_task_delete_request t.(delReq)))
  else
    StateRelMonad.bind (get' (fun s => s.(TskState).(prioTbl) prio))
      (fun slot => match slot with
       | PTFree => StateRelMonad.ret 67
       | PTReserved => StateRelMonad.ret 61
       | PTTask tid =>
           StateRelMonad.bind (get (fun s t => s.(TskState).(inUsedTaskStates) tid = Some t))
             (fun t => StateRelMonad.bind (update' (fun s => task_del_req_state s tid t))
               (fun _ => StateRelMonad.ret 0))
       end).

(** Preserve the source's ordered checks and both enabled-interrupt intervals.
    This is a sequential program, not an atomic lift of the whole API. *)
Definition task_del_req_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (prio : Z)
  : program UCOS2_Verify_State Z :=
  if Z.eqb prio 63 then StateRelMonad.ret 62
  else if andb (Z.leb 63 prio) (negb (Z.eqb prio 255)) then StateRelMonad.ret 42
  else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (task_del_req_protected_program prio)
      (fun code => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret code))).

Definition task_del_req_safe critical sg invocation prio before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_del_req_program critical sg invocation prio) X.

Definition task_del_req_post critical sg invocation prio before result current
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  task_del_req_result critical sg invocation prio before result current /\
  safeExec (fun state => state = current) (StateRelMonad.ret result) X.

Lemma task_del_req_protected_step : forall prio before result after,
  (prio = 255 \/ 0 <= prio < 63) ->
  task_del_req_step prio before result after ->
  task_del_req_protected_program prio before result after.
Proof.
  intros prio before result after Hdomain Hstep.
  destruct Hstep; try (destruct Hdomain; lia).
  - subst prio; cbn [task_del_req_protected_program].
    exists t, before; split; [split; [exists tid; assumption|reflexivity]|].
    split; reflexivity.
  - unfold task_del_req_protected_program.
    assert (E : Z.eqb prio 255 = false) by (apply Z.eqb_neq; lia).
    rewrite E; exists PTFree, before; split.
    + split; [symmetry; assumption|reflexivity].
    + split; reflexivity.
  - unfold task_del_req_protected_program.
    assert (E : Z.eqb prio 255 = false) by (apply Z.eqb_neq; lia).
    rewrite E; exists PTReserved, before; split.
    + split; [symmetry; assumption|reflexivity].
    + split; reflexivity.
  - unfold task_del_req_protected_program.
    assert (E : Z.eqb prio 255 = false) by (apply Z.eqb_neq; lia).
    rewrite E; exists (PTTask tid), before; split.
    + split; [symmetry; assumption|reflexivity].
    + exists t, before; split; [split; [assumption|reflexivity]|].
      exists tt, (task_del_req_state before tid t); split; [reflexivity|].
      split; reflexivity.
Qed.

Lemma task_del_req_result_program : forall critical sg invocation prio before result current,
  task_del_req_result critical sg invocation prio before result current ->
  task_del_req_program critical sg invocation prio before result current.
Proof.
  intros critical sg invocation prio before result current Hresult.
  destruct Hresult as [[Hearly [Hstep ->]]|[Hdomain [acquired [released [Hacquire [Hstep Hrelease]]]]]].
  - destruct Hstep; try (destruct Hearly; lia); unfold task_del_req_program.
    + subst prio; split; reflexivity.
    + assert (Eidle : Z.eqb prio 63 = false) by (apply Z.eqb_neq; lia).
      assert (Ebound : Z.leb 63 prio = true) by (apply Z.leb_le; lia).
      assert (Eself : Z.eqb prio 255 = false) by (apply Z.eqb_neq; lia).
      rewrite Eidle, Ebound, Eself; split; reflexivity.
  - unfold task_del_req_program.
    assert (Eidle : Z.eqb prio 63 = false) by (apply Z.eqb_neq; destruct Hdomain; lia).
    assert (Einvalid : andb (Z.leb 63 prio) (negb (Z.eqb prio 255)) = false).
    { destruct Hdomain as [->|Hrange]; [reflexivity|].
      assert (E : Z.leb 63 prio = false) by (apply Z.leb_gt; lia).
      rewrite E; reflexivity. }
    rewrite Eidle, Einvalid.
    exists tt, acquired; split; [exact Hacquire|].
    exists result, released; split; [eapply task_del_req_protected_step; eassumption|].
    exists tt, current; split; [exact Hrelease|split; reflexivity].
Qed.

Lemma task_del_req_safe_return : forall critical sg invocation prio before result current X,
  task_del_req_result critical sg invocation prio before result current ->
  task_del_req_safe critical sg invocation prio before X ->
  task_del_req_post critical sg invocation prio before result current X.
Proof.
  intros critical sg invocation prio before result current X Hresult Hsafe.
  split; [exact Hresult|].
  eapply (highstependret_derive
    (task_del_req_program critical sg invocation prio)
    (fun state => state = before) result (fun _ state => state = current)).
  - intros state ->; exists current; split; [|reflexivity].
    apply task_del_req_result_program; exact Hresult.
  - exact Hsafe.
Qed.

Definition task_del_req_closed platform critical sg invocation origin mask state : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  critical_region_outside critical sg invocation state.

(** Program-fixed C address interpretation. The positive, four-byte-aligned
    TCB base is the same static ABI premise as init_tcb_list_layout. It
    excludes the RESERVED address 1, without a dynamic task restriction.
    This conditional contract does not claim all linker layouts satisfy it. *)
Definition task_del_req_addresses (sg : StableGlobVars) (table current : addr) : Prop :=
  table = sg.(g_OSTCBPrioTbl) /\ current = sg.(g_OSTCBCur) /\
  0 < sg.(g_OSTCBTbl) /\ sg.(g_OSTCBTbl) mod 4 = 0.

Lemma task_del_req_addresses_base : forall sg table current,
  task_del_req_addresses sg table current -> 1 < sg.(g_OSTCBTbl).
Proof.
  intros sg table current [_ [_ [Hpositive Haligned]]].
  pose proof (Z.div_mod sg.(g_OSTCBTbl) 4 ltac:(lia)); lia.
Qed.

Definition task_del_req_table_entry sg s prio :=
  prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) prio).

Definition task_del_req_table_frame sg s prio : Assertion :=
  store_prio_tbl_missing_i sg s.(TskState).(prioTbl) prio **
  UCOS2_raw_rep_missing_priority_table sg s.

Definition task_del_req_sched_without_current sg s : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(SchedState).(readyList) s.(TskState) **
  sched_rows_rep sg s.(TskState) s.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0).

Definition task_del_req_self_frame sg s tid t : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid t (TCBCommonField TCBDelReq) **
  task_del_req_sched_without_current sg s ** UCOS2_raw_rep_missing_task_storage_sched sg s.

Lemma task_del_req_admission_explicit : forall critical sg invocation prio before,
  prio <> 255 -> task_del_req_admission critical sg invocation prio before.
Proof. unfold task_del_req_admission; intros; contradiction. Qed.

Lemma task_del_req_admission_current : forall critical sg invocation before,
  task_del_req_admission critical sg invocation 255 before ->
  exists tid t, task_del_req_current before tid t.
Proof. intros; apply (H eq_refl before); constructor. Qed.

Lemma task_del_req_admission_no_environment : forall critical sg invocation prio before tid t,
  (forall action, ~ critical.(critical_region_clients) action) ->
  task_del_req_current before tid t ->
  task_del_req_admission critical sg invocation prio before.
Proof.
  intros critical sg invocation prio before tid t Hnone Hcurrent Hself acquired Htrace.
  apply critical_region_interval_raw_trace in Htrace.
  inversion Htrace; subst; [exists tid, t; exact Hcurrent|].
  exfalso; eapply Hnone; eassumption.
Qed.

(** Admission can be established from a checked registered-source stability
    property. This is not implied by generic CSL handles alone. In particular
    a source family which can delete the current TCB needs a separate check. *)
Lemma task_del_req_admission_clients : forall critical sg invocation prio before,
  (forall action initial final, critical.(critical_region_clients) action ->
    kernel_client_step action sg initial final ->
    (exists tid t, task_del_req_current initial tid t) ->
    exists tid t, task_del_req_current final tid t) ->
  (exists tid t, task_del_req_current before tid t) ->
  task_del_req_admission critical sg invocation prio before.
Proof.
  intros critical sg invocation prio before Hclients Hlive Hself acquired Htrace.
  apply critical_region_interval_raw_trace in Htrace.
  revert Hlive; induction Htrace; intros Hlive; [exact Hlive|].
  apply IHHtrace; eapply Hclients; eassumption.
Qed.

(** A concrete existing source family for which SELF admission is stable:
    private allocation/image writes, publication, and invocation retirement.
    This theorem does not register arbitrary IRQ code or TaskDel as harmless. *)
Lemma task_del_req_task_creation_client_current : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  (exists tid t, task_del_req_current before tid t) ->
  exists tid t, task_del_req_current after tid t.
Proof.
  intros action sg before after [_ [_ ->]] [tid [t [Hcurrent Hlookup]]].
  destruct action as [p entry slot rest image|p entry allocation image|p invocation node|retired];
    try (exists tid, t; split; assumption).
  destruct (proj2 (task_commit_live_iff before.(TskState) p invocation node tid)
    (or_intror (ex_intro _ t Hlookup))) as [updated Hupdated].
  exists tid, updated; split; [exact Hcurrent|exact Hupdated].
Qed.

Lemma task_del_req_admission_task_creation : forall critical sg invocation prio before,
  (forall action, critical.(critical_region_clients) action -> task_creation_client_family action) ->
  (exists tid t, task_del_req_current before tid t) ->
  task_del_req_admission critical sg invocation prio before.
Proof.
  intros; eapply task_del_req_admission_clients; [|eassumption].
  intros action initial final Hin Hstep Hlive.
  destruct (H action Hin) as [source ->].
  eapply task_del_req_task_creation_client_current; eassumption.
Qed.

Lemma task_del_req_admission_task_creation_iff : forall critical sg invocation before,
  (forall action, critical.(critical_region_clients) action -> task_creation_client_family action) ->
  (task_del_req_admission critical sg invocation 255 before <->
   exists tid t, task_del_req_current before tid t).
Proof.
  intros; split; [apply task_del_req_admission_current|].
  apply task_del_req_admission_task_creation; assumption.
Qed.

Lemma task_del_req_priority_observation : forall tasks tid old requested slot,
  tasks.(inUsedTaskStates) tid = Some old ->
  option_map curPrio
    ((glob_task_set_usedtask tasks tid (task_set_delete_request old requested)).(inUsedTaskStates) slot) =
  option_map curPrio (tasks.(inUsedTaskStates) slot).
Proof. intros; eapply glob_task_set_usedtask_observation; [eassumption|reflexivity]. Qed.

Lemma task_del_req_preserves_ready : forall sg tasks sched tid old requested,
  tasks.(inUsedTaskStates) tid = Some old -> sched_ready_in_range sg tasks sched ->
  sched_ready_in_range sg (glob_task_set_usedtask tasks tid
    (task_set_delete_request old requested)) sched.
Proof.
  intros sg tasks sched tid old requested Hold [Hmembers [Hsorted [Hcomplete Hnodup]]].
  split.
  - intros slot Hin; destruct (Hmembers slot Hin) as [t [Ht [Hp Hr]]].
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (t = old) by congruence; subst t.
      exists (task_set_delete_request old requested); auto.
    + exists t; auto.
  - split.
    + eapply strictly_sorted_by_key_ext; [|exact Hsorted].
      intro slot; cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E;
        [apply Z.eqb_eq in E; subst; rewrite Hold|]; reflexivity.
    + split; [|exact Hnodup].
      intros slot t Ht Hr; cbn [glob_task_set_usedtask inUsedTaskStates] in Ht.
      destruct (Z.eqb slot tid) eqn:E.
      * apply Z.eqb_eq in E; subst slot; inversion Ht; subst t; eapply Hcomplete; eassumption.
      * eapply Hcomplete; eassumption.
Qed.

Lemma task_del_req_preserves_cross_module : forall sg s tid old,
  s.(TskState).(inUsedTaskStates) tid = Some old -> cross_module_consistency sg s ->
  cross_module_consistency sg (task_del_req_state s tid old).
Proof.
  intros sg s tid old Hold [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  split; [eapply task_mutex_priotbl_consistency_update_task; eauto; reflexivity|].
  split; [eapply mutex_owner_snapshot_update_task; eauto|].
  split.
  - eapply event_wait_object_update_task; try eassumption; try reflexivity.
    intros kind Hphase; exact Hphase.
  - split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_task; try eassumption; try reflexivity;
      intros H; exact H.
Qed.

Lemma task_del_req_preserves_invariant : forall sg s tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  UCOS2_state_inv sg (task_del_req_state s tid old).
Proof.
  intros sg s tid old
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] Hold.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg (task_del_req_state s tid old)).
  { eapply kernel_names_valid_replace_task; [exact Hreferences|].
    eapply task_update_name_references; [exact Hold|reflexivity]. }
  assert (HstacksAfter : parked_stacks_consistent
    (task_del_req_state s tid old).(TskState) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + destruct Hsched as [Hready Hmetadata]; split; [|exact Hmetadata].
      eapply task_del_req_preserves_ready; eassumption.
    + split.
      * eapply event_update_task_preserves_in_range; try eassumption; try reflexivity.
        intros kind Hphase; exact Hphase.
      * split; [apply task_del_req_preserves_cross_module; assumption|]. split.
        -- intro Hrunning; eapply task_update_preserves_idle_tail;
             [exact Hold|reflexivity|apply Hidle; exact Hrunning].
        -- split.
           ++ apply task_reserved_bits_clear_update_task;
                [exact Hstatus|exact (Hstatus tid old Hold)].
           ++ split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
              split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
              split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact Hpending].
Qed.

Definition task_del_req_frame sg s : Assertion :=
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.

Lemma task_del_req_raw_split : forall sg s,
  UCOS2_raw_rep sg s --||-- task_public_storage sg s.(TskState) ** task_del_req_frame sg s.
Proof.
  intros; unfold UCOS2_raw_rep, task_shared_rep, task_del_req_frame,
    UCOS2_raw_rep_missing_task_storage_sched; split; entailer!.
Qed.

Lemma task_del_req_frame_update_eq : forall sg s tid old,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  task_del_req_frame sg s = task_del_req_frame sg (task_del_req_state s tid old).
Proof.
  intros sg s tid old Hold.
  assert (Hprio : forall slot, option_map curPrio (s.(TskState).(inUsedTaskStates) slot) =
    option_map curPrio ((task_del_req_state s tid old).(TskState).(inUsedTaskStates) slot)).
  { intros; symmetry; apply task_del_req_priority_observation; exact Hold. }
  assert (Hencoded : forall ids,
    encode_ready_grp ids s.(TskState) = encode_ready_grp ids (task_del_req_state s tid old).(TskState) /\
    forall y, encode_ready_tbl_at_or ids s.(TskState) y =
      encode_ready_tbl_at_or ids (task_del_req_state s tid old).(TskState) y).
  { intro ids; apply event_wait_encoding_priority_ext; intros; apply Hprio. }
  unfold task_del_req_frame, sched_raw_rep, UCOS2_raw_rep_missing_task_storage_sched.
  cbn [task_del_req_state replace_TskS SchedState IntrState EventState TickState FlagState
    MemoryState TimerState StatsState ControlState NameState TskState glob_task_set_usedtask parkedTaskStacks].
  rewrite (event_raw_rep_change_task_index sg s.(TskState)
    (glob_task_set_usedtask s.(TskState) tid (task_set_delete_request old true)) s.(EventState)).
  2: { apply event_wait_priority_agreement_encodes; intros eid e slot He Hin; apply Hprio. }
  destruct (Hencoded s.(SchedState).(readyList)) as [Hgrp Hrows].
  rewrite Hgrp; cbn [sched_rows_rep]; rewrite !Hrows; reflexivity.
Qed.

Definition task_del_req_field_frame sg s tid t : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid t (TCBCommonField TCBDelReq) **
  task_del_req_frame sg s.

Lemma task_del_req_split_field : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  UCOS2_raw_rep sg s |--
  tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |->
    encode_task_delete_request t.(delReq) ** task_del_req_field_frame sg s tid t.
Proof.
  intros sg s tid t Hlookup; rewrite task_del_req_raw_split.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid t
    (TCBCommonField TCBDelReq) Hlookup (tcb_configured_common_field_in _ _ _)).
  unfold task_del_req_field_frame; entailer!.
Qed.

Lemma task_del_req_merge_field : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |->
    encode_task_delete_request t.(delReq) ** task_del_req_field_frame sg s tid t |-- UCOS2_raw_rep sg s.
Proof.
  intros sg s tid t Hlookup; rewrite task_del_req_raw_split.
  unfold task_del_req_field_frame.
  pose proof (task_public_storage_merge_field sg s.(TskState) tid t
    (TCBCommonField TCBDelReq) Hlookup (tcb_configured_common_field_in _ _ _)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell task_layout_image tcb_layout_image task_tcb64_image] in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Lemma task_del_req_merge_updated_field : forall sg s tid old,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |-> 63 **
    task_del_req_field_frame sg s tid old |-- UCOS2_inv sg (task_del_req_state s tid old).
Proof.
  intros sg s tid old Hvalid Hold.
  unfold task_del_req_field_frame.
  pose proof (task_public_storage_merge_updated_field sg s.(TskState) tid old
    (task_set_delete_request old true) (TCBCommonField TCBDelReq) (Some 63)
    (tcb_configured_common_field_in _ _ _) (task_set_delete_request_layout_image_eq sg old true)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell] in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite (task_del_req_frame_update_eq sg s tid old Hold).
  unfold UCOS2_inv; rewrite task_del_req_raw_split.
  pose proof (task_del_req_preserves_invariant sg s tid old Hvalid Hold); entailer!.
Qed.

Lemma task_del_req_split_self : forall sg s tid t,
  task_del_req_current s tid t -> UCOS2_raw_rep sg s |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |->
    encode_task_delete_request t.(delReq) ** task_del_req_self_frame sg s tid t.
Proof.
  intros sg s tid t [Hcurrent Hlookup].
  sep_apply_l_atomic (task_del_req_split_field sg s tid t Hlookup).
  unfold task_del_req_field_frame, task_del_req_frame, sched_raw_rep, sched_physical_rep,
    task_del_req_self_frame, task_del_req_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.

Lemma task_del_req_merge_self : forall sg s tid t,
  UCOS2_state_inv sg s -> task_del_req_current s tid t ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |->
    encode_task_delete_request t.(delReq) ** task_del_req_self_frame sg s tid t |-- UCOS2_inv sg s.
Proof.
  intros sg s tid t Hvalid [Hcurrent Hlookup].
  assert (Hfold : sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |->
      encode_task_delete_request t.(delReq) ** task_del_req_self_frame sg s tid t |--
    tcb_field_address (task_slot_addr sg tid) TCBDelReq # UChar |->
      encode_task_delete_request t.(delReq) ** task_del_req_field_frame sg s tid t).
  { unfold task_del_req_field_frame, task_del_req_frame, sched_raw_rep, sched_physical_rep,
      task_del_req_self_frame, task_del_req_sched_without_current.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!. }
  sep_apply_l_atomic Hfold.
  sep_apply_l_atomic (task_del_req_merge_field sg s tid t Hlookup).
  unfold UCOS2_inv; entailer!.
Qed.

Lemma task_del_req_split_table : forall sg s prio,
  0 <= prio < 63 -> UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s) &&
  ((sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |-> task_del_req_table_entry sg s prio **
   task_del_req_table_frame sg s prio).
Proof.
  intros; unfold task_del_req_table_entry, task_del_req_table_frame.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg s prio ltac:(lia)); entailer!.
Qed.

Lemma task_del_req_merge_table : forall sg s prio,
  0 <= prio < 63 -> UCOS2_state_inv sg s ->
  (sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |-> task_del_req_table_entry sg s prio **
    task_del_req_table_frame sg s prio |-- UCOS2_inv sg s.
Proof.
  intros sg s prio Hprio Hvalid.
  unfold task_del_req_table_entry, task_del_req_table_frame.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg s.(TskState).(prioTbl) prio ltac:(lia)).
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.

Lemma task_del_req_table_task : forall sg s prio tid,
  UCOS2_state_inv sg s -> 0 <= prio < 63 -> s.(TskState).(prioTbl) prio = PTTask tid ->
  exists t, s.(TskState).(inUsedTaskStates) tid = Some t.
Proof.
  intros sg s prio tid Hvalid Hprio Hentry.
  destruct Hvalid as [Hprofile [_ [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Htable _]] _].
  assert (Hrange : task_priority_in_range sg prio).
  { destruct Hprofile as [Hsg _]; unfold valid_stable_glob_vars in Hsg.
    unfold task_priority_in_range; intuition lia. }
  specialize (Htable prio Hrange); rewrite Hentry in Htable; exact Htable.
Qed.

Lemma task_del_req_task_pointer : forall sg s tid t,
  UCOS2_state_inv sg s -> 1 < sg.(g_OSTCBTbl) ->
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  1 < task_slot_addr sg tid.
Proof.
  intros sg s tid t Hvalid Hbase Hget.
  destruct Hvalid as [_ [[Hpool _] _]].
  assert (Hslot : task_slot_in_range sg tid).
  { apply (proj2 (proj1 Hpool tid)); left; exists t; exact Hget. }
  unfold task_slot_in_range in Hslot.
  unfold task_slot_addr, tcb_configured_size, tcb_layout_size.
  destruct (cfgEventMultiEnabled (osKernelConfig sg)), (cfgTaskProfile (osKernelConfig sg)); lia.
Qed.

Lemma task_del_req_table_classify : forall sg s prio table current,
  UCOS2_state_inv sg s -> task_del_req_addresses sg table current -> 0 <= prio < 63 ->
  (task_del_req_table_entry sg s prio = 0 /\ s.(TskState).(prioTbl) prio = PTFree) \/
  (task_del_req_table_entry sg s prio = 1 /\ s.(TskState).(prioTbl) prio = PTReserved) \/
  (exists tid t, s.(TskState).(prioTbl) prio = PTTask tid /\
    s.(TskState).(inUsedTaskStates) tid = Some t /\
    task_del_req_table_entry sg s prio = task_slot_addr sg tid /\
    1 < task_slot_addr sg tid).
Proof.
  intros sg s prio table current Hvalid Haddresses Hprio.
  pose proof (task_del_req_addresses_base sg table current Haddresses) as Hbase.
  unfold task_del_req_table_entry; destruct (prioTbl (TskState s) prio) eqn:Hentry.
  - left; split; reflexivity.
  - right; left; split; reflexivity.
  - right; right; destruct (task_del_req_table_task sg s prio tid Hvalid Hprio Hentry) as [t Hget].
    exists tid, t; repeat split; try reflexivity; try assumption.
    eapply task_del_req_task_pointer; eassumption.
Qed.

Lemma task_del_req_step_total : forall sg prio s,
  UCOS2_state_inv sg s -> 0 <= prio <= 255 ->
  (prio = 255 -> exists tid t, task_del_req_current s tid t) ->
  exists result after, task_del_req_step prio s result after.
Proof.
  intros sg prio s Hvalid Hprio Hself.
  destruct (Z.eq_dec prio 63) as [->|Hidle].
  - exists 62, s; constructor; reflexivity.
  - destruct (Z.eq_dec prio 255) as [->|Hother].
    + destruct (Hself eq_refl) as [tid [t Hcurrent]].
      exists (encode_task_delete_request t.(delReq)), s; econstructor; eauto.
    + destruct (Z_lt_dec prio 63) as [Hlow|Hhigh].
      * destruct (prioTbl (TskState s) prio) eqn:Hentry.
        -- exists 67, s; apply TaskDelReqFree; [lia|assumption].
        -- exists 61, s; apply TaskDelReqReserved; [lia|assumption].
        -- destruct (task_del_req_table_task sg s prio tid Hvalid ltac:(lia) Hentry) as [t Hget].
           exists 0, (task_del_req_state s tid t); apply TaskDelReqSet; auto; lia.
      * exists 42, s; apply TaskDelReqInvalid; lia.
Qed.

Lemma task_del_req_generic_restore_consequence : forall platform critical sg invocation origin saved released,
  task_del_req_closed platform critical sg invocation origin (armv7a_irq_fiq_mask saved) released |--
  EX current, coq_prop (critical_region_interval critical sg invocation released current) &&
    task_del_req_closed platform critical sg invocation origin (armv7a_irq_fiq_mask saved) current.
Proof. intros; Exists released; entailer!; constructor. Qed.

Lemma task_del_req_protected_program_step : forall prio before result after,
  (prio = 255 \/ 0 <= prio < 63) ->
  task_del_req_protected_program prio before result after ->
  task_del_req_step prio before result after.
Proof.
  intros prio before result after Hdomain Hprogram.
  unfold task_del_req_protected_program in Hprogram.
  destruct (Z.eqb prio 255) eqn:Eself.
  - apply Z.eqb_eq in Eself.
    destruct Hprogram as [t [mid [[[tid Hcurrent] Hmid] [Hresult Hafter]]]].
    subst mid result after; eapply TaskDelReqSelf; eassumption.
  - apply Z.eqb_neq in Eself.
    assert (Hrange : 0 <= prio < 63) by (destruct Hdomain; lia).
    destruct Hprogram as [slot [mid [[Hslot Hmid] Hprogram]]].
    subst slot mid; destruct (prioTbl (TskState before) prio) eqn:Hslot.
    + destruct Hprogram as [Hresult Hafter]; subst result after.
      apply TaskDelReqFree; assumption.
    + destruct Hprogram as [Hresult Hafter]; subst result after.
      apply TaskDelReqReserved; assumption.
    + destruct Hprogram as [t [mid [[Hlookup Hmid] [u [written [Hwrite [Hresult Hafter]]]]]]].
      change (written = task_del_req_state mid tid t) in Hwrite.
      subst mid written result after; eapply TaskDelReqSet; eassumption.
Qed.

Lemma task_del_req_program_result : forall critical sg invocation prio before result current,
  0 <= prio <= 255 ->
  task_del_req_program critical sg invocation prio before result current ->
  task_del_req_result critical sg invocation prio before result current.
Proof.
  intros critical sg invocation prio before result current Hrange Hprogram.
  unfold task_del_req_program in Hprogram.
  destruct (Z.eqb prio 63) eqn:Eidle.
  - apply Z.eqb_eq in Eidle.
    destruct Hprogram as [Hresult Hcurrent]; subst result current.
    left; split; [left; assumption|split; [apply TaskDelReqIdle; assumption|reflexivity]].
  - apply Z.eqb_neq in Eidle.
    destruct (andb (Z.leb 63 prio) (negb (Z.eqb prio 255))) eqn:Einvalid.
    + apply Bool.andb_true_iff in Einvalid; destruct Einvalid as [Hlower Hself].
      apply Z.leb_le in Hlower; apply Bool.negb_true_iff in Hself; apply Z.eqb_neq in Hself.
      destruct Hprogram as [Hresult Hcurrent]; subst result current.
      left; split; [right; lia|split; [apply TaskDelReqInvalid; lia|reflexivity]].
    + assert (Hdomain : prio = 255 \/ 0 <= prio < 63).
      { apply Bool.andb_false_iff in Einvalid.
        destruct Einvalid as [Hlower|Hself].
        - apply Z.leb_gt in Hlower; right; lia.
        - apply Bool.negb_false_iff in Hself; apply Z.eqb_eq in Hself; left; assumption. }
      destruct Hprogram as [u [acquired [Hacquire [code [released [Hprotected
        [v [returned [Hrelease [Hresult Hcurrent]]]]]]]]]].
      subst code returned; right; split; [exact Hdomain|].
      exists acquired, released; split; [exact Hacquire|].
      split; [eapply task_del_req_protected_program_step; eassumption|exact Hrelease].
Qed.

Lemma task_del_req_program_result_iff : forall critical sg invocation prio before result current,
  0 <= prio <= 255 ->
  (task_del_req_program critical sg invocation prio before result current <->
   task_del_req_result critical sg invocation prio before result current).
Proof.
  intros; split; [apply task_del_req_program_result; assumption|apply task_del_req_result_program].
Qed.

Lemma task_del_req_program_has_result : forall critical sg invocation prio before,
  UCOS2_state_inv sg before -> 0 <= prio <= 255 ->
  task_del_req_admission critical sg invocation prio before ->
  exists result current, task_del_req_program critical sg invocation prio before result current.
Proof.
  intros critical sg invocation prio before Hvalid Hrange Hadmit.
  destruct (task_del_req_step_total sg prio before Hvalid Hrange) as [result [after Hstep]].
  { intro Hself; apply (Hadmit Hself before); constructor. }
  exists result, after; apply task_del_req_result_program.
  destruct Hstep.
  - left; split; [left; assumption|split; [apply TaskDelReqIdle; assumption|reflexivity]].
  - left; split; [right; assumption|split; [apply TaskDelReqInvalid; assumption|reflexivity]].
  - right; split; [left; assumption|].
    exists before, before; split; [constructor|].
    split; [eapply TaskDelReqSelf; eassumption|constructor].
  - right; split; [right; assumption|].
    exists before, before; split; [constructor|].
    split; [apply TaskDelReqFree; assumption|constructor].
  - right; split; [right; assumption|].
    exists before, before; split; [constructor|].
    split; [apply TaskDelReqReserved; assumption|constructor].
  - right; split; [right; assumption|].
    exists before, (task_del_req_state before tid t); split; [constructor|].
    split; [eapply TaskDelReqSet; eassumption|constructor].
Qed.
