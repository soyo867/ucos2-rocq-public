Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Logic.FunctionalExtensionality String.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.task Ucos2Verify.lib.task_storage Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.array_abstraction Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.lib.event Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.cross_module_invariants Ucos2Verify.lib.mutex.
Require Export Ucos2Verify.lib.kernel_names Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.interrupt.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Exact pointer store: no string byte, task identity, scheduling or lifetime
    field changes. The separate Name owner supplies the published string. *)
Definition task_set_name (t : TaskAbstractState) (name : addr) : TaskAbstractState :=
  {| taskID := t.(taskID); taskGeneration := t.(taskGeneration);
     tcbStkPtr := t.(tcbStkPtr); tcbExtPtr := t.(tcbExtPtr);
     tcbStkBottom := t.(tcbStkBottom); tcbStkSize := t.(tcbStkSize);
     tcbOpt := t.(tcbOpt); tcbPublicId := t.(tcbPublicId);
     tcbFlagNode := t.(tcbFlagNode); tcbFlagsRdy := t.(tcbFlagsRdy);
     tcbTaskName := name; tcbReg0 := t.(tcbReg0);
     tcbCtxSwCtr := t.(tcbCtxSwCtr); tcbCyclesTot := t.(tcbCyclesTot);
     tcbCyclesStart := t.(tcbCyclesStart); tcbStkBase := t.(tcbStkBase);
     tcbStkUsed := t.(tcbStkUsed);
     tcbPadding42 := t.(tcbPadding42); tcbPadding43 := t.(tcbPadding43);
     tcbEventMultiPtr := t.(tcbEventMultiPtr);
     curPrio := t.(curPrio); stat := t.(stat); statPend := t.(statPend);
     dly := t.(dly); eventPtr := t.(eventPtr);
     eventMultiWaitEvents := t.(eventMultiWaitEvents); eventMultiRdy := t.(eventMultiRdy);
     msg := t.(msg); nextTCB := t.(nextTCB); prevTCB := t.(prevTCB); delReq := t.(delReq) |}.

Lemma task_set_name_same : forall t, task_set_name t t.(tcbTaskName) = t.
Proof. intros []; reflexivity. Qed.
Lemma task_set_name_last : forall t first last,
  task_set_name (task_set_name t first) last = task_set_name t last.
Proof. reflexivity. Qed.
Lemma task_set_name_layout_image_eq : forall sg t name,
  task_layout_image sg (task_set_name t name) =
  tcb_layout_write (task_layout_image sg t) (TCBCommonField TCBTaskName) (Some name).
Proof.
  intros; apply functional_extensionality; intros [field| | | | | | |];
    [destruct field| | | | | | |]; reflexivity.
Qed.

Definition task_name_set_update (s : UCOS2_Verify_State) tid t name :=
  replace_TskS (glob_task_set_usedtask s.(TskState) tid (task_set_name t name)) s.
Definition task_name_set_current (s : UCOS2_Verify_State) tid t : Prop :=
  s.(SchedState).(curTaskID) = Some tid /\ s.(TskState).(inUsedTaskStates) tid = Some t.
Definition task_name_set_target (s : UCOS2_Verify_State) prio tid t : Prop :=
  s.(TskState).(prioTbl) prio = PTTask tid /\ s.(TskState).(inUsedTaskStates) tid = Some t.
Definition task_name_set_resolved request (s : UCOS2_Verify_State) prio : Prop :=
  (request <> 255 /\ prio = request) \/
  (request = 255 /\ exists tid t, task_name_set_current s tid t /\ prio = t.(curPrio)).
Definition task_name_set_valid_priority (p : Z) : Prop := 0 <= p <= 63 \/ p = 255.
Definition task_name_set_nesting (s : UCOS2_Verify_State) := s.(IntrState).(intNesting).
Definition task_name_set_table_entry sg s prio :=
  prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) prio).

(** Conditional memory-safety/lifetime protocol, not a runtime branch. Early
    errors require neither a live current task nor new name bytes. Save does
    not itself establish SELF access. Only a real selected live publication
    consumes readable_name; failed acquired lookups impose no such demand. *)
Definition task_name_set_admission (critical : CriticalRegionResources)
  sg invocation request name before : Prop :=
  task_name_set_valid_priority request -> name <> 0 ->
  task_name_set_nesting before = 0 ->
  forall acquired, critical_region_interval critical sg invocation before acquired ->
    (request = 255 -> exists tid t, task_name_set_current acquired tid t) /\
    (forall prio tid t, task_name_set_resolved request acquired prio ->
      task_name_set_target acquired prio tid t ->
      exists chars, readable_name acquired.(NameState) name chars).

Inductive task_name_set_step (prio name : Z) (s : UCOS2_Verify_State)
  : Z -> UCOS2_Verify_State -> Prop :=
| TaskNameSetFree : s.(TskState).(prioTbl) prio = PTFree ->
    task_name_set_step prio name s 67 s
| TaskNameSetReserved : s.(TskState).(prioTbl) prio = PTReserved ->
    task_name_set_step prio name s 67 s
| TaskNameSetStore : forall tid t, task_name_set_target s prio tid t ->
    task_name_set_step prio name s 0 (task_name_set_update s tid t name).

Definition task_name_set_result critical sg invocation request name before err current : Prop :=
  (64 <= request < 255 /\ err = 42 /\ current = before) \/
  (task_name_set_valid_priority request /\ name = 0 /\ err = 12 /\ current = before) \/
  (task_name_set_valid_priority request /\ name <> 0 /\
    0 < task_name_set_nesting before /\ err = 18 /\ current = before) \/
  (task_name_set_valid_priority request /\ name <> 0 /\
    task_name_set_nesting before = 0 /\ exists acquired prio released,
      critical_region_interval critical sg invocation before acquired /\
      task_name_set_resolved request acquired prio /\
      task_name_set_step prio name acquired err released /\
      critical_region_interval critical sg invocation released current).

(** SELF resolves the acquired current priority before the protected table
    lookup. The existing step records NULL/reserved errors or exactly the
    name-pointer write; it does not include either environment interval. *)
Definition task_name_set_protected_program (request name : Z)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind (get (fun s prio => task_name_set_resolved request s prio))
    (fun prio => task_name_set_step prio name).

(** The result observes the private error byte of this void C API. Argument
    errors precede the nesting read, and only the remaining path enters the
    critical region. No string bytes are copied by this operation. *)
Definition task_name_set_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (request name : Z)
  : program UCOS2_Verify_State Z :=
  if andb (Z.ltb 63 request) (negb (Z.eqb request 255)) then StateRelMonad.ret 42
  else if Z.eqb name 0 then StateRelMonad.ret 12
  else StateRelMonad.bind (get' task_name_set_nesting)
    (fun nesting => if Z.ltb 0 nesting then StateRelMonad.ret 18
      else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.bind (task_name_set_protected_program request name)
          (fun err => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
            (fun _ => StateRelMonad.ret err)))).

Definition task_name_set_safe critical sg invocation request name before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (task_name_set_program critical sg invocation request name) X.

Definition task_name_set_post critical sg invocation request name before err current
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  task_name_set_result critical sg invocation request name before err current /\
  safeExec (eq current) (StateRelMonad.ret err) X.

Lemma task_name_set_result_program : forall critical sg invocation request name before err current,
  task_name_set_result critical sg invocation request name before err current ->
  task_name_set_program critical sg invocation request name before err current.
Proof.
  intros critical sg invocation request name before err current Hresult.
  unfold task_name_set_result in Hresult.
  destruct Hresult as [[Hrange [-> ->]]|[[Hvalid [-> [-> ->]]]|[Hresult|Hresult]]].
  - unfold task_name_set_program.
    assert (Ebound : Z.ltb 63 request = true) by (apply Z.ltb_lt; lia).
    assert (Eself : Z.eqb request 255 = false) by (apply Z.eqb_neq; lia).
    rewrite Ebound, Eself; split; reflexivity.
  - unfold task_name_set_program.
    assert (Einvalid : andb (Z.ltb 63 request) (negb (Z.eqb request 255)) = false).
    { destruct Hvalid as [Hrange | ->]; [|reflexivity].
      assert (E : Z.ltb 63 request = false) by (apply Z.ltb_ge; lia).
      rewrite E; reflexivity. }
    rewrite Einvalid; split; reflexivity.
  - destruct Hresult as [Hvalid [Hname [Hnest [-> ->]]]].
    unfold task_name_set_program.
    assert (Einvalid : andb (Z.ltb 63 request) (negb (Z.eqb request 255)) = false).
    { destruct Hvalid as [Hrange | ->]; [|reflexivity].
      assert (E : Z.ltb 63 request = false) by (apply Z.ltb_ge; lia).
      rewrite E; reflexivity. }
    assert (Ename : Z.eqb name 0 = false) by (apply Z.eqb_neq; exact Hname).
    rewrite Einvalid, Ename.
    exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    assert (Enest : Z.ltb 0 (task_name_set_nesting before) = true) by (apply Z.ltb_lt; exact Hnest).
    rewrite Enest; split; reflexivity.
  - destruct Hresult as [Hvalid [Hname [Hnest [acquired [prio [released
      [Hacquire [Hresolved [Hstep Hrelease]]]]]]]]].
    unfold task_name_set_program.
    assert (Einvalid : andb (Z.ltb 63 request) (negb (Z.eqb request 255)) = false).
    { destruct Hvalid as [Hrange | ->]; [|reflexivity].
      assert (E : Z.ltb 63 request = false) by (apply Z.ltb_ge; lia).
      rewrite E; reflexivity. }
    assert (Ename : Z.eqb name 0 = false) by (apply Z.eqb_neq; exact Hname).
    rewrite Einvalid, Ename.
    exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    rewrite Hnest; cbn.
    exists tt, acquired; split; [exact Hacquire|].
    exists err, released; split.
    + exists prio, acquired; split; [split; [exact Hresolved|reflexivity]|exact Hstep].
    + exists tt, current; split; [exact Hrelease|split; reflexivity].
Qed.

Lemma task_name_set_safe_return : forall critical sg invocation request name before err current X,
  task_name_set_result critical sg invocation request name before err current ->
  task_name_set_safe critical sg invocation request name before X ->
  task_name_set_post critical sg invocation request name before err current X.
Proof.
  intros critical sg invocation request name before err current X Hresult Hsafe.
  split; [exact Hresult|].
  eapply (highstependret_derive (task_name_set_program critical sg invocation request name)
    (eq before) err (fun _ => eq current)).
  - intros state Hstate; subst state; exists current; split; [|reflexivity].
    apply task_name_set_result_program; exact Hresult.
  - exact Hsafe.
Qed.

Definition task_name_set_addresses (sg : StableGlobVars) table current nesting : Prop :=
  table = sg.(g_OSTCBPrioTbl) /\ current = sg.(g_OSTCBCur) /\
  nesting = sg.(g_OSIntNesting) /\ 1 < sg.(g_OSTCBTbl).
Definition task_name_set_layout (sg : StableGlobVars) : Prop :=
  forall tid, let base := task_slot_addr sg tid in
    tcb_field_address base TCBPrio = &(base # "os_tcb" ->ₛ "OSTCBPrio") /\
    tcb_field_address base TCBTaskName = &(base # "os_tcb" ->ₛ "OSTCBTaskName").
Lemma task_name_set_layout_holds : forall sg, task_name_set_layout sg.
Proof. intros sg tid; split; reflexivity. Qed.
Definition task_name_set_closed platform critical sg invocation origin mask s : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  critical_region_outside critical sg invocation s.
Definition task_name_set_observation_frame sg s : Assertion :=
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  UCOS2_raw_rep_missing_interrupt sg s.
Definition task_name_set_restore_post platform critical sg invocation origin saved released : Assertion :=
  EX current,
    coq_prop (critical_region_interval critical sg invocation released current /\
      UCOS2_state_inv sg current) &&
    task_name_set_closed platform critical sg invocation origin
      (armv7a_irq_fiq_mask saved) current.
Definition task_name_set_context critical sg invocation request name mask saved before acquired : Prop :=
  task_name_set_valid_priority request /\ name <> 0 /\ task_name_set_nesting before = 0 /\
  task_name_set_admission critical sg invocation request name before /\
  critical_region_interval critical sg invocation before acquired /\
  interrupt_saved_value mask saved /\ UCOS2_state_inv sg acquired.

Lemma task_name_set_observation_split : forall critical sg invocation s,
  critical_region_outside critical sg invocation s |--
  coq_prop (0 <= task_name_set_nesting s <= 255) &&
  (sg.(g_OSIntNesting) # UChar |-> task_name_set_nesting s **
   task_name_set_observation_frame sg s).
Proof.
  intros; unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module sg s InterruptModule).
  cbn [UCOS2_module_rep].
  unfold task_name_set_observation_frame, task_name_set_nesting,
    interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  Intros.
  prop_apply_p (store_uchar_range sg.(g_OSIntNesting) s.(IntrState).(intNesting)).
  entailer!.
Qed.
Lemma task_name_set_observation_merge : forall critical sg invocation s,
  sg.(g_OSIntNesting) # UChar |-> task_name_set_nesting s **
  task_name_set_observation_frame sg s |--
  critical_region_outside critical sg invocation s.
Proof.
  intros; unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module sg s InterruptModule).
  cbn [UCOS2_module_rep].
  unfold task_name_set_observation_frame,
    task_name_set_nesting, interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  entailer!.
Qed.

Lemma task_name_set_restore_immediate_consequence :
  forall platform critical sg invocation origin saved released,
  UCOS2_state_inv sg released ->
  task_name_set_closed platform critical sg invocation origin
    (armv7a_irq_fiq_mask saved) released |--
  task_name_set_restore_post platform critical sg invocation origin saved released.
Proof.
  intros; unfold task_name_set_restore_post; Exists released.
  assert (critical_region_interval critical sg invocation released released) by constructor.
  entailer!.
Qed.

Lemma task_name_set_priority_observation : forall tasks tid old name slot,
  tasks.(inUsedTaskStates) tid = Some old ->
  option_map curPrio ((glob_task_set_usedtask tasks tid (task_set_name old name)).(inUsedTaskStates) slot) =
  option_map curPrio (tasks.(inUsedTaskStates) slot).
Proof. intros; eapply glob_task_set_usedtask_observation; [eassumption|reflexivity]. Qed.
Lemma task_name_set_preserves_ready : forall sg tasks sched tid old name,
  tasks.(inUsedTaskStates) tid = Some old -> sched_ready_in_range sg tasks sched ->
  sched_ready_in_range sg (glob_task_set_usedtask tasks tid (task_set_name old name)) sched.
Proof.
  intros sg tasks sched tid old name Hold [Hmembers [Hsorted [Hcomplete Hnodup]]].
  split.
  - intros slot Hin; destruct (Hmembers slot Hin) as [t [Ht [Hp Hr]]].
    cbn [glob_task_set_usedtask inUsedTaskStates]; destruct (Z.eqb slot tid) eqn:E.
    + apply Z.eqb_eq in E; subst slot; assert (t = old) by congruence; subst t.
      exists (task_set_name old name); auto.
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
Lemma task_name_set_preserves_cross_module : forall sg s tid old name,
  s.(TskState).(inUsedTaskStates) tid = Some old -> cross_module_consistency sg s ->
  cross_module_consistency sg (task_name_set_update s tid old name).
Proof.
  intros sg s tid old name Hold [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  split; [eapply task_mutex_priotbl_consistency_update_task; eauto; reflexivity|].
  split; [eapply mutex_owner_snapshot_update_task; eauto|].
  split.
  - eapply event_wait_object_update_task; try eassumption; try reflexivity.
    intros kind Hphase; exact Hphase.
  - split; [exact Hprotocol|]. split; [exact Hunique|]. split; [|exact Htimer].
    eapply task_flag_waiter_consistency_update_task; try eassumption; try reflexivity;
      intros H; exact H.
Qed.
Lemma task_name_set_new_roots : forall sg s tid old name p,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  kernel_name_root sg (task_name_set_update s tid old name) p ->
  kernel_name_root sg s p \/ p = name.
Proof.
  intros sg s tid old name p Hold Hroot.
  destruct Hroot as [[Henabled [slot [t [Ht Hp]]]]|Hother].
  - change ((if Z.eqb slot tid then Some (task_set_name old name)
      else s.(TskState).(inUsedTaskStates) slot) = Some t) in Ht.
    destruct (Z.eqb slot tid) eqn:E.
    + inversion Ht; subst t; right; exact Hp.
    + left; left; split; [exact Henabled|exists slot, t; auto].
  - left; right; exact Hother.
Qed.
Lemma task_name_set_preserves_invariant : forall sg s tid old name chars,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  readable_name s.(NameState) name chars ->
  UCOS2_state_inv sg (task_name_set_update s tid old name).
Proof.
  intros sg s tid old name chars
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus Hmodules]]]]]]] Hold Hread.
  destruct Hmodules as [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]].
  assert (HreferencesAfter : kernel_names_valid sg (task_name_set_update s tid old name)).
  { eapply kernel_names_valid_add_root; [exact Hreferences|exact Hread|reflexivity|].
    intros; eapply task_name_set_new_roots; eassumption. }
  assert (HstacksAfter : parked_stacks_consistent
    (task_name_set_update s tid old name).(TskState) s.(TskState).(parkedTaskStacks)).
  { eapply parked_stacks_consistent_update_task;
      [exact Hold|reflexivity|reflexivity|reflexivity|exact Hstacks]. }
  split; [exact Hprofile|]. split.
  - eapply task_update_preserves_in_range; try eassumption; reflexivity.
  - split.
    + destruct Hsched as [Hready Hmetadata]; split; [|exact Hmetadata].
      eapply task_name_set_preserves_ready; eassumption.
    + split.
      * eapply event_update_task_preserves_in_range; try eassumption; try reflexivity.
        intros kind Hphase; exact Hphase.
      * split; [apply task_name_set_preserves_cross_module; assumption|]. split.
        -- intro Hrunning; eapply task_update_preserves_idle_tail;
             [exact Hold|reflexivity|apply Hidle; exact Hrunning].
        -- split.
           ++ apply task_reserved_bits_clear_update_task;
                [exact Hstatus|exact (Hstatus tid old Hold)].
           ++ split; [exact Hflags|]. split; [exact Hmemory|]. split; [exact Htimer|].
              split; [exact Hstats|]. split; [exact Hcontrol|]. split; [exact Hnames|].
              split; [exact HreferencesAfter|]. split; [exact HstacksAfter|exact Hpending].
Qed.

Definition task_name_set_frame sg s : Assertion :=
  sched_raw_rep sg s.(TskState) s.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg s.
Lemma task_name_set_raw_split : forall sg s,
  UCOS2_raw_rep sg s --||-- task_public_storage sg s.(TskState) ** task_name_set_frame sg s.
Proof.
  intros; unfold UCOS2_raw_rep, task_shared_rep, task_name_set_frame,
    UCOS2_raw_rep_missing_task_storage_sched; split; entailer!.
Qed.
Lemma task_name_set_frame_update_eq : forall sg s tid old name,
  s.(TskState).(inUsedTaskStates) tid = Some old ->
  task_name_set_frame sg s = task_name_set_frame sg (task_name_set_update s tid old name).
Proof.
  intros sg s tid old name Hold.
  assert (Hprio : forall slot, option_map curPrio (s.(TskState).(inUsedTaskStates) slot) =
    option_map curPrio ((task_name_set_update s tid old name).(TskState).(inUsedTaskStates) slot)).
  { intros; symmetry; apply task_name_set_priority_observation; exact Hold. }
  assert (Hencoded : forall ids,
    encode_ready_grp ids s.(TskState) = encode_ready_grp ids (task_name_set_update s tid old name).(TskState) /\
    forall y, encode_ready_tbl_at_or ids s.(TskState) y =
      encode_ready_tbl_at_or ids (task_name_set_update s tid old name).(TskState) y).
  { intro ids; apply event_wait_encoding_priority_ext; intros; apply Hprio. }
  unfold task_name_set_frame, sched_raw_rep, UCOS2_raw_rep_missing_task_storage_sched.
  cbn [task_name_set_update replace_TskS SchedState IntrState EventState TickState FlagState
    MemoryState TimerState StatsState ControlState NameState TskState glob_task_set_usedtask parkedTaskStacks].
  rewrite (event_raw_rep_change_task_index sg s.(TskState)
    (glob_task_set_usedtask s.(TskState) tid (task_set_name old name)) s.(EventState)).
  2: { apply event_wait_priority_agreement_encodes; intros eid e slot He Hin; apply Hprio. }
  destruct (Hencoded s.(SchedState).(readyList)) as [Hgrp Hrows].
  rewrite Hgrp; cbn [sched_rows_rep]; rewrite !Hrows; reflexivity.
Qed.
Definition task_name_set_field_frame sg s tid t : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid t (TCBCommonField TCBTaskName) **
  task_name_set_frame sg s.
Lemma task_name_set_split_field : forall sg s tid t,
  s.(TskState).(inUsedTaskStates) tid = Some t -> UCOS2_raw_rep sg s |--
  tcb_field_address (task_slot_addr sg tid) TCBTaskName # Ptr |-> t.(tcbTaskName) **
  task_name_set_field_frame sg s tid t.
Proof.
  intros sg s tid t Hlookup; rewrite task_name_set_raw_split.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid t
    (TCBCommonField TCBTaskName) Hlookup (tcb_configured_common_field_in _ _ _)).
  unfold task_name_set_field_frame; entailer!.
Qed.
Lemma task_name_set_merge_updated_field : forall sg s tid old name chars,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some old ->
  readable_name s.(NameState) name chars ->
  tcb_field_address (task_slot_addr sg tid) TCBTaskName # Ptr |-> name **
    task_name_set_field_frame sg s tid old |-- UCOS2_inv sg (task_name_set_update s tid old name).
Proof.
  intros sg s tid old name chars Hvalid Hold Hread.
  unfold task_name_set_field_frame.
  pose proof (task_public_storage_merge_updated_field sg s.(TskState) tid old
    (task_set_name old name) (TCBCommonField TCBTaskName) (Some name)
    (tcb_configured_common_field_in _ _ _) (task_set_name_layout_image_eq sg old name)) as Hmerge.
  cbn [tcb_layout_cell tcb_cell] in Hmerge.
  sep_apply_l_atomic Hmerge.
  rewrite (task_name_set_frame_update_eq sg s tid old name Hold).
  unfold UCOS2_inv; rewrite task_name_set_raw_split.
  pose proof (task_name_set_preserves_invariant sg s tid old name chars Hvalid Hold Hread); entailer!.
Qed.

Definition task_name_set_table_frame sg s prio : Assertion :=
  store_prio_tbl_missing_i sg s.(TskState).(prioTbl) prio **
  UCOS2_raw_rep_missing_priority_table sg s.
Lemma task_name_set_split_table : forall sg s prio,
  0 <= prio <= 63 -> UCOS2_inv sg s |--
  coq_prop (UCOS2_state_inv sg s) &&
  ((sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |-> task_name_set_table_entry sg s prio **
   task_name_set_table_frame sg s prio).
Proof.
  intros; unfold task_name_set_table_entry, task_name_set_table_frame.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg s prio ltac:(lia)); entailer!.
Qed.
Lemma task_name_set_merge_table : forall sg s prio,
  0 <= prio <= 63 -> UCOS2_state_inv sg s ->
  (sg.(g_OSTCBPrioTbl) + prio * sizeof(PTR)) # Ptr |-> task_name_set_table_entry sg s prio **
    task_name_set_table_frame sg s prio |-- UCOS2_inv sg s.
Proof.
  intros sg s prio Hprio Hvalid.
  unfold task_name_set_table_entry, task_name_set_table_frame.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg s.(TskState).(prioTbl) prio ltac:(lia)).
  unfold UCOS2_inv; rewrite UCOS2_raw_rep_priority_table_equiv; entailer!.
Qed.
Lemma task_name_set_table_task : forall sg s prio tid,
  UCOS2_state_inv sg s -> 0 <= prio <= 63 -> s.(TskState).(prioTbl) prio = PTTask tid ->
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

Definition task_name_set_sched_without_current sg s : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(SchedState).(readyList) s.(TskState) **
  sched_rows_rep sg s.(TskState) s.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0).
Definition task_name_set_self_frame sg s tid t : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid t (TCBCommonField TCBPrio) **
  task_name_set_sched_without_current sg s ** UCOS2_raw_rep_missing_task_storage_sched sg s.
Definition task_name_set_priority_frame sg s tid t : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid t (TCBCommonField TCBPrio) **
  task_name_set_frame sg s.
Lemma task_name_set_split_self : forall sg s tid t,
  task_name_set_current s tid t -> UCOS2_raw_rep sg s |--
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> t.(curPrio) **
  task_name_set_self_frame sg s tid t.
Proof.
  intros sg s tid t [Hcurrent Hlookup]; rewrite task_name_set_raw_split.
  sep_apply_l_atomic (task_public_storage_split_field sg s.(TskState) tid t
    (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ _)).
  unfold task_name_set_frame, sched_raw_rep, sched_physical_rep,
    task_name_set_self_frame, task_name_set_sched_without_current.
  rewrite Hcurrent; cbn [encode_task_link]; entailer!.
Qed.
Lemma task_name_set_merge_self : forall sg s tid t,
  UCOS2_state_inv sg s -> task_name_set_current s tid t ->
  sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
  tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> t.(curPrio) **
  task_name_set_self_frame sg s tid t |-- UCOS2_inv sg s.
Proof.
  intros sg s tid t Hvalid [Hcurrent Hlookup].
  assert (Hfold :
    sg.(g_OSTCBCur) # Ptr |-> task_slot_addr sg tid **
    tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> t.(curPrio) **
    task_name_set_self_frame sg s tid t |--
    tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> t.(curPrio) **
    task_name_set_priority_frame sg s tid t).
  { unfold task_name_set_priority_frame, task_name_set_frame, sched_raw_rep,
      sched_physical_rep, task_name_set_self_frame, task_name_set_sched_without_current.
    rewrite Hcurrent; cbn [encode_task_link]; entailer!. }
  sep_apply_l_atomic Hfold.
  unfold task_name_set_priority_frame.
  assert (Hmerge :
    tcb_field_address (task_slot_addr sg tid) TCBPrio # UChar |-> t.(curPrio) **
    task_public_storage_without_field sg s.(TskState) tid t (TCBCommonField TCBPrio) |--
    task_public_storage sg s.(TskState)).
  { apply (task_public_storage_merge_field sg s.(TskState) tid t
      (TCBCommonField TCBPrio) Hlookup (tcb_configured_common_field_in _ _ _)). }
  sep_apply_l_atomic Hmerge.
  unfold UCOS2_inv; rewrite task_name_set_raw_split; entailer!.
Qed.
Lemma task_name_set_task_pointer : forall sg s tid t,
  UCOS2_state_inv sg s -> 1 < sg.(g_OSTCBTbl) ->
  s.(TskState).(inUsedTaskStates) tid = Some t -> 1 < task_slot_addr sg tid.
Proof.
  intros sg s tid t Hvalid Hbase Hget; destruct Hvalid as [_ [[Hpool _] _]].
  assert (Hslot : task_slot_in_range sg tid).
  { apply (proj2 (proj1 Hpool tid)); left; exists t; exact Hget. }
  unfold task_slot_in_range in Hslot.
  unfold task_slot_addr, tcb_configured_size, tcb_layout_size.
  destruct (cfgEventMultiEnabled (osKernelConfig sg)), (cfgTaskProfile (osKernelConfig sg)); lia.
Qed.
Lemma task_name_set_table_classify : forall sg s prio table current nesting,
  UCOS2_state_inv sg s -> task_name_set_addresses sg table current nesting -> 0 <= prio <= 63 ->
  (task_name_set_table_entry sg s prio = 0 /\ s.(TskState).(prioTbl) prio = PTFree) \/
  (task_name_set_table_entry sg s prio = 1 /\ s.(TskState).(prioTbl) prio = PTReserved) \/
  (exists tid t, task_name_set_target s prio tid t /\
    task_name_set_table_entry sg s prio = task_slot_addr sg tid /\ 1 < task_slot_addr sg tid).
Proof.
  intros sg s prio table current nesting Hvalid [_ [_ [_ Hbase]]] Hprio.
  unfold task_name_set_table_entry; destruct (prioTbl (TskState s) prio) eqn:Hentry.
  - left; split; reflexivity.
  - right; left; split; reflexivity.
  - right; right; destruct (task_name_set_table_task sg s prio tid Hvalid Hprio Hentry) as [t Hget].
    exists tid, t; split; [split; assumption|]. split; [reflexivity|].
    eapply task_name_set_task_pointer; eassumption.
Qed.

Lemma task_name_set_admission_early_error : forall critical sg invocation request name before,
  (~ task_name_set_valid_priority request \/ name = 0 \/ task_name_set_nesting before <> 0) ->
  task_name_set_admission critical sg invocation request name before.
Proof. unfold task_name_set_admission; intros; tauto. Qed.
Lemma task_name_set_admission_from_name_source : forall critical sg invocation request name before chars,
  readable_name before.(NameState) name chars ->
  (request = 255 -> forall acquired,
    critical_region_interval critical sg invocation before acquired ->
    exists tid t, task_name_set_current acquired tid t) ->
  task_name_set_admission critical sg invocation request name before.
Proof.
  unfold task_name_set_admission; intros critical sg invocation request name before chars
    Hname Hcurrent Hprio Hnonnull Hnest acquired Hinterval.
  split; [intros; apply Hcurrent; assumption|].
  intros; exists chars.
  rewrite <- (critical_region_interval_preserves_name_state critical sg invocation before acquired Hinterval).
  exact Hname.
Qed.
Lemma task_name_set_step_total : forall sg s prio name,
  UCOS2_state_inv sg s -> 0 <= prio <= 63 ->
  exists err released, task_name_set_step prio name s err released.
Proof.
  intros sg s prio name Hvalid Hprio; destruct (s.(TskState).(prioTbl) prio) eqn:Hentry.
  - exists 67, s; constructor; exact Hentry.
  - exists 67, s; apply TaskNameSetReserved; exact Hentry.
  - destruct (task_name_set_table_task sg s prio tid Hvalid Hprio Hentry) as [t Ht].
    exists 0, (task_name_set_update s tid t name); constructor; split; assumption.
Qed.
Lemma task_name_set_update_frame : forall s tid t name,
  let after := task_name_set_update s tid t name in
  after.(TskState).(prioTbl) = s.(TskState).(prioTbl) /\
  after.(TskState).(taskLifecycle) = s.(TskState).(taskLifecycle) /\
  after.(TskState).(parkedTaskStacks) = s.(TskState).(parkedTaskStacks) /\
  after.(SchedState) = s.(SchedState) /\ after.(IntrState) = s.(IntrState) /\
  after.(EventState) = s.(EventState) /\ after.(TickState) = s.(TickState) /\
  after.(FlagState) = s.(FlagState) /\ after.(MemoryState) = s.(MemoryState) /\
  after.(TimerState) = s.(TimerState) /\ after.(StatsState) = s.(StatsState) /\
  after.(ControlState) = s.(ControlState) /\ after.(NameState) = s.(NameState).
Proof. intros; repeat split; reflexivity. Qed.

Lemma task_name_set_used_priority_in_range__g01_protected_name_store :
  forall sg s tid t,
  UCOS2_state_inv sg s ->
  s.(TskState).(inUsedTaskStates) tid = Some t ->
  0 <= t.(curPrio) <= 63.
Proof.
  intros sg s tid t [Hprofile [Htasks Hrest]] Hlookup.
  destruct Hprofile as [Hsg Hprofile].
  destruct Htasks as [_ [_ [_ [_ [_ [_ [_ [Hpriority _]]]]]]]].
  specialize (Hpriority tid t Hlookup).
  unfold task_priority_in_range in Hpriority.
  unfold valid_stable_glob_vars in Hsg; intuition lia.
Qed.
