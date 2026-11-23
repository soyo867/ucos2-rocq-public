Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import SumLib.ZRange.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.task_stack.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.VC.code.core.spec.os_strlen_spec.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules TaskStateDef SchedStateDef.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Original V2.93.01 NameGet: the observation before Save, the acquired
    lookup and the state resumed by Restore are deliberately distinct.
    None of the operation's successful or failed branches writes kernel
    storage. A returned pointer is a value, not a surviving byte loan. *)
Definition task_name_get_early_error (prio pname nesting : Z) : option Z :=
  if (Z.ltb 63 prio && negb (Z.eqb prio 255))%bool then Some 42
  else if Z.eqb pname 0 then Some 12
  else if Z.ltb 0 nesting then Some 17
  else None.

Definition task_name_get_nesting (s : UCOS2_Verify_State) : Z := s.(IntrState).(intNesting).

Definition task_name_get_output_cell (pname : Z) (old : option Z) : Assertion :=
  match old with None => emp | Some previous => pname # Ptr |-> previous end.

Definition task_name_get_closed (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (s : UCOS2_Verify_State) : Assertion :=
  interrupt_platform_running platform invocation origin mask **
  critical_region_outside critical sg invocation s.

(** The caller's private TCBs are separate from the public kernel owner.
    They are needed only by a reached SELF read; the existing creation-frame
    theorem transports their original image across acquisition. *)
Definition task_name_get_private (sg : StableGlobVars) (invocation : nat)
  (prio : Z) (s : UCOS2_Verify_State) : Assertion :=
  if Z.eqb prio 255 then task_private_storage sg s.(TskState) invocation else emp.

Definition task_name_get_guarded_private (sg : StableGlobVars) (invocation : nat)
  (request pname : Z) (s : UCOS2_Verify_State) : Assertion :=
  match task_name_get_early_error request pname (task_name_get_nesting s) with
  | Some _ => emp
  | None => task_name_get_private sg invocation request s
  end.

Inductive TaskNameGetCurrentView : Type :=
| TaskNameGetLive (tid : TaskID) (node : TaskAbstractState)
| TaskNameGetFree (tid : TaskID) (image : TCBLayoutImage)
    (prefix suffix : list TaskID)
| TaskNameGetPrivate (priority : Priority) (entry : TaskCreationEntry)
    (allocation : TaskPrivateAllocation).

Definition task_name_get_current_slot (view : TaskNameGetCurrentView) : TaskID :=
  match view with
  | TaskNameGetLive tid _ | TaskNameGetFree tid _ _ _ => tid
  | TaskNameGetPrivate _ _ allocation => allocation.(privateSlot)
  end.

Definition task_name_get_current_image (sg : StableGlobVars)
  (view : TaskNameGetCurrentView) : TCBLayoutImage :=
  match view with
  | TaskNameGetLive _ node => task_layout_image sg node
  | TaskNameGetFree _ image _ _ => image
  | TaskNameGetPrivate _ _ allocation => allocation.(privateStorage)
  end.

Definition task_name_get_current_view (sg : StableGlobVars) (invocation : nat)
  (s : UCOS2_Verify_State) (view : TaskNameGetCurrentView) (priority : Z) : Prop :=
  s.(SchedState).(curTaskID) = Some (task_name_get_current_slot view) /\
  task_name_get_current_image sg view (TCBCommonField TCBPrio) = Some priority /\
  0 <= priority <= 63 /\
  match view with
  | TaskNameGetLive tid node => s.(TskState).(inUsedTaskStates) tid = Some node
  | TaskNameGetFree tid image prefix suffix =>
      s.(TskState).(unUsedTaskStates) = prefix ++ tid :: suffix /\
      s.(TskState).(taskLifecycle).(taskFreeStorage) tid = Some image
  | TaskNameGetPrivate p entry allocation =>
      s.(TskState).(taskLifecycle).(taskReservations) p = Some entry /\
      entry.(creationInvocation) = invocation /\ entry.(creationAllocation) = Some allocation
  end.

Definition task_name_get_resolved (sg : StableGlobVars) (invocation : nat)
  (s : UCOS2_Verify_State) (request priority : Z) : Prop :=
  if Z.eqb request 255 then
    exists view, task_name_get_current_view sg invocation s view priority
  else priority = request /\ 0 <= request <= 63.

Definition task_name_get_lookup (sg : StableGlobVars) (invocation : nat)
  (s : UCOS2_Verify_State) (request priority pointer : Z) : Prop :=
  task_name_get_resolved sg invocation s request priority /\
  pointer = prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) priority).

(** NULL is covered by the actual StrLen source contract; in a globally
    valid Task-root state the separate name invariant normally rules it out. *)
Definition task_name_get_readable (names : NameResourceState)
  (name : Z) (chars : list Z) : Prop :=
  name <> 0 -> readable_name names name chars.

Definition task_name_get_success (sg : StableGlobVars) (invocation : nat)
  (s : UCOS2_Verify_State) (request priority pointer name : Z)
  (chars : list Z) : Prop :=
  task_name_get_lookup sg invocation s request priority pointer /\
  exists tid node,
    s.(TskState).(prioTbl) priority = PTTask tid /\
    s.(TskState).(inUsedTaskStates) tid = Some node /\
    pointer = task_slot_addr sg tid /\ pointer <> 0 /\ pointer <> 1 /\
    name = node.(tcbTaskName) /\ task_name_get_readable s.(NameState) name chars.

Definition task_name_get_length (name : Z) (chars : list Z) : Z :=
  if Z.eqb name 0 then 0 else name_length_result chars.

(** Memory-safety protocol is guarded by the actually reached C accesses.
    It requires an initialized current-priority cell only for SELF, permits
    public-free and this invocation's private images, and does not require
    the subsequent table entry to contain a live task. The optional caller
    output cell is required only when an acquired lookup can succeed. *)
Definition task_name_get_access (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (request pname : Z) (old : option Z) : Prop :=
  task_name_get_early_error request pname (task_name_get_nesting before) = None ->
  forall acquired,
    critical_region_interval critical sg invocation before acquired ->
    UCOS2_state_inv sg acquired ->
    (exists priority, task_name_get_resolved sg invocation acquired request priority) /\
    (forall priority pointer,
      task_name_get_lookup sg invocation acquired request priority pointer ->
      pointer <> 0 -> pointer <> 1 -> exists value, old = Some value).

Definition task_name_get_pre (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (request pname perr : Z) (old : option Z) : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\ 0 <= request < 256 /\
    task_name_get_access critical sg invocation before request pname old) &&
  (task_name_get_closed platform critical sg invocation origin mask before **
   perr # UChar |->_ ** task_name_get_output_cell pname old **
   match task_name_get_early_error request pname (task_name_get_nesting before) with
   | Some _ => emp
   | None => task_name_get_private sg invocation request before
   end).

Definition task_name_get_effect (sg : StableGlobVars) (invocation : nat)
  (observed acquired : UCOS2_Verify_State) (request pname result error : Z)
  (output : option Z) : Prop :=
  match task_name_get_early_error request pname (task_name_get_nesting observed) with
  | Some code => acquired = observed /\ result = 0 /\ error = code /\ output = None
  | None =>
      (exists priority pointer,
        task_name_get_lookup sg invocation acquired request priority pointer /\
        (pointer = 0 \/ pointer = 1) /\ result = 0 /\ error = 67 /\ output = None) \/
      (exists priority pointer name chars,
        task_name_get_success sg invocation acquired request priority pointer name chars /\
        result = task_name_get_length name chars /\ error = 0 /\ output = Some name)
  end.

(** The observation includes every caller-visible output. [None] means that
    the caller's old name cell is preserved, not that its ownership is lost.
    X sees this observation and the complete kernel state; the spatial post
    below additionally returns the original invocation and private resources. *)
Record TaskNameGetObservation : Type := task_name_get_observation {
  task_name_get_observed_length : Z;
  task_name_get_observed_error : Z;
  task_name_get_observed_output : option Z
}.

Definition task_name_get_strlen_program (name : Z)
  : program UCOS2_Verify_State Z :=
  StateRelMonad.bind
    (get (fun state chars => task_name_get_readable state.(NameState) name chars))
    (fun chars => StateRelMonad.ret (task_name_get_length name chars)).

Definition task_name_get_protected_program (sg : StableGlobVars)
  (invocation : nat) (request : Z)
  : program UCOS2_Verify_State TaskNameGetObservation :=
  StateRelMonad.bind (get (fun state priority =>
    task_name_get_resolved sg invocation state request priority))
    (fun priority => StateRelMonad.bind (get' (fun state =>
      prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) priority)))
      (fun pointer =>
        if ((pointer =? 0) || (pointer =? 1))%bool
        then StateRelMonad.ret (task_name_get_observation 0 67 None)
        else StateRelMonad.bind (get (fun state node => exists tid,
          state.(TskState).(prioTbl) priority = PTTask tid /\
          state.(TskState).(inUsedTaskStates) tid = Some node))
          (fun node => StateRelMonad.bind (task_name_get_strlen_program node.(tcbTaskName))
            (fun length => StateRelMonad.ret
              (task_name_get_observation length 0 (Some node.(tcbTaskName))))))).

(** Save and Restore contribute separate, source-backed environment intervals.
    Protected lookup and the real StrLen observation do not mutate kernel state.
    Early errors return at the entry state without either interval. *)
Definition task_name_get_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (request pname : Z)
  : program UCOS2_Verify_State TaskNameGetObservation :=
  StateRelMonad.bind (get' task_name_get_nesting) (fun nesting =>
    match task_name_get_early_error request pname nesting with
    | Some code => StateRelMonad.ret (task_name_get_observation 0 code None)
    | None => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.bind (task_name_get_protected_program sg invocation request)
          (fun observed => StateRelMonad.bind
            (update (critical_region_interval critical sg invocation))
            (fun _ => StateRelMonad.ret observed)))
    end).

Definition task_name_get_safe critical sg invocation request pname before
  (X : TaskNameGetObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_name_get_program critical sg invocation request pname) X.

Definition task_name_get_return_safe current result error output
  (X : TaskNameGetObservation -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = current)
    (StateRelMonad.ret (task_name_get_observation result error output)) X.

Lemma task_name_get_effect_program : forall critical sg invocation request pname
  before acquired current result error output,
  task_name_get_effect sg invocation before acquired request pname result error output ->
  critical_region_interval critical sg invocation before acquired ->
  critical_region_interval critical sg invocation acquired current ->
  (task_name_get_early_error request pname (task_name_get_nesting before) <> None ->
    current = before) ->
  task_name_get_program critical sg invocation request pname before
    (task_name_get_observation result error output) current.
Proof.
  intros critical sg invocation request pname before acquired current result error output
    Heffect Hacquire Hrelease Hearly_current.
  unfold task_name_get_program.
  exists (task_name_get_nesting before), before; split; [split; reflexivity|].
  unfold task_name_get_effect in Heffect.
  destruct (task_name_get_early_error request pname (task_name_get_nesting before))
    as [code|] eqn:Hearly.
  - destruct Heffect as [-> [-> [-> ->]]].
    specialize (Hearly_current ltac:(discriminate)); subst current; split; reflexivity.
  - exists tt, acquired; split; [exact Hacquire|].
    exists (task_name_get_observation result error output), acquired; split.
    + unfold task_name_get_protected_program.
      destruct Heffect as [[priority [pointer [Hlookup [Hbad [-> [-> ->]]]]]]|
        [priority [pointer [name [chars [Hsuccess [-> [-> ->]]]]]]]].
      * destruct Hlookup as [Hresolved Hpointer].
        exists priority, acquired; split; [split; [exact Hresolved|reflexivity]|].
        exists pointer, acquired; split; [split; [exact Hpointer|reflexivity]|].
        assert (Hbadb : ((pointer =? 0) || (pointer =? 1))%bool = true).
        { apply Bool.orb_true_iff; destruct Hbad as [-> | ->]; auto. }
        rewrite Hbadb; split; reflexivity.
      * destruct Hsuccess as [[Hresolved Hpointer]
          [tid [node [Htable [Hnode [Haddr [Hnull [Hreserved [Hname Hread]]]]]]]]].
        exists priority, acquired; split; [split; [exact Hresolved|reflexivity]|].
        exists pointer, acquired; split; [split; [exact Hpointer|reflexivity]|].
        rewrite (proj2 (Z.eqb_neq pointer 0) Hnull),
          (proj2 (Z.eqb_neq pointer 1) Hreserved); cbn.
        exists node, acquired; split; [split; [exists tid; auto|reflexivity]|].
        exists (task_name_get_length name chars), acquired; split.
        -- unfold task_name_get_strlen_program; exists chars, acquired.
           split; [split; [rewrite <- Hname; exact Hread|reflexivity]|].
           rewrite Hname; split; reflexivity.
        -- rewrite Hname; split; reflexivity.
    + exists tt, current; split; [exact Hrelease|split; reflexivity].
Qed.

Lemma task_name_get_safe_return : forall critical sg invocation request pname
  before acquired current result error output X,
  task_name_get_effect sg invocation before acquired request pname result error output ->
  critical_region_interval critical sg invocation before acquired ->
  critical_region_interval critical sg invocation acquired current ->
  (task_name_get_early_error request pname (task_name_get_nesting before) <> None ->
    current = before) ->
  task_name_get_safe critical sg invocation request pname before X ->
  task_name_get_return_safe current result error output X.
Proof.
  intros critical sg invocation request pname before acquired current result error output X
    Heffect Hacquire Hrelease Hearly Hsafe.
  eapply (highstependret_derive
    (task_name_get_program critical sg invocation request pname)
    (fun state => state = before) (task_name_get_observation result error output)
    (fun _ state => state = current)).
  - intros state ->; exists current; split; [|reflexivity].
    eapply task_name_get_effect_program; eassumption.
  - exact Hsafe.
Qed.

Definition task_name_get_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (released : UCOS2_Verify_State) : Assertion :=
  EX current,
    coq_prop (critical_region_interval critical sg invocation released current /\
      UCOS2_state_inv sg current) &&
    task_name_get_closed platform critical sg invocation origin
      (armv7a_irq_fiq_mask saved) current.

Definition task_name_get_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (before : UCOS2_Verify_State)
  (request pname perr : Z) (old : option Z) (result : Z)
  (X : TaskNameGetObservation -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX acquired current error output,
    coq_prop (task_name_get_effect sg invocation before acquired request pname result error output /\
      critical_region_interval critical sg invocation before acquired /\
      critical_region_interval critical sg invocation acquired current /\
      UCOS2_state_inv sg current /\ task_name_get_return_safe current result error output X) &&
    (task_name_get_closed platform critical sg invocation origin mask current **
     perr # UChar |-> error **
     task_name_get_output_cell pname
       (match output with None => old | Some name => Some name end) **
     match task_name_get_early_error request pname (task_name_get_nesting before) with
     | Some _ => emp
     | None => task_name_get_private sg invocation request before
     end).

(** Structural residuals retain the original owners. They describe a field
    read, never a Task update or a permanent name-reader lease. *)
Definition task_name_get_nesting_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  interrupt_inv_no_int_nesting sg s.(IntrState) **
  UCOS2_raw_rep_missing_interrupt sg s.

Definition task_name_get_sched_without_current (sg : StableGlobVars)
  (s : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp s.(SchedState).(readyList) s.(TskState) **
  sched_rows_rep sg s.(TskState) s.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte s.(SchedState).(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte s.(SchedState).(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg s.(SchedState).(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> s.(SchedState).(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if s.(SchedState).(isRunning) then 1 else 0).

Definition task_name_get_public_without_free (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) : Assertion :=
  store_used_task_map sg tasks.(inUsedTaskStates) **
  sg.(g_OSTCBFreeList) # Ptr |-> encode_task_link sg (hd_error tasks.(unUsedTaskStates)) **
  sg.(g_OSTCBList) # Ptr |-> encode_task_link sg tasks.(tcbListHead) **
  sg.(g_OSTaskCtr) # UChar |-> tasks.(taskCount) **
  store_prio_tbl sg tasks.(prioTbl) ** task_reg_allocator_rep sg tasks.

Definition task_name_get_current_residual (sg : StableGlobVars) (invocation : nat)
  (s : UCOS2_Verify_State) (view : TaskNameGetCurrentView) : Assertion :=
  (match view with
   | TaskNameGetLive tid node =>
       task_public_storage_without_field sg s.(TskState) tid node (TCBCommonField TCBPrio) **
       task_private_storage sg s.(TskState) invocation
   | TaskNameGetFree tid image prefix suffix =>
       tcb_configured_storage_without_field sg.(osKernelConfig).(cfgEventMultiEnabled)
         sg.(osKernelConfig).(cfgTaskProfile) (task_slot_addr sg tid) image (TCBCommonField TCBPrio) **
       task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage) prefix **
       task_free_storage_rep sg s.(TskState).(taskLifecycle).(taskFreeStorage) suffix **
       task_name_get_public_without_free sg s.(TskState) **
       task_private_storage sg s.(TskState) invocation
   | TaskNameGetPrivate p entry allocation =>
       task_public_storage sg s.(TskState) **
       task_private_storage_without_field sg s.(TskState) invocation p allocation (TCBCommonField TCBPrio)
   end) **
   store_parked_stacks s.(TskState).(parkedTaskStacks) **
   task_name_get_sched_without_current sg s ** UCOS2_raw_rep_missing_task_sched sg s.

Definition task_name_get_table_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (priority : Z) : Assertion :=
  PtrArray.missing_i sg.(g_OSTCBPrioTbl) priority 0 64
    (map (fun p => prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) p)) (Zrange 0 64)) **
  task_public_storage_without_prio_tbl sg s.(TskState) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) ** UCOS2_raw_rep_missing_task sg s.

Definition task_name_get_name_field_residual (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (tid : TaskID) (node : TaskAbstractState) : Assertion :=
  task_public_storage_without_field sg s.(TskState) tid node (TCBCommonField TCBTaskName) **
  store_parked_stacks s.(TskState).(parkedTaskStacks) ** UCOS2_raw_rep_missing_task sg s.

Definition task_name_get_remove_byte (bytes : addr -> option Z) (p : addr)
  : addr -> option Z := fun q => if Z.eqb q p then None else bytes q.

Fixpoint task_name_get_remove_bytes (bytes : addr -> option Z) (p : addr)
  (count : nat) : addr -> option Z :=
  match count with
  | O => bytes
  | S rest => task_name_get_remove_bytes (task_name_get_remove_byte bytes p) (p + 1) rest
  end.

Definition task_name_get_name_residual (names : NameResourceState)
  (p : addr) (chars : list Z) : Assertion :=
  store_map name_byte_rep
    (task_name_get_remove_bytes names.(nameBytes) p (S (List.length chars))).

Definition task_name_get_name_bytes (p : addr) (chars : list Z) : Assertion :=
  if Z.eqb p 0 then emp else os_strlen_bytes p chars.

Definition task_name_get_name_frame (sg : StableGlobVars)
  (s : UCOS2_Verify_State) (p : addr) (chars : list Z) : Assertion :=
  (if Z.eqb p 0 then store_name_bytes s.(NameState)
   else task_name_get_name_residual s.(NameState) p chars) **
  UCOS2_raw_rep_missing_module sg s NamesModule.

Definition task_name_get_call_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (saved : Z) (before acquired : UCOS2_Verify_State)
  (request perr name : Z) (chars : list Z) : Assertion :=
  task_name_get_name_frame sg acquired name chars **
  task_name_get_private sg invocation request before **
  critical_region_masked platform critical sg invocation origin saved acquired **
  perr # UChar |->_ .

Definition task_name_get_addresses (sg : StableGlobVars)
  (nesting current table : Z) : Prop :=
  sg.(g_OSIntNesting) = nesting /\ sg.(g_OSTCBCur) = current /\ sg.(g_OSTCBPrioTbl) = table /\
  1 < sg.(g_OSTCBTbl).

Definition task_name_get_table_value (sg : StableGlobVars) (s : UCOS2_Verify_State)
  (priority : Z) : Z := prio_tbl_entry_to_addr sg (s.(TskState).(prioTbl) priority).

Definition task_name_get_current_pointer (sg : StableGlobVars)
  (view : TaskNameGetCurrentView) : Z := task_slot_addr sg (task_name_get_current_slot view).

Definition task_name_get_name (node : TaskAbstractState) : Z := node.(tcbTaskName).

Definition task_name_get_target (s : UCOS2_Verify_State) (priority : Z)
  (tid : TaskID) (node : TaskAbstractState) : Prop :=
  s.(TskState).(prioTbl) priority = PTTask tid /\ s.(TskState).(inUsedTaskStates) tid = Some node.

Definition task_name_get_names (s : UCOS2_Verify_State) : NameResourceState := s.(NameState).

Lemma task_name_get_length_in_range : forall name chars,
  0 <= task_name_get_length name chars < 256.
Proof.
  intros; unfold task_name_get_length; destruct (Z.eqb name 0); [lia|apply name_length_result_in_range].
Qed.

Lemma task_name_get_task_root_readable : forall sg s tid node,
  UCOS2_state_inv sg s -> s.(TskState).(inUsedTaskStates) tid = Some node ->
  exists chars, readable_name s.(NameState) node.(tcbTaskName) chars.
Proof.
  intros sg s tid node Hvalid Hnode.
  assert (Hnames : kernel_names_valid sg s).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Henabled : sg.(osKernelConfig).(cfgTaskNames) = true).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, selected_kernel_profile,
      tcb64_configuration in Hvalid; tauto. }
  apply Hnames; left; split; [exact Henabled|].
  exists tid, node; auto.
Qed.

Lemma task_name_get_private_acquired_eq : forall critical sg invocation request before acquired,
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before acquired ->
  task_name_get_private sg invocation request acquired =
    task_name_get_private sg invocation request before.
Proof.
  intros; unfold task_name_get_private; destruct (Z.eqb request 255); [|reflexivity].
  apply task_creation_frame_private_storage.
  exact (proj1 (proj2 (critical_region_interval_transports_resources critical sg invocation before acquired H0 H))).
Qed.

Lemma uchar_unsigned32_eq__critical_control : forall value,
  0 <= value < 256 -> unsigned_last_nbits value 32 = value.
Proof.
  intros value Hrange; unfold unsigned_last_nbits.
  apply Z.mod_small; change (0 <= value < 4294967296); lia.
Qed.
Lemma task_name_get_early_error_none__critical_control : forall request pname nesting,
  (request = 255 \/ 0 <= request <= 63) -> pname <> 0 -> nesting = 0 ->
  task_name_get_early_error request pname nesting = None.
Proof.
  intros request pname nesting Hrequest Hpname ->.
  assert (Hpriority : ((63 <? request) && negb (request =? 255))%bool = false).
  { destruct Hrequest as [->|Hrange]; [reflexivity|].
    apply Bool.andb_false_iff; left; apply Z.ltb_ge; lia. }
  assert (Hp : (pname =? 0) = false) by (apply Z.eqb_neq; exact Hpname).
  unfold task_name_get_early_error; rewrite Hpriority, Hp; reflexivity.
Qed.
Lemma task_name_get_closed_nesting_in_range__critical_control :
  forall platform critical sg invocation origin mask s,
  task_name_get_closed platform critical sg invocation origin mask s |--
  coq_prop (0 <= task_name_get_nesting s < 256) &&
  task_name_get_closed platform critical sg invocation origin mask s.
Proof.
  intros; unfold task_name_get_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite <- UCOS2_raw_rep_split_running.
  rewrite (UCOS2_raw_rep_split_module sg s InterruptModule).
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, store_int_state, task_name_get_nesting.
  unfold store_uchar.
  entailer!.
  change Byte.max_unsigned with 255 in *; lia.
Qed.
Lemma task_name_get_resolved_in_range__task_lookup_fields :
  forall sg invocation s request priority,
  task_name_get_resolved sg invocation s request priority ->
  0 <= priority < 64.
Proof.
  intros sg invocation s request priority Hresolved.
  unfold task_name_get_resolved in Hresolved.
  destruct (Z.eqb request 255).
  - destruct Hresolved as [view [_ [_ [Hrange _]]]]; lia.
  - destruct Hresolved as [-> Hrange]; lia.
Qed.
Lemma task_free_storage_focus_equiv__task_lookup_fields :
  forall sg storage prefix tid suffix image,
  storage tid = Some image ->
  task_free_storage_rep sg storage (prefix ++ tid :: suffix) --||--
    task_slot_storage_rep sg tid image **
    task_free_storage_rep sg storage prefix **
    task_free_storage_rep sg storage suffix.
Proof.
  intros sg storage prefix tid suffix image Himage.
  induction prefix as [|head prefix IH].
  - simpl; split.
    + Intros observed.
      assert (observed = image) by congruence; subst observed; entailer!.
    + Exists image; entailer!.
  - simpl; rewrite IH; split; Intros observed; Exists observed; entailer!.
Qed.
Lemma task_name_get_current_fields_equiv__task_lookup_fields :
  forall sg invocation s view priority,
  task_name_get_current_view sg invocation s view priority ->
  UCOS2_raw_rep sg s ** task_private_storage sg s.(TskState) invocation --||--
    sg.(g_OSTCBCur) # Ptr |-> task_name_get_current_pointer sg view **
    tcb_cell (task_name_get_current_pointer sg view) TCBPrio (Some priority) **
    task_name_get_current_residual sg invocation s view.
Proof.
  intros sg invocation s view priority Hview.
  destruct Hview as [Hcurrent [Himage [Hrange Hstorage]]].
  rewrite (UCOS2_raw_rep_split_two sg s TaskModule SchedModule) by discriminate.
  cbn [UCOS2_module_rep].
  unfold task_shared_rep, sched_raw_rep, sched_physical_rep.
  rewrite Hcurrent; cbn [encode_task_link].
  destruct view as [tid node|tid image prefix suffix|p entry allocation];
    unfold task_name_get_current_pointer, task_name_get_current_slot,
      task_name_get_current_image, task_name_get_current_residual in *;
    cbn beta iota in *;
    unfold tcb_cell, tcb_field_address; cbn beta iota;
    unfold task_name_get_sched_without_current.
  - pose proof (task_public_storage_split_field sg s.(TskState) tid node
      (TCBCommonField TCBPrio) Hstorage
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hsplit.
    pose proof (task_public_storage_merge_field sg s.(TskState) tid node
      (TCBCommonField TCBPrio) Hstorage
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hmerge.
    rewrite Himage in Hsplit, Hmerge.
    cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hsplit, Hmerge.
    assert (Hfields : task_public_storage sg s.(TskState) --||--
      tcb_cell (task_slot_addr sg tid) TCBPrio (Some priority) **
      task_public_storage_without_field sg s.(TskState) tid node (TCBCommonField TCBPrio)).
    { split; assumption. }
    rewrite Hfields; unfold tcb_cell, tcb_field_address; cbn beta iota.
    split; entailer!.
  - destruct Hstorage as [Hlist Hstorage].
    unfold task_public_storage, task_name_get_public_without_free.
    rewrite Hlist.
    rewrite (task_free_storage_focus_equiv__task_lookup_fields
      sg _ prefix tid suffix image Hstorage).
    pose proof (tcb_configured_storage_split_field
      sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg tid) image (TCBCommonField TCBPrio)
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hsplit.
    pose proof (tcb_configured_storage_merge_field
      sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg tid) image (TCBCommonField TCBPrio)
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hmerge.
    rewrite Himage in Hsplit, Hmerge.
    cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hsplit, Hmerge.
    unfold task_slot_storage_rep.
    assert (Hfields : tcb_configured_storage_rep
      sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
      (task_slot_addr sg tid) image --||--
      tcb_cell (task_slot_addr sg tid) TCBPrio (Some priority) **
      tcb_configured_storage_without_field
        sg.(osKernelConfig).(cfgEventMultiEnabled) sg.(osKernelConfig).(cfgTaskProfile)
        (task_slot_addr sg tid) image (TCBCommonField TCBPrio)).
    { split; assumption. }
    rewrite Hfields; unfold tcb_cell, tcb_field_address; cbn beta iota.
    split; entailer!.
  - destruct Hstorage as [Hentry [Hinvocation Hallocation]].
    pose proof (task_private_storage_split_field sg s.(TskState) p entry allocation
      invocation (TCBCommonField TCBPrio) Hentry Hinvocation Hallocation
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hsplit.
    pose proof (task_private_storage_merge_field sg s.(TskState) p entry allocation
      invocation (TCBCommonField TCBPrio) Hentry Hinvocation Hallocation
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hmerge.
    rewrite Himage in Hsplit, Hmerge.
    cbn [tcb_layout_cell tcb_cell tcb_field_address] in Hsplit, Hmerge.
    assert (Hfields : task_private_storage sg s.(TskState) invocation --||--
      tcb_cell (task_slot_addr sg allocation.(privateSlot)) TCBPrio (Some priority) **
      task_private_storage_without_field sg s.(TskState) invocation p allocation
        (TCBCommonField TCBPrio)).
    { split; assumption. }
    rewrite Hfields; unfold tcb_cell, tcb_field_address; cbn beta iota.
    split; entailer!.
Qed.
Lemma task_name_get_table_cell_equiv__task_lookup_fields : forall sg s priority,
  0 <= priority < 64 ->
  UCOS2_raw_rep sg s --||--
    (sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
      task_name_get_table_value sg s priority **
    task_name_get_table_residual sg s priority.
Proof.
  intros sg s priority Hpriority.
  rewrite (UCOS2_raw_rep_split_module sg s TaskModule).
  cbn [UCOS2_module_rep].
  unfold task_shared_rep, task_name_get_table_residual, task_name_get_table_value.
  rewrite (task_public_storage_prio_tbl_equiv sg s.(TskState)).
  pose proof (array_abstraction.store_prio_tbl_split_cell
    sg s.(TskState).(prioTbl) priority Hpriority) as Hsplit.
  pose proof (array_abstraction.store_prio_tbl_merge_cell
    sg s.(TskState).(prioTbl) priority Hpriority) as Hmerge.
  unfold array_abstraction.store_prio_tbl_missing_i in Hsplit, Hmerge.
  split; [sep_apply_l_atomic Hsplit|sep_apply_l_atomic Hmerge]; entailer!.
Qed.
Lemma task_name_get_name_field_equiv__task_lookup_fields : forall sg s tid node,
  s.(TskState).(inUsedTaskStates) tid = Some node ->
  UCOS2_raw_rep sg s --||--
    tcb_cell (task_slot_addr sg tid) TCBTaskName (Some (task_name_get_name node)) **
    task_name_get_name_field_residual sg s tid node.
Proof.
  intros sg s tid node Hnode.
  rewrite (UCOS2_raw_rep_split_module sg s TaskModule).
  cbn [UCOS2_module_rep].
  unfold task_shared_rep, task_name_get_name_field_residual, task_name_get_name.
  pose proof (task_public_storage_split_field sg s.(TskState) tid node
    (TCBCommonField TCBTaskName) Hnode
    (tcb_configured_common_field_in _ _ TCBTaskName)) as Hsplit.
  pose proof (task_public_storage_merge_field sg s.(TskState) tid node
    (TCBCommonField TCBTaskName) Hnode
    (tcb_configured_common_field_in _ _ TCBTaskName)) as Hmerge.
  cbn [task_layout_image tcb_layout_image task_tcb64_image
    tcb_layout_cell tcb_cell tcb_field_address] in Hsplit, Hmerge.
  split; [sep_apply_l_atomic Hsplit|sep_apply_l_atomic Hmerge]; entailer!.
Qed.
Lemma task_name_get_lookup_task__task_lookup_fields :
  forall sg invocation s request priority pointer,
  UCOS2_state_inv sg s ->
  task_name_get_lookup sg invocation s request priority pointer ->
  pointer <> 0 -> pointer <> 1 ->
  exists tid node, task_name_get_target s priority tid node /\
    pointer = task_slot_addr sg tid.
Proof.
  intros sg invocation s request priority pointer Hvalid
    [Hresolved Hpointer] Hnull Hreserved.
  pose proof (task_name_get_resolved_in_range__task_lookup_fields
    sg invocation s request priority Hresolved) as Hpriority.
  assert (Hlowest : sg.(osLowestPrio) = 63).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      selected_kernel_profile, valid_stable_glob_vars in Hvalid; tauto. }
  assert (Htable : cross_module_invariants.task_mutex_priotbl_consistency
    sg s.(TskState) s.(EventState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      cross_module_invariants.cross_module_consistency in Hvalid; tauto. }
  destruct Htable as [_ [Htable _]].
  specialize (Htable priority ltac:(unfold task_priority_in_range; lia)).
  destruct (s.(TskState).(prioTbl) priority) as [| |tid] eqn:Hentry;
    cbn [prio_tbl_entry_to_addr] in Hpointer; try contradiction.
  destruct Htable as [node Hnode].
  exists tid, node; unfold task_name_get_target; auto.
Qed.
Lemma task_name_get_closed_raw_rep__resource_stages_strlen :
  forall platform critical sg invocation origin mask s,
  task_name_get_closed platform critical sg invocation origin mask s --||--
  interrupt_platform_running platform invocation origin mask ** UCOS2_raw_rep sg s.
Proof.
  intros; unfold task_name_get_closed, critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite UCOS2_raw_rep_split_running.
  split; entailer!.
Qed.
Lemma task_name_get_raw_rep_split_nesting__resource_stages_strlen : forall sg s,
  UCOS2_raw_rep sg s --||--
  sg.(g_OSIntNesting) # UChar |-> task_name_get_nesting s **
  task_name_get_nesting_frame sg s.
Proof.
  intros; rewrite (UCOS2_raw_rep_split_module sg s InterruptModule).
  cbn [UCOS2_module_rep].
  unfold task_name_get_nesting_frame, task_name_get_nesting,
    interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  split; entailer!.
Qed.
Lemma store_uchar_with_range__resource_stages_strlen : forall p value,
  p # UChar |-> value |--
  coq_prop (0 <= value < 256) && p # UChar |-> value.
Proof.
  intros; unfold store_uchar; entailer!.
  change compcert.lib.Integers.Byte.max_unsigned with 255 in *; lia.
Qed.
Lemma task_name_get_missing_byte_eq__resource_stages_strlen : forall bytes p,
  store_map_missing_i name_byte_rep bytes p --||--
  store_map name_byte_rep (task_name_get_remove_byte bytes p).
Proof.
  intros bytes p.
  assert (Houtside : forall q, q <> p -> bytes q = task_name_get_remove_byte bytes p q).
  { intros q Hq; unfold task_name_get_remove_byte.
    rewrite (proj2 (Z.eqb_neq q p) Hq); reflexivity. }
  assert (Hnone : task_name_get_remove_byte bytes p p = None).
  { unfold task_name_get_remove_byte; rewrite Z.eqb_refl; reflexivity. }
  split.
  - rewrite (store_map_missing_i_equiv name_byte_rep bytes
      (task_name_get_remove_byte bytes p) p Houtside).
    apply store_map_missing_equiv_store_map; exact Hnone.
  - rewrite (store_map_missing_i_equiv name_byte_rep bytes
      (task_name_get_remove_byte bytes p) p Houtside).
    apply store_map_equiv_store_map_missing; exact Hnone.
Qed.
Lemma task_name_get_byte_split__resource_stages_strlen : forall bytes p value,
  bytes p = Some value ->
  store_map name_byte_rep bytes --||--
    p # UChar |-> value ** store_map name_byte_rep (task_name_get_remove_byte bytes p).
Proof.
  intros bytes p value Hbyte; rewrite <- task_name_get_missing_byte_eq__resource_stages_strlen.
  split.
  - sep_apply_l_atomic (store_map_split name_byte_rep p value bytes Hbyte).
    unfold name_byte_rep; entailer!.
  - unfold name_byte_rep in *.
    sep_apply_l_atomic (store_map_merge (fun q b => q # UChar |-> b) p value bytes Hbyte).
    entailer!.
Qed.
Lemma task_name_get_array_split__resource_stages_strlen : forall values bytes base lo,
  (forall i c, nth_error values i = Some c -> bytes (base + lo + Z.of_nat i) = Some c) ->
  store_map name_byte_rep bytes --||--
    UCharArray.seg base lo (lo + Zlength values) values **
    store_map name_byte_rep (task_name_get_remove_bytes bytes (base + lo) (List.length values)).
Proof.
  induction values as [|value values IH]; intros bytes base lo Hbytes.
  - cbn [List.length task_name_get_remove_bytes].
    change (Zlength (@nil Z)) with 0; rewrite Z.add_0_r, UCharArray.seg_empty.
    split; entailer!.
  - assert (Hhead : bytes (base + lo) = Some value).
    { specialize (Hbytes O value eq_refl); cbn in Hbytes; rewrite Z.add_0_r in Hbytes; exact Hbytes. }
    assert (Htail : forall i c, nth_error values i = Some c ->
      task_name_get_remove_byte bytes (base + lo) (base + (lo + 1) + Z.of_nat i) = Some c).
    { intros i c Hi; unfold task_name_get_remove_byte.
      rewrite (proj2 (Z.eqb_neq (base + (lo + 1) + Z.of_nat i) (base + lo)) ltac:(lia)).
      replace (base + (lo + 1) + Z.of_nat i) with (base + lo + Z.of_nat (S i)) by lia.
      apply Hbytes; exact Hi. }
    rewrite (task_name_get_byte_split__resource_stages_strlen bytes (base + lo) value Hhead).
    rewrite (IH (task_name_get_remove_byte bytes (base + lo)) base (lo + 1) Htail).
    rewrite UCharArray.seg_unfold.
    cbn [List.length task_name_get_remove_bytes].
    rewrite Zlength_cons.
    replace (Z.succ (Zlength values)) with (Zlength values + 1) by lia.
    replace (lo + (Zlength values + 1)) with (lo + 1 + Zlength values) by lia.
    replace (base + lo + 1) with (base + (lo + 1)) by lia.
    change (sizeof(UCHAR)) with 1; rewrite Z.mul_1_r.
    split; entailer!.
Qed.
Lemma task_name_get_readable_source__resource_stages_strlen : forall names p chars,
  readable_name names p chars ->
  forall i c, nth_error (chars ++ [0]) i = Some c ->
    names.(nameBytes) (p + Z.of_nat i) = Some c.
Proof.
  intros names p chars [_ [Hchars Hnul]] i c Hi.
  destruct (lt_dec i (List.length chars)) as [Hlt|Hge].
  - rewrite nth_error_app1 in Hi by exact Hlt; apply Hchars; exact Hi.
  - rewrite nth_error_app2 in Hi by lia.
    destruct (i - List.length chars)%nat eqn:Hdiff; [|destruct n; discriminate].
    cbn in Hi; inversion Hi; subst c.
    assert (i = List.length chars) by lia; subst i; exact Hnul.
Qed.
Lemma task_name_get_name_split__resource_stages_strlen : forall names p chars,
  readable_name names p chars ->
  store_name_bytes names --||-- os_strlen_bytes p chars **
    task_name_get_name_residual names p chars.
Proof.
  intros names p chars Hread; unfold store_name_bytes, os_strlen_bytes, task_name_get_name_residual.
  rewrite (task_name_get_array_split__resource_stages_strlen (chars ++ [0]) names.(nameBytes) p 0).
  - unfold UCharArray.full, store_array, UCharArray.seg.
    rewrite Z.add_0_r, app_length; cbn [List.length].
    replace (List.length chars + 1)%nat with (S (List.length chars)) by lia.
    rewrite Z.add_0_l, Zlength_app_cons, Zlength_correct.
    replace (Z.of_nat (List.length chars) + 1) with (Z.of_nat (S (List.length chars))) by lia.
    split; reflexivity.
  - intros i c Hi; rewrite Z.add_0_r.
    eapply task_name_get_readable_source__resource_stages_strlen; eassumption.
Qed.

Lemma task_name_get_program_effect : forall critical sg invocation request pname
  before current result error output,
  task_name_get_program critical sg invocation request pname before
    (task_name_get_observation result error output) current ->
  exists acquired,
    task_name_get_effect sg invocation before acquired request pname result error output /\
    critical_region_interval critical sg invocation before acquired /\
    critical_region_interval critical sg invocation acquired current /\
    (task_name_get_early_error request pname (task_name_get_nesting before) <> None ->
      current = before).
Proof.
  intros critical sg invocation request pname before current result error output Hprogram.
  unfold task_name_get_program in Hprogram.
  destruct Hprogram as [nesting [entry [[Hnest Hentry] Hprogram]]].
  subst nesting entry.
  destruct (task_name_get_early_error request pname (task_name_get_nesting before))
    as [code|] eqn:Hearly.
  - destruct Hprogram as [Hobserved Hcurrent].
    inversion Hobserved; subst result error output current.
    exists before; split.
    + unfold task_name_get_effect; rewrite Hearly; auto.
    + split; [|split]; try (unfold critical_region_interval, kernel_resumption_trace; constructor).
  - destruct Hprogram as [u [acquired [Hacquire [observed [released [Hprotected
      [v [resumed [Hrelease [Hobserved Hcurrent]]]]]]]]]].
    subst observed resumed.
    unfold task_name_get_protected_program in Hprotected.
    destruct Hprotected as [priority [read_priority [[Hresolved Hpriority]
      [pointer [read_pointer [[Hpointer Hstate] Hbranch]]]]]].
    subst read_priority read_pointer.
    destruct ((pointer =? 0) || (pointer =? 1))%bool eqn:Hbad.
    + destruct Hbranch as [Hobserved Hreleased].
      inversion Hobserved; subst result error output released.
      exists acquired; split.
      * unfold task_name_get_effect; rewrite Hearly; left.
        exists priority, pointer; split; [split; assumption|].
        apply Bool.orb_true_iff in Hbad.
        destruct Hbad as [Hnull|Hreserved]; apply Z.eqb_eq in Hnull || apply Z.eqb_eq in Hreserved;
          repeat split; auto.
      * split; [exact Hacquire|split; [exact Hrelease|contradiction]].
    + destruct Hbranch as [node [read_node [[Hnode Hstate]
        [length [measured [Hstrlen [Hobserved Hreleased]]]]]]].
      subst read_node.
      unfold task_name_get_strlen_program in Hstrlen.
      destruct Hstrlen as [chars [read_chars [[Hread Hstate] [Hlength Hmeasured]]]].
      subst read_chars measured released length.
      inversion Hobserved; subst result error output.
      destruct Hnode as [tid [Htable Hnode]].
      apply Bool.orb_false_iff in Hbad; destruct Hbad as [Hnull Hreserved].
      apply Z.eqb_neq in Hnull, Hreserved.
      exists acquired; split.
      * unfold task_name_get_effect; rewrite Hearly; right.
        exists priority, pointer, node.(tcbTaskName), chars; split; [|auto].
        split; [split; assumption|].
        exists tid, node; split; [exact Htable|].
        split; [exact Hnode|].
        split; [rewrite Htable in Hpointer; exact Hpointer|].
        split; [exact Hnull|]. split; [exact Hreserved|].
        split; [reflexivity|exact Hread].
      * split; [exact Hacquire|split; [exact Hrelease|contradiction]].
Qed.

Lemma task_name_get_program_effect_iff : forall critical sg invocation request pname
  before current result error output,
  (task_name_get_program critical sg invocation request pname before
    (task_name_get_observation result error output) current <->
   exists acquired,
    task_name_get_effect sg invocation before acquired request pname result error output /\
    critical_region_interval critical sg invocation before acquired /\
    critical_region_interval critical sg invocation acquired current /\
    (task_name_get_early_error request pname (task_name_get_nesting before) <> None ->
      current = before)).
Proof.
  intros; split; [apply task_name_get_program_effect|].
  intros [acquired [Heffect [Hacquire [Hrelease Hearly]]]].
  eapply task_name_get_effect_program; eassumption.
Qed.

Lemma task_name_get_program_has_result : forall critical sg invocation request pname old before,
  UCOS2_state_inv sg before ->
  task_name_get_access critical sg invocation before request pname old ->
  exists observed current,
    task_name_get_program critical sg invocation request pname before observed current.
Proof.
  intros critical sg invocation request pname old before Hvalid Haccess.
  assert (Hrefl : critical_region_interval critical sg invocation before before).
  { unfold critical_region_interval, kernel_resumption_trace; constructor. }
  destruct (task_name_get_early_error request pname (task_name_get_nesting before))
    as [code|] eqn:Hearly.
  - exists (task_name_get_observation 0 code None), before.
    eapply task_name_get_effect_program with (acquired := before); try exact Hrefl;
      [unfold task_name_get_effect; rewrite Hearly; auto|intros; reflexivity].
  - destruct (proj1 (Haccess Hearly before Hrefl Hvalid)) as [priority Hresolved].
    set (pointer := prio_tbl_entry_to_addr sg (before.(TskState).(prioTbl) priority)).
    assert (Hlookup : task_name_get_lookup sg invocation before request priority pointer).
    { split; [exact Hresolved|reflexivity]. }
    destruct (Z.eq_dec pointer 0) as [Hnull|Hnull];
      [|destruct (Z.eq_dec pointer 1) as [Hreserved|Hreserved]].
    1,2: exists (task_name_get_observation 0 67 None), before;
      eapply task_name_get_effect_program with (acquired := before); try exact Hrefl;
      [unfold task_name_get_effect; rewrite Hearly; left; exists priority, pointer; auto
      |intros; reflexivity].
    destruct (task_name_get_lookup_task__task_lookup_fields sg invocation before
      request priority pointer Hvalid Hlookup Hnull Hreserved)
      as [tid [node [[Htable Hnode] Hpointer]]].
    destruct (task_name_get_task_root_readable sg before tid node Hvalid Hnode)
      as [chars Hread].
    exists (task_name_get_observation (task_name_get_length node.(tcbTaskName) chars)
      0 (Some node.(tcbTaskName))), before.
    eapply task_name_get_effect_program with (acquired := before); try exact Hrefl;
      [|intros; reflexivity].
    unfold task_name_get_effect; rewrite Hearly; right.
    exists priority, pointer, node.(tcbTaskName), chars; split; [|auto].
    split; [exact Hlookup|].
    exists tid, node; split; [exact Htable|]. split; [exact Hnode|].
    split; [exact Hpointer|]. split; [exact Hnull|]. split; [exact Hreserved|].
    split; [reflexivity|intros _; exact Hread].
Qed.
