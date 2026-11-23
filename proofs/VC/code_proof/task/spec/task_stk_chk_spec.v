Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.task.
Require Export Ucos2Verify.lib.sched.
Require Export Ucos2Verify.lib.array_abstraction.
Require Export Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.task.spec.task_stack_check_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.task_storage.
Require Export Ucos2Verify.lib.task_stack.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Static source interpretation for the first native TCB field.  It
    binds the actual QCP field-address term; it supplies no runtime owner
    and imposes no inequality on the priority-table entry. *)
Definition task_stk_chk_layout (sg : StableGlobVars) : Prop :=
  forall slot, task_slot_in_range sg slot ->
    tcb_field_address (task_slot_addr sg slot) TCBStkPtr =
      task_slot_addr sg slot.

Definition task_stk_chk_global_addresses (sg : StableGlobVars)
  (current table : addr) : Prop :=
  sg.(g_OSTCBCur) = current /\ sg.(g_OSTCBPrioTbl) = table /\
  task_stk_chk_layout sg.

(** Conditional projection of the existing basic64 initialization ABI.
    This does not prove deployment, linker layout, or an OSInit execution. *)
Lemma init_tcb_list_layout_implies_task_stk_chk_layout : forall sg,
  init_tcb_list_profile sg -> init_tcb_list_layout sg ->
  task_stk_chk_layout sg.
Proof.
  intros sg Hprofile Hlayout slot Hslot.
  pose proof (init_tcb_list_profile_no_multi sg Hprofile) as Hmulti.
  pose proof (init_tcb_list_profile_no_profiling sg Hprofile) as Hprofiling.
  destruct Hprofile as [Htasks [Hsystem _]].
  unfold task_slot_in_range in Hslot; rewrite Htasks, Hsystem in Hslot.
  rewrite (task_slot_addr_tcb64 sg slot Hmulti Hprofiling).
  destruct Hlayout as [_ [_ [_ [_ [_ [_ [_ Hfields]]]]]]].
  rewrite (Hfields slot TCBStkPtr Hslot).
  cbn [tcb_field_offset]; lia.
Qed.

Definition task_stk_chk_configuration (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osLowestPrio) = 63 /\ sg.(osPrioSelf) = 255.

Definition task_stk_chk_valid_arguments (priority output : Z) : Prop :=
  0 <= priority <= 255 /\ (priority <= 63 \/ priority = 255) /\ output <> 0.

Definition task_stk_chk_current_pointer (sg : StableGlobVars)
  (state : UCOS2_Verify_State) : addr :=
  encode_task_link sg state.(SchedState).(curTaskID).

Definition task_stk_chk_table_pointer (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (priority : Z) : addr :=
  prio_tbl_entry_to_addr sg (state.(TskState).(prioTbl) priority).

Definition task_stk_chk_output_undef (output : addr) : Assertion :=
  (&(output # "os_stk_data" ->ₛ "OSFree")) # UInt |->_ **
  (&(output # "os_stk_data" ->ₛ "OSUsed")) # UInt |->_ .

(** Prefix errors do not dereference output at all. Any old output owner
    may remain in caller; valid nonnull calls supply just its two fields. *)
Definition task_stk_chk_output_pre (sg : StableGlobVars)
  (priority output : addr) : Assertion :=
  match task_stack_check_argument_error sg priority output with
  | Some _ => emp
  | None => task_stk_chk_output_undef output
  end.

Definition task_stk_chk_output_post (output : addr)
  (data : option TaskStackCheckData) : Assertion :=
  match data with None => emp | Some result_data => task_stack_check_data_rep output result_data end.

Definition task_stk_chk_world (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion) (output : addr) : Assertion :=
  UCOS2_raw_rep sg state ** caller **
  task_stack_check_data_rep output task_stack_check_zero_data.

(** The SAME heap supplies the current-pointer cell and the actually read
    Prio byte. This permits any source-readable current object; no blanket
    live-current or task-only requirement is introduced. *)
Definition task_stk_chk_self_view (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion) (output selected : addr)
  (residual : Assertion) : Prop :=
  0 <= selected <= 63 /\
  (task_stk_chk_world sg state caller output |--
    sg.(g_OSTCBCur) # Ptr |-> task_stk_chk_current_pointer sg state **
    tcb_field_address (task_stk_chk_current_pointer sg state) TCBPrio
      # UChar |-> selected ** residual) /\
  (sg.(g_OSTCBCur) # Ptr |-> task_stk_chk_current_pointer sg state **
    tcb_field_address (task_stk_chk_current_pointer sg state) TCBPrio
      # UChar |-> selected ** residual |--
    task_stk_chk_world sg state caller output).

Definition task_stk_chk_selected (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion)
  (priority output selected : addr) : Prop :=
  if Z.eqb priority 255 then
    exists residual, task_stk_chk_self_view sg state caller output selected residual
  else selected = priority.

(** Existing protected semantics at the RESOLVED explicit priority. The
    extra SELF view records the actual source read without making effective
    priority an object identity or excluding aliases. *)
Definition task_stk_chk_critical (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion)
  (priority output selected : addr) (decision : TaskStackCheckDecision) : Prop :=
  task_stk_chk_selected sg state caller priority output selected /\
  task_stack_check_critical sg selected state decision state.

Definition task_stk_chk_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  UCOS2_state_inv sg before /\ interrupt_saved_value mask saved /\
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry.

(** OSTaskStkChk, selected growth=1 / UInt32 source.

    These are case-local, source-produced initial-image consequences and
    reversible read views. They are deliberately not a whole-API Require:
    neither creation identity nor a saved frame establishes that the
    snapshot-selected prefix is available after Restore. In particular,
    callers whose output is on the scanned stack must use the SAME resource
    partition; this file never adds a second full-stack owner to the output.

    Ordered errors, actual critical lookup, dynamic reads, exact modular
    output and the final nonzero read's cursor increment are imported from
    task_stack_check_spec. No bounded replacement scan is defined here. *)

Definition task_stk_chk_snapshot_region
  (snapshot : TaskStackCheckSnapshot) (region : TaskStackRegion) : Prop :=
  snapshot.(stackCheckBottom) = region.(stackRegionBase) /\
  region.(stackRegionGrowsDown) = true /\ valid_task_stack_region region.

(** The readable extent is independent of the sampled TCB Size. In
    particular Size=0 and a scan longer than Size retain source modular
    subtraction; neither case becomes an extra executable guard. *)

(** A concrete sufficient image, not an admitted successful execution.
    Its pure clauses do not supply the spatial storage assertion. *)
Definition task_stk_chk_initialized_prefix
  (snapshot : TaskStackCheckSnapshot) (region : TaskStackRegion)
  (words : list (option Z)) (count : nat) (stop : Z) : Prop :=
  task_stk_chk_snapshot_region snapshot region /\
  Zlength words = region.(stackRegionWords) /\
  task_stack_scan_prefix words count stop.

(** A reversible view, not separately supplied stack ownership. In SELF,
    the array can contain both zeroed output cells: the forward direction
    consumes them and the reverse direction returns them. In a parked
    case it consumes the appropriate real map fragments instead. *)
Definition task_stk_chk_scan_view (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion) (output : addr)
  (snapshot : TaskStackCheckSnapshot) (region : TaskStackRegion)
  (words : list (option Z)) (count : nat) (stop : Z)
  (residual : Assertion) : Prop :=
  task_stk_chk_initialized_prefix snapshot region words count stop /\
  (task_stk_chk_world sg state caller output |--
    task_stack_storage region words ** residual) /\
  (task_stack_storage region words ** residual |--
    task_stk_chk_world sg state caller output).

(** Ordinary Hoare read admission for this invocation and its registered
    rely. Only SELF requires its actual byte view, and only the successful
    decision requires readable initialized storage after its actual Restore.
    This is not an existential successful read trace, a promise about every
    task, an ISR rejection or an additional CPU/platform law. *)
Definition task_stk_chk_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before : UCOS2_Verify_State)
  (caller : Assertion) (priority output : addr) : Prop :=
  task_stack_check_argument_error sg priority output = None ->
  (priority = 255 -> forall entry,
    critical_region_interval critical sg invocation before entry ->
    UCOS2_state_inv sg entry ->
    exists selected residual, task_stk_chk_self_view sg entry caller output selected residual) /\
  (forall entry selected snapshot,
    critical_region_interval critical sg invocation before entry ->
    UCOS2_state_inv sg entry ->
    task_stk_chk_critical sg entry caller priority output selected
      (TaskStackCheckScan snapshot) ->
    forall after, critical_region_interval critical sg invocation entry after ->
    UCOS2_state_inv sg after ->
    exists region words count stop residual,
      task_stk_chk_scan_view sg after caller output snapshot region words count stop residual).

Definition task_stk_chk_call_post (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask : Z)
  (before : UCOS2_Verify_State) (caller : Assertion) (priority output error : addr)
  (data : option TaskStackCheckData) (after : UCOS2_Verify_State) : Prop :=
  match task_stack_check_argument_error sg priority output with
  | Some prefix_error => error = encode_os_err_code prefix_error /\
      data = None /\ after = before
  | None => exists entry saved selected decision,
      task_stk_chk_acquire_facts critical sg invocation mask saved before entry /\
      task_stk_chk_critical sg entry caller priority output selected decision /\
      critical_region_interval critical sg invocation entry after /\
      match decision with
      | TaskStackCheckError critical_error =>
          error = encode_os_err_code critical_error /\
          data = Some task_stack_check_zero_data
      | TaskStackCheckScan snapshot =>
          exists region words count stop residual,
            task_stk_chk_scan_view sg after caller output snapshot region words count stop residual /\
            error = 0 /\ data = Some (task_stack_scan_data snapshot.(stackCheckSize) count)
      end
  end.

(* The acquired SELF byte and table/option/snapshot decision use the existing
   source relation. The read view is the same one used by the concrete proof;
   it neither requires a live current task nor treats an alias as an identity. *)
Definition task_stk_chk_protected_program (sg : StableGlobVars)
  (caller : Assertion) (priority output : Z)
  : program UCOS2_Verify_State TaskStackCheckDecision :=
  StateRelMonad.bind
    (get (fun state selected =>
      task_stk_chk_selected sg state caller priority output selected))
    (fun selected => task_stack_check_critical sg selected).

(* A read from the actual stable image lent by scan_view. No size guard or
   end-of-array success is introduced. The imported trace tests every word
   and advances the cursor even on the final nonzero observation. *)
Definition task_stk_chk_image_read (base : addr) (words : list (option Z))
  (cursor : addr) : program UCOS2_Verify_State Z :=
  get (fun _ value => exists index,
    0 <= index < Zlength words /\ cursor = base + index * sizeof(UINT) /\
    Znth index words None = Some value).

Definition task_stk_chk_scan_program (sg : StableGlobVars) (caller : Assertion)
  (output : addr) (snapshot : TaskStackCheckSnapshot)
  : program UCOS2_Verify_State nat :=
  fun before count after => exists region words stop residual final_cursor,
    task_stk_chk_scan_view sg before caller output snapshot region words count stop residual /\
    task_stack_scan_trace
      (task_stk_chk_image_read region.(stackRegionBase) words)
      snapshot.(stackCheckBottom) before count final_cursor after.

(* Private output initialization precedes Save. Its two concrete stores and
   their order remain spatial C obligations; this program observes the zeroed
   data, then the actual return code and final output after Restore/scan.
   None means no output access, not an invented value for a NULL output. *)
Definition task_stk_chk_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (caller : Assertion)
  (priority output : Z)
  : program UCOS2_Verify_State (Z * option TaskStackCheckData) :=
  match task_stack_check_argument_error sg priority output with
  | Some error => StateRelMonad.ret (encode_os_err_code error, None)
  | None => StateRelMonad.bind (StateRelMonad.ret task_stack_check_zero_data)
      (fun zeroed => StateRelMonad.bind
        (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.bind
          (task_stk_chk_protected_program sg caller priority output)
          (fun decision => StateRelMonad.bind
            (update (critical_region_interval critical sg invocation))
            (fun _ => match decision with
              | TaskStackCheckError error =>
                  StateRelMonad.ret (encode_os_err_code error, Some zeroed)
              | TaskStackCheckScan snapshot => StateRelMonad.bind
                  (task_stk_chk_scan_program sg caller output snapshot)
                  (fun count => StateRelMonad.ret
                    (0, Some (task_stack_scan_data snapshot.(stackCheckSize) count)))
              end))))
  end.

Definition task_stk_chk_safe critical sg invocation before caller priority output
  (X : Z -> option TaskStackCheckData -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = before)
    (task_stk_chk_program critical sg invocation caller priority output)
    (fun result state => X (fst result) (snd result) state).

Definition task_stk_chk_post critical sg invocation mask before caller
  priority output error data after
  (X : Z -> option TaskStackCheckData -> UCOS2_Verify_State -> Prop) : Prop :=
  task_stk_chk_call_post critical sg invocation mask before caller
    priority output error data after /\
  safeExec (fun state => state = after) (StateRelMonad.ret (error, data))
    (fun result state => X (fst result) (snd result) state).

Lemma task_stk_chk_protected_program_iff :
  forall sg caller priority output before decision after,
  task_stk_chk_protected_program sg caller priority output before decision after <->
  after = before /\ exists selected,
    task_stk_chk_critical sg before caller priority output selected decision.
Proof.
  intros sg caller priority output before decision after; split.
  - intros [selected [entry [[Hselected Hentry] Hcritical]]]; subst entry.
    pose proof (task_stack_check_critical_frame _ _ _ _ _ Hcritical) as ->.
    split; [reflexivity|]; exists selected; split; assumption.
  - intros [-> [selected [Hselected Hcritical]]].
    exists selected, before; split; [split; [exact Hselected|reflexivity]|exact Hcritical].
Qed.

Lemma task_stk_chk_scan_program_iff : forall sg caller output snapshot before count after,
  task_stk_chk_scan_program sg caller output snapshot before count after <->
  after = before /\ exists region words stop residual,
    task_stk_chk_scan_view sg before caller output snapshot region words count stop residual.
Proof.
  intros sg caller output snapshot before count after; split.
  - intros [region [words [stop [residual [cursor [Hview Htrace]]]]]].
    split.
    + eapply (task_stack_scan_trace_preserves
        (task_stk_chk_image_read region.(stackRegionBase) words)
        (fun state => state = before)); [|exact Htrace|reflexivity].
      intros address first value last [_ ->]; auto.
    + exists region, words, stop, residual; exact Hview.
  - intros [-> [region [words [stop [residual Hview]]]]].
    exists region, words, stop, residual,
      (snapshot.(stackCheckBottom) + (Z.of_nat count + 1) * sizeof(UINT)).
    split; [exact Hview|].
    pose proof Hview as [[[Hbase _] [_ Hprefix]] _].
    eapply task_stack_scan_prefix_trace; [exact Hprefix|].
    intros index value Hindex Hword; split; [|reflexivity].
    exists index; split; [exact Hindex|].
    split; [now rewrite Hbase|exact Hword].
Qed.

Lemma task_stk_chk_call_post_program :
  forall critical sg invocation mask before caller priority output error data after,
  task_stk_chk_call_post critical sg invocation mask before caller
    priority output error data after ->
  task_stk_chk_program critical sg invocation caller priority output
    before (error, data) after.
Proof.
  intros critical sg invocation mask before caller priority output error data after Hpost.
  unfold task_stk_chk_call_post in Hpost; unfold task_stk_chk_program.
  destruct (task_stack_check_argument_error sg priority output).
  - destruct Hpost as [-> [-> ->]]; split; reflexivity.
  - destruct Hpost as (entry & saved & selected & decision &
      (Hbefore & Hsaved & Hacquire & Hentry) & Hcritical & Hrelease & Hresult).
    exists task_stack_check_zero_data, before; split; [split; reflexivity|].
    exists tt, entry; split; [exact Hacquire|].
    exists decision, entry; split.
    + apply task_stk_chk_protected_program_iff; split; [reflexivity|].
      exists selected; exact Hcritical.
    + exists tt, after; split; [exact Hrelease|].
      destruct decision as [critical_error|snapshot].
      * destruct Hresult as [-> ->]; split; reflexivity.
      * destruct Hresult as [region [words [count [stop [residual [Hview [-> ->]]]]]]].
        exists count, after; split; [|split; reflexivity].
        apply task_stk_chk_scan_program_iff; split; [reflexivity|].
        exists region, words, stop, residual; exact Hview.
Qed.

Lemma task_stk_chk_safe_return :
  forall critical sg invocation mask before caller priority output error data after X,
  task_stk_chk_call_post critical sg invocation mask before caller
    priority output error data after ->
  task_stk_chk_safe critical sg invocation before caller priority output X ->
  task_stk_chk_post critical sg invocation mask before caller
    priority output error data after X.
Proof.
  intros critical sg invocation mask before caller priority output error data after X Hpost Hsafe.
  split; [exact Hpost|].
  eapply (highstependret_derive
    (task_stk_chk_program critical sg invocation caller priority output)
    (fun state => state = before) (error, data) (fun _ state => state = after)).
  - intros state ->; exists after; split; [|reflexivity].
    eapply task_stk_chk_call_post_program; exact Hpost.
  - exact Hsafe.
Qed.

Definition TaskStkChkWords := list (option Z).

Definition task_stk_chk_residual (residual : Assertion) : Assertion := residual.

Definition task_stk_chk_count (count : nat) : Z := Z.of_nat count.

Definition task_stk_chk_word (count : nat) (stop index : Z) : Z :=
  if Z.ltb index (Z.of_nat count) then 0 else stop.

Definition task_stk_chk_bottom (snapshot : TaskStackCheckSnapshot) : addr :=
  snapshot.(stackCheckBottom).

Definition task_stk_chk_size (snapshot : TaskStackCheckSnapshot) : Z :=
  snapshot.(stackCheckSize).

Definition task_stk_chk_cursor (snapshot : TaskStackCheckSnapshot) (index : Z) : addr :=
  snapshot.(stackCheckBottom) + index * sizeof(UINT).

Definition task_stk_chk_scan_read_frame (region : TaskStackRegion)
  (words : TaskStkChkWords) (index : Z) (residual : Assertion) : Assertion :=
  UIntArray.mixed_missing_i region.(stackRegionBase) index 0
    region.(stackRegionWords) words ** residual.

Definition task_stk_chk_scan_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask : Z)
  (before : UCOS2_Verify_State) (caller : Assertion) (priority output saved : Z)
  (entry after : UCOS2_Verify_State) (selected : Z)
  (snapshot : TaskStackCheckSnapshot) (region : TaskStackRegion)
  (words : TaskStkChkWords) (count : nat) (stop : Z) (residual : Assertion) : Prop :=
  task_stk_chk_configuration sg /\ task_stk_chk_valid_arguments priority output /\
  task_stk_chk_acquire_facts critical sg invocation mask saved before entry /\
  task_stk_chk_critical sg entry caller priority output selected
    (TaskStackCheckScan snapshot) /\
  critical_region_interval critical sg invocation entry after /\
  UCOS2_state_inv sg after /\
  task_stk_chk_scan_view sg after caller output snapshot region words count stop residual.

Definition task_stk_chk_error_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask : Z)
  (before : UCOS2_Verify_State) (caller : Assertion) (priority output saved : Z)
  (entry : UCOS2_Verify_State) (selected error : Z) : Prop :=
  task_stk_chk_configuration sg /\ task_stk_chk_valid_arguments priority output /\
  task_stk_chk_acquire_facts critical sg invocation mask saved before entry /\
  exists critical_error, error = encode_os_err_code critical_error /\
    task_stk_chk_critical sg entry caller priority output selected
      (TaskStackCheckError critical_error).

Definition task_stk_chk_node (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (selected pointer : Z) (slot : TaskID) (node : TaskAbstractState) : Prop :=
  state.(TskState).(prioTbl) selected = PTTask slot /\
  state.(TskState).(inUsedTaskStates) slot = Some node /\
  pointer = task_slot_addr sg slot.

Definition task_stk_chk_node_option (node : TaskAbstractState) : Z := node.(tcbOpt).
Definition task_stk_chk_node_size (node : TaskAbstractState) : Z := node.(tcbStkSize).
Definition task_stk_chk_node_bottom (node : TaskAbstractState) : Z := node.(tcbStkBottom).
Definition task_stk_chk_node_snapshot (slot : TaskID) (node : TaskAbstractState)
  : TaskStackCheckSnapshot := task_stack_check_snapshot slot node.

Lemma task_stk_chk_outside_raw : forall critical sg invocation state,
  critical_region_outside critical sg invocation state --||-- UCOS2_raw_rep sg state.
Proof.
  intros; unfold critical_region_outside.
  rewrite critical_region_outside_without_running_rep.
  rewrite UCOS2_raw_rep_split_running; split; reflexivity.
Qed.

Lemma task_stk_chk_admission_prefix_error :
  forall critical sg invocation before caller priority output error,
  task_stack_check_argument_error sg priority output = Some error ->
  task_stk_chk_admission critical sg invocation before caller priority output.
Proof. intros; intro Hnone; congruence. Qed.

Definition task_stk_chk_sched_without_current (sg : StableGlobVars)
  (tasks : Glob_TaskAbstractState) (state : SchedAbstractState) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp state.(readyList) tasks **
  sched_rows_rep sg tasks state.(readyList) [0;1;2;3;4;5;6;7] **
  sg.(g_OSPrioCur) # UChar |-> sched_priority_byte state.(curSchedPrio) **
  sg.(g_OSPrioHighRdy) # UChar |-> sched_priority_byte state.(highRdyPrio) **
  sg.(g_OSTCBHighRdy) # Ptr |-> encode_task_link sg state.(highRdyTid) **
  sg.(g_OSCtxSwCtr) # UInt |-> state.(ctxSwCtr) **
  sg.(g_OSRunning) # UChar |-> (if state.(isRunning) then 1 else 0).

Definition task_stk_chk_self_live_residual (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion) (output : addr)
  (slot : TaskID) (node : TaskAbstractState) : Assertion :=
  task_public_storage_without_field sg state.(TskState) slot node (TCBCommonField TCBPrio) **
  task_stk_chk_sched_without_current sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state ** caller **
  task_stack_check_data_rep output task_stack_check_zero_data.

Lemma task_stk_chk_self_view_live : forall sg state caller output slot node,
  state.(SchedState).(curTaskID) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  0 <= node.(curPrio) <= 63 ->
  task_stk_chk_self_view sg state caller output node.(curPrio)
    (task_stk_chk_self_live_residual sg state caller output slot node).
Proof.
  intros sg state caller output slot node Hcurrent Hnode Hprio.
  unfold task_stk_chk_self_view; split; [exact Hprio|].
  unfold task_stk_chk_world, task_stk_chk_self_live_residual,
    task_stk_chk_current_pointer; rewrite Hcurrent.
  change (encode_task_link sg (Some slot)) with (task_slot_addr sg slot).
  split; unfold UCOS2_raw_rep, task_shared_rep,
    UCOS2_raw_rep_missing_task_storage_sched, task_stk_chk_sched_without_current,
    sched_raw_rep, sched_physical_rep.
  - rewrite Hcurrent.
    change (encode_task_link sg (Some slot)) with (task_slot_addr sg slot).
    pose proof (task_public_storage_split_field sg state.(TskState)
      slot node (TCBCommonField TCBPrio) Hnode
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hsplit.
    cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell]
      in Hsplit.
    sep_apply_l_atomic Hsplit; entailer!.
  - rewrite Hcurrent.
    change (encode_task_link sg (Some slot)) with (task_slot_addr sg slot).
    pose proof (task_public_storage_merge_field sg state.(TskState)
      slot node (TCBCommonField TCBPrio) Hnode
      (tcb_configured_common_field_in _ _ TCBPrio)) as Hmerge.
    cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell]
      in Hmerge.
    rewrite <- Hmerge; entailer!.
Qed.

Definition task_stk_chk_table_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (priority : Z) : Assertion :=
  store_prio_tbl_missing_i sg state.(TskState).(prioTbl) priority **
  UCOS2_raw_rep_missing_priority_table sg state.

Lemma task_stk_chk_table_split : forall sg state priority,
  0 <= priority < 64 -> UCOS2_inv sg state |--
  coq_prop (UCOS2_state_inv sg state) &&
  ((sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_stk_chk_table_pointer sg state priority ** task_stk_chk_table_frame sg state priority).
Proof.
  intros sg state priority Hpriority.
  unfold task_stk_chk_table_pointer, task_stk_chk_table_frame.
  sep_apply_l_atomic (UCOS2_inv_split_priority_cell sg state priority Hpriority); entailer!.
Qed.

Lemma task_stk_chk_table_merge : forall sg state priority,
  0 <= priority < 64 ->
  coq_prop (UCOS2_state_inv sg state) &&
  ((sg.(g_OSTCBPrioTbl) + priority * sizeof(PTR)) # Ptr |->
    task_stk_chk_table_pointer sg state priority ** task_stk_chk_table_frame sg state priority)
  |-- UCOS2_inv sg state.
Proof.
  intros sg state priority Hpriority.
  unfold task_stk_chk_table_frame, task_stk_chk_table_pointer, UCOS2_inv.
  rewrite UCOS2_raw_rep_priority_table_equiv; Intros.
  sep_apply_l_atomic (store_prio_tbl_merge_cell sg state.(TskState).(prioTbl)
    priority Hpriority); entailer!.
Qed.

Lemma task_stk_chk_table_task_live : forall sg state priority slot,
  UCOS2_state_inv sg state -> task_priority_in_range sg priority ->
  state.(TskState).(prioTbl) priority = PTTask slot ->
  exists node, state.(TskState).(inUsedTaskStates) slot = Some node.
Proof.
  intros sg state priority slot
    [_ [_ [_ [_ [[[_ [Htable _]] _] _]]]]] Hpriority Hentry.
  specialize (Htable priority Hpriority); rewrite Hentry in Htable; exact Htable.
Qed.

Definition task_stk_chk_field_frame (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (slot : TaskID) (node : TaskAbstractState)
  (field : TCBField) : Assertion :=
  task_public_storage_without_field sg state.(TskState) slot node (TCBCommonField field) **
  sched_raw_rep sg state.(TskState) state.(SchedState) **
  UCOS2_raw_rep_missing_task_storage_sched sg state.

Lemma task_stk_chk_field_split : forall sg state slot node field,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  UCOS2_inv sg state |-- coq_prop (UCOS2_state_inv sg state) &&
  (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg slot)
    (TCBCommonField field) (task_layout_image sg node (TCBCommonField field)) **
    task_stk_chk_field_frame sg state slot node field).
Proof.
  intros sg state slot node field Hnode.
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep, task_stk_chk_field_frame,
    UCOS2_raw_rep_missing_task_storage_sched.
  Intros.
  sep_apply_l_atomic (task_public_storage_split_field sg state.(TskState) slot node
    (TCBCommonField field) Hnode (tcb_configured_common_field_in _ _ field)); entailer!.
Qed.

Lemma task_stk_chk_field_merge : forall sg state slot node field,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  coq_prop (UCOS2_state_inv sg state) &&
  (tcb_layout_cell sg.(osKernelConfig).(cfgEventMultiEnabled) (task_slot_addr sg slot)
    (TCBCommonField field) (task_layout_image sg node (TCBCommonField field)) **
    task_stk_chk_field_frame sg state slot node field) |-- UCOS2_inv sg state.
Proof.
  intros sg state slot node field Hnode.
  unfold UCOS2_inv, UCOS2_raw_rep, task_shared_rep, task_stk_chk_field_frame,
    UCOS2_raw_rep_missing_task_storage_sched.
  Intros.
  rewrite <- (task_public_storage_merge_field sg state.(TskState) slot node
    (TCBCommonField field) Hnode (tcb_configured_common_field_in _ _ field)); entailer!.
Qed.

(** The acquired live node's real Ptr cell supplies alignment.  The
    original value and the same kernel invariant are retained afterwards;
    the stored stack pointer itself is allowed to be zero. *)
Lemma task_stk_chk_live_slot_address_not_reserved : forall sg entry slot node,
  task_stk_chk_layout sg ->
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  UCOS2_inv sg entry |--
    coq_prop (task_slot_addr sg slot <> 1) && UCOS2_inv sg entry.
Proof.
  intros sg entry slot node Hlayout Hnode.
  apply _derivable1_andp_intros; [|entailer!].
  pose proof (task_stk_chk_field_split sg entry slot node TCBStkPtr Hnode)
    as Hsplit.
  cbn [tcb_layout_cell task_layout_image tcb_layout_image task_tcb64_image tcb_cell]
    in Hsplit.
  sep_apply_l_atomic Hsplit.
  apply (coq_prop_andp_left (UCOS2_state_inv sg entry)); intro Hstate.
  assert (Hslot : task_slot_in_range sg slot).
  { destruct Hstate as [_ [[[Hslots _] _] _]].
    apply (proj2 (Hslots slot)); left; exists node; exact Hnode. }
  prop_apply_p (valid_store_ptr
    (tcb_field_address (task_slot_addr sg slot) TCBStkPtr) node.(tcbStkPtr)).
  coq_prop_lift.
  apply (coq_prop_andp_left
    (isvalidptr (tcb_field_address (task_slot_addr sg slot) TCBStkPtr) /\
      valid_ptr_value node.(tcbStkPtr))); intro Hpointer.
  assert (Hnot_reserved : task_slot_addr sg slot <> 1).
  { destruct Hpointer as [[_ [_ Halign]] _].
    rewrite (Hlayout slot Hslot) in Halign.
    change (task_slot_addr sg slot mod 4 = 0) in Halign.
    intro Hreserved; rewrite Hreserved in Halign; discriminate. }
  entailer!.
Qed.

Lemma task_stk_chk_reserved_table_entry : forall sg entry priority,
  task_stk_chk_layout sg -> task_priority_in_range sg priority ->
  task_stk_chk_table_pointer sg entry priority = 1 ->
  UCOS2_inv sg entry |--
    coq_prop (entry.(TskState).(prioTbl) priority = PTReserved) &&
    UCOS2_inv sg entry.
Proof.
  intros sg entry priority Hlayout Hpriority Hpointer.
  apply _derivable1_andp_intros; [|entailer!].
  unfold task_stk_chk_table_pointer in Hpointer.
  destruct (entry.(TskState).(prioTbl) priority) as [| |slot] eqn:Hentry.
  - discriminate Hpointer.
  - entailer!.
  - assert (Hpure : UCOS2_inv sg entry |-- coq_prop (UCOS2_state_inv sg entry)).
    { unfold UCOS2_inv; entailer!. }
    prop_apply_p Hpure.
    coq_prop_lift.
    apply (coq_prop_andp_left (UCOS2_state_inv sg entry)); intro Hstate.
    destruct (task_stk_chk_table_task_live sg entry priority slot
      Hstate Hpriority Hentry) as [node Hnode].
    sep_apply_l_atomic (task_stk_chk_live_slot_address_not_reserved
      sg entry slot node Hlayout Hnode).
    apply (coq_prop_andp_left (task_slot_addr sg slot <> 1));
      intro Hnot_reserved.
    change (task_slot_addr sg slot = 1) in Hpointer.
    contradiction.
Qed.

Lemma task_stk_chk_initial_status_nonzero : forall entry,
  task_stack_init_cpsr entry <> 0.
Proof.
  intros entry; unfold task_stack_init_cpsr; destruct Z.eqb; lia.
Qed.

(** Actual NoVFP StackInit image. The lower list is its INPUT image;
    complete initialization of that list has an independent producer. *)
Lemma task_stk_chk_initial_image_prefix : forall args task_return count upper,
  task_stack_scan_prefix
    (task_create_stack_image TaskStackNoVFP args task_return
      (repeat (Some 0) count) upper)
    count (task_stack_init_cpsr args.(createEntry)).
Proof.
  intros args task_return count upper; split.
  - apply task_stk_chk_initial_status_nonzero.
  - unfold task_create_stack_image.
    rewrite task_stack_init_no_vfp_frame_words; cbn [map].
    eexists; reflexivity.
Qed.

Lemma task_stk_chk_initial_image_scan_count : forall args task_return count upper,
  task_stack_scan_count
    (task_create_stack_image TaskStackNoVFP args task_return
      (repeat (Some 0) count) upper) = Some count.
Proof.
  intros; apply task_stack_scan_count_prefix_iff.
  eexists; apply task_stk_chk_initial_image_prefix.
Qed.

Lemma task_stk_chk_initial_image_certificate :
  forall snapshot region args task_return count upper,
  task_stk_chk_snapshot_region snapshot region ->
  task_create_stack_layout TaskStackNoVFP region args
    (repeat (Some 0) count) upper ->
  task_stk_chk_initialized_prefix snapshot region
    (task_create_stack_image TaskStackNoVFP args task_return
      (repeat (Some 0) count) upper)
    count (task_stack_init_cpsr args.(createEntry)).
Proof.
  intros snapshot region args task_return count upper Hregion Hlayout.
  split; [exact Hregion|]; split.
  - eapply task_create_stack_image_length; exact Hlayout.
  - apply task_stk_chk_initial_image_prefix.
Qed.

(** This consumes the actual StackInit post, including its written frame
    and unchanged lower/upper buffers. The prefix certificate alone never
    creates storage. The lower image here is the actual clear-call output. *)
Lemma task_stk_chk_stack_init_post_scan_storage :
  forall snapshot region args task_return count upper returned_sp,
  task_stk_chk_snapshot_region snapshot region ->
  task_create_stack_layout TaskStackNoVFP region args
    (repeat (Some 0) count) upper ->
  task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return (task_create_options args)
    (repeat (Some 0) count) upper returned_sp |--
  coq_prop (task_stk_chk_initialized_prefix snapshot region
    (task_create_stack_image TaskStackNoVFP args task_return (repeat (Some 0) count) upper)
    count (task_stack_init_cpsr args.(createEntry))) &&
  task_stack_storage region
    (task_create_stack_image TaskStackNoVFP args task_return (repeat (Some 0) count) upper).
Proof.
  intros snapshot region args task_return count upper returned_sp Hregion Hlayout.
  pose proof (task_stk_chk_initial_image_certificate snapshot region args task_return
    count upper Hregion Hlayout) as Hprefix.
  sep_apply_l_atomic (task_create_stack_init_post_storage TaskStackNoVFP region args
    task_return (repeat (Some 0) count) upper returned_sp Hlayout).
  entailer!.
Qed.

(** An explicit native-layout bridge, local to this carrier. It is used
    only when a caller's two output fields belong to the scanned image.
    The equations are about actual C field addresses, not an extra owner. *)
Definition task_stk_chk_output_layout (output first : addr) : Prop :=
  (&(output # "os_stk_data" ->ₛ "OSFree")) = first /\
  (&(output # "os_stk_data" ->ₛ "OSUsed")) = first + sizeof(UINT).

Lemma task_stk_chk_output_zero_array : forall output first,
  task_stk_chk_output_layout output first ->
  task_stack_check_data_rep output task_stack_check_zero_data --||--
  UIntArray.mixed_full first 2 [Some 0; Some 0].
Proof.
  intros output first [Hfree Hused].
  unfold task_stack_check_data_rep, task_stack_check_zero_data.
  change (((&(output # "os_stk_data" ->ₛ "OSFree")) # UInt |-> 0 **
    (&(output # "os_stk_data" ->ₛ "OSUsed")) # UInt |-> 0) --||--
    UIntArray.mixed_full first 2 [Some 0; Some 0]).
  rewrite Hfree, Hused.
  rewrite UIntArray.mixed_full_unfold, UIntArray.mixed_seg_unfold,
    UIntArray.mixed_seg_empty.
  cbn [UIntArray.mixedstoreA StoreUIntAsElement.storeA].
  replace (first + 0 * sizeof(UINT)) with first by lia.
  replace (first + 1 * sizeof(UINT)) with (first + sizeof(UINT)) by lia.
  split; entailer!.
Qed.

(** Actual SELF/output partition: the caller owns the array with a two
    word hole, and output owns precisely that hole. Both directions use
    the existing split/merge rules; the full array is never a second input. *)
Lemma task_stk_chk_scan_view_from_output_partition :
  forall sg state output snapshot region lower upper count stop extra,
  region.(stackRegionWords) = Zlength lower + 2 + Zlength upper ->
  task_stk_chk_output_layout output
    (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) ->
  task_stk_chk_initialized_prefix snapshot region
    (lower ++ [Some 0; Some 0] ++ upper) count stop ->
  task_stk_chk_scan_view sg state
    (task_stack_storage_without_region region lower 2 upper ** extra)
    output snapshot region (lower ++ [Some 0; Some 0] ++ upper) count stop
    (UCOS2_raw_rep sg state ** extra).
Proof.
  intros sg state output snapshot region lower upper count stop extra
    Hsize Hlayout Hprefix.
  split; [exact Hprefix|]; split; unfold task_stk_chk_world.
  - rewrite (task_stk_chk_output_zero_array output
      (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) Hlayout).
    sep_apply_l_atomic (task_stack_storage_merge_region region lower
      [Some 0; Some 0] upper 2 Hsize eq_refl); entailer!.
  - sep_apply_l_atomic (task_stack_storage_split_region region lower
      [Some 0; Some 0] upper Hsize).
    rewrite <- (task_stk_chk_output_zero_array output
      (region.(stackRegionBase) + Zlength lower * sizeof(UINT)) Hlayout).
    entailer!.
Qed.

Definition task_stk_chk_parked_residual (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (caller : Assertion) (output : addr)
  (slot : TaskID) (generation : nat) : Assertion :=
  store_map_missing_i task_stack_map_entry state.(TskState).(parkedTaskStacks)
    (slot, generation) ** UCOS2_raw_rep_missing_parked_stacks sg state ** caller **
  task_stack_check_data_rep output task_stack_check_zero_data.

(** A genuine map entry, not a lease or geometry fact, produces this view.
    Only the selected entry needs a complete initialized image. Other
    entries remain in the ordinary missing-map residual. *)
Lemma task_stk_chk_scan_view_from_parked_image :
  forall sg state caller output snapshot region words count stop slot generation,
  state.(TskState).(parkedTaskStacks) (slot, generation) =
    Some (region, task_stack_complete_fragments region words) ->
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  task_stk_chk_scan_view sg state caller output snapshot region words count stop
    (task_stk_chk_parked_residual sg state caller output slot generation).
Proof.
  intros sg state caller output snapshot region words count stop slot generation
    Hentry Hprefix; split; [exact Hprefix|].
  unfold task_stk_chk_world, task_stk_chk_parked_residual,
    UCOS2_raw_rep, task_shared_rep, UCOS2_raw_rep_missing_task_storage_sched,
    UCOS2_raw_rep_missing_parked_stacks, store_parked_stacks.
  split.
  - sep_apply_l_atomic (store_map_split task_stack_map_entry (slot, generation)
      (region, task_stack_complete_fragments region words)
      state.(TskState).(parkedTaskStacks) Hentry).
    unfold task_stack_map_entry; cbn [fst snd].
    rewrite task_stack_fragments_rep_complete; entailer!.
  - rewrite <- (task_stack_fragments_rep_complete region words).
    change (task_stack_fragments_rep region (task_stack_complete_fragments region words))
      with (task_stack_map_entry (slot, generation)
        (region, task_stack_complete_fragments region words)).
    rewrite <- (store_map_merge task_stack_map_entry (slot, generation)
      (region, task_stack_complete_fragments region words)
      state.(TskState).(parkedTaskStacks) Hentry); entailer!.
Qed.

(** Concrete same-partition producer. The hypotheses are the actual
    forward/reverse storage decomposition of the caller/kernel owner;
    they neither duplicate an array nor assert execution of a scan. *)
Lemma task_stk_chk_scan_view_from_initial_partition :
  forall sg state caller output snapshot region args task_return count upper residual,
  task_stk_chk_snapshot_region snapshot region ->
  task_create_stack_layout TaskStackNoVFP region args (repeat (Some 0) count) upper ->
  (task_stk_chk_world sg state caller output |--
    task_stack_storage region
      (task_create_stack_image TaskStackNoVFP args task_return (repeat (Some 0) count) upper) **
    residual) ->
  (task_stack_storage region
      (task_create_stack_image TaskStackNoVFP args task_return (repeat (Some 0) count) upper) **
    residual |-- task_stk_chk_world sg state caller output) ->
  task_stk_chk_scan_view sg state caller output snapshot region
    (task_create_stack_image TaskStackNoVFP args task_return (repeat (Some 0) count) upper)
    count (task_stack_init_cpsr args.(createEntry)) residual.
Proof.
  intros sg state caller output snapshot region args task_return count upper residual
    Hregion Hlayout Hsplit Hmerge.
  split; [|split; assumption].
  eapply task_stk_chk_initial_image_certificate; eassumption.
Qed.

Lemma task_stk_chk_initialized_prefix_bounds :
  forall snapshot region words count stop,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  0 <= Z.of_nat count < region.(stackRegionWords) /\
  0 < snapshot.(stackCheckBottom) /\
  snapshot.(stackCheckBottom) + (Z.of_nat count + 1) * sizeof(UINT)
    <= 4294967295.
Proof.
  intros snapshot region words count stop
    [[Hbottom [Hdown Hvalid]] [Hlength Hprefix]].
  pose proof (task_stack_scan_first_stop_in_owned_extent
    region words count stop Hlength Hprefix) as Hcount.
  destruct Hvalid as [Hwords [Hbase [Halign Hend]]].
  unfold task_stack_region_end in Hend.
  rewrite Hbottom; rewrite sizeof_uint in *; repeat split; lia.
Qed.

(** Read and restore precisely one existing typed word. These views leave
    every other word in the genuine UIntArray residual. *)
Lemma task_stk_chk_initialized_prefix_split_zero :
  forall snapshot region words count stop index,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  0 <= index < Z.of_nat count ->
  task_stack_storage region words |--
    (snapshot.(stackCheckBottom) + index * sizeof(UINT)) # UInt |-> 0 **
    UIntArray.mixed_missing_i region.(stackRegionBase) index
      0 region.(stackRegionWords) words.
Proof.
  intros snapshot region words count stop index
    [[Hbottom Hregion] [Hlength Hprefix]] Hindex.
  rewrite Hbottom; apply task_stack_scan_split_initialized_cell.
  - pose proof (task_stack_scan_first_stop_in_owned_extent
      region words count stop Hlength Hprefix); lia.
  - eapply task_stack_scan_prefix_has_initialized_zero; eassumption.
Qed.

Lemma task_stk_chk_initialized_prefix_merge_zero :
  forall snapshot region words count stop index,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  0 <= index < Z.of_nat count ->
  (snapshot.(stackCheckBottom) + index * sizeof(UINT)) # UInt |-> 0 **
    UIntArray.mixed_missing_i region.(stackRegionBase) index
      0 region.(stackRegionWords) words |-- task_stack_storage region words.
Proof.
  intros snapshot region words count stop index
    [[Hbottom Hregion] [Hlength Hprefix]] Hindex.
  rewrite Hbottom; apply task_stack_scan_merge_read_cell.
  - pose proof (task_stack_scan_first_stop_in_owned_extent
      region words count stop Hlength Hprefix); lia.
  - eapply task_stack_scan_prefix_has_initialized_zero; eassumption.
Qed.

Lemma task_stk_chk_initialized_prefix_split_stop :
  forall snapshot region words count stop,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  task_stack_storage region words |--
    (snapshot.(stackCheckBottom) + Z.of_nat count * sizeof(UINT)) # UInt |-> stop **
    UIntArray.mixed_missing_i region.(stackRegionBase) (Z.of_nat count)
      0 region.(stackRegionWords) words.
Proof.
  intros snapshot region words count stop
    [[Hbottom Hregion] [Hlength Hprefix]].
  rewrite Hbottom; apply task_stack_scan_split_first_stop; assumption.
Qed.

Lemma task_stk_chk_initialized_prefix_merge_stop :
  forall snapshot region words count stop,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  (snapshot.(stackCheckBottom) + Z.of_nat count * sizeof(UINT)) # UInt |-> stop **
    UIntArray.mixed_missing_i region.(stackRegionBase) (Z.of_nat count)
      0 region.(stackRegionWords) words |-- task_stack_storage region words.
Proof.
  intros snapshot region words count stop
    [[Hbottom Hregion] [Hlength Hprefix]].
  rewrite Hbottom; apply task_stack_scan_merge_read_cell.
  - eapply task_stack_scan_first_stop_in_owned_extent; eassumption.
  - eapply task_stack_scan_prefix_has_initialized_stop; eassumption.
Qed.

Lemma task_stk_chk_initialized_prefix_split_word :
  forall snapshot region words count stop index,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  0 <= index <= Z.of_nat count ->
  task_stack_storage region words |--
  (snapshot.(stackCheckBottom) + index * sizeof(UINT)) # UInt |->
    task_stk_chk_word count stop index **
  UIntArray.mixed_missing_i region.(stackRegionBase) index
    0 region.(stackRegionWords) words.
Proof.
  intros snapshot region words count stop index Hprefix Hindex.
  unfold task_stk_chk_word; destruct (Z.ltb index (Z.of_nat count)) eqn:Hlt.
  - apply Z.ltb_lt in Hlt; eapply task_stk_chk_initialized_prefix_split_zero; eauto; lia.
  - apply Z.ltb_ge in Hlt; assert (index = Z.of_nat count) by lia; subst index.
    eapply task_stk_chk_initialized_prefix_split_stop; eassumption.
Qed.

Lemma task_stk_chk_initialized_prefix_merge_word :
  forall snapshot region words count stop index,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  0 <= index <= Z.of_nat count ->
  (snapshot.(stackCheckBottom) + index * sizeof(UINT)) # UInt |->
    task_stk_chk_word count stop index **
  UIntArray.mixed_missing_i region.(stackRegionBase) index
    0 region.(stackRegionWords) words |-- task_stack_storage region words.
Proof.
  intros snapshot region words count stop index Hprefix Hindex.
  unfold task_stk_chk_word; destruct (Z.ltb index (Z.of_nat count)) eqn:Hlt.
  - apply Z.ltb_lt in Hlt; eapply task_stk_chk_initialized_prefix_merge_zero; eauto; lia.
  - apply Z.ltb_ge in Hlt; assert (index = Z.of_nat count) by lia; subst index.
    eapply task_stk_chk_initialized_prefix_merge_stop; eassumption.
Qed.

Lemma task_stk_chk_selected_valid_arguments__lookup_and_error_paths :
  forall sg state caller priority output selected,
  task_stk_chk_selected sg state caller priority output selected ->
  0 <= selected <= 63 -> output <> 0 ->
  task_stk_chk_valid_arguments priority output.
Proof.
  intros sg state caller priority output selected Hselected Hrange Houtput.
  unfold task_stk_chk_selected in Hselected.
  unfold task_stk_chk_valid_arguments.
  destruct (Z.eqb priority 255) eqn:Hself.
  - apply Z.eqb_eq in Hself; subst priority; intuition lia.
  - subst selected; intuition lia.
Qed.
Lemma task_stk_chk_valid_arguments_no_error__lookup_and_error_paths :
  forall sg priority output,
  task_stk_chk_configuration sg ->
  task_stk_chk_valid_arguments priority output ->
  task_stack_check_argument_error sg priority output = None.
Proof.
  intros sg priority output [Hchecks [Hlowest Hself]]
    [[Hlower Hupper] [Hpriority Houtput]].
  unfold task_stack_check_argument_error; rewrite Hchecks, Hlowest, Hself.
  rewrite (proj2 (Z.eqb_neq output 0) Houtput).
  destruct Hpriority as [Hpriority|Hpriority].
  - rewrite (proj2 (Z.ltb_ge 63 priority) Hpriority); reflexivity.
  - subst priority; reflexivity.
Qed.
Lemma task_stk_chk_null_table_entry__lookup_and_error_paths :
  forall sg state priority,
  UCOS2_state_inv sg state -> task_priority_in_range sg priority ->
  task_stk_chk_table_pointer sg state priority = 0 ->
  state.(TskState).(prioTbl) priority = PTFree.
Proof.
  intros sg state priority Hstate Hpriority Hzero.
  unfold task_stk_chk_table_pointer in Hzero.
  destruct (state.(TskState).(prioTbl) priority) as [| |slot] eqn:Hentry;
    [reflexivity|discriminate Hzero|].
  destruct (task_stk_chk_table_task_live sg state priority slot
    Hstate Hpriority Hentry) as [node Hnode].
  destruct Hstate as [Hprofile [[[Hslots _] _] _]].
  assert (Hslot : task_slot_in_range sg slot).
  { apply (proj2 (Hslots slot)); left; exists node; exact Hnode. }
  assert (Hstable : valid_stable_glob_vars sg)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  assert (Hconfig : tcb64_configuration sg.(osKernelConfig))
    by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable
    ltac:(unfold stable_global_addresses; simpl; auto)) as Hbase.
  change (task_slot_addr sg slot = 0) in Hzero.
  rewrite task_slot_addr_object_size, (task_object_size_tcb64 _ Hconfig) in Hzero.
  unfold task_slot_in_range in Hslot; lia.
Qed.
Lemma task_stk_chk_error_facts_call_post__lookup_and_error_paths :
  forall critical sg invocation mask before caller priority output saved
    entry selected error after,
  task_stk_chk_error_facts critical sg invocation mask before caller priority
    output saved entry selected error ->
  critical_region_interval critical sg invocation entry after ->
  task_stk_chk_call_post critical sg invocation mask before caller priority
    output error (Some task_stack_check_zero_data) after.
Proof.
  intros critical sg invocation mask before caller priority output saved
    entry selected error after
    [Hconfiguration [Harguments [Hacquire [critical_error [Herror Hcritical]]]]]
    Hinterval.
  unfold task_stk_chk_call_post.
  rewrite (task_stk_chk_valid_arguments_no_error__lookup_and_error_paths
    sg priority output Hconfiguration Harguments).
  exists entry, saved, selected, (TaskStackCheckError critical_error).
  split; [exact Hacquire|].
  split; [exact Hcritical|].
  split; [exact Hinterval|].
  split; [exact Herror|reflexivity].
Qed.
Lemma task_stk_chk_selected_valid_arguments__self_and_snapshot_fields :
  forall sg state caller priority output selected,
  task_stk_chk_selected sg state caller priority output selected ->
  0 <= selected <= 63 -> output <> 0 ->
  task_stk_chk_valid_arguments priority output.
Proof.
  intros sg state caller priority output selected Hselected Hrange Houtput.
  unfold task_stk_chk_selected in Hselected.
  destruct (Z.eqb priority 255) eqn:Hself.
  - apply Z.eqb_eq in Hself; subst priority.
    unfold task_stk_chk_valid_arguments; lia.
  - subst selected; unfold task_stk_chk_valid_arguments; lia.
Qed.
Lemma task_stk_chk_valid_arguments_no_error__self_and_snapshot_fields :
  forall sg priority output,
  task_stk_chk_configuration sg ->
  task_stk_chk_valid_arguments priority output ->
  task_stack_check_argument_error sg priority output = None.
Proof.
  intros sg priority output [Hchecks [Hlowest Hself]]
    [Hrange [Hpriority Houtput]].
  unfold task_stack_check_argument_error.
  rewrite Hchecks, Hlowest, Hself, (proj2 (Z.eqb_neq _ _) Houtput).
  destruct Hpriority as [Hpriority|Hpriority].
  - rewrite (proj2 (Z.ltb_ge _ _) Hpriority); reflexivity.
  - subst priority; reflexivity.
Qed.
Lemma task_stk_chk_scan_facts_prefix__scan_loop_and_result :
  forall critical sg invocation mask before caller priority output saved
    entry after selected snapshot region words count stop residual,
  task_stk_chk_scan_facts critical sg invocation mask before caller priority
    output saved entry after selected snapshot region words count stop residual ->
  task_stk_chk_initialized_prefix snapshot region words count stop.
Proof.
  unfold task_stk_chk_scan_facts, task_stk_chk_scan_view; tauto.
Qed.
Lemma task_stk_chk_prefix_uint32_count__scan_loop_and_result :
  forall snapshot region words count stop,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  0 <= task_stk_chk_count count < 4294967296.
Proof.
  intros snapshot region words count stop Hprefix.
  pose proof (task_stk_chk_initialized_prefix_bounds
    snapshot region words count stop Hprefix) as [Hcount [Hbottom Hend]].
  unfold task_stk_chk_count; rewrite sizeof_uint in Hend; lia.
Qed.
Lemma task_stk_chk_word_zero_index_lt__scan_loop_and_result :
  forall count stop index,
  stop <> 0 -> 0 <= index <= task_stk_chk_count count ->
  task_stk_chk_word count stop index = 0 ->
  index < task_stk_chk_count count.
Proof.
  intros count stop index Hstop Hindex Hword.
  unfold task_stk_chk_word in Hword; unfold task_stk_chk_count in *.
  destruct (Z.ltb index (Z.of_nat count)) eqn:Hlt.
  - apply Z.ltb_lt in Hlt; exact Hlt.
  - contradiction.
Qed.
Lemma task_stk_chk_word_nonzero_index_eq__scan_loop_and_result :
  forall count stop index,
  0 <= index <= task_stk_chk_count count ->
  task_stk_chk_word count stop index <> 0 ->
  index = task_stk_chk_count count.
Proof.
  intros count stop index Hindex Hword.
  unfold task_stk_chk_word in Hword; unfold task_stk_chk_count in *.
  destruct (Z.ltb index (Z.of_nat count)) eqn:Hlt.
  - contradiction.
  - apply Z.ltb_ge in Hlt; lia.
Qed.
Lemma task_stk_chk_word_at_count__scan_loop_and_result :
  forall count stop,
  task_stk_chk_word count stop (task_stk_chk_count count) = stop.
Proof.
  intros; unfold task_stk_chk_word, task_stk_chk_count.
  rewrite Z.ltb_irrefl; reflexivity.
Qed.
Lemma task_stk_chk_cursor_successor__scan_loop_and_result :
  forall snapshot index,
  task_stk_chk_cursor snapshot (index + 1) =
    task_stk_chk_cursor snapshot index + 4.
Proof.
  intros; unfold task_stk_chk_cursor; rewrite sizeof_uint; lia.
Qed.
Lemma task_stk_chk_valid_arguments_no_error__scan_loop_and_result :
  forall sg priority output,
  task_stk_chk_configuration sg -> task_stk_chk_valid_arguments priority output ->
  task_stack_check_argument_error sg priority output = None.
Proof.
  intros sg priority output [Hchecks [Hlowest Hself]]
    [Hbyte [Hpriority Houtput]].
  unfold task_stack_check_argument_error; rewrite Hchecks, Hlowest, Hself.
  rewrite (proj2 (Z.eqb_neq output 0) Houtput).
  destruct Hpriority as [Hpriority|Hpriority].
  - rewrite (proj2 (Z.ltb_ge 63 priority) Hpriority); reflexivity.
  - rewrite Hpriority, Z.eqb_refl, Bool.andb_false_r; reflexivity.
Qed.
Lemma task_stk_chk_scan_data_fields__scan_loop_and_result :
  forall snapshot region words count stop size,
  task_stk_chk_initialized_prefix snapshot region words count stop ->
  task_stack_scan_data size count =
    {| stackCheckFree := task_stk_chk_count count;
       stackCheckUsed := unsigned_last_nbits
         (size - task_stk_chk_count count) 32 |}.
Proof.
  intros snapshot region words count stop size Hprefix.
  pose proof (task_stk_chk_prefix_uint32_count__scan_loop_and_result
    snapshot region words count stop Hprefix) as Hcount.
  unfold task_stack_scan_data, Ucos2Verify.lib.kernel_resources.kernel_u32, task_stk_chk_count,
    unsigned_last_nbits in *.
  rewrite (Z.mod_small (Z.of_nat count) 4294967296) by exact Hcount.
  reflexivity.
Qed.
