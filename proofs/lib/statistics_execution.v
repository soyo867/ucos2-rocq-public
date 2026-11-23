Require Import Coq.ZArith.ZArith Coq.Bool.Bool Coq.Lists.List Coq.micromega.Lia.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_observation.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.statistics.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_state_machine.
Import UCOS2_C_Rules KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source/OS_TaskIdle, OSStatInit and OS_TaskStat segments.  These laws
    connect existing local operations to the whole invariant; they do not
    make an entire task loop atomic or authorize arbitrary ISR/callback
    interference.  The source caller must supply the actual changed cells
    and justify any observations retained across Restore.

    Original and statistics-sampling-variant updates remain separate.  In
    particular, the original zero-divisor execution has no defined update;
    it is not silently replaced by the repaired branch. *)

Lemma statistics_replace_preserves_validity : forall sg s post,
  UCOS2_state_inv sg s -> valid_statistics_configuration sg post ->
  UCOS2_state_inv sg (replace_StatsS post s).
Proof.
  intros sg s post Hvalid Hpost.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [replace_StatsS]; tauto.
Qed.

Definition statistics_modules (owner : UCOS2Module) : bool :=
  match owner with StatisticsModule => true | _ => false end.

Lemma statistics_update_selected_transition : forall sg update,
  (forall before, valid_statistics_configuration sg before ->
    valid_statistics_configuration sg (update before)) ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (update before.(StatsState)) before).
Proof.
  intros sg update Hupdate; constructor.
  - intros before after Hvalid ->.
    apply statistics_replace_preserves_validity; [exact Hvalid|].
    apply Hupdate; unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
  - intros before after Hvalid -> owner Hkept.
    destruct owner; simpl in Hkept; discriminate || reflexivity.
Qed.

Lemma statistics_enabled_update_preserves_configuration : forall sg update,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (forall s, valid_statistics_state s -> valid_statistics_state (update s)) ->
  forall s, valid_statistics_configuration sg s ->
    valid_statistics_configuration sg (update s).
Proof.
  intros sg update Henabled Hupdate s [Hvalid Hcfg].
  unfold valid_statistics_configuration; rewrite Henabled; split; [apply Hupdate; exact Hvalid|exact I].
Qed.

Lemma statistics_idle_selected_transition : forall sg,
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (statistics_idle_step before.(StatsState)) before).
Proof.
  intro sg; apply statistics_update_selected_transition.
  apply statistics_idle_step_preserves_configuration.
Qed.

Lemma statistics_reset_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (statistics_reset_counter before.(StatsState)) before).
Proof.
  intros sg Henabled; apply statistics_update_selected_transition.
  apply statistics_enabled_update_preserves_configuration; [exact Henabled|].
  apply statistics_reset_counter_preserves_validity.
Qed.

Lemma statistics_calibrate_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (statistics_calibrate before.(StatsState)) before).
Proof.
  intros sg Henabled; apply statistics_update_selected_transition.
  apply statistics_enabled_update_preserves_configuration; [exact Henabled|].
  apply statistics_calibrate_preserves_validity.
Qed.

Lemma statistics_scale_divisor_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (statistics_scale_divisor before.(StatsState)) before).
Proof.
  intros sg Henabled; apply statistics_update_selected_transition.
  apply statistics_enabled_update_preserves_configuration; [exact Henabled|].
  apply statistics_scale_divisor_preserves_validity.
Qed.

Lemma statistics_capture_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (snd (statistics_capture before.(StatsState))) before).
Proof.
  intros sg Henabled; apply (statistics_update_selected_transition sg
    (fun s => snd (statistics_capture s))).
  apply (statistics_enabled_update_preserves_configuration sg
    (fun s => snd (statistics_capture s))); [exact Henabled|].
  intros s Hvalid; exact (proj2 (statistics_capture_preserves_validity s Hvalid)).
Qed.

Lemma statistics_original_update_selected_transition : forall sg,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => exists post,
      statistics_original_update before.(StatsState) = Some post /\
      after = replace_StatsS post before).
Proof.
  intros sg Henabled; constructor.
  - intros before after Hvalid [post [Hstep ->]].
    apply statistics_replace_preserves_validity; [exact Hvalid|].
    unfold valid_statistics_configuration; rewrite Henabled; split; [|exact I].
    eapply statistics_original_preserves_machine_ranges; [|exact Hstep].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_statistics_configuration in Hvalid; tauto.
  - intros before after Hvalid [post [Hstep ->]] owner Hkept.
    destruct owner; simpl in Hkept; discriminate || reflexivity.
Qed.

Lemma statistics_repaired_update_selected_transition : forall sg sample,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  valid_statistics_sample sample ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after =>
      after = replace_StatsS (statistics_repaired_update sample before.(StatsState)) before).
Proof.
  intros sg sample Henabled Hsample; apply statistics_update_selected_transition.
  apply statistics_enabled_update_preserves_configuration; [exact Henabled|].
  intros; apply statistics_repaired_preserves_validity; assumption.
Qed.

(** The two stores which can change during usage/recalibration.  This
    residual retains the three other real statistics cells, not a ghost
    permission.  Merge requires their unchanged observations explicitly. *)
Definition statistics_rep_without_calibration_usage (sg : StableGlobVars)
  (s : StatisticsState) : Assertion :=
  sg.(g_OSIdleCtr) # UInt |-> s.(idleCtr) **
  sg.(g_OSIdleCtrRun) # UInt |-> s.(idleCtrRun) **
  sg.(g_OSStatRdy) # UChar |-> (if s.(statReady) then 1 else 0).

Lemma statistics_rep_split_calibration_usage : forall sg s,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg s |--
    sg.(g_OSIdleCtrMax) # UInt |-> s.(idleCtrMax) **
    sg.(g_OSCPUUsage) # UChar |-> s.(cpuUsage) **
    statistics_rep_without_calibration_usage sg s.
Proof.
  intros sg s Henabled; unfold statistics_rep, statistics_rep_without_calibration_usage;
    rewrite Henabled; entailer!.
Qed.

Lemma statistics_rep_merge_updated_calibration_usage : forall sg before after,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  before.(idleCtr) = after.(idleCtr) -> before.(idleCtrRun) = after.(idleCtrRun) ->
  before.(statReady) = after.(statReady) ->
  sg.(g_OSIdleCtrMax) # UInt |-> after.(idleCtrMax) **
    sg.(g_OSCPUUsage) # UChar |-> after.(cpuUsage) **
    statistics_rep_without_calibration_usage sg before |-- statistics_rep sg after.
Proof.
  intros sg before after Henabled Hctr Hrun Hready.
  unfold statistics_rep, statistics_rep_without_calibration_usage;
    rewrite Henabled, Hctr, Hrun, Hready; entailer!.
Qed.

Lemma statistics_repaired_update_resources_merge : forall sg s sample,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2_state_inv sg s -> valid_statistics_sample sample ->
  let post := statistics_repaired_update sample s.(StatsState) in
  sg.(g_OSIdleCtrMax) # UInt |-> post.(idleCtrMax) **
    sg.(g_OSCPUUsage) # UChar |-> post.(cpuUsage) **
    statistics_rep_without_calibration_usage sg s.(StatsState) **
    UCOS2_raw_rep_missing_module sg s StatisticsModule |--
    UCOS2_inv sg (replace_StatsS post s).
Proof.
  intros sg s sample Henabled Hvalid Hsample post.
  assert (Hpost : UCOS2_state_inv sg (replace_StatsS post s)).
  { apply statistics_replace_preserves_validity; [exact Hvalid|].
    apply statistics_enabled_update_preserves_configuration with
      (update := statistics_repaired_update sample); [exact Henabled| |].
    - intros; apply statistics_repaired_preserves_validity; assumption.
    - unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  sep_apply_l_atomic (statistics_rep_merge_updated_calibration_usage sg s.(StatsState) post
    Henabled eq_refl eq_refl eq_refl).
  apply (UCOS2_inv_merge_updated_module sg s (replace_StatsS post s) StatisticsModule Hpost).
  reflexivity.
Qed.

Lemma statistics_original_update_resources_merge : forall sg s post,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2_state_inv sg s -> statistics_original_update s.(StatsState) = Some post ->
  sg.(g_OSIdleCtrMax) # UInt |-> post.(idleCtrMax) **
    sg.(g_OSCPUUsage) # UChar |-> post.(cpuUsage) **
    statistics_rep_without_calibration_usage sg s.(StatsState) **
    UCOS2_raw_rep_missing_module sg s StatisticsModule |--
    UCOS2_inv sg (replace_StatsS post s).
Proof.
  intros sg s post Henabled Hvalid Hstep.
  assert (Hpost : UCOS2_state_inv sg (replace_StatsS post s)).
  { apply statistics_replace_preserves_validity; [exact Hvalid|].
    unfold valid_statistics_configuration; rewrite Henabled; split; [|exact I].
    eapply statistics_original_preserves_machine_ranges; [|exact Hstep].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_statistics_configuration in Hvalid; tauto. }
  assert (Hframe : s.(StatsState).(idleCtr) = post.(idleCtr) /\
    s.(StatsState).(idleCtrRun) = post.(idleCtrRun) /\
    s.(StatsState).(statReady) = post.(statReady)).
  { unfold statistics_original_update in Hstep.
    destruct (Z.eqb (idleCtrMax (StatsState s)) 0); [discriminate|].
    inversion Hstep; subst post; repeat split; reflexivity. }
  destruct Hframe as [Hctr [Hrun Hready]].
  sep_apply_l_atomic (statistics_rep_merge_updated_calibration_usage sg s.(StatsState) post
    Henabled Hctr Hrun Hready).
  apply (UCOS2_inv_merge_updated_module sg s (replace_StatsS post s) StatisticsModule Hpost).
  reflexivity.
Qed.


(** A scalar source instruction, kept separate from every possible
    environment interval.  Normalization is the existing selected ARM32
    C assignment conversion; the source operation is total in its value.
    Neither scaling nor usage followed by calibration is one instruction. *)
Inductive StatisticsStoreField : Type :=
| StatisticsUsageField
| StatisticsCalibrationField.

Definition statistics_store_value (field : StatisticsStoreField) (stored : Z) : Z :=
  match field with
  | StatisticsUsageField => kernel_u8 stored
  | StatisticsCalibrationField => kernel_u32 stored
  end.

Definition statistics_store_state (field : StatisticsStoreField) (stored : Z)
  (state : StatisticsState) : StatisticsState :=
  match field with
  | StatisticsUsageField =>
      {| idleCtr := state.(idleCtr); idleCtrMax := state.(idleCtrMax);
         idleCtrRun := state.(idleCtrRun); cpuUsage := kernel_u8 stored;
         statReady := state.(statReady) |}
  | StatisticsCalibrationField =>
      {| idleCtr := state.(idleCtr); idleCtrMax := kernel_u32 stored;
         idleCtrRun := state.(idleCtrRun); cpuUsage := state.(cpuUsage);
         statReady := state.(statReady) |}
  end.

Definition statistics_store_writes (sg : StableGlobVars)
  (field : StatisticsStoreField) (stored : Z) : list (addr * Mem.byte) :=
  match field with
  | StatisticsUsageField => [(sg.(g_OSCPUUsage), kernel_u8 stored)]
  | StatisticsCalibrationField => pointer_store_writes sg.(g_OSIdleCtrMax) (kernel_u32 stored)
  end.

Definition statistics_store_fragment sg field stored (before after : model) : Prop :=
  kernel_heap_execution (statistics_store_writes sg field stored) before after.

Inductive StatisticsLoadField : Type :=
| StatisticsReadyField
| StatisticsMaxField.

Definition statistics_load_value (field : StatisticsLoadField) (state : StatisticsState) : Z :=
  match field with
  | StatisticsReadyField => if state.(statReady) then 1 else 0
  | StatisticsMaxField => state.(idleCtrMax)
  end.

Definition statistics_load_fragment (sg : StableGlobVars)
  (field : StatisticsLoadField) (observed : Z) (heap : model) : Prop :=
  match field with
  | StatisticsReadyField => uchar_load sg.(g_OSStatRdy) observed heap
  | StatisticsMaxField => pointer_load sg.(g_OSIdleCtrMax) observed heap
  end.

(** UInt and Ptr share the selected 32-bit representation.  This equality
    of storage conditions is proved from that existing architecture, not
    assumed from an equal sizeof or introduced as a new layout law. *)
Lemma statistics_uint_pointer_rep : forall address stored,
  address # UInt |-> stored --||-- address # Ptr |-> stored.
Proof.
  intros address stored; unfold store_uint, store_ptr, isvalidptr_int,
    isvalidptr, valid_ptr_value, aligned_4, ptr_size_Z, ptr_size, addr_max_unsigned.
  cbn; replace (address + 4 - 1) with (address + 3) by lia.
  split; entailer!.
Qed.

Lemma statistics_framed_uint_store : forall address old stored (frame : Assertion) before,
  0 <= stored < 4294967296 -> (address # UInt |-> old ** frame) before ->
  exists after,
    kernel_heap_execution (pointer_store_writes address stored) before after /\
    (address # UInt |-> stored ** frame) after.
Proof.
  intros address old stored frame before Hrange Hbefore.
  assert (Hsplit : address # UInt |-> old ** frame |-- address # Ptr |->_ ** frame).
  { rewrite statistics_uint_pointer_rep.
    sep_apply_l_atomic (store_ptr_undef_store_ptr address old); entailer!. }
  destruct (framed_pointer_store_execution address stored frame before Hrange (Hsplit _ Hbefore))
    as [after [Hrun Hafter]].
  exists after; split; [exact Hrun|].
  assert (Hmerge : address # Ptr |-> stored ** frame |-- address # UInt |-> stored ** frame).
  { rewrite statistics_uint_pointer_rep; entailer!. }
  exact (Hmerge _ Hafter).
Qed.

Lemma statistics_store_preserves_validity : forall field stored state,
  valid_statistics_state state -> valid_statistics_state (statistics_store_state field stored state).
Proof.
  intros field stored state Hvalid; destruct field;
    unfold statistics_store_state, valid_statistics_state in *; cbn in *.
  - repeat split; try tauto; apply kernel_u8_in_range.
  - repeat split; try tauto; apply kernel_u32_in_range.
Qed.

Lemma statistics_store_selected_transition : forall sg field stored,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  UCOS2SelectedTransition sg statistics_modules
    (fun before after => after = replace_StatsS (statistics_store_state field stored before.(StatsState)) before).
Proof.
  intros; apply statistics_update_selected_transition.
  apply statistics_enabled_update_preserves_configuration; [assumption|].
  intros; apply statistics_store_preserves_validity; assumption.
Qed.

Definition statistics_store_cell (sg : StableGlobVars) (field : StatisticsStoreField) (stored : Z) : Assertion :=
  match field with
  | StatisticsUsageField => sg.(g_OSCPUUsage) # UChar |-> stored
  | StatisticsCalibrationField => sg.(g_OSIdleCtrMax) # UInt |-> stored
  end.

Definition statistics_stored_value (field : StatisticsStoreField) (state : StatisticsState) : Z :=
  match field with
  | StatisticsUsageField => state.(cpuUsage)
  | StatisticsCalibrationField => state.(idleCtrMax)
  end.

Definition statistics_rep_without_store (sg : StableGlobVars) (field : StatisticsStoreField)
  (state : StatisticsState) : Assertion :=
  match field with
  | StatisticsUsageField => statistics_rep_without_usage sg state
  | StatisticsCalibrationField =>
      sg.(g_OSIdleCtr) # UInt |-> state.(idleCtr) **
      sg.(g_OSIdleCtrRun) # UInt |-> state.(idleCtrRun) **
      sg.(g_OSCPUUsage) # UChar |-> state.(cpuUsage) **
      sg.(g_OSStatRdy) # UChar |-> (if state.(statReady) then 1 else 0)
  end.

Lemma statistics_rep_split_store : forall sg field state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_rep sg state |-- statistics_store_cell sg field (statistics_stored_value field state) **
    statistics_rep_without_store sg field state.
Proof.
  intros; destruct field; unfold statistics_rep, statistics_store_cell,
    statistics_stored_value, statistics_rep_without_store, statistics_rep_without_usage;
    rewrite H; entailer!.
Qed.

Lemma statistics_rep_merge_store : forall sg field stored state,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  statistics_store_cell sg field (statistics_store_value field stored) **
    statistics_rep_without_store sg field state |-- statistics_rep sg (statistics_store_state field stored state).
Proof.
  intros; destruct field; unfold statistics_rep, statistics_store_cell,
    statistics_store_value, statistics_store_state, statistics_rep_without_store,
    statistics_rep_without_usage; cbn; rewrite H; entailer!.
Qed.

Lemma statistics_store_cell_produces : forall sg field old stored (frame : Assertion) before,
  (statistics_store_cell sg field old ** frame) before ->
  exists after, statistics_store_fragment sg field stored before after /\
    (statistics_store_cell sg field (statistics_store_value field stored) ** frame) after.
Proof.
  intros sg field old stored frame before Hbefore; destruct field.
  - exact (kernel_heap_framed_uchar_store sg.(g_OSCPUUsage) old (kernel_u8 stored)
      frame before (kernel_u8_in_range stored) Hbefore).
  - exact (statistics_framed_uint_store sg.(g_OSIdleCtrMax) old (kernel_u32 stored)
      frame before (kernel_u32_in_range stored) Hbefore).
Qed.

Lemma statistics_store_produces_raw : forall sg field stored state (frame : Assertion) before,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_raw_rep sg state ** frame) before ->
  exists after, statistics_store_fragment sg field stored before after /\
    (UCOS2_raw_rep sg (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame) after.
Proof.
  intros sg field stored state frame before Henabled Hbefore.
  assert (Hsplit : UCOS2_raw_rep sg state ** frame |--
    statistics_store_cell sg field (statistics_stored_value field state.(StatsState)) **
    (statistics_rep_without_store sg field state.(StatsState) **
     UCOS2_raw_rep_missing_module sg state StatisticsModule ** frame)).
  { rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); cbn [UCOS2_module_rep].
    sep_apply_l_atomic (statistics_rep_split_store sg field state.(StatsState) Henabled); entailer!. }
  destruct (statistics_store_cell_produces sg field _ stored _ before (Hsplit _ Hbefore))
    as [after [Hrun Hafter]].
  assert (Hmissing : UCOS2_raw_rep_missing_module sg state StatisticsModule =
    UCOS2_raw_rep_missing_module sg
      (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) StatisticsModule).
  { apply UCOS2_raw_rep_missing_module_frame.
    intros owner Howner; destruct owner; try reflexivity; contradiction. }
  assert (Hmerge : statistics_store_cell sg field (statistics_store_value field stored) **
    (statistics_rep_without_store sg field state.(StatsState) **
     UCOS2_raw_rep_missing_module sg state StatisticsModule ** frame) |--
    UCOS2_raw_rep sg (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame).
  { sep_apply_l_atomic (statistics_rep_merge_store sg field stored state.(StatsState) Henabled).
    rewrite Hmissing. rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule).
    cbn [UCOS2_module_rep replace_StatsS]; entailer!. }
  exists after; split; [exact Hrun|exact (Hmerge _ Hafter)].
Qed.

(** Recover resources on the supplied actual endpoint, rather than
    substituting an unrelated heap obtained by an existence theorem. *)
Lemma statistics_store_raw_resources : forall sg field stored state (frame : Assertion) before after,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_raw_rep sg state ** frame) before ->
  statistics_store_fragment sg field stored before after ->
  (UCOS2_raw_rep sg (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame) after.
Proof.
  intros sg field stored state frame before after Henabled Hbefore Hrun.
  destruct (statistics_store_produces_raw sg field stored state frame before Henabled Hbefore)
    as [produced [Hproduced Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption).
  subst produced; exact Hpost.
Qed.

Lemma statistics_store_resources : forall sg field stored state (frame : Assertion) before after,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_inv sg state ** frame) before ->
  statistics_store_fragment sg field stored before after ->
  (UCOS2_inv sg (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame) after.
Proof.
  intros sg field stored state frame before after Henabled Hbefore Hrun.
  assert (Hsplit : UCOS2_inv sg state ** frame |--
    coq_prop (UCOS2_state_inv sg state) && (UCOS2_raw_rep sg state ** frame))
    by (unfold UCOS2_inv; entailer!).
  destruct (Hsplit _ Hbefore) as [Hvalid Hraw].
  change (UCOS2_state_inv sg state) in Hvalid.
  pose proof (statistics_store_raw_resources sg field stored state frame before after Henabled Hraw Hrun) as Hpost.
  assert (Hvalid_post : UCOS2_state_inv sg
    (replace_StatsS (statistics_store_state field stored state.(StatsState)) state)).
  { apply statistics_replace_preserves_validity; [exact Hvalid|].
    apply statistics_enabled_update_preserves_configuration with
      (update := statistics_store_state field stored); [exact Henabled| |].
    - intros; apply statistics_store_preserves_validity; assumption.
    - unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hmerge : UCOS2_raw_rep sg
    (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame |--
    UCOS2_inv sg (replace_StatsS (statistics_store_state field stored state.(StatsState)) state) ** frame).
  { unfold UCOS2_inv; entailer!. }
  exact (Hmerge _ Hpost).
Qed.

Lemma statistics_load_resources : forall sg field state (frame : Assertion) heap,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_raw_rep sg state ** frame) heap ->
  statistics_load_fragment sg field (statistics_load_value field state.(StatsState)) heap.
Proof.
  intros sg field state frame heap Henabled Hheap; destruct field.
  - apply framed_uchar_store_load with (frame := TT).
    assert (Hfocus : UCOS2_raw_rep sg state ** frame |--
      sg.(g_OSStatRdy) # UChar |-> (if state.(StatsState).(statReady) then 1 else 0) ** TT).
    { rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); cbn [UCOS2_module_rep].
      unfold statistics_rep; rewrite Henabled; entailer!; intros ? ?; exact I. }
    exact (Hfocus _ Hheap).
  - apply framed_pointer_store_load with (frame := TT).
    assert (Hfocus : UCOS2_raw_rep sg state ** frame |--
      sg.(g_OSIdleCtrMax) # Ptr |-> state.(StatsState).(idleCtrMax) ** TT).
    { rewrite UCOS2_raw_rep_split_module with (m := StatisticsModule); cbn [UCOS2_module_rep].
      unfold statistics_rep; rewrite Henabled, (statistics_uint_pointer_rep sg.(g_OSIdleCtrMax) state.(StatsState).(idleCtrMax));
        entailer!; intros ? ?; exact I. }
    exact (Hfocus _ Hheap).
Qed.

Lemma statistics_load_value_eq : forall sg field state (frame : Assertion) heap observed,
  sg.(osKernelConfig).(cfgStatisticsEnabled) = true ->
  (UCOS2_raw_rep sg state ** frame) heap ->
  statistics_load_fragment sg field observed heap ->
  observed = statistics_load_value field state.(StatsState).
Proof.
  intros sg field state frame heap observed Henabled Hheap Hload.
  pose proof (statistics_load_resources sg field state frame heap Henabled Hheap) as Hcurrent.
  destruct field; [eapply uchar_load_deterministic|eapply pointer_load_deterministic]; eassumption.
Qed.

Definition statistics_store_client (field : StatisticsStoreField) (stored : Z) : KernelClientAction :=
  {| kernel_client_actor := None; kernel_client_event_actor := None;
     kernel_client_stops := fun _ => false;
     kernel_client_step := fun sg before after =>
       sg.(osKernelConfig).(cfgStatisticsEnabled) = true /\
       after = replace_StatsS (statistics_store_state field stored before.(StatsState)) before |}.

Lemma statistics_store_client_certificate : forall field stored,
  KernelClientCertificate (statistics_store_client field stored).
Proof.
  intros field stored; constructor.
  - intros sg before after Hvalid [Henabled ->].
    apply statistics_replace_preserves_validity; [exact Hvalid|].
    apply statistics_enabled_update_preserves_configuration with
      (update := statistics_store_state field stored); [exact Henabled| |].
    + intros; apply statistics_store_preserves_validity; assumption.
    + unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto.
  - intros sg before after observer Hvalid [Henabled ->] Hactor; reflexivity.
  - intros sg before after observer origin Hvalid [Henabled ->] Hstop Hactive; exact Hactive.
  - intros sg before after observer Hvalid [Henabled ->] Hactor; reflexivity.
Qed.
