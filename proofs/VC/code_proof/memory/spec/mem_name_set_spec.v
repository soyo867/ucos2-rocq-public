Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String Coq.Logic.FunctionalExtensionality.
Require Export Ucos2Verify.VC.code.memory.spec.mem_query_spec.
Require Export Ucos2Verify.VC.code.task.spec.task_name_set_spec.
Require Export Ucos2Verify.lib.memory_execution.
From SimpleC.SL Require Import Mem SeparationLogic MapLib.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** A shared free control keeps its free-chain link and never acquires a
    partition. An allocated control updates the matching abstract name as
    well as its physical image. These are the effects of the one C store. *)
Definition mem_name_set_free_update (s : GlobMemoryState) id image name : GlobMemoryState :=
  {| memPartitions := s.(memPartitions); memFreeControls := s.(memFreeControls);
     memControlImages := kernel_map_set s.(memControlImages) id
       (Some (memory_control_set_field image MCBName name));
     memPrivateControls := s.(memPrivateControls);
     memNextGeneration := s.(memNextGeneration) |}.

Definition mem_name_set_pool_update (s : GlobMemoryState) id image name : GlobMemoryState :=
  match s.(memPartitions) id with
  | Some p => memory_replace_partition s id (memory_partition_set_name p name)
  | None => mem_name_set_free_update s id image name
  end.

Definition mem_name_set_update (view : MemQueryView) (s : UCOS2_Verify_State)
  (image : MemoryControlImage) name : UCOS2_Verify_State :=
  match view with
  | MemQueryRaw _ => s
  | MemQueryPool id => replace_MemoryS (mem_name_set_pool_update s.(MemoryState) id image name) s
  end.

Definition mem_name_set_updated_view (view : MemQueryView) name : MemQueryView :=
  match view with
  | MemQueryRaw image => MemQueryRaw (memory_control_set_field image MCBName name)
  | MemQueryPool id => MemQueryPool id
  end.

Lemma mem_name_set_partition_preserves_validity : forall id p name,
  valid_memory_partition id p -> valid_memory_partition id (memory_partition_set_name p name).
Proof. intros; exact H. Qed.

Lemma mem_name_set_free_preserves_validity : forall sg s id image name,
  valid_memory_state sg s -> s.(memPartitions) id = None ->
  s.(memControlImages) id = Some image ->
  valid_memory_state sg (mem_name_set_free_update s id image name).
Proof.
  intros sg s id image name [Hpool [Hparts [Hprivateimage [Hdomain [Hlinks Hprivate]]]]] Hnone Himage.
  assert (Hprivate_none : s.(memPrivateControls) id = None).
  { destruct (s.(memPrivateControls) id) as [p|] eqn:E; [|reflexivity].
    specialize (Hprivateimage id p E); congruence. }
  assert (Hid : 0 <= id < sg.(osKernelConfig).(cfgMaxMemPartitions)).
  { apply (proj1 (Hdomain id Hprivate_none)); eauto. }
  unfold valid_memory_state, mem_name_set_free_update; cbn.
  split; [exact Hpool|]. split.
  - intros j p Hp; destruct (Hparts j p Hp) as [Hj [Hvalid Hcontrol]].
    split; [exact Hj|]. split; [exact Hvalid|].
    rewrite kernel_map_set_other; [exact Hcontrol|congruence].
  - split.
    + intros j p Hp; rewrite kernel_map_set_other; [eapply Hprivateimage; eassumption|congruence].
    + split.
      * intros j Hj; destruct (Z.eq_dec j id) as [->|Hne].
        -- rewrite kernel_map_set_same; split; [intros; exact Hid|eauto].
        -- rewrite kernel_map_set_other by exact Hne; apply Hdomain; exact Hj.
      * split.
        -- intros pre j rest Hlist; destruct (Hlinks pre j rest Hlist) as [old [Hold Hnext]].
           destruct (Z.eq_dec j id) as [->|Hne].
           ++ assert (old = image) by congruence; subst old.
              exists (memory_control_set_field image MCBName name); split;
                [apply kernel_map_set_same|exact Hnext].
           ++ exists old; split; [rewrite kernel_map_set_other by exact Hne; exact Hold|exact Hnext].
        -- exact Hprivate.
Qed.

Lemma mem_name_set_pool_preserves_validity : forall sg s id image name,
  valid_memory_state sg s -> s.(memControlImages) id = Some image ->
  valid_memory_state sg (mem_name_set_pool_update s id image name).
Proof.
  intros sg s id image name Hvalid Himage; unfold mem_name_set_pool_update.
  destruct (s.(memPartitions) id) as [p|] eqn:Hp.
  - eapply memory_replace_partition_preserves_validity; [exact Hvalid|exact Hp|].
    apply mem_name_set_partition_preserves_validity.
    exact (proj1 (proj2 ((proj1 (proj2 Hvalid)) id p Hp))).
  - eapply mem_name_set_free_preserves_validity; eassumption.
Qed.

Lemma mem_name_set_pool_image : forall sg s id image name,
  valid_memory_state sg s -> s.(memControlImages) id = Some image ->
  (mem_name_set_pool_update s id image name).(memControlImages) id =
    Some (memory_control_set_field image MCBName name).
Proof.
  intros sg s id image name Hvalid Himage; unfold mem_name_set_pool_update.
  destruct (s.(memPartitions) id) as [p|] eqn:Hp; cbn.
  - pose proof (proj2 (proj2 ((proj1 (proj2 Hvalid)) id p Hp))) as E.
    assert (image = memory_partition_image p) by congruence; subst image.
    rewrite kernel_map_set_same, memory_partition_set_name_image_eq; reflexivity.
  - apply kernel_map_set_same.
Qed.

Lemma mem_name_set_pool_new_references : forall s id image name p,
  memory_name_reference (mem_name_set_pool_update s id image name) p ->
  memory_name_reference s p \/ p = name.
Proof.
  intros s id image name p; unfold mem_name_set_pool_update.
  destruct (s.(memPartitions) id) as [part|];
    intros [[j [v [Hv Hp]]]|[j [v [Hv Hp]]]].
  - change (kernel_map_set s.(memControlImages) id
      (Some (memory_partition_image (memory_partition_set_name part name))) j = Some v) in Hv.
    unfold kernel_map_set in Hv; destruct (Z.eq_dec j id).
    + inversion Hv; subst v; right; exact Hp.
    + left; left; exists j, v; auto.
  - left; right; exists j, v; auto.
  - change (kernel_map_set s.(memControlImages) id
      (Some (memory_control_set_field image MCBName name)) j = Some v) in Hv.
    unfold kernel_map_set in Hv; destruct (Z.eq_dec j id).
    + inversion Hv; subst v; right; exact Hp.
    + left; left; exists j, v; auto.
  - left; right; exists j, v; auto.
Qed.

Lemma mem_name_set_pool_new_roots : forall sg s id image name p,
  kernel_name_root sg (mem_name_set_update (MemQueryPool id) s image name) p ->
  kernel_name_root sg s p \/ p = name.
Proof.
  intros sg s id image name p [Ht|[He|[Hf|[[Hm [Hn Hr]]|Htm]]]].
  - left; left; exact Ht.
  - left; right; left; exact He.
  - left; right; right; left; exact Hf.
  - destruct (mem_name_set_pool_new_references s.(MemoryState) id image name p Hr) as [Hold|E].
    + left; right; right; right; left; auto.
    + right; exact E.
  - left; right; right; right; right; exact Htm.
Qed.

Lemma mem_name_set_pool_preserves_invariant : forall sg s id image name chars,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  s.(MemoryState).(memControlImages) id = Some image ->
  readable_name s.(NameState) name chars ->
  UCOS2_state_inv sg (mem_name_set_update (MemQueryPool id) s image name).
Proof.
  intros sg s id image name chars Henabled Hvalid Himage Hread.
  assert (Hnames : kernel_names_valid sg (mem_name_set_update (MemQueryPool id) s image name)).
  { eapply kernel_names_valid_add_root; [exact (UCOS2_state_inv_names_valid sg s Hvalid)|exact Hread|reflexivity|].
    intros; eapply mem_name_set_pool_new_roots; eassumption. }
  assert (Hmemory : valid_memory_configuration sg
    (mem_name_set_pool_update s.(MemoryState) id image name)).
  { unfold valid_memory_configuration; rewrite Henabled.
    apply mem_name_set_pool_preserves_validity; [|exact Himage].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_memory_configuration in Hvalid.
    rewrite Henabled in Hvalid; tauto. }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in *.
  cbn [mem_name_set_update replace_MemoryS] in *; tauto.
Qed.

(** Only a real shared publication consumes the Name owner's readable_name.
    Raw storage does not dereference pname, and all early errors are exempt. *)
Definition mem_name_set_admission critical sg invocation pe name view before : Prop :=
  pe <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  mem_query_admission critical sg invocation pe view before /\
  match view with
  | MemQueryRaw _ => True
  | MemQueryPool _ => exists chars, readable_name before.(NameState) name chars
  end.

Definition mem_name_set_name_available (view : MemQueryView)
  (s : UCOS2_Verify_State) name : Prop :=
  match view with
  | MemQueryRaw _ => True
  | MemQueryPool _ => exists chars, readable_name s.(NameState) name chars
  end.

Definition mem_name_set_nesting_address (sg : StableGlobVars) (nesting : addr) : Prop :=
  nesting = sg.(g_OSIntNesting).

Lemma mem_name_set_acquired_resources : forall critical sg invocation pe name view before entry,
  pe <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  mem_name_set_admission critical sg invocation pe name view before ->
  UCOS2_state_inv sg before -> critical_region_interval critical sg invocation before entry ->
  mem_query_admission critical sg invocation pe view before /\
  (exists image, mem_query_selected view entry image) /\
  mem_name_set_name_available view entry name.
Proof.
  intros critical sg invocation pe name view before entry Hpe Hname Hnest Hadmit Hvalid Hinterval.
  destruct (Hadmit Hpe Hname Hnest) as [Haccess Hread].
  split; [exact Haccess|]. split.
  - eapply mem_query_acquired_image; eassumption.
  - destruct view as [image|id]; [exact I|].
    destruct Hread as [chars Hread]; exists chars.
    rewrite <- (critical_region_interval_preserves_name_state critical sg invocation before entry Hinterval).
    exact Hread.
Qed.

Definition mem_name_set_step (view : MemQueryView) name
  (entry : UCOS2_Verify_State) : Z -> UCOS2_Verify_State -> Prop :=
  fun err checkpoint => exists image, mem_query_selected view entry image /\
    checkpoint = mem_name_set_update view entry image name /\ err = 0.

(** The result is the actual perr byte of this void API, not a C return
    value. The kernel endpoint is after Restore, not the protected snapshot.
    Exact raw-control resources are returned separately in the spatial post. *)
Definition mem_name_set_program critical sg invocation view pe name
  : program UCOS2_Verify_State Z :=
  if Z.eqb pe 0 then StateRelMonad.ret 96
  else if Z.eqb name 0 then StateRelMonad.ret 12
  else StateRelMonad.bind (get' task_name_set_nesting) (fun nesting =>
    if Z.ltb 0 nesting then StateRelMonad.ret 18
    else StateRelMonad.bind (update (critical_region_interval critical sg invocation)) (fun _ =>
      StateRelMonad.bind (mem_name_set_step view name) (fun err =>
        StateRelMonad.bind (update (critical_region_interval critical sg invocation))
          (fun _ => StateRelMonad.ret err)))).

Definition mem_name_set_safe critical sg invocation view pe name before
  (X : Z -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (mem_name_set_program critical sg invocation view pe name) X.

Lemma mem_name_set_program_null_control : forall critical sg invocation view name before,
  mem_name_set_program critical sg invocation view 0 name before 96 before.
Proof. intros; unfold mem_name_set_program; split; reflexivity. Qed.

Lemma mem_name_set_program_null_name : forall critical sg invocation view pe before,
  pe <> 0 -> mem_name_set_program critical sg invocation view pe 0 before 12 before.
Proof.
  intros; unfold mem_name_set_program; rewrite (proj2 (Z.eqb_neq _ _) H); split; reflexivity.
Qed.

Lemma mem_name_set_program_isr : forall critical sg invocation view pe name before,
  pe <> 0 -> name <> 0 -> 0 < task_name_set_nesting before ->
  mem_name_set_program critical sg invocation view pe name before 18 before.
Proof.
  intros critical sg invocation view pe name before Hpe Hname Hnest.
  unfold mem_name_set_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hname).
  exists (task_name_set_nesting before), before; split; [split; reflexivity|].
  rewrite (proj2 (Z.ltb_lt _ _) Hnest); split; reflexivity.
Qed.

Lemma mem_name_set_program_success : forall critical sg invocation view pe name before entry checkpoint current,
  pe <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  critical_region_interval critical sg invocation before entry ->
  mem_name_set_step view name entry 0 checkpoint ->
  critical_region_interval critical sg invocation checkpoint current ->
  mem_name_set_program critical sg invocation view pe name before 0 current.
Proof.
  intros critical sg invocation view pe name before entry checkpoint current Hpe Hname Hnest Hacquire Hstep Hrestore.
  unfold mem_name_set_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hname).
  exists (task_name_set_nesting before), before; split; [split; reflexivity|].
  rewrite Hnest; cbn.
  exists tt, entry; split; [exact Hacquire|].
  exists 0, checkpoint; split; [exact Hstep|].
  exists tt, current; split; [exact Hrestore|]; split; reflexivity.
Qed.

Lemma mem_name_set_safe_return : forall critical sg invocation view pe name before err current X,
  mem_name_set_program critical sg invocation view pe name before err current ->
  mem_name_set_safe critical sg invocation view pe name before X ->
  safeExec (eq current) (StateRelMonad.ret err) X.
Proof.
  intros critical sg invocation view pe name before err current X Hprogram Hsafe.
  eapply (highstependret_derive (mem_name_set_program critical sg invocation view pe name)
    (eq before) err (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; [exact Hprogram|reflexivity].
Qed.

Lemma mem_name_set_program_result_iff : forall critical sg invocation view pe name before err current,
  mem_name_set_program critical sg invocation view pe name before err current <->
  if Z.eqb pe 0 then err = 96 /\ before = current
  else if Z.eqb name 0 then err = 12 /\ before = current
  else if Z.ltb 0 (task_name_set_nesting before) then err = 18 /\ before = current
  else exists entry image,
    critical_region_interval critical sg invocation before entry /\
    mem_query_selected view entry image /\
    critical_region_interval critical sg invocation
      (mem_name_set_update view entry image name) current /\ err = 0.
Proof.
  intros critical sg invocation view pe name before err current.
  unfold mem_name_set_program; destruct (Z.eqb pe 0); [reflexivity|].
  destruct (Z.eqb name 0); [reflexivity|].
  unfold StateRelMonad.bind, get', get.
  split.
  - intros [nesting [observed [[Hnest Hstate] Htail]]]; subst nesting observed.
    destruct (Z.ltb 0 (task_name_set_nesting before)) eqn:E; [exact Htail|].
    destruct Htail as [u [entry [Hacquire [code [checkpoint [Hstep
      [v [returned [Hrestore [Hcode Hcurrent]]]]]]]]]].
    destruct Hstep as [image [Himage [Hcheckpoint Hzero]]].
    subst checkpoint returned code err; exists entry, image; auto.
  - intro H; exists (task_name_set_nesting before), before; split; [split; reflexivity|].
    destruct (Z.ltb 0 (task_name_set_nesting before)) eqn:E; [exact H|].
    destruct H as [entry [image [Hacquire [Himage [Hrestore Herr]]]]]; subst err.
    exists tt, entry; split; [exact Hacquire|].
    exists 0, (mem_name_set_update view entry image name); split.
    + exists image; repeat split; assumption || reflexivity.
    + exists tt, current; split; [exact Hrestore|split; reflexivity].
Qed.

Lemma mem_name_set_update_other_modules : forall view entry image name,
  let checkpoint := mem_name_set_update view entry image name in
  checkpoint.(TskState) = entry.(TskState) /\ checkpoint.(SchedState) = entry.(SchedState) /\
  checkpoint.(IntrState) = entry.(IntrState) /\ checkpoint.(EventState) = entry.(EventState) /\
  checkpoint.(TickState) = entry.(TickState) /\ checkpoint.(FlagState) = entry.(FlagState) /\
  checkpoint.(TimerState) = entry.(TimerState) /\ checkpoint.(StatsState) = entry.(StatsState) /\
  checkpoint.(ControlState) = entry.(ControlState) /\ checkpoint.(NameState) = entry.(NameState).
Proof. intros [old|id] entry image name; repeat split; reflexivity. Qed.

Lemma mem_name_set_pool_control_frame : forall s id image name,
  let updated := mem_name_set_pool_update s id image name in
  updated.(memFreeControls) = s.(memFreeControls) /\
  updated.(memPrivateControls) = s.(memPrivateControls) /\
  updated.(memNextGeneration) = s.(memNextGeneration) /\
  (forall other, other <> id -> updated.(memControlImages) other = s.(memControlImages) other) /\
  (forall other, other <> id -> updated.(memPartitions) other = s.(memPartitions) other).
Proof.
  intros s id image name; cbn zeta; unfold mem_name_set_pool_update; destruct (memPartitions s id);
    cbn; repeat split; intros; try reflexivity; apply kernel_map_set_other; assumption.
Qed.

Lemma mem_name_set_source_merge_updated : forall sg pe view entry image name,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  UCOS2_state_inv sg entry -> mem_query_address sg pe view ->
  mem_query_selected view entry image -> mem_name_set_name_available view entry name ->
  store_memory_control sg pe (memory_control_set_field image MCBName name) **
    mem_query_source_frame sg view entry |--
  UCOS2_inv sg (mem_name_set_update view entry image name) **
    mem_query_source_rep sg pe (mem_name_set_updated_view view name).
Proof.
  intros sg pe [original|id] entry image name Henabled Hvalid Haddress Himage Hread.
  - cbn [mem_query_selected] in Himage; subst image.
    cbn [mem_query_source_frame mem_name_set_update mem_name_set_updated_view mem_query_source_rep]; entailer!.
  - cbn [mem_query_address] in Haddress; subst pe.
    cbn [mem_query_selected] in Himage.
    destruct Hread as [chars Hread].
    pose proof (mem_name_set_pool_preserves_invariant sg entry id image name chars
      Henabled Hvalid Himage Hread) as Hupdated.
    assert (Hmemory : valid_memory_state sg entry.(MemoryState)).
    { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_memory_configuration in Hvalid.
      rewrite Henabled in Hvalid; tauto. }
    cbn [mem_query_source_frame mem_name_set_updated_view mem_query_source_rep].
    Intros.
    pose proof (UCOS2_inv_merge_updated_memory sg entry
      (mem_name_set_update (MemQueryPool id) entry image name) Hupdated eq_refl) as Hmerge.
    cbn [mem_name_set_update replace_MemoryS] in Hmerge.
    unfold memory_configured_rep in Hmerge; rewrite Henabled in Hmerge.
    sep_apply_r_atomic Hmerge.
    unfold mem_name_set_pool_update.
    destruct (entry.(MemoryState).(memPartitions) id) as [p|] eqn:Hp.
    + pose proof (proj2 (proj2 ((proj1 (proj2 Hmemory)) id p Hp))) as E.
      assert (image = memory_partition_image p) by congruence; subst image.
      rewrite <- memory_partition_set_name_image_eq.
      sep_apply_l_atomic (store_map_split
        (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) id p _ Hp).
      sep_apply_r_atomic (memory_raw_rep_merge_updated_partition sg entry.(MemoryState) id
        (memory_partition_set_name p name)).
      unfold memory_partition_rep, memory_raw_rep_without_partition.
      cbn [memory_partition_set_name memFreeBlocks].
      rewrite <- (store_memory_free_blocks_frame p (memory_partition_set_name p name)
        p.(memFreeBlocks) eq_refl eq_refl).
      entailer!.
    + unfold memory_raw_rep.
      sep_apply_l_atomic (memory_controls_merge_updated_control sg entry.(MemoryState)
        (mem_name_set_free_update entry.(MemoryState) id image name) id
        (memory_control_set_field image MCBName name) (kernel_map_set_same _ _ _ _)
        ltac:(intros; symmetry; apply kernel_map_set_other; assumption)).
      cbn [mem_name_set_free_update]; entailer!.
Qed.

Definition mem_name_set_field_frame sg pe view entry image : Assertion :=
  memory_control_without_field sg pe image MCBName ** mem_query_source_frame sg view entry.

Lemma mem_name_set_source_split_field : forall sg pe view entry image,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  sg.(osKernelConfig).(cfgMemoryNames) = true ->
  mem_query_address sg pe view -> mem_query_selected view entry image ->
  UCOS2_inv sg entry ** mem_query_source_rep sg pe view |--
    &(pe # "os_mem" ->ₛ "OSMemName") # Ptr |-> image.(memImageName) **
      mem_name_set_field_frame sg pe view entry image.
Proof.
  intros sg pe view entry image Henabled Hnames Haddress Himage.
  sep_apply_l_atomic (mem_query_source_split sg pe view entry image Henabled Haddress Himage).
  assert (Hin : In MCBName (memory_control_fields sg.(osKernelConfig))).
  { unfold memory_control_fields; rewrite Hnames; simpl; tauto. }
  sep_apply_l_atomic (store_memory_control_split_field sg pe image MCBName Hin).
  unfold mem_name_set_field_frame; cbn [memory_control_cell memory_control_value]; entailer!.
Qed.

Lemma mem_name_set_source_merge_updated_field : forall sg pe view entry image name,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  sg.(osKernelConfig).(cfgMemoryNames) = true -> UCOS2_state_inv sg entry ->
  mem_query_address sg pe view -> mem_query_selected view entry image ->
  mem_name_set_name_available view entry name ->
  &(pe # "os_mem" ->ₛ "OSMemName") # Ptr |-> name **
    mem_name_set_field_frame sg pe view entry image |--
  UCOS2_inv sg (mem_name_set_update view entry image name) **
    mem_query_source_rep sg pe (mem_name_set_updated_view view name).
Proof.
  intros sg pe view entry image name Henabled Hnames Hvalid Haddress Himage Hread.
  assert (Hin : In MCBName (memory_control_fields sg.(osKernelConfig))).
  { unfold memory_control_fields; rewrite Hnames; simpl; tauto. }
  unfold mem_name_set_field_frame.
  pose proof (store_memory_control_merge_updated_field sg pe image MCBName name Hin) as Hmerge.
  cbn [memory_control_cell] in Hmerge; sep_apply_l_atomic Hmerge.
  apply mem_name_set_source_merge_updated; assumption.
Qed.

Lemma mem_name_set_update_preserves_invariant : forall sg view entry image name,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg entry ->
  mem_query_selected view entry image -> mem_name_set_name_available view entry name ->
  UCOS2_state_inv sg (mem_name_set_update view entry image name).
Proof.
  intros sg [old|id] entry image name Henabled Hvalid Himage Hread; [exact Hvalid|].
  destruct Hread as [chars Hread]; eapply mem_name_set_pool_preserves_invariant; eassumption.
Qed.

Lemma mem_name_set_pool_runtime_step : forall s id image name,
  memory_runtime_step s (mem_name_set_pool_update s id image name).
Proof.
  intros; unfold mem_name_set_pool_update; destruct (memPartitions s id) eqn:Hp.
  - apply MemoryRuntimeSetName; exact Hp.
  - apply MemoryRuntimeFramesPartitions; reflexivity.
Qed.

Lemma mem_name_set_admission_early_error : forall critical sg invocation pe name view before,
  pe = 0 \/ name = 0 \/ task_name_set_nesting before <> 0 ->
  mem_name_set_admission critical sg invocation pe name view before.
Proof. unfold mem_name_set_admission; intros; tauto. Qed.

Lemma mem_name_set_program_has_result : forall critical sg invocation view pe name before,
  0 <= task_name_set_nesting before -> UCOS2_state_inv sg before ->
  mem_name_set_admission critical sg invocation pe name view before ->
  exists err current, mem_name_set_program critical sg invocation view pe name before err current.
Proof.
  intros critical sg invocation view pe name before Hnest Hvalid Hadmit.
  destruct (Z.eq_dec pe 0) as [->|Hpe].
  - exists 96, before; apply mem_name_set_program_null_control.
  - destruct (Z.eq_dec name 0) as [->|Hname].
    + exists 12, before; apply mem_name_set_program_null_name; exact Hpe.
    + destruct (Z_lt_dec 0 (task_name_set_nesting before)) as [Hisr|Htask].
      * exists 18, before; apply mem_name_set_program_isr; assumption.
      * assert (Hzero : task_name_set_nesting before = 0) by lia.
        destruct (Hadmit Hpe Hname Hzero) as [Haccess Hread].
        destruct (mem_query_acquired_image critical sg invocation pe view before before
          Haccess Hvalid ltac:(constructor)) as [image Himage].
        exists 0, (mem_name_set_update view before image name).
        eapply mem_name_set_program_success; try eassumption; try constructor.
        exists image; repeat split; assumption || reflexivity.
Qed.

Definition mem_name_set_return_resources platform critical sg invocation origin mask
  view pe name before current : Assertion :=
  if Z.eqb pe 0 then emp else if Z.eqb name 0 then emp else
  mutex_query_closed platform critical sg invocation origin mask current **
  (if Z.ltb 0 (task_name_set_nesting before) then emp else
    mem_query_source_rep sg pe (mem_name_set_updated_view view name)).

Definition mem_name_set_api_post platform critical sg invocation origin mask
  view pe name error_addr before (X : Z -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX err current,
    coq_prop (mem_name_set_program critical sg invocation view pe name before err current /\
      safeExec (eq current) (StateRelMonad.ret err) X) &&
    (mem_name_set_return_resources platform critical sg invocation origin mask
       view pe name before current ** error_addr # UChar |-> err).

(** The earlier annotation embedded these two Props as separated Assertions.
    Such an input is not equivalent to the native-Prop input at a fixed
    caller_frame: its two untyped heap pieces must remain owned. This rule
    transports them into the existing arbitrary caller frame. Both return
    rules below return that whole enlarged frame, as well as the exact API
    resources. NULL branches have no such carriers and keep their frame. *)
Lemma mem_name_set_nonnull_input_frame_equiv : forall platform critical sg invocation origin mask
  view pe name nesting_address before branch_resources caller_frame,
  coq_prop (mem_name_set_nesting_address sg nesting_address) **
    coq_prop (mem_name_set_admission critical sg invocation pe name view before) **
    mutex_query_closed platform critical sg invocation origin mask before **
    branch_resources ** caller_frame --||--
  coq_prop (mem_name_set_nesting_address sg nesting_address /\
    mem_name_set_admission critical sg invocation pe name view before) &&
    (mutex_query_closed platform critical sg invocation origin mask before **
     branch_resources ** (TT ** TT ** caller_frame)).
Proof. intros; split; entailer!. Qed.

(** These return rules consume the native Prop facts carried by the C
    annotation. The exact closed kernel, output cell and arbitrary caller
    frame are preserved; no separated pure carrier is discarded. *)
Lemma mem_name_set_isr_return : forall platform critical sg invocation origin mask
  view pe name error_addr before X caller_frame,
  pe <> 0 -> name <> 0 -> 0 < task_name_set_nesting before ->
  mem_name_set_safe critical sg invocation view pe name before X ->
  mutex_query_closed platform critical sg invocation origin mask before **
    error_addr # UChar |-> 18 ** caller_frame |--
  mem_name_set_api_post platform critical sg invocation origin mask
    view pe name error_addr before X ** caller_frame.
Proof.
  intros platform critical sg invocation origin mask view pe name error_addr before X
    caller_frame Hpe Hname Hnest Hsafe.
  pose proof (mem_name_set_program_isr critical sg invocation view pe name before
    Hpe Hname Hnest) as Hprogram.
  pose proof (mem_name_set_safe_return critical sg invocation view pe name before 18 before X
    Hprogram Hsafe) as Hreturn.
  unfold mem_name_set_api_post; Exists 18 before.
  unfold mem_name_set_return_resources.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hname),
    (proj2 (Z.ltb_lt _ _) Hnest).
  entailer!.
Qed.

Lemma mem_name_set_success_return : forall platform critical sg invocation origin mask saved
  view pe name error_addr before entry checkpoint X caller_frame,
  pe <> 0 -> name <> 0 -> task_name_set_nesting before = 0 ->
  mem_name_set_safe critical sg invocation view pe name before X ->
  mem_query_acquire_facts critical sg invocation mask saved before entry ->
  mem_name_set_step view name entry 0 checkpoint ->
  mem_query_restore_post platform critical sg invocation origin saved checkpoint **
    mem_query_source_rep sg pe (mem_name_set_updated_view view name) **
    error_addr # UChar |-> 0 ** caller_frame |--
  mem_name_set_api_post platform critical sg invocation origin mask
    view pe name error_addr before X ** caller_frame.
Proof.
  intros platform critical sg invocation origin mask saved view pe name error_addr
    before entry checkpoint X caller_frame Hpe Hname Hnest Hsafe Hacquire Hstep.
  destruct Hacquire as [Hinterval [Hbefore [Hentry [Hsaved Hmask]]]].
  unfold mem_query_restore_post; Intros current.
  match goal with
  | Hrestore : critical_region_interval critical sg invocation checkpoint current |- _ =>
      pose proof (mem_name_set_program_success critical sg invocation view pe name before
        entry checkpoint current Hpe Hname Hnest Hinterval Hstep Hrestore) as Hprogram
  end.
  pose proof (mem_name_set_safe_return critical sg invocation view pe name before 0 current X
    Hprogram Hsafe) as Hreturn.
  unfold mem_name_set_api_post; Exists 0 current.
  unfold mem_name_set_return_resources.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hname), Hnest.
  rewrite Hmask; entailer!.
Qed.
