Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import SetsClass.SetsClass.
Require Import AUXLib.Axioms.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
From SumLib Require Import ZRange.
From SimpleC.SL Require Import Mem SeparationLogic CArch.
From compcert.lib Require Import Integers.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.lib.memory.
Require Export Ucos2Verify.lib.memory_execution.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.error_codes.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.

Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(** OSMemCreate, V2.93.01 selected profile.  These are independently
    checkable parts of the API design.  In particular, the local resource
    lemmas below do NOT assert that an unmasked shared snapshot is stable,
    or that a pure client trace executes on the same physical heap. *)
Definition mem_create_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgMemoryEnabled) = true /\
  sg.(osKernelConfig).(cfgMemoryNames) = true.

Definition mem_create_argument_error (base count size : Z) : option OSErrCode :=
  memory_create_argument_error selected_kernel_configuration
    (kernel_u32 base) (kernel_u32 count) (kernel_u32 size).

Definition mem_create_arguments_valid (base count size : Z) : Prop :=
  mem_create_argument_error base count size = None.

(** A fact obtained from the three C argument cells, not an additional
    caller restriction.  It survives local-cell cleanup at early returns. *)
Definition mem_create_arguments_in_range (base count size : Z) : Prop :=
  0 <= base <= 4294967295 /\ 0 <= count <= 4294967295 /\ 0 <= size <= 4294967295.

Lemma mem_create_argument_error_null : forall count size,
  mem_create_argument_error 0 count size = Some OS_ERR_MEM_INVALID_ADDR.
Proof. reflexivity. Qed.

Lemma mem_create_alignment_guard_mod : forall base,
  Z.land (kernel_u32 base) 3 = kernel_u32 base mod 4.
Proof.
  intros; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity.
Qed.

Lemma mem_create_argument_error_alignment : forall base count size,
  kernel_u32 base <> 0 -> kernel_u32 base mod 4 <> 0 ->
  mem_create_argument_error base count size = Some OS_ERR_MEM_INVALID_ADDR.
Proof.
  intros base count size Hb Ha; unfold mem_create_argument_error,
    memory_create_argument_error; simpl.
  rewrite (proj2 (Z.eqb_neq _ _) Hb), (proj2 (Z.eqb_neq _ _) Ha); reflexivity.
Qed.

Lemma mem_create_argument_error_count : forall base count size,
  kernel_u32 base <> 0 -> kernel_u32 base mod 4 = 0 -> kernel_u32 count < 2 ->
  mem_create_argument_error base count size = Some OS_ERR_MEM_INVALID_BLKS.
Proof.
  intros base count size Hb Ha Hn; unfold mem_create_argument_error,
    memory_create_argument_error; simpl.
  rewrite (proj2 (Z.eqb_neq _ _) Hb), Ha, Z.eqb_refl.
  simpl; rewrite (proj2 (Z.ltb_lt _ _) Hn); reflexivity.
Qed.

Lemma mem_create_argument_error_size : forall base count size,
  kernel_u32 base <> 0 -> kernel_u32 base mod 4 = 0 ->
  2 <= kernel_u32 count -> kernel_u32 size < 4 ->
  mem_create_argument_error base count size = Some OS_ERR_MEM_INVALID_SIZE.
Proof.
  intros base count size Hb Ha Hn Hs; unfold mem_create_argument_error,
    memory_create_argument_error; simpl.
  rewrite (proj2 (Z.eqb_neq _ _) Hb), Ha, Z.eqb_refl.
  simpl; rewrite (proj2 (Z.ltb_ge _ _) Hn), (proj2 (Z.ltb_lt _ _) Hs); reflexivity.
Qed.

Lemma mem_create_argument_error_none_iff : forall base count size,
  mem_create_argument_error base count size = None <->
  kernel_u32 base <> 0 /\ kernel_u32 base mod 4 = 0 /\
  2 <= kernel_u32 count /\ 4 <= kernel_u32 size.
Proof.
  intros; unfold mem_create_argument_error, memory_create_argument_error; simpl.
  destruct (kernel_u32 base =? 0) eqn:Hb;
    destruct (kernel_u32 base mod 4 =? 0) eqn:Ha;
    destruct (kernel_u32 count <? 2) eqn:Hn;
    destruct (kernel_u32 size <? 4) eqn:Hs;
    simpl; repeat match goal with
    | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
    | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    end;
    split; intros; try discriminate; intuition lia.
Qed.

(** Detach transfers a pre-existing name root to the private descriptor;
    publication transfers that SAME root back.  Neither transition owns,
    reads, writes or duplicates string bytes. *)
Lemma mem_create_reserve_name_references : forall s base extent size count private post,
  memory_reserve_control s base extent size count = Some (private, post) ->
  forall name, memory_name_reference post name -> memory_name_reference s name.
Proof.
  intros s base extent size count private post Hreserve name Hname.
  unfold memory_reserve_control in Hreserve.
  destruct (memFreeControls s) as [|id rest]; [discriminate|].
  destruct (memControlImages s id) as [image|] eqn:Himage; [|discriminate].
  inversion Hreserve; subst; clear Hreserve.
  destruct Hname as [[other [v [Hlookup Hname]]]|[other [p [Hlookup Hname]]]];
    simpl in Hlookup; unfold kernel_map_set in Hlookup;
    destruct (Z.eq_dec other id) as [->|Hne].
  - discriminate.
  - left; exists other, v; auto.
  - inversion Hlookup; subst p; left; exists id, image; auto.
  - right; exists other, p; auto.
Qed.

Lemma mem_create_publish_name_references : forall s private,
  s.(memPrivateControls) private.(memPrivateSlot) = Some private ->
  forall name, memory_name_reference (memory_publish_control s private) name ->
    memory_name_reference s name.
Proof.
  intros s private Hprivate name Hname.
  destruct Hname as [[id [image [Hlookup Hname]]]|[id [p [Hlookup Hname]]]];
    simpl in Hlookup; unfold kernel_map_set in Hlookup;
    destruct (Z.eq_dec id (memPrivateSlot private)) as [->|Hne].
  - inversion Hlookup; subst image; right; exists (memPrivateSlot private), private;
      split; [exact Hprivate|exact Hname].
  - left; exists id, image; auto.
  - discriminate.
  - right; exists id, p; auto.
Qed.

Lemma mem_create_reserve_preserves_global_validity : forall sg s base extent size count private post,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  memory_reserve_control s.(MemoryState) base extent size count = Some (private, post) ->
  UCOS2_state_inv sg (replace_MemoryS post s).
Proof.
  intros sg s base extent size count private post Henabled Hvalid Hreserve.
  apply UCOS2_replace_memory_preserves_validity; [exact Hvalid| |].
  - unfold valid_memory_configuration; rewrite Henabled.
    eapply memory_reserve_preserves_state_validity; [|exact Hreserve].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      valid_memory_configuration in Hvalid; rewrite Henabled in Hvalid; tauto.
  - eapply mem_create_reserve_name_references; exact Hreserve.
Qed.

Lemma mem_create_publish_preserves_global_validity : forall sg s private,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  s.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = Some private ->
  memory_private_initialization_valid private ->
  UCOS2_state_inv sg (replace_MemoryS (memory_publish_control s.(MemoryState) private) s).
Proof.
  intros sg s private Henabled Hvalid Hprivate [Hregion _].
  apply UCOS2_replace_memory_preserves_validity; [exact Hvalid| |].
  - unfold valid_memory_configuration; rewrite Henabled.
    eapply memory_publish_preserves_state_validity; [|exact Hprivate|exact Hregion].
    unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      valid_memory_configuration in Hvalid; rewrite Henabled in Hvalid; tauto.
  - apply mem_create_publish_name_references; exact Hprivate.
Qed.

Lemma mem_create_reserve_resources_merge : forall sg s base extent size count private post,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  memory_reserve_control s.(MemoryState) base extent size count = Some (private, post) ->
  sg.(g_OSMemFreeList) # Ptr |-> private.(memPrivateImage).(memImageFree) **
  memory_raw_rep_without_free_root sg s.(MemoryState) **
  UCOS2_raw_rep_missing_memory sg s |--
    memory_private_control_rep sg private ** UCOS2_inv sg (replace_MemoryS post s).
Proof.
  intros sg s base extent size count private post Henabled Hvalid Hreserve.
  assert (Hmemory : valid_memory_state sg s.(MemoryState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      valid_memory_configuration in Hvalid; rewrite Henabled in Hvalid; tauto. }
  sep_apply_l_atomic (memory_reserve_reconstructs_raw_rep sg s.(MemoryState)
    base extent size count private post Hmemory Hreserve).
  pose proof (UCOS2_inv_merge_updated_memory sg s (replace_MemoryS post s)
    (mem_create_reserve_preserves_global_validity sg s base extent size count
      private post Henabled Hvalid Hreserve) eq_refl) as Hmerge.
  cbn [replace_MemoryS] in Hmerge; unfold memory_configured_rep in Hmerge;
    rewrite Henabled in Hmerge.
  sep_apply_r_atomic Hmerge; entailer!.
Qed.

Lemma mem_create_publish_resources_merge : forall sg s private,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg s ->
  s.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = Some private ->
  memory_private_initialization_valid private ->
  store_memory_control sg (memory_control_addr sg private.(memPrivateSlot))
    (memory_create_control_image private) **
  memory_private_linked_prefix_rep
    (memory_private_set_prefix private private.(memPrivateBlockCount)) **
  UCOS2_inv sg s |--
  UCOS2_inv sg (replace_MemoryS (memory_publish_control s.(MemoryState) private) s).
Proof.
  intros sg s private Henabled Hvalid Hprivate Hinit.
  assert (Hmemory : valid_memory_state sg s.(MemoryState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      valid_memory_configuration in Hvalid; rewrite Henabled in Hvalid; tauto. }
  destruct Hmemory as [_ [_ [Himages [_ [_ Hprivates]]]]].
  pose proof (Himages _ _ Hprivate) as Himage.
  pose proof (proj1 (proj2 (proj2 (Hprivates _ _ Hprivate)))) as Hpartition.
  assert (Hcount : 0 < private.(memPrivateBlockCount)).
  { destruct Hinit as [Hr _]; unfold memory_region_valid,
      memory_partition_initial in Hr; simpl in Hr; lia. }
  rewrite (memory_create_control_image_partition_eq private
    s.(MemoryState).(memNextGeneration) Hcount).
  rewrite (UCOS2_inv_split_memory sg s); unfold memory_configured_rep;
    rewrite Henabled; Intros.
  sep_apply_l_atomic (memory_publish_reconstructs_raw_rep sg s.(MemoryState)
    private Hinit Himage Hpartition).
  pose proof (UCOS2_inv_merge_updated_memory sg s
    (replace_MemoryS (memory_publish_control s.(MemoryState) private) s)
    (mem_create_publish_preserves_global_validity sg s private Henabled Hvalid Hprivate Hinit)
    eq_refl) as Hmerge.
  cbn [replace_MemoryS] in Hmerge; unfold memory_configured_rep in Hmerge;
    rewrite Henabled in Hmerge.
  sep_apply_r_atomic Hmerge; entailer!.
Qed.

(** A source-operation rely for the reservation currently owned by this
    call.  It does not strengthen the CPU contract.  [MemoryRuntimeStep]
    alone is insufficient: its frames-partitions branch leaves the private
    registry unconstrained.  Real foreign publishers must establish the
    distinct-slot premise from their own reservation/ownership protocol. *)
Inductive mem_create_foreign_step (protected : MemID)
  : GlobMemoryState -> GlobMemoryState -> Prop :=
| MemCreateForeignFrames : forall before after,
    after.(memPrivateControls) = before.(memPrivateControls) ->
    after.(memFreeControls) = before.(memFreeControls) ->
    mem_create_foreign_step protected before after
| MemCreateForeignGet : forall before id loan after,
    memory_get before id = Some (loan, after) ->
    mem_create_foreign_step protected before after
| MemCreateForeignPut : forall before id block after,
    memory_put before id block = Some after ->
    mem_create_foreign_step protected before after
| MemCreateForeignReserve : forall before base extent size count private after,
    private.(memPrivateSlot) <> protected ->
    memory_reserve_control before base extent size count = Some (private, after) ->
    mem_create_foreign_step protected before after
| MemCreateForeignPublish : forall before private,
    private.(memPrivateSlot) <> protected ->
    mem_create_foreign_step protected before (memory_publish_control before private).

Lemma mem_create_foreign_reserve_distinct : forall sg before protected owned
  base extent size count private after,
  valid_memory_state sg before ->
  before.(memPrivateControls) protected = Some owned ->
  memory_reserve_control before base extent size count = Some (private, after) ->
  private.(memPrivateSlot) <> protected.
Proof.
  intros sg before protected owned base extent size count private after
    [_ [_ [_ [_ [_ Hprivate]]]]] Howned Hreserve.
  pose proof (proj2 (proj2 (proj2 (Hprivate protected owned Howned)))) as Hnotfree.
  unfold memory_reserve_control in Hreserve.
  destruct (memFreeControls before) as [|head rest] eqn:Hfree; [discriminate|].
  destruct (memControlImages before head); [|discriminate].
  inversion Hreserve; subst; simpl; intro Hequal; subst head.
  apply Hnotfree; left; reflexivity.
Qed.

Lemma mem_create_private_controls_same_slot_conflict : forall sg first second,
  first.(memPrivateSlot) = second.(memPrivateSlot) ->
  memory_private_control_rep sg first ** memory_private_control_rep sg second |--
    coq_prop False.
Proof.
  intros sg first second Hslot; unfold memory_private_control_rep.
  rewrite !store_memory_control_layout_equiv, Hslot.
  set (base := memory_control_addr sg (memPrivateSlot second)).
  sepcon_right_assoc.
  sep_apply_l_atomic (dup_store_ptr
    (&(base # "os_mem" ->ₛ "OSMemAddr"))
    first.(memPrivateImage).(memImageBase) second.(memPrivateImage).(memImageBase));
    entailer!.
Qed.

Lemma mem_create_private_controls_distinct : forall sg first second,
  memory_private_control_rep sg first ** memory_private_control_rep sg second |--
    coq_prop (first.(memPrivateSlot) <> second.(memPrivateSlot)) &&
    (memory_private_control_rep sg first ** memory_private_control_rep sg second).
Proof.
  intros sg first second; destruct (Z.eq_dec first.(memPrivateSlot) second.(memPrivateSlot)).
  - prop_apply (mem_create_private_controls_same_slot_conflict sg first second e);
      Intros; contradiction.
  - entailer!.
Qed.

Lemma mem_create_foreign_step_preserves_reservation : forall protected before after,
  mem_create_foreign_step protected before after ->
  after.(memPrivateControls) protected = before.(memPrivateControls) protected.
Proof.
  intros protected before after Hstep; destruct Hstep.
  - rewrite H; reflexivity.
  - unfold memory_get in H; destruct (memPartitions before id); [|discriminate].
    destruct (memory_get_partition id m) as [[l p]|]; [|discriminate].
    inversion H; reflexivity.
  - unfold memory_put in H; destruct (memPartitions before id); [|discriminate].
    inversion H; reflexivity.
  - unfold memory_reserve_control in H0.
    destruct (memFreeControls before) as [|id rest]; [discriminate|].
    destruct (memControlImages before id); [|discriminate].
    inversion H0; subst; simpl in *; apply kernel_map_set_other; congruence.
  - simpl; apply kernel_map_set_other; congruence.
Qed.

Lemma mem_create_foreign_step_preserves_empty_controls : forall protected before after,
  mem_create_foreign_step protected before after ->
  before.(memFreeControls) = [] -> after.(memFreeControls) = [].
Proof.
  intros protected before after Hstep Hempty; destruct Hstep.
  - rewrite H0; exact Hempty.
  - unfold memory_get in H; destruct (memPartitions before id); [|discriminate].
    destruct (memory_get_partition id m) as [[l p]|]; [|discriminate].
    inversion H; exact Hempty.
  - unfold memory_put in H; destruct (memPartitions before id); [|discriminate].
    inversion H; exact Hempty.
  - unfold memory_reserve_control in H0; rewrite Hempty in H0; discriminate.
  - exact Hempty.
Qed.

Definition mem_create_client_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (protected : MemID) : Prop :=
  forall action before after,
    critical_region_clients critical action -> kernel_client_actor action <> Some invocation ->
    kernel_client_step action sg before after ->
    mem_create_foreign_step protected before.(MemoryState) after.(MemoryState).

Lemma mem_create_interval_preserves_reservation : forall critical sg invocation protected before after,
  mem_create_client_protocol critical sg invocation protected ->
  critical_region_interval critical sg invocation before after ->
  after.(MemoryState).(memPrivateControls) protected =
    before.(MemoryState).(memPrivateControls) protected.
Proof.
  intros critical sg invocation protected before after Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  induction Hinterval as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH].
  - reflexivity.
  - rewrite IH; apply mem_create_foreign_step_preserves_reservation;
      eapply Hprotocol; eassumption.
Qed.

Lemma mem_create_interval_preserves_empty_controls : forall critical sg invocation protected before after,
  mem_create_client_protocol critical sg invocation protected ->
  critical_region_interval critical sg invocation before after ->
  before.(MemoryState).(memFreeControls) = [] -> after.(MemoryState).(memFreeControls) = [].
Proof.
  intros critical sg invocation protected before after Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  induction Hinterval as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intro Hempty; [exact Hempty|].
  apply IH; eapply mem_create_foreign_step_preserves_empty_controls;
    [eapply Hprotocol; eassumption|exact Hempty].
Qed.

Lemma mem_create_task_creation_foreign_step : forall protected action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  mem_create_foreign_step protected before.(MemoryState) after.(MemoryState).
Proof.
  intros protected action sg before after [_ [_ ->]]; destruct action;
    apply MemCreateForeignFrames; reflexivity.
Qed.

(** Public C rely: every foreign action has an actual Memory source shape,
    but its slot is NOT fixed to differ from every possible reservation.
    This admits foreign reserve/publish.  The same physical detached MCB
    returned in Restore's ordinary SL frame rules out publication of OUR
    slot at the actual endpoint; no ownership fact is added to the CPU. *)
Definition mem_create_source_protocol critical sg invocation : Prop :=
  forall action before after,
    critical_region_clients critical action -> kernel_client_actor action <> Some invocation ->
    kernel_client_step action sg before after ->
    exists protected, mem_create_foreign_step protected before.(MemoryState) after.(MemoryState).

Lemma mem_create_source_reserve_allowed : forall before base extent size count private after,
  memory_reserve_control before base extent size count = Some (private, after) ->
  exists protected, mem_create_foreign_step protected before after.
Proof.
  intros; exists (private.(memPrivateSlot) + 1).
  eapply MemCreateForeignReserve with (private := private); [lia|eassumption].
Qed.

Lemma mem_create_source_publish_allowed : forall before private,
  exists protected, mem_create_foreign_step protected before (memory_publish_control before private).
Proof. intros; exists (private.(memPrivateSlot) + 1); apply MemCreateForeignPublish; lia. Qed.

Definition mem_create_reservation_status (state : GlobMemoryState)
  (private : MemoryPrivatePartition) : Prop :=
  ~ In private.(memPrivateSlot) state.(memFreeControls) /\
  (state.(memPrivateControls) private.(memPrivateSlot) = Some private \/
   state.(memPrivateControls) private.(memPrivateSlot) = None).

Lemma mem_create_source_step_preserves_reservation_status : forall protected before after private,
  mem_create_foreign_step protected before after ->
  mem_create_reservation_status before private -> mem_create_reservation_status after private.
Proof.
  intros protected before after private Hstep [Hfree Hstatus]; destruct Hstep.
  - unfold mem_create_reservation_status; rewrite H, H0; auto.
  - unfold memory_get in H; destruct (memPartitions before id); [|discriminate].
    destruct (memory_get_partition id m) as [[l p]|]; [|discriminate].
    inversion H; subst; split; assumption.
  - unfold memory_put in H; destruct (memPartitions before id); [|discriminate].
    inversion H; subst; split; assumption.
  - unfold memory_reserve_control in H0.
    destruct (memFreeControls before) as [|head rest] eqn:Hhead; [discriminate|].
    destruct (memControlImages before head); [|discriminate].
    inversion H0; subst; unfold mem_create_reservation_status; simpl.
    assert (Hd : memPrivateSlot private <> head) by (simpl in Hfree; intuition).
    rewrite kernel_map_set_other by exact Hd; split; [|exact Hstatus].
    simpl in Hfree; tauto.
  - unfold mem_create_reservation_status; simpl; split; [exact Hfree|].
    destruct (Z.eq_dec (memPrivateSlot private) (memPrivateSlot private0)) as [Hequal|Hdifferent].
    + rewrite Hequal, kernel_map_set_same; right; reflexivity.
    + rewrite kernel_map_set_other by exact Hdifferent; exact Hstatus.
Qed.

Lemma mem_create_source_interval_reservation_status : forall critical sg invocation before after private,
  mem_create_source_protocol critical sg invocation ->
  critical_region_interval critical sg invocation before after ->
  mem_create_reservation_status before.(MemoryState) private ->
  mem_create_reservation_status after.(MemoryState) private.
Proof.
  intros critical sg invocation before after private Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  induction Hinterval as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intro Hstatus; [exact Hstatus|].
  destruct (Hprotocol action before middle Hin Hforeign Hstep) as [protected Hmemory].
  apply IH; eapply mem_create_source_step_preserves_reservation_status; eassumption.
Qed.

Lemma mem_create_source_interval_preserves_empty_controls : forall critical sg invocation before after,
  mem_create_source_protocol critical sg invocation ->
  critical_region_interval critical sg invocation before after ->
  before.(MemoryState).(memFreeControls) = [] -> after.(MemoryState).(memFreeControls) = [].
Proof.
  intros critical sg invocation before after Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  induction Hinterval as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intro Hempty; [exact Hempty|].
  destruct (Hprotocol action before middle Hin Hforeign Hstep) as [protected Hmemory].
  apply IH; eapply mem_create_foreign_step_preserves_empty_controls; eassumption.
Qed.

Lemma mem_create_unregistered_private_control_conflict : forall sg state private,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  0 <= private.(memPrivateSlot) < sg.(osKernelConfig).(cfgMaxMemPartitions) ->
  state.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = None ->
  UCOS2_inv sg state ** memory_private_control_rep sg private |-- coq_prop False.
Proof.
  intros sg state private Henabled Hslot Hnone whole Howned.
  pose proof Howned as [shared [detached [Hjoin [[Hvalid Hraw] Hprivate]]]].
  change (UCOS2_state_inv sg state) in Hvalid.
  assert (Hmemory : valid_memory_state sg state.(MemoryState)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
      valid_memory_configuration in Hvalid; rewrite Henabled in Hvalid; tauto. }
  destruct Hmemory as [_ [_ [_ [Himages _]]]].
  destruct (proj2 (Himages _ Hnone) Hslot) as [image Himage].
  set (control := memory_control_addr sg private.(memPrivateSlot)).
  assert (Hconflict : UCOS2_inv sg state ** memory_private_control_rep sg private |-- coq_prop False).
  { rewrite (UCOS2_inv_split_memory sg state); Intros.
    unfold memory_configured_rep; rewrite Henabled.
    unfold memory_raw_rep; sepcon_right_assoc.
    sep_apply_l_atomic (memory_controls_split_control sg state.(MemoryState)
      private.(memPrivateSlot) image Himage).
    unfold memory_private_control_rep; rewrite !store_memory_control_layout_equiv.
    fold control; sepcon_right_assoc.
    sep_apply_l_atomic (dup_store_ptr
      (&(control # "os_mem" ->ₛ "OSMemAddr"))
      image.(memImageBase) private.(memPrivateImage).(memImageBase)); entailer!. }
  exact (Hconflict whole Howned).
Qed.

Lemma mem_create_source_interval_private_frame_preserves_reservation :
  forall critical sg invocation before after private,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  valid_memory_state sg before.(MemoryState) ->
  before.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = Some private ->
  mem_create_source_protocol critical sg invocation ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_inv sg after ** memory_private_control_rep sg private |--
    coq_prop (after.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = Some private) &&
    (UCOS2_inv sg after ** memory_private_control_rep sg private).
Proof.
  intros critical sg invocation before after private Henabled Hvalid Hprivate Hprotocol Hinterval.
  destruct Hvalid as [_ [_ [_ [_ [_ Hprivates]]]]].
  destruct (Hprivates _ _ Hprivate) as [Hslot [_ [_ Hfree]]].
  assert (Hstatus : mem_create_reservation_status after.(MemoryState) private).
  { eapply mem_create_source_interval_reservation_status; [exact Hprotocol|exact Hinterval|].
    split; [exact Hfree|left; exact Hprivate]. }
  destruct Hstatus as [_ [Hsame|Hnone]].
  - entailer!.
  - prop_apply (mem_create_unregistered_private_control_conflict sg after private
      Henabled Hslot Hnone); Intros; contradiction.
Qed.

(** The C for-loop performs precisely the nonfinal links.  The final NULL
    is a separate store after its exit.  Prefix advancement is local: none
    of these operations changes the global private registry. *)
Lemma mem_create_prefix_valid : forall private i,
  memory_private_initialization_valid private ->
  0 <= i <= private.(memPrivateBlockCount) ->
  memory_private_initialization_valid (memory_private_set_prefix private i).
Proof.
  intros private i [Hregion [Hextent _]] Hi.
  split; [exact Hregion|]; split; assumption.
Qed.

Lemma mem_create_prefix_set_twice : forall private first second,
  memory_private_set_prefix (memory_private_set_prefix private first) second =
    memory_private_set_prefix private second.
Proof. intros []; reflexivity. Qed.

Lemma mem_create_loop_next_link : forall private i,
  i < private.(memPrivateBlockCount) - 1 ->
  memory_initialize_next_link (memory_private_set_prefix private i) =
    Some ((private.(memPrivateBase) + i * private.(memPrivateBlockSize),
      private.(memPrivateBase) + (i + 1) * private.(memPrivateBlockSize)),
      memory_private_set_prefix private (i + 1)).
Proof.
  intros private i Hi; unfold memory_initialize_next_link; simpl.
  rewrite (proj2 (Z.ltb_lt i (memPrivateBlockCount private)) ltac:(lia)),
    (proj2 (Z.eqb_neq (i + 1) (memPrivateBlockCount private)) ltac:(lia)),
    mem_create_prefix_set_twice; reflexivity.
Qed.

Lemma mem_create_loop_store_merge : forall private i,
  memory_private_initialization_valid private ->
  0 <= i < private.(memPrivateBlockCount) - 1 ->
  (private.(memPrivateBase) + i * private.(memPrivateBlockSize)) # Ptr |->
    (private.(memPrivateBase) + (i + 1) * private.(memPrivateBlockSize)) **
  memory_private_next_link_frame (memory_private_set_prefix private i) |--
    memory_private_linked_prefix_rep (memory_private_set_prefix private (i + 1)).
Proof.
  intros private i Hvalid Hi; eapply memory_private_linked_prefix_merge_next_word.
  - apply mem_create_prefix_valid; [exact Hvalid|lia].
  - apply mem_create_loop_next_link; lia.
Qed.

Lemma mem_create_tail_null_store_merge : forall private,
  memory_private_initialization_valid private ->
  (private.(memPrivateBase) + (private.(memPrivateBlockCount) - 1) *
    private.(memPrivateBlockSize)) # Ptr |-> 0 **
  memory_private_next_link_frame
    (memory_private_set_prefix private (private.(memPrivateBlockCount) - 1)) |--
  memory_private_linked_prefix_rep
    (memory_private_set_prefix private private.(memPrivateBlockCount)).
Proof.
  intros private Hvalid.
  assert (Hcount : 2 <= private.(memPrivateBlockCount)).
  { destruct Hvalid as [Hr _]; unfold memory_region_valid,
      memory_partition_initial in Hr; simpl in Hr; lia. }
  pose proof (memory_initialize_next_link_last_store
    (memory_private_set_prefix private (private.(memPrivateBlockCount) - 1))
    ltac:(simpl; lia)) as Hstep.
  rewrite mem_create_prefix_set_twice in Hstep; simpl in Hstep.
  eapply memory_private_linked_prefix_merge_next_word; [|exact Hstep].
  apply mem_create_prefix_valid; [exact Hvalid|lia].
Qed.

Lemma mem_create_loop_variant : forall count i,
  0 <= i < count - 1 -> 0 <= count - 1 - (i + 1) < count - 1 - i.
Proof. intros; lia. Qed.

Lemma mem_create_arena_byte_in_block : forall private output,
  memory_private_initialization_valid private ->
  private.(memPrivateBase) <= output <
    private.(memPrivateBase) + private.(memPrivateBlockCount) * private.(memPrivateBlockSize) ->
  exists block offset,
    0 <= block < private.(memPrivateBlockCount) /\
    0 <= offset < private.(memPrivateBlockSize) /\
    output = private.(memPrivateBase) + block * private.(memPrivateBlockSize) + offset.
Proof.
  intros private output [Hregion _] Houtput.
  unfold memory_region_valid, memory_partition_initial in Hregion; simpl in Hregion.
  exists ((output - memPrivateBase private) / memPrivateBlockSize private),
    ((output - memPrivateBase private) mod memPrivateBlockSize private).
  pose proof (Z.mod_pos_bound (output - memPrivateBase private)
    (memPrivateBlockSize private) ltac:(lia)) as Hmod.
  pose proof (Z.div_mod (output - memPrivateBase private)
    (memPrivateBlockSize private) ltac:(lia)) as Hdiv.
  assert (Hlower : 0 <= (output - memPrivateBase private) / memPrivateBlockSize private).
  { apply Z.div_pos; lia. }
  assert (Hupper : (output - memPrivateBase private) / memPrivateBlockSize private <
    memPrivateBlockCount private).
  { apply Z.div_lt_upper_bound; nia. }
  repeat split; try lia; nia.
Qed.

(** This parameterized return relation records the remaining source/C-RG
    obligation explicitly.  It is NOT a completed API contract: the caller
    of the theorem must supply the very private execution that produced
    its resource endpoint.  There is no assertion that an arbitrary raw
    heap or a validity predicate produces such an execution. *)
Definition mem_create_acquire (base count size : Z)
  : program UCOS2_Verify_State (option MemoryPrivatePartition) :=
  fun entry selected checkpoint =>
    (entry.(MemoryState).(memFreeControls) = [] /\ selected = None /\ checkpoint = entry) \/
    (exists private post,
      memory_reserve_control entry.(MemoryState) (kernel_u32 base)
        (kernel_u32 size * kernel_u32 count) (kernel_u32 size) (kernel_u32 count) =
        Some (private, post) /\ selected = Some private /\
      checkpoint = replace_MemoryS post entry).

Definition mem_create_program_with_private_return
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (base count size : Z)
  (private_return : MemoryPrivatePartition -> program UCOS2_Verify_State (addr * Z))
  : program UCOS2_Verify_State (addr * Z) :=
  match mem_create_argument_error base count size with
  | Some error => StateRelMonad.ret (0, encode_os_err_code error)
  | None => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
      (fun _ => StateRelMonad.bind (mem_create_acquire base count size)
        (fun selected => StateRelMonad.bind (update (critical_region_interval critical sg invocation))
          (fun _ => match selected with
            | None => StateRelMonad.ret (0, 90)
            | Some private => private_return private
            end)))
  end.

Lemma mem_create_program_argument_return : forall critical sg invocation base count size
  private_return before error,
  mem_create_argument_error base count size = Some error ->
  mem_create_program_with_private_return critical sg invocation base count size private_return
    before (0, encode_os_err_code error) before.
Proof.
  intros; unfold mem_create_program_with_private_return; rewrite H.
  split; reflexivity.
Qed.

Lemma mem_create_reserve_nonempty : forall sg state base count size,
  valid_memory_state sg state -> state.(memFreeControls) <> [] ->
  exists private post,
    memory_reserve_control state base (size * count) size count = Some (private, post).
Proof.
  intros sg state base count size Hvalid Hnonempty.
  destruct (memFreeControls state) as [|head rest] eqn:Hfree; [contradiction|].
  destruct Hvalid as [_ [_ [_ [_ [Hlinks _]]]]].
  destruct (Hlinks [] head rest Hfree) as [old [Himage Hnext]].
  unfold memory_reserve_control; rewrite Hfree, Himage; eauto.
Qed.

Lemma mem_create_program_empty_return : forall critical sg invocation base count size
  private_return before entry current,
  mem_create_argument_error base count size = None ->
  critical_region_interval critical sg invocation before entry ->
  entry.(MemoryState).(memFreeControls) = [] ->
  critical_region_interval critical sg invocation entry current ->
  mem_create_program_with_private_return critical sg invocation base count size private_return
    before (0, 90) current.
Proof.
  intros critical sg invocation base count size private_return before entry current
    Hargs Hentry Hempty Hcurrent.
  unfold mem_create_program_with_private_return; rewrite Hargs.
  unfold StateRelMonad.bind; exists tt, entry; split; [exact Hentry|].
  exists None, entry; split; [left; auto|].
  exists tt, current; split; [exact Hcurrent|]; split; reflexivity.
Qed.

Lemma mem_create_program_private_return : forall critical sg invocation base count size
  private_return before entry private post restored outcome current,
  mem_create_argument_error base count size = None ->
  critical_region_interval critical sg invocation before entry ->
  memory_reserve_control entry.(MemoryState) (kernel_u32 base)
    (kernel_u32 size * kernel_u32 count) (kernel_u32 size) (kernel_u32 count) =
    Some (private, post) ->
  critical_region_interval critical sg invocation (replace_MemoryS post entry) restored ->
  private_return private restored outcome current ->
  mem_create_program_with_private_return critical sg invocation base count size private_return
    before outcome current.
Proof.
  intros critical sg invocation base count size private_return before entry private post restored
    outcome current Hargs Hentry Hreserve Hrestore Hprivate.
  unfold mem_create_program_with_private_return; rewrite Hargs.
  unfold StateRelMonad.bind; exists tt, entry; split; [exact Hentry|].
  exists (Some private), (replace_MemoryS post entry); split.
  - right; exists private, post; auto.
  - exists tt, restored; split; assumption.
Qed.

Lemma mem_create_program_safe_return : forall critical sg invocation base count size
  private_return before outcome current (X : (addr * Z) -> UCOS2_Verify_State -> Prop),
  mem_create_program_with_private_return critical sg invocation base count size private_return
    before outcome current ->
  safeExec (eq before)
    (mem_create_program_with_private_return critical sg invocation base count size private_return) X ->
  safeExec (eq current) (StateRelMonad.ret outcome) X.
Proof.
  intros critical sg invocation base count size private_return before outcome current X Hrun Hsafe.
  eapply (highstependret_derive
    (mem_create_program_with_private_return critical sg invocation base count size private_return)
    (eq before) outcome (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

(** A genuine byte hole, suitable for a payload output.  Its byte is not
    also owned by the arena.  After the actual final store the byte can be
    merged back, while an observation is retained on the SAME whole heap. *)
Definition mem_create_bytes_missing_output (base extent output : Z) : Assertion :=
  UCharArray.undef_missing_i base (output - base) 0 extent.

Lemma mem_create_bytes_split_output : forall base extent output,
  base <= output < base + extent ->
  UCharArray.undef_full base extent |-- output # UChar |->_ **
    mem_create_bytes_missing_output base extent output.
Proof.
  intros base extent output Hrange.
  pose proof (UCharArray.undef_full_split_to_undef_missing_i base
    (output - base) extent ltac:(lia)) as Hsplit.
  unfold StoreUCharAsElement.undefstoreA in Hsplit; simpl in Hsplit.
  replace (base + (output - base) * 1) with output in Hsplit by ring; exact Hsplit.
Qed.

Lemma mem_create_bytes_merge_output : forall base extent output value,
  base <= output < base + extent ->
  output # UChar |-> value ** mem_create_bytes_missing_output base extent output |--
    UCharArray.undef_full base extent.
Proof.
  intros base extent output value Hrange.
  sep_apply_l_atomic (store_uchar_undef_store_uchar output value).
  pose proof (UCharArray.undef_missing_i_merge_to_undef_full base
    (output - base) extent ltac:(lia)) as Hmerge.
  unfold StoreUCharAsElement.undefstoreA in Hmerge; simpl in Hmerge.
  replace (base + (output - base) * 1) with output in Hmerge by ring; exact Hmerge.
Qed.

Definition mem_create_linked_block_missing_output (private : MemoryPrivatePartition)
  (block output : Z) : Assertion :=
  (private.(memPrivateBase) + block * private.(memPrivateBlockSize)) # Ptr |->
    (if Z.eqb (block + 1) private.(memPrivateBlockCount) then 0
      else private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize)) **
  mem_create_bytes_missing_output
    (private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4)
    (private.(memPrivateBlockSize) - 4) output.

Lemma mem_create_linked_block_split_payload_output : forall private block output,
  private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4 <= output <
    private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize) ->
  memory_private_linked_block_rep private block |--
    output # UChar |->_ ** mem_create_linked_block_missing_output private block output.
Proof.
  intros private block output Houtput.
  unfold memory_private_linked_block_rep, mem_create_linked_block_missing_output.
  sep_apply_l_atomic (mem_create_bytes_split_output
    (memPrivateBase private + block * memPrivateBlockSize private + 4)
    (memPrivateBlockSize private - 4) output ltac:(nia)); entailer!.
Qed.

Lemma mem_create_linked_block_merge_payload_output : forall private block output value,
  private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4 <= output <
    private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize) ->
  output # UChar |-> value ** mem_create_linked_block_missing_output private block output |--
    memory_private_linked_block_rep private block.
Proof.
  intros private block output value Houtput.
  unfold memory_private_linked_block_rep, mem_create_linked_block_missing_output.
  sep_apply_l_atomic (mem_create_bytes_merge_output
    (memPrivateBase private + block * memPrivateBlockSize private + 4)
    (memPrivateBlockSize private - 4) output value ltac:(nia)); entailer!.
Qed.

Definition mem_create_linked_arena_missing_output (private : MemoryPrivatePartition)
  (left : list Z) (block : Z) (right : list Z) (output : Z) : Assertion :=
  iter_sepcon (map (memory_private_linked_block_rep private) left) **
  mem_create_linked_block_missing_output private block output **
  iter_sepcon (map (memory_private_linked_block_rep private) right) **
  UCharArray.undef_full
    (private.(memPrivateBase) + private.(memPrivateBlockCount) * private.(memPrivateBlockSize)) 0.

Lemma mem_create_linked_arena_split_payload_output : forall private left block right output,
  private.(memPrivateLinkedPrefix) = private.(memPrivateBlockCount) ->
  Zrange 0 private.(memPrivateBlockCount) = left ++ block :: right ->
  private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4 <= output <
    private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize) ->
  memory_private_linked_prefix_rep private |--
    output # UChar |->_ ** mem_create_linked_arena_missing_output private left block right output.
Proof.
  intros private left block right output Hdone Hrange Houtput.
  unfold memory_private_linked_prefix_rep, mem_create_linked_arena_missing_output.
  rewrite Hdone, Z.sub_diag, Z.mul_0_l, Hrange, map_app.
  change (map (memory_private_linked_block_rep private) (block :: right)) with
    ([memory_private_linked_block_rep private block] ++
      map (memory_private_linked_block_rep private) right).
  rewrite !derivable1_sepcon_iter_sepcon2.
  rewrite (derivable1_iter_sepcon_l [memory_private_linked_block_rep private block]); simpl.
  sep_apply_l_atomic (mem_create_linked_block_split_payload_output private block output Houtput);
    entailer!.
Qed.

Lemma mem_create_linked_arena_merge_payload_output : forall private left block right output value,
  private.(memPrivateLinkedPrefix) = private.(memPrivateBlockCount) ->
  Zrange 0 private.(memPrivateBlockCount) = left ++ block :: right ->
  private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4 <= output <
    private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize) ->
  output # UChar |-> value ** mem_create_linked_arena_missing_output private left block right output |--
    memory_private_linked_prefix_rep private.
Proof.
  intros private left block right output value Hdone Hrange Houtput.
  unfold memory_private_linked_prefix_rep, mem_create_linked_arena_missing_output.
  rewrite Hdone, Z.sub_diag, Z.mul_0_l, Hrange, map_app.
  change (map (memory_private_linked_block_rep private) (block :: right)) with
    ([memory_private_linked_block_rep private block] ++
      map (memory_private_linked_block_rep private) right).
  rewrite <- !derivable1_sepcon_iter_sepcon1.
  rewrite <- (derivable1_iter_sepcon_r [memory_private_linked_block_rep private block]); simpl.
  sep_apply_l_atomic (mem_create_linked_block_merge_payload_output private block output value Houtput);
    entailer!.
Qed.

Lemma mem_create_output_store_with_frame : forall output old value (frame : Assertion) heap,
  0 <= value < 256 -> (output # UChar |-> old ** frame) heap ->
  exists after, kernel_heap_execution [(output, value)] heap after /\
    (output # UChar |-> value ** frame) after.
Proof. exact kernel_heap_framed_uchar_store. Qed.

(** A raw endpoint retains the genuine byte cut used by the final C store.
    [initialized] may include the complete initialized private control,
    arena, and the current shared residual.  Its old output byte is owned
    only once.  The final assertion owns the SAME residual plus the actual
    zero byte; it does not claim [initialized] still holds after an alias
    changed a link or metadata byte.  The pure entailment reconstructs the
    pre-store representation, never supplies a future environment trace. *)
Definition mem_create_output_cut (initialized : Assertion) (output previous : Z)
  (residual : Assertion) : Assertion :=
  coq_prop (output # UChar |-> previous ** residual |-- initialized) &&
    (output # UChar |-> previous ** residual).

Definition mem_create_word_bytes (base b0 b1 b2 b3 : Z) : Assertion :=
  base # UChar |-> b0 ** (base + 1) # UChar |-> b1 **
  (base + 2) # UChar |-> b2 ** (base + 3) # UChar |-> b3.

Lemma mem_create_pointer_bytes_equiv : forall base word,
  base # Ptr |-> word --||--
  EX b0 : Z, EX b1 : Z, EX b2 : Z, EX b3 : Z,
    coq_prop (isvalidptr base /\ valid_ptr_value word /\ merge_int b0 b1 b2 b3 word) &&
      mem_create_word_bytes base b0 b1 b2 b3.
Proof.
  intros base word.
  change (base # Ptr |-> word) with
    (coq_prop (isvalidptr base /\ valid_ptr_value word) && store_4byte base word).
  split.
  - unfold store_4byte; Intros b0 b1 b2 b3.
    Exists (Byte.unsigned (Byte.repr b0)) (Byte.unsigned (Byte.repr b1))
      (Byte.unsigned (Byte.repr b2)) (Byte.unsigned (Byte.repr b3)).
    unfold mem_create_word_bytes, store_uchar.
    pose proof (Byte.unsigned_range_2 (Byte.repr b0)).
    pose proof (Byte.unsigned_range_2 (Byte.repr b1)).
    pose proof (Byte.unsigned_range_2 (Byte.repr b2)).
    pose proof (Byte.unsigned_range_2 (Byte.repr b3)).
    entailer!.
    + assert (Hbyte0 : store_byte base b0 |--
        store_byte base (Byte.unsigned (Byte.repr b0)))
        by (apply store_byte_eqm, Byte.eqm_unsigned_repr).
      assert (Hbyte1 : store_byte (base + 1) b1 |--
        store_byte (base + 1) (Byte.unsigned (Byte.repr b1)))
        by (apply store_byte_eqm, Byte.eqm_unsigned_repr).
      assert (Hbyte2 : store_byte (base + 2) b2 |--
        store_byte (base + 2) (Byte.unsigned (Byte.repr b2)))
        by (apply store_byte_eqm, Byte.eqm_unsigned_repr).
      assert (Hbyte3 : store_byte (base + 3) b3 |--
        store_byte (base + 3) (Byte.unsigned (Byte.repr b3)))
        by (apply store_byte_eqm, Byte.eqm_unsigned_repr).
      sepcon_right_assoc.
      sep_apply_l_atomic Hbyte0; sep_apply_l_atomic Hbyte1;
        sep_apply_l_atomic Hbyte2; sep_apply_l_atomic Hbyte3; entailer!.
    + unfold isvalidptr_char, isvalidptr, ptr_size_Z, Arch32.ptr_size_Z,
        Arch32.ptr_size in *; simpl in *; lia.
    + unfold isvalidptr_char, isvalidptr, ptr_size_Z, Arch32.ptr_size_Z,
        Arch32.ptr_size in *; simpl in *; lia.
    + unfold isvalidptr_char, isvalidptr, ptr_size_Z, Arch32.ptr_size_Z,
        Arch32.ptr_size in *; simpl in *; lia.
    + unfold isvalidptr_char, isvalidptr, ptr_size_Z, Arch32.ptr_size_Z,
        Arch32.ptr_size in *; simpl in *; lia.
    + eapply merge_int_eqm; try apply Byte.eqm_unsigned_repr; eassumption.
  - Intros b0 b1 b2 b3.
    unfold store_4byte, mem_create_word_bytes, store_uchar.
    Exists b0 b1 b2 b3; entailer!.
Qed.

Definition mem_create_word_byte (b0 b1 b2 b3 offset : Z) : Z :=
  if Z.eqb offset 0 then b0 else if Z.eqb offset 1 then b1
  else if Z.eqb offset 2 then b2 else b3.

Definition mem_create_word_bytes_missing (base b0 b1 b2 b3 offset : Z) : Assertion :=
  if Z.eqb offset 0 then
    (base + 1) # UChar |-> b1 ** (base + 2) # UChar |-> b2 ** (base + 3) # UChar |-> b3
  else if Z.eqb offset 1 then
    base # UChar |-> b0 ** (base + 2) # UChar |-> b2 ** (base + 3) # UChar |-> b3
  else if Z.eqb offset 2 then
    base # UChar |-> b0 ** (base + 1) # UChar |-> b1 ** (base + 3) # UChar |-> b3
  else
    base # UChar |-> b0 ** (base + 1) # UChar |-> b1 ** (base + 2) # UChar |-> b2.

Lemma mem_create_word_bytes_split_output : forall base b0 b1 b2 b3 offset,
  0 <= offset < 4 ->
  mem_create_word_bytes base b0 b1 b2 b3 --||--
    (base + offset) # UChar |-> mem_create_word_byte b0 b1 b2 b3 offset **
      mem_create_word_bytes_missing base b0 b1 b2 b3 offset.
Proof.
  intros base b0 b1 b2 b3 offset Hoffset.
  assert (offset = 0 \/ offset = 1 \/ offset = 2 \/ offset = 3) by lia.
  destruct H as [-> | [-> | [-> | ->]]]; unfold mem_create_word_byte,
    mem_create_word_bytes_missing, mem_create_word_bytes; simpl;
    try rewrite Z.add_0_r; split; entailer!.
Qed.

Lemma mem_create_pointer_byte_cut_reconstruct : forall base word b0 b1 b2 b3 offset,
  0 <= offset < 4 -> isvalidptr base -> valid_ptr_value word ->
  merge_int b0 b1 b2 b3 word ->
  (base + offset) # UChar |-> mem_create_word_byte b0 b1 b2 b3 offset **
    mem_create_word_bytes_missing base b0 b1 b2 b3 offset |-- base # Ptr |-> word.
Proof.
  intros base word b0 b1 b2 b3 offset Hoffset Hbase Hword Hmerge.
  rewrite <- (proj2 (mem_create_pointer_bytes_equiv base word)).
  Exists b0 b1 b2 b3.
  sep_apply_l_atomic (proj2 (mem_create_word_bytes_split_output base b0 b1 b2 b3 offset Hoffset));
    entailer!.
Qed.

Lemma mem_create_pointer_split_output_cut : forall base word offset,
  0 <= offset < 4 ->
  base # Ptr |-> word |-- EX previous : Z, EX residual : Assertion,
    mem_create_output_cut (base # Ptr |-> word) (base + offset) previous residual.
Proof.
  intros base word offset Hoffset.
  rewrite (proj1 (mem_create_pointer_bytes_equiv base word)); Intros b0 b1 b2 b3.
  Exists (mem_create_word_byte b0 b1 b2 b3 offset)
    (mem_create_word_bytes_missing base b0 b1 b2 b3 offset).
  unfold mem_create_output_cut.
  pose proof (mem_create_pointer_byte_cut_reconstruct base word b0 b1 b2 b3 offset
    Hoffset ltac:(tauto) ltac:(tauto) ltac:(tauto)) as Hreconstruct.
  sep_apply_l_atomic (proj1 (mem_create_word_bytes_split_output base b0 b1 b2 b3 offset Hoffset));
    entailer!.
Qed.

Definition mem_create_raw_output_post (initialized : Assertion) (output : Z) : Assertion :=
  EX previous : Z, EX residual : Assertion,
    coq_prop (output # UChar |-> previous ** residual |-- initialized) &&
      (output # UChar |-> 0 ** residual).

Lemma mem_create_output_cut_frame : forall initialized output previous residual frame,
  mem_create_output_cut initialized output previous residual ** frame |--
    mem_create_output_cut (initialized ** frame) output previous (residual ** frame).
Proof.
  intros initialized output previous residual frame; unfold mem_create_output_cut; Intros.
  assert (Hreconstruct : output # UChar |-> previous ** (residual ** frame) |-- initialized ** frame).
  { sep_apply_l_atomic H; entailer!. }
  entailer!.
Qed.

Lemma mem_create_output_cut_reconstructs_input : forall initialized output previous residual,
  mem_create_output_cut initialized output previous residual |-- initialized.
Proof.
  intros initialized output previous residual heap [Hreconstruct Howned];
    apply Hreconstruct; exact Howned.
Qed.

Lemma mem_create_output_store_raw_post : forall initialized output previous residual,
  coq_prop (output # UChar |-> previous ** residual |-- initialized) &&
    (output # UChar |-> 0 ** residual) |-- mem_create_raw_output_post initialized output.
Proof.
  intros; unfold mem_create_raw_output_post; Intros;
    Exists previous residual; entailer!.
Qed.

Lemma mem_create_raw_output_observation : forall initialized output heap,
  mem_create_raw_output_post initialized output heap ->
  KernelHeapObservation.uchar_load output 0 heap.
Proof.
  intros initialized output heap [previous [residual [Hreconstruct Howned]]].
  eapply KernelHeapObservation.framed_uchar_store_load; exact Howned.
Qed.

Lemma mem_create_zero_byte_alias_preserves_initialized : forall initialized output residual,
  (output # UChar |-> 0 ** residual |-- initialized) ->
  output # UChar |-> 0 ** residual |--
    initialized && mem_create_raw_output_post initialized output.
Proof.
  intros initialized output residual Hreconstruct heap Howned; split.
  - apply Hreconstruct; exact Howned.
  - exists 0, residual; split; assumption.
Qed.

Lemma mem_create_payload_output_example :
  4096 + 4 <= 4100 < 4096 + 8 /\
  4100 <> 4096 /\ 4100 <> 4104 /\
  memory_create_argument_error selected_kernel_configuration 4096 2 8 = None.
Proof. repeat split; try lia; reflexivity. Qed.

(** An in-range output can instead hit a link byte.  This records the
    concrete last write, not a C implementation-defect claim: an API may
    expose this wider source-readable mode only with its raw endpoint.
    The initialized-partition consequence cannot apply to this endpoint. *)
Lemma mem_create_output_store_byte : forall output before after,
  kernel_heap_execution [(output, 0)] before after ->
  after.(ConAssertion.s_mem) output = value 0.
Proof.
  intros output before after [Hwrite _].
  inversion Hwrite; subst.
  match goal with Htail : kernel_heap_writes [] _ _ |- _ => inversion Htail; subst end.
  apply mem_update_eq.
Qed.

Lemma mem_create_link_output_changes_initial_pointer : forall before after,
  kernel_heap_execution [(4096, 0)] before after ->
  ~ KernelHeapObservation.pointer_load 4096 4104 after.
Proof.
  intros before after Hwrite [Hrange [a [b [c [d [Ha [Hb [Hc [Hd Hmerge]]]]]]]]].
  pose proof (mem_create_output_store_byte 4096 before after Hwrite) as Hzero.
  rewrite Hzero in Ha; inversion Ha; subst a.
  change (4104 = b mod 256 * 256 + c mod 256 * 65536 + d mod 256 * 16777216) in Hmerge.
  lia.
Qed.

(** Checked rejection of the insufficient old runtime shape.  This is a
    model-interface counterexample, not a claim that a kernel C client can
    execute this replacement. *)
Definition mem_create_clear_private_registry (s : GlobMemoryState) : GlobMemoryState :=
  {| memPartitions := s.(memPartitions); memFreeControls := s.(memFreeControls);
     memControlImages := s.(memControlImages); memPrivateControls := fun _ => None;
     memNextGeneration := s.(memNextGeneration) |}.

Lemma mem_create_runtime_shape_can_drop_reservation : forall s id private,
  s.(memPrivateControls) id = Some private ->
  memory_runtime_step s (mem_create_clear_private_registry s) /\
  (mem_create_clear_private_registry s).(memPrivateControls) id <> Some private /\
  forall sg, memory_raw_rep sg (mem_create_clear_private_registry s) = memory_raw_rep sg s.
Proof.
  intros; split; [apply MemoryRuntimeFramesPartitions; reflexivity|].
  split; [discriminate|reflexivity].
Qed.

(** The output byte is permitted to overlap an owned arena, control or
    shared field.  Accessibility is a property of the resource footprint,
    not a second separated ownership of the same byte.  In particular it
    is established before executing a store and contains no future trace. *)
Definition mem_create_byte_access (owned : Assertion) (output : addr) : Prop :=
  forall heap, owned heap -> isvalidptr_char output /\
    heap.(ConAssertion.s_mem) output <> Noperm.

Definition mem_create_replace_byte (heap : mem) (output : addr) (old : mem_var) : mem :=
  fun address => if addr_eqb address output then old else heap address.

Definition mem_create_output_residual (owned : Assertion) (output : addr) : Assertion :=
  fun rest => rest.(ConAssertion.s_mem) output = Noperm /\
    exists old, old <> Noperm /\
      owned (kernel_state_with_memory rest
        (mem_create_replace_byte rest.(ConAssertion.s_mem) output old)).

(** QCP permits noncanonical integer encodings of a byte.  The logical
    observation is [value], but the physical byte uses the SAME encoding
    returned by the actual UChar cell.  This is a last-store relation,
    not a new execution model for the preceding C statements. *)
Definition mem_create_output_effect (output value : Z) (before after : model) : Prop :=
  exists encoded, Byte.eqm value encoded /\
    after.(ConAssertion.s_mem) = mem_byte_update before.(ConAssertion.s_mem) output encoded /\
    after.(ConAssertion.s_STS) = before.(ConAssertion.s_STS) /\
    after.(ConAssertion.s_token) = before.(ConAssertion.s_token).

Definition mem_create_overwritten (owned : Assertion) (output value : Z) : Assertion :=
  fun after => exists before, owned before /\ mem_create_output_effect output value before after.

Lemma mem_create_byte_access_consequence : forall first second output,
  first |-- second -> mem_create_byte_access second output ->
  mem_create_byte_access first output.
Proof. intros first second output Hent Haccess heap Hfirst; apply Haccess, Hent, Hfirst. Qed.

Lemma mem_create_replace_removed_byte : forall heap output,
  mem_create_replace_byte (mem_remove heap output) output (heap output) = heap.
Proof.
  intros; apply functional_extensionality; intro address.
  unfold mem_create_replace_byte, mem_remove.
  destruct (addr_eqb address output) eqn:Hequal; [|reflexivity].
  apply addr_eqb_eq in Hequal; subst; reflexivity.
Qed.

Lemma mem_create_byte_access_split : forall owned output,
  mem_create_byte_access owned output ->
  owned |-- output # UChar |->_ ** mem_create_output_residual owned output.
Proof.
  intros owned output Haccess whole Howned.
  destruct (Haccess whole Howned) as [Haddress Hpermission].
  set (old := whole.(ConAssertion.s_mem) output).
  set (cell := ConAssertion.mk_Lstate
    (mem_create_replace_byte empty_mem output old) Sets.full Sets.empty : model).
  set (rest := kernel_state_with_memory whole (mem_remove whole.(ConAssertion.s_mem) output)).
  exists cell, rest; split.
  - split.
    + intro address; unfold cell, rest, kernel_state_with_memory; simpl.
      unfold mem_create_replace_byte, mem_remove, empty_mem.
      destruct (addr_eqb address output) eqn:Hequal.
      * apply addr_eqb_eq in Hequal; subst address.
        unfold old; destruct (ConAssertion.s_mem whole output) eqn:Hbyte;
          try contradiction; eauto 8.
      * destruct (ConAssertion.s_mem whole address); eauto 8.
    + unfold cell, rest, kernel_state_with_memory; simpl.
      unfold ConAssertion.TokenSet_join, ConAssertion.STS_state_join.
      sets_unfold; tauto.
  - split.
    + unfold cell; unfold undef_store_uchar, store_byte_noninit, mstore_noninit; simpl.
      split; [exact Haddress|].
      split; [sets_unfold; tauto|]; split; [sets_unfold; tauto|].
      unfold old in *; destruct (ConAssertion.s_mem whole output) eqn:Hbyte;
        try contradiction.
      * left; reflexivity.
      * right; exists b; reflexivity.
    + split.
      * unfold rest, kernel_state_with_memory; simpl; apply mem_remove_eq.
      * exists old; split; [exact Hpermission|].
        unfold rest, kernel_state_with_memory; simpl.
        rewrite mem_create_replace_removed_byte.
        destruct whole; exact Howned.
Qed.

Lemma mem_create_byte_access_from_split : forall owned output residual,
  owned |-- output # UChar |->_ ** residual ->
  mem_create_byte_access owned output.
Proof.
  intros owned output residual Hsplit whole Howned.
  destruct (Hsplit whole Howned) as
    [cell [rest [[Hjoin Hsts] [[Haddress [Hcellsts [Hcelltokens Hcellmem]]] Hrest]]]].
  split; [exact Haddress|].
  assert (Hcellowned : ConAssertion.s_mem cell output <> Noperm).
  { destruct Hcellmem as [Hcellmem|[old Hcellmem]]; rewrite Hcellmem;
      [unfold single_Noninit_mem|unfold single_byte_mem]; rewrite addr_eqb_refl; discriminate. }
  specialize (Hjoin output).
  destruct Hjoin as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[b [? [? ?]]]|[b [? [? ?]]]]]]]; congruence.
Qed.

Lemma mem_create_payload_byte_access_example : forall frame,
  mem_create_byte_access (UCharArray.undef_full 4096 16 ** frame) 4100.
Proof.
  intros; eapply mem_create_byte_access_from_split with
    (residual := mem_create_bytes_missing_output 4096 16 4100 ** frame).
  sep_apply_l_atomic (mem_create_bytes_split_output 4096 16 4100 ltac:(lia)); entailer!.
Qed.

Lemma mem_create_output_store_effect : forall owned output value,
  output # UChar |-> value ** mem_create_output_residual owned output |--
    mem_create_overwritten owned output value.
Proof.
  intros owned output observed whole
    [cell [rest [[Hjoin [Htokens Hsts]] [Hcell [Habsent [old [Hold Howned]]]]]]].
  destruct Hcell as [Hrange [encoded [Heqm [Hmem [Hcellsts Hcelltokens]]]]].
  exists (kernel_state_with_memory rest
    (mem_create_replace_byte rest.(ConAssertion.s_mem) output old)); split; [exact Howned|].
  exists encoded; split; [exact Heqm|]; split.
  - apply functional_extensionality; intro address.
    unfold kernel_state_with_memory; simpl; unfold mem_byte_update, mem_create_replace_byte.
    specialize (Hjoin address); rewrite Hmem in Hjoin; unfold single_byte_mem in Hjoin.
    destruct (addr_eqb address output) eqn:Hequal.
    + apply addr_eqb_eq in Hequal; subst address.
      destruct Hjoin as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[b [? [? ?]]]|[b [? [? ?]]]]]]]; congruence.
    + destruct Hjoin as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[b [? [? ?]]]|[b [? [? ?]]]]]]]; congruence.
  - split.
    + apply pred_ext1; intro state.
      unfold ConAssertion.STS_state_join in Hsts; specialize (Hsts state);
        specialize (Hcellsts state); unfold kernel_state_with_memory; simpl;
        sets_unfold in Hsts; sets_unfold in Hcellsts; tauto.
    + apply pred_ext1; intro token.
      unfold ConAssertion.TokenSet_join in Htokens; destruct Htokens as [Htokens _].
      specialize (Htokens token); specialize (Hcelltokens token);
        unfold kernel_state_with_memory; simpl;
        sets_unfold in Htokens; sets_unfold in Hcelltokens; tauto.
Qed.

Lemma mem_create_overwritten_observation : forall owned output value heap,
  0 <= value < 256 -> mem_create_overwritten owned output value heap ->
  KernelHeapObservation.uchar_load output value heap.
Proof.
  intros owned output observed heap Hrange [before [_ [encoded [Heqm [Hmem _]]]]].
  split; [exact Hrange|]; exists encoded; split; [rewrite Hmem; apply mem_update_eq|exact Heqm].
Qed.

Definition mem_create_output_preserves (owned : Assertion) (output value : Z) : Prop :=
  forall before after, owned before -> mem_create_output_effect output value before after -> owned after.

Lemma mem_create_overwritten_preserves : forall owned output value,
  mem_create_output_preserves owned output value ->
  mem_create_overwritten owned output value |-- owned.
Proof. intros owned output value Hpreserve after [before [Howned Heffect]]; eapply Hpreserve; eassumption. Qed.

Lemma mem_create_output_effect_byte_frame : forall output observed frame before after,
  0 <= observed < 256 ->
  (output # UChar |->_ ** frame) before ->
  mem_create_output_effect output observed before after ->
  (output # UChar |-> observed ** frame) after.
Proof.
  intros output observed frame before after Hrange
    [cell [rest [[Hjoin [Htokens Hsts]] [[Haddress [Hcellsts [Hcelltokens Hcellmem]]] Hframe]]]]
    [encoded [Heqm [Hafter [Haftersts Haftertokens]]]].
  set (updated := kernel_state_with_memory cell (single_byte_mem output encoded)).
  exists updated, rest; split.
  - split.
    + intro address; specialize (Hjoin address).
      unfold updated, kernel_state_with_memory; simpl.
      rewrite Hafter; unfold mem_byte_update, single_byte_mem.
      destruct (addr_eqb address output) eqn:Hequal.
      * apply addr_eqb_eq in Hequal; subst address.
        assert (Hcellowned : ConAssertion.s_mem cell output <> Noperm).
        { destruct Hcellmem as [Hcellmem|[old Hcellmem]]; rewrite Hcellmem;
            [unfold single_Noninit_mem|unfold single_byte_mem];
            rewrite addr_eqb_refl; discriminate. }
        assert (Hrest : ConAssertion.s_mem rest output = Noperm).
        { destruct Hjoin as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[b [? [? ?]]]|[b [? [? ?]]]]]]];
            congruence. }
        rewrite Hrest; eauto 8.
      * assert (Hcellabsent : ConAssertion.s_mem cell address = Noperm).
        { destruct Hcellmem as [Hcellmem|[old Hcellmem]]; rewrite Hcellmem;
            [unfold single_Noninit_mem|unfold single_byte_mem]; rewrite Hequal; reflexivity. }
        rewrite Hcellabsent in Hjoin; exact Hjoin.
    + unfold updated, kernel_state_with_memory; simpl;
        rewrite Haftertokens, Haftersts; auto.
  - split; [|exact Hframe].
    split; [change (isvalidptr_char output /\ observed >= 0 /\ observed <= 255);
      split; [exact Haddress|lia]|].
    exists encoded; split; [exact Heqm|].
    unfold updated, kernel_state_with_memory; simpl; auto.
Qed.

Lemma mem_create_output_preserves_from_byte_cut : forall owned output observed residual,
  0 <= observed < 256 ->
  owned |-- output # UChar |->_ ** residual ->
  output # UChar |-> observed ** residual |-- owned ->
  mem_create_output_preserves owned output observed.
Proof.
  intros owned output observed residual Hrange Hsplit Hmerge before after Howned Heffect.
  apply Hmerge; eapply mem_create_output_effect_byte_frame;
    [exact Hrange|apply Hsplit; exact Howned|exact Heffect].
Qed.

Lemma mem_create_payload_output_preserves_linked_arena : forall private left block right output observed,
  private.(memPrivateLinkedPrefix) = private.(memPrivateBlockCount) ->
  Zrange 0 private.(memPrivateBlockCount) = left ++ block :: right ->
  private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4 <= output <
    private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize) ->
  0 <= observed < 256 ->
  mem_create_output_preserves (memory_private_linked_prefix_rep private) output observed.
Proof.
  intros; eapply mem_create_output_preserves_from_byte_cut; [eassumption| |].
  - eapply mem_create_linked_arena_split_payload_output; eassumption.
  - eapply mem_create_linked_arena_merge_payload_output; eassumption.
Qed.

Lemma mem_create_zero_output_preserves_zero_cut : forall output residual,
  mem_create_output_preserves (output # UChar |-> 0 ** residual) output 0.
Proof.
  intros; eapply mem_create_output_preserves_from_byte_cut with (residual := residual).
  - lia.
  - sep_apply_l_atomic (store_uchar_undef_store_uchar output 0); entailer!.
  - intros heap Howned; exact Howned.
Qed.

(** A kernel reference plus a literal final byte overlay.  When that byte
    aliases a link or metadata this is deliberately NOT an invariant-bearing
    UCOS2 state.  The spatial interpretation below binds the snapshot and
    overlay to one heap; a separate preservation theorem recovers stable
    publication for independent/payload/unchanged-byte outputs. *)
Record MemCreateWorld : Type := {
  mem_create_reference_state : UCOS2_Verify_State;
  mem_create_output_overlay : option (addr * Z)
}.
Definition MemCreateOutcome : Type := (addr * Z)%type.
Definition mem_create_outcome (pointer error : Z) : MemCreateOutcome := (pointer, error).
Definition mem_create_initial_world before : MemCreateWorld :=
  {| mem_create_reference_state := before; mem_create_output_overlay := None |}.
Definition mem_create_return_world current output value : MemCreateWorld :=
  {| mem_create_reference_state := current;
     mem_create_output_overlay := Some (output, value) |}.

Definition mem_create_publish_state (state : UCOS2_Verify_State) (private : MemoryPrivatePartition)
  : UCOS2_Verify_State :=
  replace_MemoryS (memory_publish_control state.(MemoryState) private) state.

(** The concrete private continuation is fixed here.  Its optional interval
    is the declared C environment; the sequential C guarantee uses its
    reflexive embedding.  No claim of an arbitrary nonzero foreign physical
    producer is made.  Canonical C VCs, not this definition, establish all
    n-1 link stores, the final NULL and the five control stores. *)
Definition mem_create_private_return critical sg invocation private
  : program UCOS2_Verify_State (addr * Z) :=
  StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => fun state outcome current =>
      outcome = (memory_control_addr sg private.(memPrivateSlot), 0) /\
      current = mem_create_publish_state state private).

Definition mem_create_kernel_program critical sg invocation base count size :=
  mem_create_program_with_private_return critical sg invocation base count size
    (mem_create_private_return critical sg invocation).

Definition mem_create_program critical sg invocation base count size output
  : program MemCreateWorld (addr * Z) :=
  fun initial outcome final =>
    initial.(mem_create_output_overlay) = None /\
    mem_create_kernel_program critical sg invocation base count size
      initial.(mem_create_reference_state) outcome final.(mem_create_reference_state) /\
    final.(mem_create_output_overlay) = Some (output, snd outcome).

Definition mem_create_safe critical sg invocation base count size output before
  (X : (addr * Z) -> MemCreateWorld -> Prop) : Prop :=
  safeExec (eq (mem_create_initial_world before))
    (mem_create_program critical sg invocation base count size output) X.

Definition mem_create_return_safe current output pointer error
  (X : (addr * Z) -> MemCreateWorld -> Prop) : Prop :=
  safeExec (eq (mem_create_return_world current output error))
    (StateRelMonad.ret (pointer, error)) X.

Lemma mem_create_api_safe_return : forall critical sg invocation base count size output before
  pointer error current X,
  mem_create_kernel_program critical sg invocation base count size before (pointer, error) current ->
  mem_create_safe critical sg invocation base count size output before X ->
  mem_create_return_safe current output pointer error X.
Proof.
  intros critical sg invocation base count size output before pointer error current X Hprogram Hsafe.
  unfold mem_create_safe in Hsafe; unfold mem_create_return_safe.
  eapply (highstependret_derive (mem_create_program critical sg invocation base count size output)
    (eq (mem_create_initial_world before)) (pointer, error)
    (fun _ => eq (mem_create_return_world current output error))); [|exact Hsafe].
  intros state Hstate; subst state; exists (mem_create_return_world current output error).
  split; [repeat split; try reflexivity; exact Hprogram|reflexivity].
Qed.

Lemma mem_create_private_return_reflexive : forall critical sg invocation private restored,
  mem_create_private_return critical sg invocation private restored
    (memory_control_addr sg private.(memPrivateSlot), 0)
    (mem_create_publish_state restored private).
Proof.
  intros; unfold mem_create_private_return, StateRelMonad.bind.
  exists tt, restored; split; [constructor|split; reflexivity].
Qed.

Inductive MemCreateInput : Type := MemCreateArena | MemCreateEmpty.

Definition mem_create_input_resources (mode : MemCreateInput) (base count size : Z) : Assertion :=
  match mem_create_argument_error base count size with
  | Some _ => emp
  | None => match mode with
    | MemCreateArena => UCharArray.undef_full (kernel_u32 base) (kernel_u32 size * kernel_u32 count)
    | MemCreateEmpty => emp
    end
  end.

Definition mem_create_call_domain critical sg invocation mode base count size before : Prop :=
  match mem_create_argument_error base count size with
  | Some _ => True
  | None =>
      mem_create_source_protocol critical sg invocation /\
      match mode with
      | MemCreateArena => memory_region_valid
          (memory_partition_initial 0 (kernel_u32 base) (kernel_u32 size) (kernel_u32 count) 0)
      | MemCreateEmpty => before.(MemoryState).(memFreeControls) = []
      end
  end.

(** An output byte in a caller-owned frame is unaffected by an environment
    action.  If instead it aliases shared storage, the selected C rely must
    preserve accessibility of that byte on the same action/interval.  This
    is an ownership condition, not a new CPU postcondition or a promise
    that the function will return.  [private] allows the detached MCB to
    stay in its actual ordinary separation frame across Restore. *)
Definition mem_create_output_protocol critical sg invocation output (fixed : Assertion) : Prop :=
  forall action before after private,
    critical_region_clients critical action -> kernel_client_actor action <> Some invocation ->
    kernel_client_step action sg before after ->
    mem_create_byte_access (UCOS2_inv sg before ** private ** fixed) output ->
    mem_create_byte_access (UCOS2_inv sg after ** private ** fixed) output.

Lemma mem_create_interval_preserves_output_access : forall critical sg invocation output fixed
  private before after,
  mem_create_output_protocol critical sg invocation output fixed ->
  critical_region_interval critical sg invocation before after ->
  mem_create_byte_access (UCOS2_inv sg before ** private ** fixed) output ->
  mem_create_byte_access (UCOS2_inv sg after ** private ** fixed) output.
Proof.
  intros critical sg invocation output fixed private before after Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval.
  induction Hinterval as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intro Haccess; [exact Haccess|].
  apply IH; eapply Hprotocol; eassumption.
Qed.

Definition mem_create_free_head sg state : addr :=
  match state.(MemoryState).(memFreeControls) with
  | [] => 0 | id :: _ => memory_control_addr sg id
  end.
Definition mem_create_root_frame sg state : Assertion :=
  memory_raw_rep_without_free_root sg state.(MemoryState) ** UCOS2_raw_rep_missing_memory sg state.

Definition mem_create_head_field_frame sg state private : Assertion :=
  memory_control_without_field sg (memory_control_addr sg private.(memPrivateSlot))
    private.(memPrivateImage) MCBFreeList **
  memory_controls_without sg state.(MemoryState) private.(memPrivateSlot) **
  store_map (fun _ partition => store_memory_free_blocks partition partition.(memFreeBlocks))
    state.(MemoryState).(memPartitions) ** UCOS2_raw_rep_missing_memory sg state.

Definition mem_create_selected_resources sg (selected : option MemoryPrivatePartition) : Assertion :=
  match selected with None => emp | Some private => memory_private_control_rep sg private end.
Definition mem_create_selected_pointer sg (selected : option MemoryPrivatePartition) : addr :=
  match selected with None => 0 | Some private => memory_control_addr sg private.(memPrivateSlot) end.

Definition MemCreateSelection : Type := option MemoryPrivatePartition.
Definition mem_create_no_selection : MemCreateSelection := None.
Definition mem_create_selection (private : MemoryPrivatePartition) : MemCreateSelection := Some private.

Definition mem_create_detached_resources sg state selected mode base count size (frame : Assertion)
  : Assertion := UCOS2_inv sg state ** mem_create_selected_resources sg selected **
    (mem_create_input_resources mode base count size ** frame).

Definition mem_create_entry_resources sg state mode base count size (frame : Assertion)
  : Assertion := UCOS2_inv sg state ** mem_create_input_resources mode base count size ** frame.

Definition mem_create_output_rely critical sg invocation mode base count size output frame : Prop :=
  mem_create_argument_error base count size = None ->
  mem_create_output_protocol critical sg invocation output
    (mem_create_input_resources mode base count size ** frame).

Definition mem_create_reservation sg base count size entry private post : Prop :=
  memory_reserve_control entry.(MemoryState) (kernel_u32 base)
    (kernel_u32 size * kernel_u32 count) (kernel_u32 size) (kernel_u32 count) = Some (private, post) /\
  valid_memory_state sg post /\
  memory_private_initialization_valid private /\
  private.(memPrivateBase) = base /\ private.(memPrivateBlockSize) = size /\
  private.(memPrivateBlockCount) = count /\ private.(memPrivateLinkedPrefix) = 0 /\
  0 < memory_control_addr sg private.(memPrivateSlot) < 4294967296.

Lemma mem_create_reservation_after_restore : forall critical sg invocation base count size
  entry private post restored,
  mem_create_profile sg ->
  mem_create_reservation sg base count size entry private post ->
  mem_create_source_protocol critical sg invocation ->
  critical_region_interval critical sg invocation (replace_MemoryS post entry) restored ->
  UCOS2_inv sg restored ** memory_private_control_rep sg private |--
    coq_prop (restored.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = Some private) &&
    (UCOS2_inv sg restored ** memory_private_control_rep sg private).
Proof.
  intros critical sg invocation base count size entry private post restored
    [_ [Henabled _]] [Hreserve [Hvalid _]] Hprotocol Hinterval.
  eapply mem_create_source_interval_private_frame_preserves_reservation
    with (before := replace_MemoryS post entry);
    [exact Henabled|exact Hvalid| |exact Hprotocol|exact Hinterval].
  exact (proj2 (memory_reserve_excludes_global_control _ _ _ _ _ _ _ Hreserve)).
Qed.

Definition mem_create_acquire_facts critical sg invocation mode base count size before entry
  selected checkpoint : Prop :=
  mem_create_argument_error base count size = None /\
  critical_region_interval critical sg invocation before entry /\
  mem_create_acquire base count size entry selected checkpoint /\
  match selected with
  | None => True
  | Some private => exists post,
      mode = MemCreateArena /\ mem_create_reservation sg base count size entry private post /\
      checkpoint = replace_MemoryS post entry
  end.

Definition mem_create_private_history critical sg invocation base count size before restored private : Prop :=
  mem_create_argument_error base count size = None /\
  exists entry post,
    critical_region_interval critical sg invocation before entry /\
    mem_create_reservation sg base count size entry private post /\
    critical_region_interval critical sg invocation (replace_MemoryS post entry) restored /\
    restored.(MemoryState).(memPrivateControls) private.(memPrivateSlot) = Some private.

Definition mem_create_cursor_resources sg state private index (frame : Assertion) : Assertion :=
  UCOS2_inv sg state ** memory_private_control_rep sg private **
    memory_private_linked_prefix_rep (memory_private_set_prefix private index) ** frame.

Definition mem_create_loop_resources sg state private index (frame : Assertion) : Assertion :=
  UCOS2_inv sg state ** memory_private_control_rep sg private **
    memory_private_next_link_frame (memory_private_set_prefix private index) ** frame.

Definition mem_create_initialized_resources sg state private (frame : Assertion) : Assertion :=
  UCOS2_inv sg state **
    store_memory_control sg (memory_control_addr sg private.(memPrivateSlot))
      (memory_create_control_image private) **
    memory_private_linked_prefix_rep
      (memory_private_set_prefix private private.(memPrivateBlockCount)) ** frame.

Definition mem_create_control_write_frame sg state private (frame : Assertion) : Assertion :=
  UCOS2_inv sg state **
    memory_private_linked_prefix_rep
      (memory_private_set_prefix private private.(memPrivateBlockCount)) ** frame.

Definition mem_create_loop_state platform critical sg invocation origin mask base count size output
  before restored private index frame (X : (addr * Z) -> MemCreateWorld -> Prop) : Assertion :=
  coq_prop (mem_create_profile sg /\
    mem_create_private_history critical sg invocation base count size before restored private /\
    mem_create_safe critical sg invocation base count size output before X /\
    mem_create_byte_access (mem_create_cursor_resources sg restored private index frame) output) &&
  (interrupt_platform_running platform invocation origin mask **
    mem_create_cursor_resources sg restored private index frame).

Definition mem_create_retained_resources mode base count size pointer : Assertion :=
  if Z.eqb pointer 0 then mem_create_input_resources mode base count size else emp.

Definition mem_create_return_resources sg mode base count size pointer current (frame : Assertion)
  : Assertion := UCOS2_inv sg current ** mem_create_retained_resources mode base count size pointer ** frame.

Definition mem_create_api_post platform critical sg invocation origin mask mode base count size output
  before pointer (frame : Assertion) (X : (addr * Z) -> MemCreateWorld -> Prop) : Assertion :=
  EX current : UCOS2_Verify_State, EX error : Z,
    coq_prop (mem_create_kernel_program critical sg invocation base count size before (pointer, error) current /\
      mem_create_return_safe current output pointer error X) &&
    (interrupt_platform_running platform invocation origin mask **
      mem_create_overwritten
        (mem_create_return_resources sg mode base count size pointer current frame) output error).

(** This is the common consumer at all six actual C return sites.  It
    keeps the SAME [current], [error] and arbitrary [X] as the last-store
    residual, including corrupting aliases whose world is only a reference
    snapshot plus an exact byte overlay. *)
Lemma mem_create_api_return_from_byte : forall platform critical sg invocation origin mask mode
  base count size output before pointer current error frame X,
  mem_create_kernel_program critical sg invocation base count size before (pointer, error) current ->
  mem_create_safe critical sg invocation base count size output before X ->
  interrupt_platform_running platform invocation origin mask **
    (output # UChar |-> error **
      mem_create_output_residual
        (mem_create_return_resources sg mode base count size pointer current frame) output) |--
  mem_create_api_post platform critical sg invocation origin mask mode base count size output
    before pointer frame X.
Proof.
  intros platform critical sg invocation origin mask mode base count size output before
    pointer current error frame X Hprogram Hsafe.
  unfold mem_create_api_post; Exists current error.
  pose proof (mem_create_api_safe_return critical sg invocation base count size output before
    pointer error current X Hprogram Hsafe) as Hreturn.
  sep_apply_l_atomic (mem_create_output_store_effect
    (mem_create_return_resources sg mode base count size pointer current frame) output error);
    entailer!.
Qed.

Lemma mem_create_initialized_payload_preserved : forall sg current private frame
  left block right output observed,
  Zrange 0 private.(memPrivateBlockCount) = left ++ block :: right ->
  private.(memPrivateBase) + block * private.(memPrivateBlockSize) + 4 <= output <
    private.(memPrivateBase) + (block + 1) * private.(memPrivateBlockSize) ->
  0 <= observed < 256 ->
  mem_create_overwritten (mem_create_initialized_resources sg current private frame) output observed |--
  mem_create_initialized_resources sg current private frame.
Proof.
  intros sg current private frame left block right output observed Hrange Houtput Hobserved.
  apply mem_create_overwritten_preserves.
  eapply mem_create_output_preserves_from_byte_cut with
    (residual := UCOS2_inv sg current **
      store_memory_control sg (memory_control_addr sg private.(memPrivateSlot))
        (memory_create_control_image private) **
      mem_create_linked_arena_missing_output
        (memory_private_set_prefix private private.(memPrivateBlockCount)) left block right output ** frame).
  - exact Hobserved.
  - unfold mem_create_initialized_resources.
    sep_apply_l_atomic (mem_create_linked_arena_split_payload_output
      (memory_private_set_prefix private private.(memPrivateBlockCount)) left block right output
      eq_refl Hrange Houtput); entailer!.
  - unfold mem_create_initialized_resources.
    sep_apply_l_atomic (mem_create_linked_arena_merge_payload_output
      (memory_private_set_prefix private private.(memPrivateBlockCount)) left block right output observed
      eq_refl Hrange Houtput); entailer!.
Qed.

Lemma mem_create_memory_valid__entry_reservation : forall sg state,
  mem_create_profile sg -> UCOS2_state_inv sg state ->
  valid_memory_state sg state.(MemoryState).
Proof.
  intros sg state [_ [Hmemory _]] Hstate.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready,
    valid_memory_configuration in Hstate.
  rewrite Hmemory in Hstate; tauto.
Qed.
Lemma memory_control_addr_in_range__entry_reservation : forall sg id,
  selected_kernel_profile sg -> sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  0 <= id < sg.(osKernelConfig).(cfgMaxMemPartitions) ->
  0 < memory_control_addr sg id < 4294967296.
Proof.
  intros sg id Hprofile Henabled Hid.
  assert (Hregion : kernel_region_valid
    (sg.(g_OSMemTbl), memory_control_size sg.(osKernelConfig) *
      sg.(osKernelConfig).(cfgMaxMemPartitions))).
  { apply (valid_selected_kernel_global_layout_region sg).
    - unfold selected_kernel_profile in Hprofile; tauto.
    - unfold selected_kernel_global_regions.
      apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; left.
      unfold kernel_independent_regions.
      apply in_or_app; right. apply in_or_app; left.
      assert (Hmax : (0 <? cfgMaxMemPartitions (osKernelConfig sg)) = true)
        by (apply Z.ltb_lt; lia).
      rewrite Henabled, Hmax; simpl; auto. }
  unfold kernel_region_valid in Hregion; cbn [fst snd] in Hregion.
  assert (Hsize : 0 < memory_control_size (osKernelConfig sg)).
  { unfold memory_control_size; destruct (cfgMemoryNames (osKernelConfig sg)); lia. }
  unfold memory_control_addr; nia.
Qed.
Lemma mem_create_free_head_zero_iff__entry_reservation : forall sg state,
  mem_create_profile sg -> UCOS2_state_inv sg state ->
  (mem_create_free_head sg state = 0 <-> state.(MemoryState).(memFreeControls) = []).
Proof.
  intros sg state Hprofile Hstate.
  pose proof (mem_create_memory_valid__entry_reservation sg state Hprofile Hstate) as Hmemory.
  destruct Hmemory as [[_ [Hids _]] _].
  assert (Hselected : selected_kernel_profile sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hstate; tauto. }
  destruct Hprofile as [_ [Henabled _]].
  unfold mem_create_free_head.
  destruct (memFreeControls (MemoryState state)) as [|id rest] eqn:Hfree;
    [tauto|].
  pose proof (memory_control_addr_in_range__entry_reservation sg id Hselected
    Henabled (Hids id (or_introl eq_refl))) as Haddr.
  split; [lia|discriminate].
Qed.
Lemma mem_create_reserve_facts__entry_reservation : forall sg entry base count size private post,
  mem_create_profile sg -> UCOS2_state_inv sg entry ->
  mem_create_arguments_in_range base count size ->
  memory_region_valid (memory_partition_initial 0 (kernel_u32 base)
    (kernel_u32 size) (kernel_u32 count) 0) ->
  memory_reserve_control entry.(MemoryState) (kernel_u32 base)
    (kernel_u32 size * kernel_u32 count) (kernel_u32 size) (kernel_u32 count) =
    Some (private, post) ->
  mem_create_reservation sg base count size entry private post /\
  entry.(MemoryState).(memControlImages) private.(memPrivateSlot) = Some private.(memPrivateImage).
Proof.
  intros sg entry base count size private post Hprofile Hstate Hrange Hregion Hreserve.
  pose proof (mem_create_memory_valid__entry_reservation sg entry Hprofile Hstate) as Hmemory.
  pose proof (memory_reserve_preserves_state_validity sg _ _ _ _ _ _ _ Hmemory Hreserve) as Hpost.
  assert (Hselected : selected_kernel_profile sg).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hstate; tauto. }
  destruct Hprofile as [_ [Henabled _]].
  destruct Hmemory as [[_ [Hids _]] _].
  unfold mem_create_arguments_in_range in Hrange.
  assert (Hb : kernel_u32 base = base) by (apply kernel_u32_identity; lia).
  assert (Hn : kernel_u32 count = count) by (apply kernel_u32_identity; lia).
  assert (Hs : kernel_u32 size = size) by (apply kernel_u32_identity; lia).
  split.
  - unfold mem_create_reservation; split; [exact Hreserve|].
    split; [exact Hpost|].
    unfold memory_reserve_control in Hreserve.
    destruct (memFreeControls (MemoryState entry)) as [|id rest] eqn:Hfree; [discriminate|].
    destruct (memControlImages (MemoryState entry) id) as [old|] eqn:Himage; [|discriminate].
    inversion Hreserve; subst private post; clear Hreserve.
    pose proof (memory_control_addr_in_range__entry_reservation sg id Hselected
      Henabled (Hids id (or_introl eq_refl))) as Haddr.
    simpl; rewrite Hb, Hn, Hs in *.
    split.
    + unfold memory_private_initialization_valid; simpl.
      split; [exact Hregion|]. split; [reflexivity|].
      unfold memory_region_valid, memory_partition_initial in Hregion; simpl in Hregion; lia.
    + repeat split; try reflexivity; lia.
  - unfold memory_reserve_control in Hreserve.
    destruct (memFreeControls (MemoryState entry)) as [|id rest]; [discriminate|].
    destruct (memControlImages (MemoryState entry) id) as [old|] eqn:Himage; [|discriminate].
    inversion Hreserve; subst; exact Himage.
Qed.
Lemma mem_create_input_prefix_zero_equiv__entry_reservation : forall private base count size,
  mem_create_arguments_valid base count size ->
  private.(memPrivateBase) = base -> private.(memPrivateBlockCount) = count ->
  private.(memPrivateBlockSize) = size -> memory_private_initialization_valid private ->
  mem_create_input_resources MemCreateArena base count size --||--
    memory_private_linked_prefix_rep (memory_private_set_prefix private 0).
Proof.
  intros private base count size Hargs Hb Hn Hs [Hregion _].
  unfold memory_region_valid, memory_partition_initial in Hregion; simpl in Hregion.
  rewrite Hb, Hn, Hs in Hregion.
  unfold mem_create_arguments_valid in Hargs.
  unfold mem_create_input_resources; rewrite Hargs; simpl.
  rewrite !kernel_u32_identity by nia.
  unfold memory_private_linked_prefix_rep, memory_private_set_prefix; simpl.
  rewrite Hb, Hn, Hs; rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r, Z.mul_comm.
  split; entailer!.
  rewrite derivable1_iter_sepcon_l; simpl; entailer!.
Qed.
Lemma mem_create_permissions_sepcon__private_initialization :
  forall (P Q R S : Assertion),
  (forall h, Q h -> exists k, P k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token)) ->
  (forall h, S h -> exists k, R k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token)) ->
  forall h, (Q ** S) h -> exists k, (P ** R) k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token).
Proof.
  intros P Q R S HP HR h [q [s [[Hjoin [Htoken Hsts]] [HQ HS]]]].
  destruct (HP q HQ) as [p [Hp [Hpm [Hpsts Hptoken]]]].
  destruct (HR s HS) as [r [Hr [Hrm [Hrsts Hrtoken]]]].
  set (k := kernel_state_with_memory h (merge p.(ConAssertion.s_mem) r.(ConAssertion.s_mem))).
  assert (Hnewjoin : mem_join p.(ConAssertion.s_mem) r.(ConAssertion.s_mem) k.(ConAssertion.s_mem)).
  { apply disjoint_merge_mem_join; intro a.
    pose proof (mem_join_disjoint Hjoin a) as Hd.
    specialize (Hpm a); specialize (Hrm a).
    destruct (ConAssertion.s_mem p a), (ConAssertion.s_mem r a),
      (ConAssertion.s_mem q a), (ConAssertion.s_mem s a); simpl in *; intuition congruence. }
  exists k; split.
  - exists p, r; split; [|auto].
    split; [exact Hnewjoin|].
    unfold k, kernel_state_with_memory; simpl; rewrite Hptoken, Hrtoken, Hpsts, Hrsts; auto.
  - split.
    + intro a; specialize (Hnewjoin a); specialize (Hjoin a).
      specialize (Hpm a); specialize (Hrm a).
      destruct Hnewjoin as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v [? [? ?]]]|[v [? [? ?]]]]]]];
      destruct Hjoin as [[? [? ?]]|[[? [? ?]]|[[? [? ?]]|[[v' [? [? ?]]]|[v' [? [? ?]]]]]]];
        intuition congruence.
    + split; reflexivity.
Qed.
Lemma mem_create_permissions_store_byte__private_initialization : forall address old new h,
  store_byte address new h -> exists k, store_byte address old k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token).
Proof.
  intros address old new h [encoded [Heqm [Hmem [Hsts Htoken]]]].
  exists (kernel_state_with_memory h (single_byte_mem address old)); split.
  - exists old; split; [apply Byte.eqm_refl|].
    unfold kernel_state_with_memory; simpl; auto.
  - split.
    + intro a; simpl; rewrite Hmem; unfold single_byte_mem.
      destruct (addr_eqb a address); split; congruence.
    + split; reflexivity.
Qed.
Lemma mem_create_word_bytes_merge__private_initialization : forall value,
  merge_int value (value / 256) (value / 256 / 256) (value / 256 / 256 / 256) value.
Proof.
  intro value.
  pose proof (Z_to_n_bytes_to_Z 4 value) as Hbytes.
  change (merge_int value (value / 256) (value / 256 / 256)
    (value / 256 / 256 / 256) value).
  change (value mod 4294967296 = value mod 256 + (value / 256) mod 256 * 256 +
    (value / 256 / 256) mod 256 * 65536 + (value / 256 / 256 / 256) mod 256 * 16777216).
  cbn [Z_to_n_bytes LittleEndian.Z_to_n_bytes n_bytes_to_Z LittleEndian.n_bytes_to_Z] in Hbytes.
  rewrite !Z.mod_mod in Hbytes by lia.
  change (value mod 256 + 256 * ((value/256) mod 256 + 256 *
    ((value/256/256) mod 256 + 256 * ((value/256/256/256) mod 256 + 256*0))) =
    value mod 4294967296) in Hbytes.
  lia.
Qed.
Lemma mem_create_undef_pointer_bytes__private_initialization : forall address,
  address # Ptr |->_ |-- UCharArray.undef_full address 4.
Proof.
  intros address.
  unfold UCharArray.undef_full, store_undef_array; simpl.
  unfold StoreUCharAsElement.undefstoreA; simpl.
  unfold undef_store_uchar, undef_store_ptr, store_4byte_noninit, isvalidptr; simpl.
  entailer!.
  all: unfold isvalidptr_char, ptr_size_Z, Arch32.ptr_size_Z, Arch32.ptr_size in *;
    simpl in *; try lia.
  rewrite Z.add_0_r; reflexivity.
Qed.
Lemma mem_create_linked_prefix_forget_last__private_initialization : forall private i,
  memory_private_initialization_valid private ->
  0 <= i < private.(memPrivateBlockCount) ->
  memory_private_linked_prefix_rep (memory_private_set_prefix private (i+1)) |--
  memory_private_linked_prefix_rep (memory_private_set_prefix private i).
Proof.
  intros private i [Hr [He Hp]] Hi.
  unfold memory_region_valid, memory_partition_initial in Hr; simpl in Hr.
  destruct Hr as [Hb [Hab [Hsize [Has [Hcount Hend]]]]].
  unfold memory_private_linked_prefix_rep.
  change (memory_private_linked_block_rep (memory_private_set_prefix private (i+1)))
    with (memory_private_linked_block_rep private).
  change (memory_private_linked_block_rep (memory_private_set_prefix private i))
    with (memory_private_linked_block_rep private).
  cbn [memory_private_set_prefix memPrivateBase memPrivateBlockSize
    memPrivateBlockCount memPrivateLinkedPrefix].
  assert (Hindices : Zrange 0 (i+1) = Zrange 0 i ++ [i]).
  { unfold Zrange; rewrite !Z.sub_0_r, Z2Nat.inj_add by lia.
    rewrite Zrange_aux_app, Z2Nat.id by lia; rewrite Z.add_0_l; reflexivity. }
  rewrite Hindices, map_app.
  rewrite derivable1_sepcon_iter_sepcon2.
  rewrite (derivable1_iter_sepcon_l [memory_private_linked_block_rep private i]); simpl.
  unfold memory_private_linked_block_rep.
  sep_apply store_ptr_undef_store_ptr.
  sep_apply mem_create_undef_pointer_bytes__private_initialization.
  sepcon_right_assoc.
  pose proof (UCharArray.undef_full_merge_to_undef_full
    (memPrivateBase private + i * memPrivateBlockSize private) 4
    (memPrivateBlockSize private) ltac:(lia)) as Hmerge4.
  change (sizeof(UCHAR)) with 1 in Hmerge4.
  rewrite Z.mul_1_r in Hmerge4.
  sep_apply Hmerge4.
  replace (memPrivateBase private + (i+1) * memPrivateBlockSize private) with
    (memPrivateBase private + i * memPrivateBlockSize private + memPrivateBlockSize private * 1) by ring.
  replace ((memPrivateBlockCount private - (i+1)) * memPrivateBlockSize private) with
    ((memPrivateBlockCount private - i) * memPrivateBlockSize private - memPrivateBlockSize private) by ring.
  pose proof (UCharArray.undef_full_merge_to_undef_full
    (memPrivateBase private + i * memPrivateBlockSize private)
    (memPrivateBlockSize private) ((memPrivateBlockCount private-i)*memPrivateBlockSize private) ltac:(nia)) as Hmergeblock.
  change (sizeof(UCHAR)) with 1 in Hmergeblock.
  sep_apply Hmergeblock.
  entailer!.
Qed.
Lemma mem_create_permissions_store4__private_initialization : forall address old new h,
  store_4byte address new h -> exists k, store_4byte address old k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token).
Proof.
  intros address old new h [b0 [b1 [b2 [b3 [Hmerge Hcells]]]]].
  assert (Hrebuild : forall h,
    (store_byte address b0 ** (store_byte (address+1) b1 **
      (store_byte (address+2) b2 ** store_byte (address+3) b3))) h ->
    exists k, (store_byte address old ** (store_byte (address+1) (old/256) **
      (store_byte (address+2) (old/256/256) ** store_byte (address+3) (old/256/256/256)))) k /\
      (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
      k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
      k.(ConAssertion.s_token) = h.(ConAssertion.s_token)).
  { repeat apply mem_create_permissions_sepcon__private_initialization;
      apply mem_create_permissions_store_byte__private_initialization. }
  destruct (Hrebuild h Hcells) as [k [Hk Hpermission]].
  exists k; split; [|exact Hpermission].
  exists old, (old/256), (old/256/256), (old/256/256/256).
  split; [apply mem_create_word_bytes_merge__private_initialization|exact Hk].
Qed.
Lemma mem_create_permissions_store_ptr__private_initialization : forall address old new,
  valid_ptr_value old -> forall h,
  (address # Ptr |-> new) h -> exists k, (address # Ptr |-> old) k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token).
Proof.
  intros address old new Hold h [[Haddress Hnew] Hbytes].
  destruct (mem_create_permissions_store4__private_initialization address old new h Hbytes)
    as [k [Hk Hpermission]].
  exists k; split; [split; [split; assumption|exact Hk]|exact Hpermission].
Qed.
Lemma mem_create_permissions_store_uint__private_initialization : forall address old new,
  0 <= old <= Int.max_unsigned -> forall h,
  (address # UInt |-> new) h -> exists k, (address # UInt |-> old) k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token).
Proof.
  intros address old new Hold h [[Haddress Hnew] Hbytes].
  destruct (mem_create_permissions_store4__private_initialization address old new h Hbytes)
    as [k [Hk Hpermission]].
  exists k; split; [split; [split; [exact Haddress|lia]|exact Hk]|exact Hpermission].
Qed.
Lemma mem_create_permissions_control__private_initialization : forall sg address old new old_heap,
  sg.(osKernelConfig).(cfgMemoryNames) = true ->
  store_memory_control sg address old old_heap ->
  forall h, store_memory_control sg address new h ->
  exists k, store_memory_control sg address old k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
    k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
    k.(ConAssertion.s_token) = h.(ConAssertion.s_token).
Proof.
  intros sg address old new old_heap Hnames Hold.
  assert (Hbounds : store_memory_control sg address old |--
    coq_prop (valid_ptr_value old.(memImageBase) /\ valid_ptr_value old.(memImageFree) /\
      0 <= old.(memImageSize) <= Int.max_unsigned /\
      0 <= old.(memImageCount) <= Int.max_unsigned /\
      0 <= old.(memImageNFree) <= Int.max_unsigned /\ valid_ptr_value old.(memImageName))).
  { rewrite store_memory_control_layout_equiv, Hnames.
    prop_apply (valid_store_ptr (&(address # "os_mem" ->ₛ "OSMemAddr")) old.(memImageBase)); Intros.
    prop_apply (valid_store_ptr (&(address # "os_mem" ->ₛ "OSMemFreeList")) old.(memImageFree)); Intros.
    prop_apply (valid_store_uint (&(address # "os_mem" ->ₛ "OSMemBlkSize")) old.(memImageSize)); Intros.
    prop_apply (valid_store_uint (&(address # "os_mem" ->ₛ "OSMemNBlks")) old.(memImageCount)); Intros.
    prop_apply (valid_store_uint (&(address # "os_mem" ->ₛ "OSMemNFree")) old.(memImageNFree)); Intros.
    prop_apply (valid_store_ptr (&(address # "os_mem" ->ₛ "OSMemName")) old.(memImageName)); Intros.
    entailer!. }
  destruct (Hbounds old_heap Hold) as [Hbase [Hfree [Hsize [Hcount [Hnfree Hname]]]]].
  pose proof (proj1 (store_memory_control_layout_equiv sg address new)) as Hsplit.
  pose proof (proj2 (store_memory_control_layout_equiv sg address old)) as Hmerge.
  rewrite Hnames in Hsplit, Hmerge.
  assert (Hrebuild : forall h,
    (&(address # "os_mem" ->ₛ "OSMemAddr") # Ptr |-> new.(memImageBase) **
     &(address # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> new.(memImageFree) **
     &(address # "os_mem" ->ₛ "OSMemBlkSize") # UInt |-> new.(memImageSize) **
     &(address # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> new.(memImageCount) **
     &(address # "os_mem" ->ₛ "OSMemNFree") # UInt |-> new.(memImageNFree) **
     &(address # "os_mem" ->ₛ "OSMemName") # Ptr |-> new.(memImageName)) h ->
    exists k,
    (&(address # "os_mem" ->ₛ "OSMemAddr") # Ptr |-> old.(memImageBase) **
     &(address # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> old.(memImageFree) **
     &(address # "os_mem" ->ₛ "OSMemBlkSize") # UInt |-> old.(memImageSize) **
     &(address # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> old.(memImageCount) **
     &(address # "os_mem" ->ₛ "OSMemNFree") # UInt |-> old.(memImageNFree) **
     &(address # "os_mem" ->ₛ "OSMemName") # Ptr |-> old.(memImageName)) k /\
      (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm) /\
      k.(ConAssertion.s_STS) = h.(ConAssertion.s_STS) /\
      k.(ConAssertion.s_token) = h.(ConAssertion.s_token)).
  { repeat apply mem_create_permissions_sepcon__private_initialization;
      first [apply mem_create_permissions_store_ptr__private_initialization; assumption |
        apply mem_create_permissions_store_uint__private_initialization; assumption]. }
  intros h Hh; destruct (Hrebuild h (Hsplit h Hh)) as [k [Hk Hpermission]].
  exists k; split; [apply Hmerge; exact Hk|exact Hpermission].
Qed.
Lemma mem_create_reserved_resources_restore__private_initialization :
  forall sg state base extent size count private post,
  valid_memory_state sg state ->
  memory_reserve_control state base extent size count = Some (private, post) ->
  memory_private_control_rep sg private ** memory_raw_rep sg post |--
  sg.(g_OSMemFreeList) # Ptr |-> private.(memPrivateImage).(memImageFree) **
    memory_raw_rep_without_free_root sg state.
Proof.
  intros sg state base extent size count private post Hvalid Hreserve.
  pose proof (proj2 (memory_reserve_root_values_eq sg state base extent size count private post
    Hvalid Hreserve)) as Hroot.
  unfold memory_reserve_control in Hreserve.
  destruct (memFreeControls state) as [|head rest] eqn:Hfree; [discriminate|].
  destruct (memControlImages state head) as [old|] eqn:Himage; [|discriminate].
  inversion Hreserve; subst private post; simpl in Hroot.
  unfold memory_private_control_rep, memory_raw_rep, memory_raw_rep_without_free_root,
    memory_controls_rep; simpl.
  rewrite Hroot.
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (fun i v => store_memory_control sg (memory_control_addr sg i) v)
    (kernel_map_set (memControlImages state) head None) head
    (kernel_map_set_same _ (memControlImages state) head None)).
  assert (Hframe : forall j, j <> head ->
    kernel_map_set (memControlImages state) head None j = memControlImages state j).
  { intros; apply kernel_map_set_other; assumption. }
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) _ _ head Hframe)).
  sep_apply_l_atomic (store_map_merge
    (fun i v => store_memory_control sg (memory_control_addr sg i) v) head old _ Himage).
  entailer!.
Qed.
Lemma mem_create_byte_access_permissions__private_initialization : forall P Q output,
  (forall h, Q h -> exists k, P k /\
    (forall a, k.(ConAssertion.s_mem) a = Noperm <-> h.(ConAssertion.s_mem) a = Noperm)) ->
  mem_create_byte_access P output -> mem_create_byte_access Q output.
Proof.
  intros P Q output Hrebuild Haccess h Hq.
  destruct (Hrebuild h Hq) as [k [Hpk Hpermission]].
  destruct (Haccess k Hpk) as [Haddress Howned].
  split; [exact Haddress|]; intro Habsent; apply Howned, Hpermission, Habsent.
Qed.
Lemma mem_create_byte_access_ptr_replace__private_initialization : forall address old new frame output,
  valid_ptr_value old ->
  mem_create_byte_access (address # Ptr |-> old ** frame) output ->
  mem_create_byte_access (address # Ptr |-> new ** frame) output.
Proof.
  intros address old new frame output Hold Haccess.
  eapply mem_create_byte_access_permissions__private_initialization; [|exact Haccess].
  intros h Hh.
  destruct (mem_create_permissions_sepcon__private_initialization
    (address # Ptr |-> old) (address # Ptr |-> new) frame frame
    (mem_create_permissions_store_ptr__private_initialization address old new Hold)
    ltac:(intros h' Hh'; exists h'; repeat split; auto) h Hh)
    as [k [Hk [Hpermission Hrest]]].
  exists k; auto.
Qed.
Lemma mem_create_output_residual_consequence__private_initialization : forall P Q output,
  P |-- Q -> mem_create_output_residual P output |-- mem_create_output_residual Q output.
Proof.
  intros P Q output Hent rest [Habsent [old [Hold Howned]]].
  split; [exact Habsent|]; exists old; split; [exact Hold|apply Hent; exact Howned].
Qed.
Lemma mem_create_byte_access_control_replace__private_initialization :
  forall sg address old new frame output old_heap,
  sg.(osKernelConfig).(cfgMemoryNames) = true ->
  store_memory_control sg address old old_heap ->
  mem_create_byte_access (store_memory_control sg address old ** frame) output ->
  mem_create_byte_access (store_memory_control sg address new ** frame) output.
Proof.
  intros sg address old new frame output old_heap Hnames Hold Haccess.
  eapply mem_create_byte_access_permissions__private_initialization; [|exact Haccess].
  intros h Hh.
  destruct (mem_create_permissions_sepcon__private_initialization
    (store_memory_control sg address old) (store_memory_control sg address new) frame frame
    (mem_create_permissions_control__private_initialization sg address old new old_heap Hnames Hold)
    ltac:(intros h' Hh'; exists h'; repeat split; auto) h Hh)
    as [k [Hk [Hpermission Hrest]]].
  exists k; auto.
Qed.
