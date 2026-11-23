Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
Require Export Ucos2Verify.lib.mutex_query_spec.
Require Export Ucos2Verify.lib.memory.
Require Export Ucos2Verify.lib.stable_glob_vars.
Require Export Ucos2Verify.lib.ucos2_verify_state_def.
Require Export Ucos2Verify.lib.ucos2_rules_lib.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.kernel_resources.
From SimpleC.SL Require Import Mem SeparationLogic MapLib IntLib.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.

Import ListNotations UCOS2_C_Rules Monad MonadNotation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope sac_scope.
Local Open Scope monad_scope.

(** A raw control belongs to the caller and is separate from the shared
    kernel region. A pool control is borrowed from that region at acquisition.
    Neither view transfers ownership of the addresses copied by Query. *)
Inductive MemQueryView :=
| MemQueryRaw (image : MemoryControlImage)
| MemQueryPool (id : MemID).

Definition mem_query_selected (view : MemQueryView)
  (state : UCOS2_Verify_State) (image : MemoryControlImage) : Prop :=
  match view with
  | MemQueryRaw original => image = original
  | MemQueryPool id => state.(MemoryState).(memControlImages) id = Some image
  end.

(** The explicit C access protocol protects availability of this control
    through foreign registered clients. It does not freeze its counters or
    its payload, and is not a CPU/platform promise. *)
Definition mem_query_access_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (id : MemID) : Prop :=
  forall action before after previous,
    critical_region_clients critical action ->
    kernel_client_actor action <> Some invocation ->
    UCOS2_state_inv sg before -> kernel_client_step action sg before after ->
    before.(MemoryState).(memControlImages) id = Some previous ->
    exists current, after.(MemoryState).(memControlImages) id = Some current.

Lemma mem_query_access_interval : forall critical sg invocation id before after previous,
  mem_query_access_protocol critical sg invocation id ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before ->
  before.(MemoryState).(memControlImages) id = Some previous ->
  exists current, after.(MemoryState).(memControlImages) id = Some current.
Proof.
  intros critical sg invocation id before after previous Hprotocol Hinterval.
  apply critical_region_interval_raw_trace in Hinterval; revert previous.
  induction Hinterval as
    [state|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros previous Hvalid Hlookup.
  - eauto.
  - destruct (Hprotocol action before middle previous Hin Hforeign Hvalid Hstep Hlookup)
      as [current Hcurrent].
    apply (IH current).
    + exact (kernel_client_preserves_validity action
        (critical_region_client_certificates critical action Hin)
        sg before middle Hvalid Hstep).
    + exact Hcurrent.
Qed.

Lemma mem_query_access_task_creation_clients : forall critical sg invocation id,
  (forall action, critical_region_clients critical action -> task_creation_client_family action) ->
  mem_query_access_protocol critical sg invocation id.
Proof.
  intros critical sg invocation id Hclients action before after previous
    Hin Hforeign Hvalid Hstep Hlookup.
  destruct (Hclients action Hin) as [source ->].
  destruct Hstep as [_ [_ ->]].
  exists previous; destruct source; exact Hlookup.
Qed.

Definition mem_query_address (sg : StableGlobVars) (pe : addr) (view : MemQueryView) : Prop :=
  match view with MemQueryRaw _ => True | MemQueryPool id => pe = memory_control_addr sg id end.

Definition mem_query_admission (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (pe : addr)
  (view : MemQueryView) (before : UCOS2_Verify_State) : Prop :=
  sg.(osKernelConfig).(cfgMemoryEnabled) = true /\
  sg.(osKernelConfig).(cfgMemoryNames) = true /\
  mem_query_address sg pe view /\
  match view with
  | MemQueryRaw _ => True
  | MemQueryPool id =>
      (exists image, before.(MemoryState).(memControlImages) id = Some image) /\
      mem_query_access_protocol critical sg invocation id
  end.

Lemma mem_query_acquired_image : forall critical sg invocation pe view before entry,
  mem_query_admission critical sg invocation pe view before ->
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before entry ->
  exists image, mem_query_selected view entry image.
Proof.
  intros critical sg invocation pe [original|id] before entry
    [Henabled [Hnames [Haddress Haccess]]] Hvalid Hinterval.
  - exists original; reflexivity.
  - destruct Haccess as [[previous Hlookup] Hprotocol].
    eapply mem_query_access_interval; eassumption.
Qed.

Definition mem_query_source_rep (sg : StableGlobVars) (pe : addr) (view : MemQueryView) : Assertion :=
  match view with
  | MemQueryRaw image => store_memory_control sg pe image
  | MemQueryPool _ => emp
  end.

Definition mem_query_source_frame (sg : StableGlobVars) (view : MemQueryView)
  (entry : UCOS2_Verify_State) : Assertion :=
  match view with
  | MemQueryRaw _ => UCOS2_inv sg entry
  | MemQueryPool id => coq_prop (UCOS2_state_inv sg entry) &&
      (memory_controls_without sg entry.(MemoryState) id **
       store_map (fun _ p => store_memory_free_blocks p p.(memFreeBlocks))
         entry.(MemoryState).(memPartitions) **
       sg.(g_OSMemFreeList) # Ptr |->
         (match entry.(MemoryState).(memFreeControls) with
          | [] => 0 | i :: _ => memory_control_addr sg i end) **
       UCOS2_raw_rep_missing_memory sg entry)
  end.

Lemma mem_query_source_split : forall sg pe view entry image,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  mem_query_address sg pe view -> mem_query_selected view entry image ->
  UCOS2_inv sg entry ** mem_query_source_rep sg pe view |--
    store_memory_control sg pe image ** mem_query_source_frame sg view entry.
Proof.
  intros sg pe [original|id] entry image Henabled Haddress Himage.
  - cbn [mem_query_selected] in Himage; subst image.
    cbn [mem_query_source_rep mem_query_source_frame]; entailer!.
  - cbn [mem_query_address] in Haddress; subst pe.
    cbn [mem_query_selected] in Himage.
    cbn [mem_query_source_rep mem_query_source_frame].
    rewrite UCOS2_inv_split_memory; Intros.
    unfold memory_configured_rep; rewrite Henabled; unfold memory_raw_rep.
    sep_apply_l_atomic (memory_controls_split_control sg entry.(MemoryState) id image Himage).
    entailer!.
Qed.

Lemma mem_query_source_merge : forall sg pe view entry image,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
  mem_query_address sg pe view -> mem_query_selected view entry image ->
  store_memory_control sg pe image ** mem_query_source_frame sg view entry |--
    UCOS2_inv sg entry ** mem_query_source_rep sg pe view.
Proof.
  intros sg pe [original|id] entry image Henabled Haddress Himage.
  - cbn [mem_query_selected] in Himage; subst image.
    cbn [mem_query_source_rep mem_query_source_frame]; entailer!.
  - cbn [mem_query_address] in Haddress; subst pe.
    cbn [mem_query_selected] in Himage.
    cbn [mem_query_source_rep mem_query_source_frame]; Intros.
    sep_apply_l_atomic (memory_controls_merge_control sg entry.(MemoryState) id image Himage).
    rewrite UCOS2_inv_split_memory; unfold memory_configured_rep; rewrite Henabled.
    unfold memory_raw_rep; entailer!.
Qed.

Definition mem_query_acquire_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (mask saved : Z)
  (before entry : UCOS2_Verify_State) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg before /\ UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved.

Lemma mem_query_save_consequence : forall platform critical sg invocation origin mask saved before entry,
  UCOS2_state_inv sg before ->
  critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_raw_rep sg entry |--
  coq_prop (mem_query_acquire_facts critical sg invocation mask saved before entry) &&
    (critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg entry).
Proof.
  intros platform critical sg invocation origin mask saved before entry Hvalid Hinterval Hsaved.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation before entry Hinterval Hvalid)) as Hentry.
  unfold mem_query_acquire_facts, UCOS2_inv; entailer!.
Qed.

Definition mem_query_restore_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (released : UCOS2_Verify_State) : Assertion :=
  EX current, coq_prop (critical_region_interval critical sg invocation released current) &&
    mutex_query_closed platform critical sg invocation origin (armv7a_irq_fiq_mask saved) current.

Lemma mem_query_restore_consequence : forall platform critical sg invocation origin saved released current,
  UCOS2_state_inv sg released ->
  critical_region_interval critical sg invocation released current ->
  interrupt_platform_running platform invocation origin (armv7a_irq_fiq_mask saved) **
    critical_region_outside critical sg invocation current |--
  mem_query_restore_post platform critical sg invocation origin saved released.
Proof.
  intros platform critical sg invocation origin saved released current Hvalid Hinterval.
  pose proof (proj1 (critical_region_interval_transports_resources
    critical sg invocation released current Hinterval Hvalid)) as Hcurrent.
  unfold mem_query_restore_post, mutex_query_closed; Exists current; entailer!.
Qed.

(** The protected observation reads the acquired image. The final ret computes
    the private output count only after the actual Restore interval. *)
Definition mem_query_observe (view : MemQueryView) : program UCOS2_Verify_State MemoryControlImage :=
  fun entry image after => after = entry /\ mem_query_selected view entry image.

Definition mem_query_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (view : MemQueryView) (pe pd : addr)
  : program UCOS2_Verify_State (Z * option (list Z)) :=
  if Z.eqb pe 0 then StateRelMonad.ret (96, None)
  else if Z.eqb pd 0 then StateRelMonad.ret (97, None)
  else StateRelMonad.bind (update (critical_region_interval critical sg invocation))
    (fun _ => StateRelMonad.bind (mem_query_observe view) (fun image =>
      StateRelMonad.bind (update (critical_region_interval critical sg invocation))
        (fun _ => StateRelMonad.ret (0, Some (memory_query_snapshot image))))).

Definition mem_query_safe critical sg invocation view pe pd before
  (X : Z -> option (list Z) -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq before) (mem_query_program critical sg invocation view pe pd)
    (fun result current => X (fst result) (snd result) current).

Lemma mem_query_program_null_control : forall critical sg invocation view pd before,
  mem_query_program critical sg invocation view 0 pd before (96, None) before.
Proof. intros; unfold mem_query_program, StateRelMonad.ret; cbn; auto. Qed.

Lemma mem_query_program_null_output : forall critical sg invocation view pe before,
  pe <> 0 -> mem_query_program critical sg invocation view pe 0 before (97, None) before.
Proof.
  intros; unfold mem_query_program; rewrite (proj2 (Z.eqb_neq _ _) H).
  unfold StateRelMonad.ret; cbn; auto.
Qed.

Lemma mem_query_program_success : forall critical sg invocation view pe pd before entry current image,
  pe <> 0 -> pd <> 0 ->
  critical_region_interval critical sg invocation before entry ->
  mem_query_selected view entry image ->
  critical_region_interval critical sg invocation entry current ->
  mem_query_program critical sg invocation view pe pd before
    (0, Some (memory_query_snapshot image)) current.
Proof.
  intros critical sg invocation view pe pd before entry current image Hpe Hpd Hacquire Himage Hrestore.
  unfold mem_query_program; rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Hpd).
  unfold StateRelMonad.bind, update, mem_query_observe, StateRelMonad.ret.
  exists tt, entry; split; [exact Hacquire|].
  exists image, entry; split; [split; assumption || reflexivity|].
  exists tt, current; split; [exact Hrestore|]; split; reflexivity.
Qed.

Lemma mem_query_program_result_iff : forall critical sg invocation view pe pd before result current,
  mem_query_program critical sg invocation view pe pd before result current <->
  if Z.eqb pe 0 then result = (96, None) /\ before = current
  else if Z.eqb pd 0 then result = (97, None) /\ before = current
  else exists entry image,
    critical_region_interval critical sg invocation before entry /\
    mem_query_selected view entry image /\
    critical_region_interval critical sg invocation entry current /\
    result = (0, Some (memory_query_snapshot image)).
Proof.
  intros critical sg invocation view pe pd before result current.
  unfold mem_query_program; destruct (Z.eqb pe 0); [reflexivity|].
  destruct (Z.eqb pd 0); [reflexivity|].
  unfold StateRelMonad.bind, update, mem_query_observe, StateRelMonad.ret.
  split.
  - intros [u [entry [Hentry [image [released [[Hreleased Himage]
      [v [returned [Hreturn [Hresult Hcurrent]]]]]]]]]].
    subst released; subst current; exists entry, image; auto.
  - intros [entry [image [Hentry [Himage [Hreturn Hresult]]]]].
    exists tt, entry; split; [exact Hentry|].
    exists image, entry; split; [split; assumption || reflexivity|].
    exists tt, current; split; [exact Hreturn|]; split; assumption || reflexivity.
Qed.

Lemma mem_query_api_safe_return : forall critical sg invocation view pe pd before current code snapshot X,
  mem_query_program critical sg invocation view pe pd before (code, snapshot) current ->
  mem_query_safe critical sg invocation view pe pd before X ->
  safeExec (eq current) (StateRelMonad.ret (code, snapshot))
    (fun result state => X (fst result) (snd result) state).
Proof.
  intros critical sg invocation view pe pd before current code snapshot X Hprogram Hsafe.
  unfold mem_query_safe in Hsafe.
  eapply (highstependret_derive (mem_query_program critical sg invocation view pe pd)
    (eq before) (code, snapshot) (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma mem_query_program_has_result : forall critical sg invocation view pe pd before,
  (pe <> 0 -> pd <> 0 -> mem_query_admission critical sg invocation pe view before) ->
  exists result, mem_query_program critical sg invocation view pe pd before result before.
Proof.
  intros critical sg invocation view pe pd before Hinput.
  destruct (Z.eq_dec pe 0) as [->|Hpe].
  - exists (96, None); apply mem_query_program_null_control.
  - destruct (Z.eq_dec pd 0) as [->|Hpd].
    + exists (97, None); apply mem_query_program_null_output; exact Hpe.
    + destruct (Hinput Hpe Hpd) as [_ [_ [_ Hview]]].
      assert (Himage : exists image, mem_query_selected view before image).
      { destruct view as [image|id]; cbn in *; [eauto|tauto]. }
      destruct Himage as [image Himage].
      exists (0, Some (memory_query_snapshot image)).
      eapply mem_query_program_success; eauto; constructor.
Qed.

Definition mem_query_unread_name (sg : StableGlobVars) (pe : addr)
  (image : MemoryControlImage) : Assertion :=
  if sg.(osKernelConfig).(cfgMemoryNames)
  then (&(pe # "os_mem" ->ₛ "OSMemName")) # Ptr |-> image.(memImageName) else emp.

Definition mem_query_copy_frame (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask saved : Z) (before entry : UCOS2_Verify_State)
  (view : MemQueryView) (pe : addr) (image : MemoryControlImage) : Assertion :=
  coq_prop (mem_query_admission critical sg invocation pe view before /\
    mem_query_acquire_facts critical sg invocation mask saved before entry /\
    mem_query_selected view entry image) **
  (critical_region_masked platform critical sg invocation origin saved entry **
   mem_query_source_frame sg view entry ** mem_query_unread_name sg pe image).

(** The generated focus separates the acquisition/admission propositions.
    Their heap residue stays in the proposition carrier when fields are
    exposed and is returned to the separated facts on source reassembly. *)
Lemma mem_query_copy_frame_split_fields :
  forall platform critical sg invocation origin mask saved before entry view pe,
  coq_prop (mem_query_acquire_facts critical sg invocation mask saved before entry) **
  coq_prop (mem_query_admission critical sg invocation pe view before) **
  critical_region_masked platform critical sg invocation origin saved entry **
  UCOS2_inv sg entry ** mem_query_source_rep sg pe view |--
  EX image,
    mem_query_copy_frame platform critical sg invocation origin mask saved before entry view pe image **
    (&(pe # "os_mem" ->ₛ "OSMemAddr")) # Ptr |-> image.(memImageBase) **
    (&(pe # "os_mem" ->ₛ "OSMemFreeList")) # Ptr |-> image.(memImageFree) **
    (&(pe # "os_mem" ->ₛ "OSMemBlkSize")) # UInt |-> image.(memImageSize) **
    (&(pe # "os_mem" ->ₛ "OSMemNBlks")) # UInt |-> image.(memImageCount) **
    (&(pe # "os_mem" ->ₛ "OSMemNFree")) # UInt |-> image.(memImageNFree).
Proof.
  intros; Intros.
  match goal with H : mem_query_admission _ _ _ _ _ _ |- _ => rename H into Hadmission end.
  match goal with H : mem_query_acquire_facts _ _ _ _ _ _ _ |- _ => rename H into Hacquire end.
  destruct (mem_query_acquired_image critical sg invocation pe view before entry Hadmission
    (proj1 (proj2 Hacquire)) (proj1 Hacquire)) as [image Himage].
  pose proof (proj1 Hadmission) as Henabled.
  pose proof (proj1 (proj2 (proj2 Hadmission))) as Haddress.
  sep_apply_l_atomic (mem_query_source_split sg pe view entry image Henabled Haddress Himage).
  rewrite store_memory_control_layout_equiv.
  sep_apply_l_atomic mutex_query_truep_sepcon_merge.
  Exists image; unfold mem_query_copy_frame, mem_query_unread_name.
  entailer!.
Qed.

Lemma mem_query_copy_frame_merge_fields :
  forall platform critical sg invocation origin mask saved before entry view pe image,
  mem_query_copy_frame platform critical sg invocation origin mask saved before entry view pe image **
  (&(pe # "os_mem" ->ₛ "OSMemAddr")) # Ptr |-> image.(memImageBase) **
  (&(pe # "os_mem" ->ₛ "OSMemFreeList")) # Ptr |-> image.(memImageFree) **
  (&(pe # "os_mem" ->ₛ "OSMemBlkSize")) # UInt |-> image.(memImageSize) **
  (&(pe # "os_mem" ->ₛ "OSMemNBlks")) # UInt |-> image.(memImageCount) **
  (&(pe # "os_mem" ->ₛ "OSMemNFree")) # UInt |-> image.(memImageNFree) |--
  coq_prop (mem_query_acquire_facts critical sg invocation mask saved before entry) **
  coq_prop (mem_query_selected view entry image) **
  critical_region_masked platform critical sg invocation origin saved entry **
  UCOS2_inv sg entry ** mem_query_source_rep sg pe view.
Proof.
  intros; unfold mem_query_copy_frame, mem_query_unread_name; Intros.
  rewrite <- mutex_query_truep_sepcon_equiv at 1.
  destruct H as [Hadmission [Hacquire Himage]].
  pose proof (proj1 Hadmission) as Henabled.
  pose proof (proj1 (proj2 (proj2 Hadmission))) as Haddress.
  entailer!.
  sep_apply_r_atomic (mem_query_source_merge sg pe view entry image Henabled Haddress Himage).
  rewrite store_memory_control_layout_equiv.
  entailer!.
Qed.

Definition mem_query_output_rep (pd : addr) (snapshot : list Z) : Assertion :=
  (&(pd # "os_mem_data" ->ₛ "OSAddr")) # Ptr |-> nth 0 snapshot 0 **
  (&(pd # "os_mem_data" ->ₛ "OSFreeList")) # Ptr |-> nth 1 snapshot 0 **
  (&(pd # "os_mem_data" ->ₛ "OSBlkSize")) # UInt |-> nth 2 snapshot 0 **
  (&(pd # "os_mem_data" ->ₛ "OSNBlks")) # UInt |-> nth 3 snapshot 0 **
  (&(pd # "os_mem_data" ->ₛ "OSNFree")) # UInt |-> nth 4 snapshot 0 **
  (&(pd # "os_mem_data" ->ₛ "OSNUsed")) # UInt |-> nth 5 snapshot 0.

Definition mem_query_result_resources (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (view : MemQueryView) (pe pd : addr)
  (snapshot : option (list Z)) (current : UCOS2_Verify_State) : Assertion :=
  match snapshot with
  | None => emp
  | Some observed => mutex_query_closed platform critical sg invocation origin mask current **
      mem_query_source_rep sg pe view ** mem_query_output_rep pd observed
  end.

Definition mem_query_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars) (invocation : nat)
  (origin : TaskInvocationOrigin) (mask : Z) (view : MemQueryView) (pe pd : addr)
  (before : UCOS2_Verify_State) (code : Z)
  (X : Z -> option (list Z) -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX snapshot current,
    coq_prop (mem_query_program critical sg invocation view pe pd before (code, snapshot) current /\
      safeExec (eq current) (StateRelMonad.ret (code, snapshot))
        (fun result state => X (fst result) (snd result) state)) **
    mem_query_result_resources platform critical sg invocation origin mask view pe pd snapshot current.

Lemma mem_query_used_machine_subtraction : forall image,
  unsigned_last_nbits (image.(memImageCount) - image.(memImageNFree)) 32 =
  nth 5 (memory_query_snapshot image) 0.
Proof. intros; unfold memory_query_snapshot, unsigned_last_nbits, kernel_u32; reflexivity. Qed.

Lemma mem_query_initialized_used_count : forall sg state id partition image,
  valid_memory_state sg state -> state.(memPartitions) id = Some partition ->
  state.(memControlImages) id = Some image ->
  0 <= image.(memImageNFree) <= image.(memImageCount) /\
  nth 5 (memory_query_snapshot image) 0 = image.(memImageCount) - image.(memImageNFree).
Proof.
  intros sg state id partition image [_ [Hpart _]] Hpartition Himage.
  destruct (Hpart id partition Hpartition) as [_ [Hvalid Hcontrol]].
  rewrite Himage in Hcontrol; injection Hcontrol as Himage'; subst image.
  pose proof (memory_free_count_in_range id partition Hvalid) as Hcount.
  pose proof (proj1 Hvalid) as Hregion.
  unfold memory_region_valid in Hregion.
  cbn [memory_partition_image memImageCount memImageNFree].
  split; [exact Hcount|].
  rewrite memory_query_snapshot_used_count; cbn [memory_partition_image memImageCount memImageNFree].
  apply kernel_u32_identity; lia.
Qed.
