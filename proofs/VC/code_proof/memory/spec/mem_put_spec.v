Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.
Require Import Coq.Strings.String.
From SimpleC.SL Require Import Mem SeparationLogic.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Export Ucos2Verify.lib.memory.
Require Export Ucos2Verify.lib.memory_execution.
Require Export Ucos2Verify.lib.kernel_resources.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_accept_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_query_spec.

Import ListNotations UCOS2_C_Rules Monad.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.
Local Open Scope Z_scope.

(** OSMemPut's source-ordered API program and spatial bridges. Runtime
    client protocols are separate caller/environment relies, not extra CPU
    guarantees. The same actual critical interval transports geometry;
    current allocation is obtained from physical free-list exclusion. *)

(** The raw image is independently owned by the caller. The two argument
    errors do not touch it; the full branch reads the count but writes no
    block word. The success observation records the exact three stores. *)
Record MemPutRawResult := {
  mem_put_raw_error : Z;
  mem_put_raw_image : MemoryControlImage;
  mem_put_raw_link : option addr
}.

Definition mem_put_raw_result (pmem pblk : addr) (image : MemoryControlImage)
  : MemPutRawResult :=
  if Z.eqb pmem 0 then
    {| mem_put_raw_error := 96; mem_put_raw_image := image; mem_put_raw_link := None |}
  else if Z.eqb pblk 0 then
    {| mem_put_raw_error := 95; mem_put_raw_image := image; mem_put_raw_link := None |}
  else if image.(memImageCount) <=? image.(memImageNFree) then
    {| mem_put_raw_error := 94; mem_put_raw_image := image; mem_put_raw_link := None |}
  else
    {| mem_put_raw_error := 0; mem_put_raw_image := memory_put_image image pblk;
       mem_put_raw_link := Some image.(memImageFree) |}.

Lemma mem_put_raw_null_control : forall pblk image,
  mem_put_raw_error (mem_put_raw_result 0 pblk image) = 96 /\
  mem_put_raw_image (mem_put_raw_result 0 pblk image) = image /\
  mem_put_raw_link (mem_put_raw_result 0 pblk image) = None.
Proof. intros; repeat split; reflexivity. Qed.

Lemma mem_put_raw_null_block : forall pmem image,
  pmem <> 0 ->
  mem_put_raw_error (mem_put_raw_result pmem 0 image) = 95 /\
  mem_put_raw_image (mem_put_raw_result pmem 0 image) = image /\
  mem_put_raw_link (mem_put_raw_result pmem 0 image) = None.
Proof.
  intros pmem image Hpmem; unfold mem_put_raw_result.
  destruct (Z.eqb pmem 0) eqn:E; [apply Z.eqb_eq in E; contradiction|].
  repeat split; reflexivity.
Qed.

Lemma mem_put_raw_full : forall pmem pblk image,
  pmem <> 0 -> pblk <> 0 -> image.(memImageCount) <= image.(memImageNFree) ->
  mem_put_raw_error (mem_put_raw_result pmem pblk image) = 94 /\
  mem_put_raw_image (mem_put_raw_result pmem pblk image) = image /\
  mem_put_raw_link (mem_put_raw_result pmem pblk image) = None.
Proof.
  intros pmem pblk image Hp Hb Hcount; unfold mem_put_raw_result.
  destruct (Z.eqb pmem 0) eqn:Ep; [apply Z.eqb_eq in Ep; contradiction|].
  destruct (Z.eqb pblk 0) eqn:Eb; [apply Z.eqb_eq in Eb; contradiction|].
  assert (E : (memImageCount image <=? memImageNFree image) = true)
    by (apply Z.leb_le; exact Hcount).
  rewrite E; repeat split; reflexivity.
Qed.

Lemma mem_put_raw_success : forall pmem pblk image,
  pmem <> 0 -> pblk <> 0 -> image.(memImageNFree) < image.(memImageCount) ->
  mem_put_raw_error (mem_put_raw_result pmem pblk image) = 0 /\
  mem_put_raw_image (mem_put_raw_result pmem pblk image) = memory_put_image image pblk /\
  mem_put_raw_link (mem_put_raw_result pmem pblk image) = Some image.(memImageFree).
Proof.
  intros pmem pblk image Hp Hb Hcount; unfold mem_put_raw_result.
  destruct (Z.eqb pmem 0) eqn:Ep; [apply Z.eqb_eq in Ep; contradiction|].
  destruct (Z.eqb pblk 0) eqn:Eb; [apply Z.eqb_eq in Eb; contradiction|].
  assert (E : (memImageCount image <=? memImageNFree image) = false)
    by (apply Z.leb_gt; exact Hcount).
  rewrite E; repeat split; reflexivity.
Qed.

(** The increment bound is derived from the two typed count cells and
    the source's strict success guard, not from partition validity. *)
Lemma mem_put_increment_in_range : forall free count,
  0 <= free < 4294967296 -> 0 <= count < 4294967296 -> free < count ->
  0 <= free + 1 < 4294967296 /\ kernel_u32 (free + 1) = free + 1.
Proof. intros; split; [lia|apply kernel_u32_identity; lia]. Qed.

Definition mem_put_control_frame (sg : StableGlobVars) (base : addr)
  (image : MemoryControlImage) : Assertion :=
  &(base # "os_mem" ->ₛ "OSMemAddr") # Ptr |-> image.(memImageBase) **
  &(base # "os_mem" ->ₛ "OSMemBlkSize") # UInt |-> image.(memImageSize) **
  (if sg.(osKernelConfig).(cfgMemoryNames) then
    &(base # "os_mem" ->ₛ "OSMemName") # Ptr |-> image.(memImageName) else emp).

Lemma mem_put_control_split_counts_head : forall sg base image,
  store_memory_control sg base image |--
  &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> image.(memImageFree) **
  &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> image.(memImageNFree) **
  &(base # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> image.(memImageCount) **
  mem_put_control_frame sg base image.
Proof.
  intros; rewrite store_memory_control_layout_equiv;
    unfold mem_put_control_frame; entailer!.
Qed.

Lemma mem_put_control_merge_counts_head : forall sg base image,
  &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> image.(memImageFree) **
  &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> image.(memImageNFree) **
  &(base # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> image.(memImageCount) **
  mem_put_control_frame sg base image |-- store_memory_control sg base image.
Proof.
  intros; rewrite store_memory_control_layout_equiv;
    unfold mem_put_control_frame; entailer!.
Qed.

Lemma mem_put_control_merge_updated_counts_head : forall sg base image block,
  &(base # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> block **
  &(base # "os_mem" ->ₛ "OSMemNFree") # UInt |-> kernel_u32 (image.(memImageNFree) + 1) **
  &(base # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> image.(memImageCount) **
  mem_put_control_frame sg base image |--
    store_memory_control sg base (memory_put_image image block).
Proof.
  intros; rewrite store_memory_control_layout_equiv;
    unfold mem_put_control_frame, memory_put_image; simpl; entailer!.
Qed.


(** A source-client rely, not an extra field of the CPU or the generic
    client certificate. It classifies each registered operation by the
    concrete Memory producer it executes; it does not assume an acquired
    lookup, generation equality or a complete Memory-state frame. *)
Definition mem_put_runtime_client_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) : Prop :=
  forall action before after,
    critical.(critical_region_clients) action -> UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    memory_runtime_step before.(MemoryState) after.(MemoryState).

(** Optional full-error caller mode. Its environment can register Put,
    reserve, publication, name stores and Get on other partitions, but no
    Get of this target during acquisition. It is not implied by historical
    fullness and is not imposed on the raw, loan or NULL-input modes. *)
Definition mem_put_full_client_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (id : MemID) : Prop :=
  forall action before after,
    critical.(critical_region_clients) action -> UCOS2_state_inv sg before ->
    kernel_client_step action sg before after ->
    memory_runtime_without_get_at id before.(MemoryState) after.(MemoryState).

Lemma mem_put_task_creation_runtime_step : forall action sg before after,
  kernel_client_step (task_creation_client action) sg before after ->
  memory_runtime_step before.(MemoryState) after.(MemoryState).
Proof.
  intros action sg before after [_ [_ ->]]; apply MemoryRuntimeFramesPartitions;
    destruct action; reflexivity.
Qed.

Lemma mem_put_client_trace_preserves_geometry :
  forall critical sg observer event_observer before stopped after,
  mem_put_runtime_client_protocol critical sg ->
  kernel_client_resource_trace critical.(critical_region_clients)
    sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before -> forall id p,
  before.(MemoryState).(memPartitions) id = Some p ->
  exists q, after.(MemoryState).(memPartitions) id = Some q /\
    memory_partition_geometry_eq p q.
Proof.
  intros critical sg observer event_observer before stopped after Hprotocol Htrace.
  induction Htrace as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid id p Hlookup.
  - exists p; split; [exact Hlookup|apply memory_partition_geometry_eq_refl].
  - destruct (memory_runtime_step_preserves_partition_geometry _ _ id p
      (Hprotocol action before middle Hin Hvalid Hstep) Hlookup) as [q [Hq Hpq]].
    pose proof (kernel_client_preserves_validity action
      (critical_region_client_certificates critical action Hin)
      sg before middle Hvalid Hstep) as Hmiddle.
    destruct (IH Hmiddle id q Hq) as [r [Hr Hqr]].
    exists r; split; [exact Hr|eapply memory_partition_geometry_eq_trans; eassumption].
Qed.

Lemma mem_put_interval_preserves_geometry : forall critical sg invocation before entry id historical,
  mem_put_runtime_client_protocol critical sg ->
  critical_region_interval critical sg invocation before entry ->
  UCOS2_state_inv sg before -> before.(MemoryState).(memPartitions) id = Some historical ->
  exists current, entry.(MemoryState).(memPartitions) id = Some current /\
    memory_partition_geometry_eq historical current.
Proof.
  intros critical sg invocation before entry id historical Hprotocol Hinterval Hvalid Hlookup.
  eapply mem_put_client_trace_preserves_geometry; try eassumption.
  apply critical_region_interval_raw_trace; exact Hinterval.
Qed.

Lemma mem_put_client_trace_preserves_full :
  forall critical sg observer event_observer before stopped after id,
  mem_put_full_client_protocol critical sg id ->
  kernel_client_resource_trace critical.(critical_region_clients)
    sg observer event_observer before stopped after ->
  UCOS2_state_inv sg before -> forall p,
  before.(MemoryState).(memPartitions) id = Some p ->
  p.(memBlockCount) <= Z.of_nat (List.length p.(memFreeBlocks)) ->
  exists q, after.(MemoryState).(memPartitions) id = Some q /\
    q.(memBlockCount) <= Z.of_nat (List.length q.(memFreeBlocks)).
Proof.
  intros critical sg observer event_observer before stopped after id Hprotocol Htrace.
  induction Htrace as [s|action before middle after stopped Hin Hforeign Hevent Hstep Htail IH];
    intros Hvalid p Hlookup Hfull.
  - exists p; auto.
  - destruct (memory_runtime_without_get_at_preserves_full id _ _ p
      (Hprotocol action before middle Hin Hvalid Hstep) Hlookup Hfull) as [q [Hq Hqfull]].
    eapply IH; [|exact Hq|exact Hqfull].
    eapply kernel_client_preserves_validity;
      [exact (critical_region_client_certificates critical action Hin)|exact Hvalid|exact Hstep].
Qed.

Lemma mem_put_interval_preserves_full : forall critical sg invocation before entry id historical,
  mem_put_full_client_protocol critical sg id ->
  critical_region_interval critical sg invocation before entry ->
  UCOS2_state_inv sg before -> before.(MemoryState).(memPartitions) id = Some historical ->
  historical.(memBlockCount) <= Z.of_nat (List.length historical.(memFreeBlocks)) ->
  exists current, entry.(MemoryState).(memPartitions) id = Some current /\
    current.(memBlockCount) <= Z.of_nat (List.length current.(memFreeBlocks)).
Proof.
  intros critical sg invocation before entry id historical Hprotocol Hinterval Hvalid Hlookup Hfull.
  eapply mem_put_client_trace_preserves_full; try eassumption.
  apply critical_region_interval_raw_trace; exact Hinterval.
Qed.

Inductive MemPutInput : Type :=
| MemPutRawInput (image : MemoryControlImage)
| MemPutPoolInput (id : MemID) (historical : MemoryPartitionState)
    (block : Z) (loan : MemoryBlockLoan)
| MemPutFullPoolInput (id : MemID) (historical : MemoryPartitionState).

Definition mem_put_input_image (input : MemPutInput) : MemoryControlImage :=
  match input with
  | MemPutRawInput image => image
  | MemPutPoolInput _ historical _ _ => memory_partition_image historical
  | MemPutFullPoolInput _ historical => memory_partition_image historical
  end.

Definition mem_put_input_protocol (critical : CriticalRegionResources)
  (sg : StableGlobVars) (before : UCOS2_Verify_State) (pmem pblk : addr)
  (input : MemPutInput) : Prop :=
  if (Z.eqb pmem 0 || Z.eqb pblk 0)%bool then True else
  match input with
  | MemPutRawInput _ => True
  | MemPutPoolInput id historical block loan =>
      pmem = memory_control_addr sg id /\ pblk = memory_block_addr historical block /\
      before.(MemoryState).(memPartitions) id = Some historical /\
      historical.(memAllocatedBlocks) block = Some loan /\
      mem_put_runtime_client_protocol critical sg
  | MemPutFullPoolInput id historical =>
      pmem = memory_control_addr sg id /\
      before.(MemoryState).(memPartitions) id = Some historical /\
      historical.(memBlockCount) <= Z.of_nat (List.length historical.(memFreeBlocks)) /\
      mem_put_full_client_protocol critical sg id
  end.

(** No storage is needed for either NULL error. A raw full image and the
    separately protected full-pool mode require no block word. A pool loan
    is real storage plus a historical identity; its identity is never
    silently reindexed at acquisition. *)
Definition mem_put_input_resources (sg : StableGlobVars) (pmem pblk : addr)
  (input : MemPutInput) : Assertion :=
  if (Z.eqb pmem 0 || Z.eqb pblk 0)%bool then emp else
  match input with
  | MemPutRawInput image => store_memory_control sg pmem image **
      (if image.(memImageCount) <=? image.(memImageNFree) then emp
       else EX first : addr, pblk # Ptr |-> first)
  | MemPutPoolInput _ historical block _ => memory_block_storage historical block
  | MemPutFullPoolInput _ _ => emp
  end.

Definition mem_put_profile (sg : StableGlobVars) : Prop :=
  sg.(osKernelConfig).(cfgArgumentChecks) = true /\
  sg.(osKernelConfig).(cfgMemoryEnabled) = true /\
  sg.(osKernelConfig).(cfgMemoryNames) = true.

Record MemPutAcquired := {
  mem_put_acquired_image : MemoryControlImage;
  mem_put_acquired_partition : option MemoryPartitionState
}.

Definition mem_put_acquired_facts (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (before entry : UCOS2_Verify_State)
  (pmem pblk : addr) (input : MemPutInput) (acquired : MemPutAcquired) : Prop :=
  pmem <> 0 /\ pblk <> 0 /\ UCOS2_state_inv sg entry /\
  critical_region_interval critical sg invocation before entry /\
  match input with
  | MemPutRawInput image => acquired =
      {| mem_put_acquired_image := image; mem_put_acquired_partition := None |}
  | MemPutPoolInput id historical block loan => exists current,
      acquired = {| mem_put_acquired_image := memory_partition_image current;
                    mem_put_acquired_partition := Some current |} /\
      pmem = memory_control_addr sg id /\ pblk = memory_block_addr current block /\
      entry.(MemoryState).(memPartitions) id = Some current /\
      valid_memory_partition id historical /\ valid_memory_partition id current /\
      historical.(memAllocatedBlocks) block = Some loan /\
      memory_partition_geometry_eq historical current
  | MemPutFullPoolInput id _ => exists current,
      acquired = {| mem_put_acquired_image := memory_partition_image current;
                    mem_put_acquired_partition := Some current |} /\
      pmem = memory_control_addr sg id /\
      entry.(MemoryState).(memPartitions) id = Some current /\
      current.(memBlockCount) <= Z.of_nat (List.length current.(memFreeBlocks))
  end.

Definition mem_put_focus_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pmem pblk : addr) (input : MemPutInput) (acquired : MemPutAcquired) : Assertion :=
  mem_put_control_frame sg pmem acquired.(mem_put_acquired_image) **
  match input, acquired.(mem_put_acquired_partition) with
  | MemPutRawInput image, None => UCOS2_inv sg entry **
      (if image.(memImageCount) <=? image.(memImageNFree) then emp
       else EX first : addr, pblk # Ptr |-> first)
  | MemPutPoolInput id historical block _, Some current =>
      memory_block_storage historical block **
      store_memory_free_blocks current current.(memFreeBlocks) **
      memory_raw_rep_without_partition sg entry.(MemoryState) id **
      UCOS2_raw_rep_missing_memory sg entry
  | MemPutFullPoolInput id _, Some current =>
      store_memory_free_blocks current current.(memFreeBlocks) **
      memory_raw_rep_without_partition sg entry.(MemoryState) id **
      UCOS2_raw_rep_missing_memory sg entry
  | _, _ => coq_prop False
  end.

Definition mem_put_count_cells (pmem : addr) (image : MemoryControlImage) : Assertion :=
  &(pmem # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> image.(memImageFree) **
  &(pmem # "os_mem" ->ₛ "OSMemNFree") # UInt |-> image.(memImageNFree) **
  &(pmem # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> image.(memImageCount).

Definition mem_put_success_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pmem : addr) (input : MemPutInput) (acquired : MemPutAcquired) : Assertion :=
  mem_put_control_frame sg pmem acquired.(mem_put_acquired_image) **
  match input, acquired.(mem_put_acquired_partition) with
  | MemPutRawInput _, None => UCOS2_inv sg entry
  | MemPutPoolInput id _ block _, Some current =>
      memory_block_tail current block **
      store_memory_free_blocks current current.(memFreeBlocks) **
      memory_raw_rep_without_partition sg entry.(MemoryState) id **
      UCOS2_raw_rep_missing_memory sg entry
  | _, _ => coq_prop False
  end.

Definition mem_put_current_allocation (input : MemPutInput) (acquired : MemPutAcquired) : Prop :=
  match input, acquired.(mem_put_acquired_partition) with
  | MemPutRawInput _, None => True
  | MemPutPoolInput _ _ block _, Some current =>
      exists current_loan, current.(memAllocatedBlocks) block = Some current_loan
  | _, _ => False
  end.

Definition mem_put_checkpoint (entry : UCOS2_Verify_State)
  (input : MemPutInput) (acquired : MemPutAcquired) : UCOS2_Verify_State :=
  if acquired.(mem_put_acquired_image).(memImageCount) <=?
     acquired.(mem_put_acquired_image).(memImageNFree) then entry else
  match input, acquired.(mem_put_acquired_partition) with
  | MemPutPoolInput id _ block _, Some current =>
      replace_MemoryS (memory_replace_partition entry.(MemoryState) id
        (memory_put_partition current block)) entry
  | _, _ => entry
  end.

Definition mem_put_result_resources (sg : StableGlobVars) (pmem pblk : addr)
  (input : MemPutInput) (result : MemPutRawResult) : Assertion :=
  if (Z.eqb pmem 0 || Z.eqb pblk 0)%bool then emp else
  match input with
  | MemPutRawInput _ => store_memory_control sg pmem result.(mem_put_raw_image) **
      match result.(mem_put_raw_link) with None => emp | Some link => pblk # Ptr |-> link end
  | MemPutPoolInput _ historical block _ =>
      if Z.eqb result.(mem_put_raw_error) 0 then emp else memory_block_storage historical block
  | MemPutFullPoolInput _ _ => emp
  end.

(** The program follows the source guards and the two actual intervals.
    No current-allocation or validity test is hidden inside its success
    guard. Those are proof obligations of the caller/resource protocol. *)
Definition mem_put_protected_result (entry : UCOS2_Verify_State)
  (pmem pblk : addr) (input : MemPutInput) (acquired : MemPutAcquired)
  (result : MemPutRawResult) (checkpoint : UCOS2_Verify_State) : Prop :=
  result = mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image) /\
  checkpoint = mem_put_checkpoint entry input acquired /\
  match input with
  | MemPutRawInput image => acquired =
      {| mem_put_acquired_image := image; mem_put_acquired_partition := None |}
  | MemPutPoolInput id _ _ _ | MemPutFullPoolInput id _ => exists current,
      entry.(MemoryState).(memPartitions) id = Some current /\
      acquired = {| mem_put_acquired_image := memory_partition_image current;
                    mem_put_acquired_partition := Some current |}
  end.

Definition mem_put_completed (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (before entry : UCOS2_Verify_State) (pmem pblk : addr)
  (input : MemPutInput) (acquired : MemPutAcquired) (code : Z)
  (checkpoint : UCOS2_Verify_State) : Prop :=
  pmem <> 0 /\ pblk <> 0 /\
  critical_region_interval critical sg invocation before entry /\
  mem_put_protected_result entry pmem pblk input acquired
    (mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image)) checkpoint /\
  code = mem_put_raw_error (mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image)).

Definition mem_put_program (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pmem pblk : addr) (input : MemPutInput)
  : program UCOS2_Verify_State MemPutRawResult :=
  fun before result after =>
    if (Z.eqb pmem 0 || Z.eqb pblk 0)%bool then
      result = mem_put_raw_result pmem pblk (mem_put_input_image input) /\ after = before
    else exists entry acquired checkpoint,
      critical_region_interval critical sg invocation before entry /\
      mem_put_protected_result entry pmem pblk input acquired result checkpoint /\
      critical_region_interval critical sg invocation checkpoint after.

Definition mem_put_safe critical sg invocation pmem pblk input before X : Prop :=
  safeExec (fun state => state = before)
    (mem_put_program critical sg invocation pmem pblk input) X.

Definition mem_put_return_safe after result
  (X : MemPutRawResult -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (fun state => state = after) (ret result) X.

Lemma mem_put_program_safe_return : forall critical sg invocation pmem pblk input before result after X,
  mem_put_safe critical sg invocation pmem pblk input before X ->
  mem_put_program critical sg invocation pmem pblk input before result after ->
  mem_put_return_safe after result X.
Proof.
  intros critical sg invocation pmem pblk input before result after X Hsafe Hstep.
  unfold mem_put_safe in Hsafe; unfold mem_put_return_safe.
  eapply highstependret_derive with
    (c1 := mem_put_program critical sg invocation pmem pblk input)
    (P := fun s => s = before) (P' := fun (_ : MemPutRawResult) s => s = after).
  - intros s ->; exists after; split; [exact Hstep|reflexivity].
  - exact Hsafe.
Qed.

Lemma mem_put_program_has_result : forall critical sg invocation pmem pblk input before,
  mem_put_input_protocol critical sg before pmem pblk input ->
  exists result after, mem_put_program critical sg invocation pmem pblk input before result after.
Proof.
  intros critical sg invocation pmem pblk input before Hinput.
  unfold mem_put_input_protocol in Hinput; unfold mem_put_program.
  destruct (Z.eqb pmem 0 || Z.eqb pblk 0)%bool eqn:E.
  - exists (mem_put_raw_result pmem pblk (mem_put_input_image input)), before; auto.
  - destruct input as [image|id historical block loan|id historical].
    + set (acquired := {| mem_put_acquired_image := image; mem_put_acquired_partition := None |}).
      exists (mem_put_raw_result pmem pblk image), (mem_put_checkpoint before (MemPutRawInput image) acquired).
      exists before, acquired, (mem_put_checkpoint before (MemPutRawInput image) acquired).
      split; [constructor|]. split; [unfold mem_put_protected_result, acquired; auto|constructor].
    + destruct Hinput as [_ [_ [Hlookup _]]].
      set (acquired := {| mem_put_acquired_image := memory_partition_image historical;
                         mem_put_acquired_partition := Some historical |}).
      exists (mem_put_raw_result pmem pblk (memory_partition_image historical)),
        (mem_put_checkpoint before (MemPutPoolInput id historical block loan) acquired).
      exists before, acquired, (mem_put_checkpoint before (MemPutPoolInput id historical block loan) acquired).
      split; [constructor|]. split; [|constructor].
      unfold mem_put_protected_result, acquired; split; [reflexivity|].
      split; [reflexivity|]. exists historical; auto.
    + destruct Hinput as [_ [Hlookup _]].
      set (acquired := {| mem_put_acquired_image := memory_partition_image historical;
                         mem_put_acquired_partition := Some historical |}).
      exists (mem_put_raw_result pmem pblk (memory_partition_image historical)),
        (mem_put_checkpoint before (MemPutFullPoolInput id historical) acquired).
      exists before, acquired, (mem_put_checkpoint before (MemPutFullPoolInput id historical) acquired).
      split; [constructor|]. split; [|constructor].
      unfold mem_put_protected_result, acquired; split; [reflexivity|].
      split; [reflexivity|]. exists historical; auto.
Qed.

Lemma mem_put_completed_safe_return :
  forall critical sg invocation before entry pmem pblk input acquired code checkpoint after X,
  mem_put_safe critical sg invocation pmem pblk input before X ->
  mem_put_completed critical sg invocation before entry pmem pblk input acquired code checkpoint ->
  critical_region_interval critical sg invocation checkpoint after ->
  exists result, code = result.(mem_put_raw_error) /\
    mem_put_program critical sg invocation pmem pblk input before result after /\
    mem_put_return_safe after result X.
Proof.
  intros critical sg invocation before entry pmem pblk input acquired code checkpoint after X
    Hsafe [Hpmem [Hpblk [Hacquire [Hprotected Hcode]]]] Hrestore.
  set (result := mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image)).
  assert (Hprogram : mem_put_program critical sg invocation pmem pblk input before result after).
  { unfold mem_put_program.
    rewrite (proj2 (Z.eqb_neq pmem 0) Hpmem), (proj2 (Z.eqb_neq pblk 0) Hpblk); simpl.
    exists entry, acquired, checkpoint; auto. }
  exists result; split; [exact Hcode|]. split; [exact Hprogram|].
  eapply mem_put_program_safe_return; eassumption.
Qed.

Definition mem_put_api_post (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (before : UCOS2_Verify_State) (pmem pblk : addr) (input : MemPutInput) (code : Z)
  (X : MemPutRawResult -> UCOS2_Verify_State -> Prop) : Assertion :=
  EX result current,
    coq_prop (code = result.(mem_put_raw_error) /\
      mem_put_program critical sg invocation pmem pblk input before result current /\
      mem_put_return_safe current result X) &&
    (mutex_query_closed platform critical sg invocation origin mask current **
     mem_put_result_resources sg pmem pblk input result).

Lemma mem_put_state_memory_valid : forall sg state,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg state ->
  valid_memory_state sg state.(MemoryState).
Proof.
  intros sg state Henabled Hvalid.
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready, valid_memory_configuration in Hvalid.
  rewrite Henabled in Hvalid; tauto.
Qed.

Lemma mem_put_acquire_count_cells : forall critical sg invocation before entry pmem pblk input,
  mem_put_profile sg -> pmem <> 0 -> pblk <> 0 ->
  mem_put_input_protocol critical sg before pmem pblk input ->
  UCOS2_state_inv sg before -> UCOS2_state_inv sg entry ->
  critical_region_interval critical sg invocation before entry ->
  UCOS2_inv sg entry ** mem_put_input_resources sg pmem pblk input |--
    EX acquired,
      coq_prop (mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired) &&
      (mem_put_count_cells pmem acquired.(mem_put_acquired_image) **
       mem_put_focus_frame sg entry pmem pblk input acquired).
Proof.
  intros critical sg invocation before entry pmem pblk input
    [_ [Henabled _]] Hpmem Hpblk Hinput Hbefore Hentry Hinterval.
  assert (Ep : (pmem =? 0) = false) by (apply Z.eqb_neq; exact Hpmem).
  assert (Eb : (pblk =? 0) = false) by (apply Z.eqb_neq; exact Hpblk).
  unfold mem_put_input_protocol in Hinput; rewrite Ep, Eb in Hinput; simpl in Hinput.
  unfold mem_put_input_resources; rewrite Ep, Eb; simpl.
  destruct input as [image|id historical block loan|id historical].
  - Exists {| mem_put_acquired_image := image; mem_put_acquired_partition := None |}.
    unfold mem_put_count_cells, mem_put_focus_frame; simpl.
    sep_apply_l_atomic (mem_put_control_split_counts_head sg pmem image).
    assert (Hfacts : mem_put_acquired_facts critical sg invocation before entry pmem pblk
      (MemPutRawInput image)
      {| mem_put_acquired_image := image; mem_put_acquired_partition := None |}).
    { unfold mem_put_acquired_facts; repeat first [assumption|reflexivity|split]. }
    entailer!.
  - destruct Hinput as [Hpmemaddr [Hpblkaddr [Hhistorical [Hloan Hprotocol]]]].
    destruct (mem_put_interval_preserves_geometry critical sg invocation before entry id historical
      Hprotocol Hinterval Hbefore Hhistorical) as [current [Hcurrent Hgeometry]].
    pose proof (mem_put_state_memory_valid sg before Henabled Hbefore) as Hbeforemem.
    pose proof (mem_put_state_memory_valid sg entry Henabled Hentry) as Hentrymem.
    assert (Hhistvalid : valid_memory_partition id historical).
    { destruct Hbeforemem as [_ [Hparts _]]; exact (proj1 (proj2 (Hparts id historical Hhistorical))). }
    assert (Hcurrentvalid : valid_memory_partition id current).
    { destruct Hentrymem as [_ [Hparts _]]; exact (proj1 (proj2 (Hparts id current Hcurrent))). }
    assert (Hblockaddr : pblk = memory_block_addr current block).
    { rewrite Hpblkaddr; apply memory_partition_geometry_block_addr_eq; exact Hgeometry. }
    set (acquired := {| mem_put_acquired_image := memory_partition_image current;
                       mem_put_acquired_partition := Some current |}).
    assert (Hfacts : mem_put_acquired_facts critical sg invocation before entry pmem pblk
      (MemPutPoolInput id historical block loan) acquired).
    { unfold mem_put_acquired_facts; split; [exact Hpmem|]. split; [exact Hpblk|].
      split; [exact Hentry|]. split; [exact Hinterval|].
      exists current; repeat first [assumption|reflexivity|split]. }
    Exists acquired; unfold acquired, mem_put_count_cells, mem_put_focus_frame; simpl.
    rewrite UCOS2_inv_split_memory; unfold memory_configured_rep; rewrite Henabled.
    Intros.
    sep_apply_l_atomic (memory_raw_rep_split_partition sg entry.(MemoryState) id current Hentrymem Hcurrent).
    unfold memory_partition_rep.
    rewrite <- Hpmemaddr.
    sep_apply_l_atomic (mem_put_control_split_counts_head sg pmem (memory_partition_image current)).
    entailer!.
  - destruct Hinput as [Hpmemaddr [Hhistorical [Hfull Hprotocol]]].
    destruct (mem_put_interval_preserves_full critical sg invocation before entry id historical
      Hprotocol Hinterval Hbefore Hhistorical Hfull) as [current [Hcurrent Hcurrentfull]].
    pose proof (mem_put_state_memory_valid sg entry Henabled Hentry) as Hentrymem.
    set (acquired := {| mem_put_acquired_image := memory_partition_image current;
                       mem_put_acquired_partition := Some current |}).
    assert (Hfacts : mem_put_acquired_facts critical sg invocation before entry pmem pblk
      (MemPutFullPoolInput id historical) acquired).
    { unfold mem_put_acquired_facts; split; [exact Hpmem|]. split; [exact Hpblk|].
      split; [exact Hentry|]. split; [exact Hinterval|].
      exists current; repeat first [assumption|reflexivity|split]. }
    Exists acquired; unfold acquired, mem_put_count_cells, mem_put_focus_frame; simpl.
    rewrite UCOS2_inv_split_memory; unfold memory_configured_rep; rewrite Henabled.
    Intros.
    sep_apply_l_atomic (memory_raw_rep_split_partition sg entry.(MemoryState) id current Hentrymem Hcurrent).
    unfold memory_partition_rep; rewrite <- Hpmemaddr.
    sep_apply_l_atomic (mem_put_control_split_counts_head sg pmem (memory_partition_image current)).
    entailer!.
Qed.

Lemma mem_put_focus_success_word : forall critical sg invocation before entry pmem pblk input acquired,
  mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ->
  acquired.(mem_put_acquired_image).(memImageNFree) < acquired.(mem_put_acquired_image).(memImageCount) ->
  mem_put_focus_frame sg entry pmem pblk input acquired |--
    coq_prop (mem_put_current_allocation input acquired) &&
    (EX first : addr, pblk # Ptr |-> first ** mem_put_success_frame sg entry pmem input acquired).
Proof.
  intros critical sg invocation before entry pmem pblk input acquired Hfacts Hlt.
  destruct Hfacts as [Hpmem [Hpblk [Hentry [Hinterval Hview]]]].
  destruct input as [image|id historical block loan|id historical].
  - subst acquired; simpl in Hlt.
    assert (E : (memImageCount image <=? memImageNFree image) = false) by (apply Z.leb_gt; lia).
    unfold mem_put_focus_frame, mem_put_success_frame, mem_put_current_allocation; simpl; rewrite E.
    Intros first; Exists first; entailer!.
  - destruct Hview as [current [-> [Haddr [Hblock [Hlookup [Hhistorical [Hcurrent [Hloan Hgeometry]]]]]]]].
    unfold mem_put_focus_frame, mem_put_success_frame, mem_put_current_allocation; simpl.
    sepcon_right_assoc.
    sep_apply_l_atomic (memory_historical_block_current_allocation id historical current block loan
      Hhistorical Hcurrent Hloan Hgeometry).
    Intros.
    unfold memory_block_storage, memory_free_block_rep; Intros first; Exists first.
    rewrite Hblock; entailer!.
  - destruct Hview as [current [-> [_ [_ Hfull]]]]; simpl in Hlt; lia.
Qed.

Lemma mem_put_acquired_completed : forall critical sg invocation before entry pmem pblk input acquired,
  mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ->
  mem_put_completed critical sg invocation before entry pmem pblk input acquired
    (mem_put_raw_error (mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image)))
    (mem_put_checkpoint entry input acquired).
Proof.
  intros critical sg invocation before entry pmem pblk input acquired
    [Hpmem [Hpblk [Hvalid [Hinterval Hview]]]].
  unfold mem_put_completed; split; [exact Hpmem|]. split; [exact Hpblk|].
  split; [exact Hinterval|]. split; [|reflexivity].
  unfold mem_put_protected_result; split; [reflexivity|]. split; [reflexivity|].
  destruct input as [image|id historical block loan|id historical].
  - exact Hview.
  - destruct Hview as [current [Hacq [_ [_ [Hlookup _]]]]]; exists current; auto.
  - destruct Hview as [current [Hacq [_ [Hlookup _]]]]; exists current; auto.
Qed.

Lemma mem_put_restore_unchanged_partition : forall sg entry id current,
  sg.(osKernelConfig).(cfgMemoryEnabled) = true -> UCOS2_state_inv sg entry ->
  entry.(MemoryState).(memPartitions) id = Some current ->
  store_memory_control sg (memory_control_addr sg id) (memory_partition_image current) **
  store_memory_free_blocks current current.(memFreeBlocks) **
  memory_raw_rep_without_partition sg entry.(MemoryState) id **
  UCOS2_raw_rep_missing_memory sg entry |-- UCOS2_inv sg entry.
Proof.
  intros sg entry id current Henabled Hvalid Hlookup.
  pose proof (mem_put_state_memory_valid sg entry Henabled Hvalid) as Hmemory.
  destruct Hmemory as [_ [Hparts _]].
  pose proof (proj2 (proj2 (Hparts id current Hlookup))) as Himage.
  rewrite UCOS2_inv_split_memory; unfold memory_configured_rep; rewrite Henabled.
  unfold memory_raw_rep_without_partition, memory_raw_rep; sepcon_right_assoc.
  sep_apply_l_atomic (memory_controls_merge_control sg entry.(MemoryState) id
    (memory_partition_image current) Himage).
  sep_apply_l_atomic (store_map_merge
    (fun _ p => store_memory_free_blocks p p.(memFreeBlocks)) id current _ Hlookup).
  entailer!.
Qed.

Lemma mem_put_full_reconstructs_resources : forall critical sg invocation before entry pmem pblk input acquired,
  mem_put_profile sg ->
  mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ->
  acquired.(mem_put_acquired_image).(memImageCount) <= acquired.(mem_put_acquired_image).(memImageNFree) ->
  mem_put_count_cells pmem acquired.(mem_put_acquired_image) **
  mem_put_focus_frame sg entry pmem pblk input acquired |--
    UCOS2_inv sg entry ** mem_put_result_resources sg pmem pblk input
      (mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image)).
Proof.
  intros critical sg invocation before entry pmem pblk input acquired [_ [Henabled _]]
    [Hpmem [Hpblk [Hentry [Hinterval Hview]]]] Hfull.
  assert (Ep : (pmem =? 0) = false) by (apply Z.eqb_neq; exact Hpmem).
  assert (Eb : (pblk =? 0) = false) by (apply Z.eqb_neq; exact Hpblk).
  assert (Ec : (memImageCount (mem_put_acquired_image acquired) <=?
    memImageNFree (mem_put_acquired_image acquired)) = true) by (apply Z.leb_le; exact Hfull).
  unfold mem_put_result_resources, mem_put_raw_result; rewrite Ep, Eb; simpl; rewrite Ec; simpl.
  destruct input as [image|id historical block loan|id historical].
  - subst acquired; simpl in Ec; unfold mem_put_count_cells, mem_put_focus_frame; simpl; rewrite Ec.
    sepcon_right_assoc; sep_apply_l_atomic (mem_put_control_merge_counts_head sg pmem image); entailer!.
  - destruct Hview as [current [-> [Haddr [Hblock [Hlookup _]]]]].
    unfold mem_put_count_cells, mem_put_focus_frame; simpl; sepcon_right_assoc.
    pose proof (mem_put_control_merge_counts_head sg pmem (memory_partition_image current)) as Hmerge.
    simpl in Hmerge; sep_apply_l_atomic Hmerge.
    rewrite Haddr; sep_apply_l_atomic (mem_put_restore_unchanged_partition sg entry id current Henabled Hentry Hlookup).
    entailer!.
  - destruct Hview as [current [-> [Haddr [Hlookup Hcurrentfull]]]].
    unfold mem_put_count_cells, mem_put_focus_frame; simpl; sepcon_right_assoc.
    pose proof (mem_put_control_merge_counts_head sg pmem (memory_partition_image current)) as Hmerge.
    simpl in Hmerge; sep_apply_l_atomic Hmerge.
    rewrite Haddr; sep_apply_l_atomic (mem_put_restore_unchanged_partition sg entry id current Henabled Hentry Hlookup).
    entailer!.
Qed.

(** Only after the C stores. The unsigned identity uses the OLD counts
    and the real strict guard; it cannot be inferred from a new cell. *)
Lemma mem_put_written_control_merge : forall sg pmem pblk image,
  0 <= image.(memImageNFree) -> image.(memImageNFree) < image.(memImageCount) ->
  image.(memImageCount) < 4294967296 ->
  &(pmem # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> pblk **
  &(pmem # "os_mem" ->ₛ "OSMemNFree") # UInt |-> (image.(memImageNFree) + 1) **
  &(pmem # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> image.(memImageCount) **
  mem_put_control_frame sg pmem image |--
    store_memory_control sg pmem (memory_put_image image pblk).
Proof.
  intros sg pmem pblk image Hlo Hlt Hhi.
  pose proof (mem_put_control_merge_updated_counts_head sg pmem image pblk) as Hmerge.
  rewrite (kernel_u32_identity (image.(memImageNFree) + 1) ltac:(lia)) in Hmerge; exact Hmerge.
Qed.

Lemma mem_put_success_reconstructs_resources : forall critical sg invocation before entry pmem pblk input acquired,
  mem_put_profile sg ->
  mem_put_acquired_facts critical sg invocation before entry pmem pblk input acquired ->
  mem_put_current_allocation input acquired ->
  0 <= acquired.(mem_put_acquired_image).(memImageNFree) ->
  acquired.(mem_put_acquired_image).(memImageNFree) < acquired.(mem_put_acquired_image).(memImageCount) ->
  acquired.(mem_put_acquired_image).(memImageCount) < 4294967296 ->
  pblk # Ptr |-> acquired.(mem_put_acquired_image).(memImageFree) **
  &(pmem # "os_mem" ->ₛ "OSMemFreeList") # Ptr |-> pblk **
  &(pmem # "os_mem" ->ₛ "OSMemNFree") # UInt |-> (acquired.(mem_put_acquired_image).(memImageNFree) + 1) **
  &(pmem # "os_mem" ->ₛ "OSMemNBlks") # UInt |-> acquired.(mem_put_acquired_image).(memImageCount) **
  mem_put_success_frame sg entry pmem input acquired |--
    coq_prop (UCOS2_state_inv sg (mem_put_checkpoint entry input acquired)) &&
    (UCOS2_inv sg (mem_put_checkpoint entry input acquired) **
     mem_put_result_resources sg pmem pblk input
       (mem_put_raw_result pmem pblk acquired.(mem_put_acquired_image))).
Proof.
  intros critical sg invocation before entry pmem pblk input acquired [_ [Henabled _]]
    [Hpmem [Hpblk [Hentry [Hinterval Hview]]]] Hallocation Hlo Hlt Hhi.
  assert (Ep : (pmem =? 0) = false) by (apply Z.eqb_neq; exact Hpmem).
  assert (Eb : (pblk =? 0) = false) by (apply Z.eqb_neq; exact Hpblk).
  assert (Ec : (memImageCount (mem_put_acquired_image acquired) <=?
    memImageNFree (mem_put_acquired_image acquired)) = false) by (apply Z.leb_gt; exact Hlt).
  unfold mem_put_result_resources, mem_put_raw_result, mem_put_checkpoint;
    rewrite Ep, Eb; simpl; rewrite Ec; simpl.
  destruct input as [image|id historical block loan|id historical].
  - subst acquired; simpl in Hlo, Hlt, Hhi; unfold mem_put_success_frame; simpl.
    sepcon_right_assoc; sep_apply_l_atomic (mem_put_written_control_merge sg pmem pblk image Hlo Hlt Hhi).
    entailer!.
  - destruct Hview as [current [-> [Haddr [Hblock [Hlookup _]]]]].
    simpl in Hallocation, Hlo, Hlt, Hhi; destruct Hallocation as [current_loan Hcurrentloan].
    assert (Hpost : UCOS2_state_inv sg (replace_MemoryS
      (memory_replace_partition entry.(MemoryState) id (memory_put_partition current block)) entry)).
    { eapply UCOS2_memory_put_preserves_validity;
        [exact Henabled|exact Hentry|exact Hlookup|exact Hcurrentloan|].
      unfold memory_put; rewrite Hlookup; reflexivity. }
    unfold mem_put_success_frame; simpl; sepcon_right_assoc.
    pose proof (mem_put_written_control_merge sg pmem pblk (memory_partition_image current) Hlo Hlt Hhi) as Hmerge.
    simpl in Hmerge; sep_apply_l_atomic Hmerge.
    rewrite Haddr, Hblock.
    pose proof (memory_put_resources_merge sg entry id current block current_loan Henabled Hentry Hlookup Hcurrentloan) as Hresources.
    unfold memory_free_block_rep in Hresources.
    entailer!; sep_apply_r_atomic Hresources; entailer!.
  - destruct Hview as [current [-> [_ [_ Hfull]]]]; simpl in Hlt; lia.
Qed.
