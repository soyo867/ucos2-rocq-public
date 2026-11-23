Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only the conditional live-SP observation depends on [tasks]. Each
    descriptor and its already owned local program cut remain unchanged.
    In particular historical entries need not remain active forever. *)
Lemma kernel_saved_continuation_map_reindex : forall external platform port
  (abi : Armv7aContinuationABI external platform port) before after local stacks,
  (forall key payload node, stacks key = Some payload ->
    after.(inUsedTaskStates) (fst key) = Some node -> node.(taskGeneration) = snd key ->
    exists old, before.(inUsedTaskStates) (fst key) = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)) ->
  store_parked_continuations (kernel_saved_continuation_entry abi before local) stacks |--
  store_parked_continuations (kernel_saved_continuation_entry abi after local) stacks.
Proof.
  intros external platform port abi before after local stacks Htransport.
  unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros saved.
  assert (Hsp : task_stack_live_sp before key saved.(armv7a_continuation_sp)) by tauto.
  assert (Hafter : task_stack_live_sp after key saved.(armv7a_continuation_sp)).
  { intros node Hnode Hgen.
    destruct (Htransport key payload node Hlookup Hnode Hgen) as [old [Hold [Hg Hv]]].
    rewrite <- Hv; apply Hsp; [exact Hold|congruence]. }
  Exists saved; entailer!.
Qed.

Lemma kernel_saved_continuation_map_used_map_eq : forall external platform port
  (abi : Armv7aContinuationABI external platform port) before after local stacks,
  before.(inUsedTaskStates) = after.(inUsedTaskStates) ->
  store_parked_continuations (kernel_saved_continuation_entry abi before local) stacks |--
  store_parked_continuations (kernel_saved_continuation_entry abi after local) stacks.
Proof.
  intros external platform port abi before after local stacks Hused.
  apply kernel_saved_continuation_map_reindex.
  intros key payload node Hlookup Hnode Hgen; exists node; rewrite Hused; auto.
Qed.

(** A fresh publication may reuse a TCB slot, but cannot replace an old
    descriptor at the same generation. The real allocation identity below
    supplies this freshness; it is not a new platform guarantee. *)
Lemma kernel_saved_continuation_map_commit : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks priority invocation node local stacks,
  stacks (node.(taskID), node.(taskGeneration)) = None ->
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi (task_commit tasks priority invocation node) local) stacks.
Proof.
  intros external platform port abi tasks priority invocation node local stacks Hfresh.
  apply kernel_saved_continuation_map_reindex.
  intros [slot generation] payload updated Hlookup Hupdated Hgen.
  change ((task_commit tasks priority invocation node).(inUsedTaskStates) slot = Some updated) in Hupdated.
  change (updated.(taskGeneration) = generation) in Hgen.
  destruct (Z.eq_dec slot node.(taskID)) as [Heq|Hneq].
  - subst slot.
    pose proof (proj1 (task_commit_publication_fields_eq tasks priority invocation node)) as Hnew.
    rewrite Hnew in Hupdated; injection Hupdated as Hupdated; subst updated.
    change (node.(taskGeneration) = generation) in Hgen.
    rewrite <- Hgen, Hfresh in Hlookup; discriminate.
  - destruct (task_commit_lookup_old_fields tasks priority invocation node slot updated Hneq Hupdated)
      as [old [Hold Hfields]].
    exists old; split; [exact Hold|]; split.
    + symmetry; exact (f_equal taskGeneration Hfields).
    + symmetry; exact (f_equal tcbStkPtr Hfields).
Qed.

(** Initial continuations carry the checked initial ABI shape, together
    with an explicitly owned [local saved]. Public TaskCreate instantiates
    its None branch with [emp]. An arbitrary nonempty local assertion is
    consumed here, never manufactured from the descriptor or its bytes. *)
Lemma kernel_saved_continuation_map_park_initial : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks local stacks saved,
  armv7a_initial_frame_binding saved -> saved.(armv7a_continuation_call) = None ->
  stacks (task_stack_key saved.(armv7a_continuation_stack)) = None ->
  task_stack_live_sp tasks (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp) ->
  local saved ** store_parked_continuations (kernel_saved_continuation_entry abi tasks local) stacks |--
  store_parked_continuations (kernel_saved_continuation_entry abi tasks local)
    (task_stack_park_fragments stacks saved.(armv7a_continuation_stack)
      saved.(armv7a_continuation_fragments)).
Proof.
  intros external platform port abi tasks local stacks saved Hinitial Hcall Hfresh Hsp.
  assert (Hbinding : armv7a_continuation_binding saved).
  { destruct Hinitial as [top [entry [argument [task_return [lower [upper [Heq Hrest]]]]]]].
    rewrite Heq; apply armv7a_initial_continuation_binding. }
  assert (Hslice : armv7a_task_frame_slice saved) by (apply armv7a_initial_frame_slice; exact Hinitial).
  assert (Hentry : local saved |--
    kernel_saved_continuation_entry abi tasks local (task_stack_key saved.(armv7a_continuation_stack))
      (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments))).
  { unfold kernel_saved_continuation_entry; Exists saved.
    unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  sep_apply_l_atomic Hentry; apply store_parked_continuations_park; exact Hfresh.
Qed.

(** The exact initial descriptor corresponding to this publication's
    already initialized physical StackInit buffer. It introduces no new
    state or registration table. *)
Definition task_create_stack_publication_continuation (publication : TaskCreateStackPublication)
  : Armv7aContinuation :=
  armv7a_initial_continuation publication.(stack_publication_lease)
    publication.(stack_publication_args).(createStackTop)
    publication.(stack_publication_args).(createEntry)
    publication.(stack_publication_args).(createArgument)
    publication.(stack_publication_return) publication.(stack_publication_lower)
    publication.(stack_publication_upper).

(** Close the real TCB publication endpoint and hand over the initialized
    stack to the same existing map. Other descriptors and their locals are
    transported directly; no weaker map is used as an intermediate result. *)
Lemma kernel_task_publication_continuation_merge : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication current local active,
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  task_stack_live_coverage current.(TskState) active ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_publication_storage sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image) **
  task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
  local (task_create_stack_publication_continuation publication) **
  store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
    current.(TskState).(parkedTaskStacks) |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current after /\
    task_stack_live_coverage after.(TskState) active) &&
  (UCOS2_inv sg after **
   store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
     after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication current local active Hvalid Hinput Hcoverage after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current after)
    by (split; [exact Hinput|reflexivity]).
  destruct Hinput as [Hlayout [Hregion [Hcommit [Hcreation [[flags Hflags] Hname]]]]].
  set (actual := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node actual publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  set (lease := publication.(stack_publication_lease)).
  set (saved := task_create_stack_publication_continuation publication).
  assert (Hidentity : task_commit_identity current.(TskState) actual.(initPrio)
    publication.(stack_publication_invocation) node)
    by (eapply task_tcb_init_commit_binding_identity; exact Hcommit).
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity) as [Hslot Hgen].
  assert (Hconsistent : parked_stacks_consistent current.(TskState) current.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hfresh : current.(TskState).(parkedTaskStacks) (task_stack_key lease) = None).
  { unfold task_stack_key, lease; rewrite <- Hslot, <- Hgen.
    eapply task_commit_stack_key_absent; [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  assert (Hcovered : task_stack_live_coverage after.(TskState) active)
    by (apply task_commit_stack_coverage; assumption).
  assert (Hinitial : armv7a_initial_frame_binding saved).
  { apply task_create_initial_frame_binding with (region := publication.(stack_publication_region)); assumption. }
  assert (Hsp : task_stack_live_sp after.(TskState) (task_stack_key lease) saved.(armv7a_continuation_sp)).
  { destruct (task_create_stack_published_initial_pointer sg publication.(stack_publication_args)
      publication.(stack_publication_return) publication.(stack_publication_lower) publication.(stack_publication_upper)
      publication.(stack_publication_name) publication.(stack_publication_invocation)
      publication.(stack_publication_origin) publication.(stack_publication_acquired) current
      publication.(stack_publication_slot) publication.(stack_publication_image) lease Hcommit Hcreation)
      as [published [Hnode [Hid [Hg Hpointer]]]].
    change (after.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some published) in Hnode.
    intros updated Hupdated Hgeneration; cbn [task_stack_key fst] in Hupdated.
    assert (updated = published) by congruence; subst updated; exact Hpointer. }
  assert (Hattachment : local saved **
      store_parked_continuations (kernel_saved_continuation_entry abi current.(TskState) local)
        current.(TskState).(parkedTaskStacks) |--
    store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
      after.(TskState).(parkedTaskStacks)).
  { assert (Hnewkey : current.(TskState).(parkedTaskStacks) (node.(taskID), node.(taskGeneration)) = None).
    { rewrite Hslot, Hgen; exact Hfresh. }
    sep_apply_l_atomic (kernel_saved_continuation_map_commit external platform port abi current.(TskState)
      actual.(initPrio) publication.(stack_publication_invocation) node local
      current.(TskState).(parkedTaskStacks) Hnewkey).
    sep_apply_l_atomic (kernel_saved_continuation_map_used_map_eq external platform port abi
      (task_commit current.(TskState) actual.(initPrio) publication.(stack_publication_invocation) node)
      after.(TskState) local current.(TskState).(parkedTaskStacks) eq_refl).
    eapply derivable1_trans with (y := local saved **
      store_parked_continuations (kernel_saved_continuation_entry abi after.(TskState) local)
        current.(TskState).(parkedTaskStacks)).
    - entailer!.
    - exact (kernel_saved_continuation_map_park_initial external platform port abi after.(TskState) local
        current.(TskState).(parkedTaskStacks) saved Hinitial eq_refl Hfresh Hsp). }
  sepcon_assoc_change; sep_apply_l_atomic Hattachment.
  set (committed := task_create_stack_publication_raw_state sg publication current).
  assert (Hmerge : task_create_publication_storage sg actual publication.(stack_publication_invocation)
      publication.(stack_publication_acquired) current publication.(stack_publication_slot)
      publication.(stack_publication_image) |-- UCOS2_inv sg committed).
  { exact (task_tcb_init_publication_storage_merge__publication_and_returns sg actual
      publication.(stack_publication_invocation) publication.(stack_publication_origin)
      publication.(stack_publication_acquired) current publication.(stack_publication_slot)
      publication.(stack_publication_image) flags Hvalid Hcommit Hflags Hname). }
  sep_apply_l_atomic Hmerge; rewrite UCOS2_inv_split_parked_stacks; Intros.
  assert (Hcommitted : UCOS2_state_inv sg committed) by assumption.
  assert (Hmap : committed.(TskState).(parkedTaskStacks) = current.(TskState).(parkedTaskStacks)) by reflexivity.
  rewrite Hmap.
  pose proof (task_create_stack_protected_commit_resources sg TaskStackNoVFP publication.(stack_publication_region)
    publication.(stack_publication_args) publication.(stack_publication_return) publication.(stack_publication_lower)
    publication.(stack_publication_upper) publication.(stack_publication_name) publication.(stack_publication_invocation)
    publication.(stack_publication_origin) publication.(stack_publication_acquired) current
    publication.(stack_publication_slot) publication.(stack_publication_image) lease
    Hlayout Hregion Hcommit Hcreation Hconsistent Hfresh) as Hpark.
  change (task_stack_storage publication.(stack_publication_region)
      (task_create_stack_publication_words publication) **
    store_parked_stacks current.(TskState).(parkedTaskStacks) |--
    coq_prop (parked_stacks_consistent after.(TskState) after.(TskState).(parkedTaskStacks)) &&
    store_parked_stacks after.(TskState).(parkedTaskStacks)) in Hpark.
  sepcon_assoc_change; sep_apply_l_atomic Hpark; Intros.
  assert (Hconsistent_after : parked_stacks_consistent committed.(TskState) after.(TskState).(parkedTaskStacks))
    by assumption.
  sepcon_assoc_change.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg committed
    after.(TskState).(parkedTaskStacks) Hcommitted Hconsistent_after).
  unfold after, task_create_stack_publication_state, task_create_stack_published_state; entailer!.
Qed.

(** Run the actual five publication stores at the supplied source
    endpoints, then consume the StackInit buffer and initial local cut.
    The allocation, priority and pointer facts are the existing TCBInit
    caller obligations. Other continuation/local resources remain owned
    throughout the concrete writes. *)
Lemma kernel_task_publication_continuation_source : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication state local active
  (frame : Assertion) before after,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_stack_live_coverage state.(TskState) active ->
  0 <= (task_create_stack_publication_args publication).(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
    local (task_create_stack_publication_continuation publication) **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame)) before ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  let published := task_create_stack_publication_state sg publication state in
  kernel_client_step (task_create_stack_publication_client publication) sg state published /\
  task_stack_live_coverage published.(TskState) active /\
  (kernel_program_inv sg published **
   store_parked_continuations (kernel_saved_continuation_entry abi published.(TskState) local)
     published.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg publication state local active frame before after
    Hvalid Hinput Hcoverage Hpriority Hpointer Hpre Hsource published.
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
  destruct (task_tcb_init_publication_tail_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid Hbinding Hpriority Hpointer Hpre)
    as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_client_publication_final_eq; eassumption); subst produced.
  pose proof (kernel_task_publication_continuation_merge external platform port abi sg publication state
    local active Hvalid Hinput Hcoverage) as Hclose; cbv zeta in Hclose.
  match type of Hpost with ?P after =>
    assert (Hmerge : P |--
      coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg state published /\
        task_stack_live_coverage published.(TskState) active) &&
      (kernel_program_inv sg published **
       store_parked_continuations (kernel_saved_continuation_entry abi published.(TskState) local)
         published.(TskState).(parkedTaskStacks) ** frame))
  end.
  { rewrite kernel_program_inv_split_unmap; sepcon_assoc_change.
    sep_apply_l_atomic Hclose; Intros; entailer!. }
  destruct (Hmerge after Hpost) as [[Hstep Hcovered] Howned].
  split; [exact Hstep|]. split; assumption.
Qed.

(** The producing form is used by TaskCreate's publication-to-return
    consumer. It obtains the concrete endpoint from the existing store
    proof, rather than requiring a post-heap or stable-world premise. *)
Lemma kernel_task_publication_continuation_produces : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication state local active
  (frame : Assertion) before,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  task_stack_live_coverage state.(TskState) active ->
  0 <= (task_create_stack_publication_args publication).(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
    local (task_create_stack_publication_continuation publication) **
    store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame)) before ->
  let published := task_create_stack_publication_state sg publication state in
  exists after,
    task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before after /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    task_stack_live_coverage published.(TskState) active /\
    (kernel_program_inv sg published **
     store_parked_continuations (kernel_saved_continuation_entry abi published.(TskState) local)
       published.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg publication state local active frame before
    Hvalid Hinput Hcoverage Hpriority Hpointer Hpre published.
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
  destruct (task_tcb_init_publication_tail_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid Hbinding Hpriority Hpointer Hpre)
    as [after [Hrun Hpost]].
  exists after; split; [exact Hrun|].
  exact (kernel_task_publication_continuation_source external platform port abi sg publication state local
    active frame before after Hvalid Hinput Hcoverage Hpriority Hpointer Hpre Hrun).
Qed.
