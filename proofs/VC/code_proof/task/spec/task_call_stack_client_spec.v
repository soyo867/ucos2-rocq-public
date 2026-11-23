Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reindex the one existing map after real TCB updates. The focused
    descriptor and dormant owner are unchanged, rather than forgotten and
    subsequently recovered from the weaker, existential continuation map. *)
Lemma armv7a_task_call_stacks_reindex : forall external platform port
  (abi : Armv7aContinuationABI external platform port) before after focus stacks,
  (forall key payload node, stacks key = Some payload ->
    after.(inUsedTaskStates) (fst key) = Some node -> node.(taskGeneration) = snd key ->
    exists old, before.(inUsedTaskStates) (fst key) = Some old /\
      old.(taskGeneration) = node.(taskGeneration) /\ old.(tcbStkPtr) = node.(tcbStkPtr)) ->
  armv7a_task_call_stacks abi before focus stacks |--
  armv7a_task_call_stacks abi after focus stacks.
Proof.
  intros external platform port abi before after focus stacks Htransport.
  unfold armv7a_task_call_stacks, store_parked_continuations.
  apply TaskFieldStorage.store_map_mono; intros key payload Hlookup.
  unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec;
    [|unfold armv7a_task_stack_entry]; Intros saved.
  all: assert (Hsp : task_stack_live_sp before key saved.(armv7a_continuation_sp)) by tauto.
  all: assert (Hafter : task_stack_live_sp after key saved.(armv7a_continuation_sp)).
  all: try (intros node Hnode Hgen;
    destruct (Htransport key payload node Hlookup Hnode Hgen) as [old [Hold [Hg Hv]]];
    rewrite <- Hv; apply Hsp; [exact Hold|congruence]).
  all: Exists saved; entailer!.
Qed.

Lemma armv7a_task_call_stacks_used_map_eq : forall external platform port
  (abi : Armv7aContinuationABI external platform port) before after focus stacks,
  before.(inUsedTaskStates) = after.(inUsedTaskStates) ->
  armv7a_task_call_stacks abi before focus stacks |--
  armv7a_task_call_stacks abi after focus stacks.
Proof.
  intros; apply armv7a_task_call_stacks_reindex.
  intros key payload node Hlookup Hnode Hgen; exists node; rewrite H; auto.
Qed.

Lemma armv7a_task_call_stacks_commit : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks priority invocation node focus stacks,
  stacks (node.(taskID), node.(taskGeneration)) = None ->
  armv7a_task_call_stacks abi tasks focus stacks |--
  armv7a_task_call_stacks abi (task_commit tasks priority invocation node) focus stacks.
Proof.
  intros external platform port abi tasks priority invocation node focus stacks Hfresh.
  apply armv7a_task_call_stacks_reindex.
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

(** Initial-entry descriptors have no suspended-call capability. This
    attachment does not manufacture stack bytes: the publication consumer
    below separately deposits the actual StackInit buffer into the heap. *)
Lemma armv7a_task_call_stacks_park_initial : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks focus stacks saved,
  armv7a_initial_frame_binding saved -> saved.(armv7a_continuation_call) = None ->
  task_stack_key saved.(armv7a_continuation_stack) <> armv7a_call_focus_key focus ->
  stacks (task_stack_key saved.(armv7a_continuation_stack)) = None ->
  task_stack_live_sp tasks (task_stack_key saved.(armv7a_continuation_stack))
    saved.(armv7a_continuation_sp) ->
  armv7a_task_call_stacks abi tasks focus stacks |--
  armv7a_task_call_stacks abi tasks focus
    (task_stack_park_fragments stacks saved.(armv7a_continuation_stack)
      saved.(armv7a_continuation_fragments)).
Proof.
  intros external platform port abi tasks focus stacks saved Hinitial Hcall Hother Hfresh Hsp.
  assert (Hbinding : armv7a_continuation_binding saved).
  { destruct Hinitial as [top [entry [argument [task_return [lower [upper [Heq Hrest]]]]]]].
    rewrite Heq; apply armv7a_initial_continuation_binding. }
  assert (Hslice : armv7a_task_frame_slice saved) by (apply armv7a_initial_frame_slice; exact Hinitial).
  unfold armv7a_task_call_stacks.
  assert (Hattach : store_parked_continuations (armv7a_task_call_stack_entry abi tasks focus) stacks |--
    armv7a_task_call_stack_entry abi tasks focus (task_stack_key saved.(armv7a_continuation_stack))
      (saved.(armv7a_continuation_stack).(stackLeaseRegion), saved.(armv7a_continuation_fragments)) **
    store_parked_continuations (armv7a_task_call_stack_entry abi tasks focus) stacks).
  { unfold armv7a_task_call_stack_entry; destruct task_stack_key_eq_dec; [contradiction|].
    unfold armv7a_task_stack_entry; Exists saved.
    unfold armv7a_task_continuation_resource; rewrite Hcall; entailer!. }
  sep_apply_l_atomic Hattach; apply store_parked_continuations_park; exact Hfresh.
Qed.

(** TCBInit's actual publication must preserve a pending, different call.
    Presence comes from the earlier IRQ deposit. Fresh allocation prevents
    the newly published initial frame from replacing that descriptor. *)
Lemma task_create_publication_call_stack_merge :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg publication current focus active payload,
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  task_stack_live_coverage current.(TskState) active ->
  current.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload ->
  let after := task_create_stack_publication_state sg publication current in
  task_create_publication_storage sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_acquired)
    current publication.(stack_publication_slot) publication.(stack_publication_image) **
  task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
  armv7a_task_call_stacks abi current.(TskState) focus current.(TskState).(parkedTaskStacks) |--
  coq_prop (kernel_client_step (task_create_stack_publication_client publication) sg current after /\
    task_stack_live_coverage after.(TskState) active /\
    after.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload) &&
  (UCOS2_inv sg after **
   armv7a_task_call_stacks abi after.(TskState) focus after.(TskState).(parkedTaskStacks)).
Proof.
  intros external platform port abi sg publication current focus active payload
    Hvalid Hinput Hcoverage Hfocus after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current after)
    by (split; [exact Hinput|reflexivity]).
  destruct Hinput as [Hlayout [Hregion [Hcommit [Hcreation [[flags Hflags] Hname]]]]].
  set (actual := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node actual publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  set (lease := publication.(stack_publication_lease)).
  set (saved := armv7a_initial_continuation lease publication.(stack_publication_args).(createStackTop)
    publication.(stack_publication_args).(createEntry) publication.(stack_publication_args).(createArgument)
    publication.(stack_publication_return) publication.(stack_publication_lower) publication.(stack_publication_upper)).
  assert (Hidentity : task_commit_identity current.(TskState) actual.(initPrio)
    publication.(stack_publication_invocation) node)
    by (eapply task_tcb_init_commit_binding_identity; exact Hcommit).
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity) as [Hslot Hgen].
  assert (Hconsistent : parked_stacks_consistent current.(TskState) current.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hfresh : current.(TskState).(parkedTaskStacks) (task_stack_key lease) = None).
  { unfold task_stack_key, lease; rewrite <- Hslot, <- Hgen.
    eapply task_commit_stack_key_absent; [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  assert (Hother : task_stack_key lease <> armv7a_call_focus_key focus) by congruence.
  assert (Hcovered : task_stack_live_coverage after.(TskState) active)
    by (apply task_commit_stack_coverage; assumption).
  assert (Hfocus_after : after.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { change ((task_stack_park current.(TskState).(parkedTaskStacks) lease
      (task_create_stack_publication_words publication)) (armv7a_call_focus_key focus) = Some payload).
    rewrite task_stack_park_lookup_other; [exact Hfocus|congruence]. }
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
  assert (Hattachment : armv7a_task_call_stacks abi current.(TskState) focus
      current.(TskState).(parkedTaskStacks) |--
    armv7a_task_call_stacks abi after.(TskState) focus after.(TskState).(parkedTaskStacks)).
  { assert (Hnewkey : current.(TskState).(parkedTaskStacks) (node.(taskID), node.(taskGeneration)) = None).
    { rewrite Hslot, Hgen; exact Hfresh. }
    sep_apply_l_atomic (armv7a_task_call_stacks_commit external platform port abi current.(TskState)
      actual.(initPrio) publication.(stack_publication_invocation) node focus
      current.(TskState).(parkedTaskStacks) Hnewkey).
    sep_apply_l_atomic (armv7a_task_call_stacks_used_map_eq external platform port abi
      (task_commit current.(TskState) actual.(initPrio) publication.(stack_publication_invocation) node)
      after.(TskState) focus current.(TskState).(parkedTaskStacks) eq_refl).
    exact (armv7a_task_call_stacks_park_initial external platform port abi after.(TskState) focus
      current.(TskState).(parkedTaskStacks) saved Hinitial eq_refl Hother Hfresh Hsp). }
  sep_apply_l_atomic Hattachment.
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
  sep_apply_l_atomic Hpark; Intros.
  assert (Hconsistent_after : parked_stacks_consistent committed.(TskState) after.(TskState).(parkedTaskStacks))
    by assumption.
  sepcon_assoc_change.
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg committed
    after.(TskState).(parkedTaskStacks) Hcommitted Hconsistent_after).
  unfold after, task_create_stack_publication_state, task_create_stack_published_state; entailer!.
Qed.
