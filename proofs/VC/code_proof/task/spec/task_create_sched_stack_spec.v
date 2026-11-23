Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Import UCOS2_C_Rules ListNotations KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Exact physical endpoint of the public TCB/list/ready-table stores.
    Stack bytes are deliberately not included: their separate owner is
    consumed by the publication handover below. *)
Definition task_create_publication_storage sg actual invocation acquired current slot image : Assertion :=
  let committed := task_tcb_init_published_state sg actual invocation acquired current slot image in
  task_slot_storage_rep sg slot
    (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
      (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
        sg.(osKernelConfig).(cfgTaskProfile) actual image)) **
  task_tcb_init_used_with_head_prev sg current slot **
  sg.(g_OSTCBList) # Ptr |-> task_slot_addr sg slot **
  sg.(g_OSTaskCtr) # UChar |-> (task_tcb_init_count current + 1) **
  sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group committed **
  UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows committed) **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg committed) **
  task_tcb_init_publication_other sg current.

(** The publication-store cut and the initialized buffer are owned on the
    same heap.  The existing TCBInit merge establishes its actual public
    node and scheduler cells; the existing StackInit handover then deposits
    the buffer under that allocation's generation.  No ready-to-frame
    totality assumption or additional initial-frame producer is used. *)
Lemma task_create_publication_stack_merge :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease flags,
  UCOS2_state_inv sg current ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node actual acquired slot image).(tcbTaskName) chars) ->
  let committed := task_tcb_init_published_state sg actual invocation acquired current slot image in
  let published := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  task_create_publication_storage sg actual invocation acquired current slot image **
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
  armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) |--
  UCOS2_inv sg published **
  armv7a_task_continuations abi published.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease flags Hvalid Hlayout Hregion
    actual Hcommit Hcreation Hflags Hname committed published.
  assert (Hmerge : task_create_publication_storage sg actual invocation acquired current slot image |--
    UCOS2_inv sg committed).
  { exact (task_tcb_init_publication_storage_merge__publication_and_returns
      sg actual invocation origin acquired current slot image flags Hvalid Hcommit Hflags Hname). }
  sep_apply_l_atomic Hmerge.
  rewrite UCOS2_inv_split_parked_stacks; Intros.
  assert (Hpublished : UCOS2_state_inv sg committed) by assumption.
  assert (Hmap : committed.(TskState).(parkedTaskStacks) =
    current.(TskState).(parkedTaskStacks)) by reflexivity.
  rewrite Hmap.
  pose proof (task_create_stack_park_initial_continuation external platform port abi
    sg region args task_return lower upper initial_name invocation origin acquired current
    slot image lease Hvalid Hlayout Hregion Hcommit Hcreation) as Hpark.
  cbv zeta in Hpark; fold actual in Hpark; fold published in Hpark.
  sep_apply_l_atomic Hpark.
  Intros.
  assert (Hconsistent : parked_stacks_consistent committed.(TskState)
    published.(TskState).(parkedTaskStacks)).
  { assert (Hpost : parked_stacks_consistent published.(TskState)
      published.(TskState).(parkedTaskStacks)) by assumption.
    exact Hpost. }
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg committed
    published.(TskState).(parkedTaskStacks) Hpublished Hconsistent).
  unfold published, task_create_stack_published_state; entailer!.
Qed.

Definition task_create_initial_selection_transfer (published : UCOS2_Verify_State)
  (initial : Armv7aContinuation) : OsIntExitTransfer :=
  {| os_int_exit_hooked_state := os_int_exit_selection_state published;
     os_int_exit_incoming_stack := initial.(armv7a_continuation_stack);
     os_int_exit_incoming_sp := initial.(armv7a_continuation_sp);
     os_int_exit_incoming_fragments := initial.(armv7a_continuation_fragments) |}.

(** On the branch where the actual selector picks this newly published
    task, its SP and complete initial frame come from TCBInit/StackInit.
    The initial-entry ABI supplies only the architecture-frame relation;
    the task, generation, cache and parked-entry facts are proved here. *)
Lemma task_create_selected_initial_destination :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (initial_abi : Armv7aInitialEntryABI external platform port abi)
    sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease tail,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  let published := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  published.(SchedState).(readyList) = lease.(stackLeaseSlot) :: tail ->
  os_int_exit_destination_binding external (task_create_initial_selection_transfer published
    (armv7a_initial_continuation lease args.(createStackTop) args.(createEntry)
      args.(createArgument) task_return lower upper)).
Proof.
  intros external platform port abi initial_abi sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease tail Hlayout Hregion actual Hcommit
    Hcreation published Hready.
  destruct (task_create_stack_published_initial_pointer sg args task_return lower upper
    initial_name invocation origin acquired current slot image lease Hcommit Hcreation)
    as [node [Hnode [Hslot [Hgeneration Hsp]]]].
  fold actual in Hnode; fold published in Hnode.
  set (initial := armv7a_initial_continuation lease args.(createStackTop) args.(createEntry)
    args.(createArgument) task_return lower upper).
  assert (Hinitial : armv7a_initial_frame_binding initial).
  { apply task_create_initial_frame_binding with (region := region); assumption. }
  change ((os_int_exit_selection_state published).(SchedState).(highRdyTid) =
      Some lease.(stackLeaseSlot) /\
    (exists node, published.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node /\
      node.(taskGeneration) = lease.(stackLeaseGeneration) /\
      (os_int_exit_selection_state published).(SchedState).(highRdyPrio) = Some node.(curPrio) /\
      node.(tcbStkPtr) = initial.(armv7a_continuation_sp)) /\
    task_stack_live_binding published.(TskState) lease /\
    published.(TskState).(parkedTaskStacks) (task_stack_key lease) =
      Some (lease.(stackLeaseRegion), initial.(armv7a_continuation_fragments)) /\
    external.(os_sched_arch_restore_source) lease initial.(armv7a_continuation_sp)
      initial.(armv7a_continuation_fragments)).
  split.
  - unfold os_int_exit_selection_state; cbn [replace_SchedS SchedState sched_refresh_high highRdyTid].
    rewrite Hready; reflexivity.
  - split.
    + exists node; split; [exact Hnode|]. split; [exact Hgeneration|]. split.
      * unfold os_int_exit_selection_state; cbn [replace_SchedS SchedState sched_refresh_high highRdyPrio].
        rewrite Hready, Hnode; reflexivity.
      * exact Hsp.
    + split.
      * exists node; split; [exact Hnode|]. split; [exact Hslot|]. split; [exact Hgeneration|].
        rewrite Hsp, Hregion.
        apply task_create_stack_pointer_in_range with (lower := lower) (upper := upper); exact Hlayout.
      * split.
        -- change ((task_stack_park current.(TskState).(parkedTaskStacks) lease
             (task_create_stack_image TaskStackNoVFP args task_return lower upper))
             (task_stack_key lease) =
             Some (lease.(stackLeaseRegion), initial.(armv7a_continuation_fragments))).
           rewrite task_stack_park_lookup; reflexivity.
        -- exact (armv7a_initial_restore_source external platform port abi initial_abi initial Hinitial).
Qed.

(** Consume the real selector's changing heap and the selected TCB-SP load,
    then take the same parked buffer exactly once.  The sixteen restore
    reads are derived from its initialized bytes, not supplied as a pure
    destination premise.  This is a composition of these two memory
    fragments: no profiling, task-level save, callback, or intervening
    client execution is silently represented by their adjacency. *)
Lemma task_create_selection_takes_initial_frame :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (initial_abi : Armv7aInitialEntryABI external platform port abi)
    sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease tail (frame : Assertion) heap,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  let published := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  let initial := armv7a_initial_continuation lease args.(createStackTop) args.(createEntry)
    args.(createArgument) task_return lower upper in
  let transfer := task_create_initial_selection_transfer published initial in
  published.(SchedState).(readyList) = lease.(stackLeaseSlot) :: tail ->
  tcb_field_address (task_slot_addr sg lease.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg lease.(stackLeaseSlot) ->
  (UCOS2_inv sg published ** armv7a_task_continuations abi published.(TskState).(parkedTaskStacks) **
   unmap_table_rep sg ** frame) heap ->
  exists selected final saved,
    os_int_exit_selection_heap_fragment sg heap selected /\
    sched_install_heap_fragment sg selected final (task_slot_addr sg lease.(stackLeaseSlot))
      initial.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads initial final /\
    task_current_at (os_int_exit_installed_state transfer)
      lease.(stackLeaseSlot) lease.(stackLeaseGeneration) /\
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
     armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep lease.(stackLeaseRegion) initial.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi saved ** unmap_table_rep sg ** frame) final.
Proof.
  intros external platform port abi initial_abi sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease tail frame heap Hlayout Hregion actual
    Hcommit Hcreation published initial transfer Hready Haddress Hheap.
  assert (Hvalid : UCOS2_state_inv sg published).
  { destruct Hheap as [owned [rest [Hj [[owned' [rest' [Hj' [[owned'' [rest''
      [Hj'' [[Hvalid Hraw] Hcaps]]]] Htable]]]] Hframe]]]]; exact Hvalid. }
  assert (Hregistered : task_current_prio_registered published.(TskState)).
  { destruct Hvalid as [_ [Htasks _]]; unfold task_in_range in Htasks; tauto. }
  assert (Hsplit : UCOS2_inv sg published **
      armv7a_task_continuations abi published.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame |--
    UCOS2_raw_rep sg published ** unmap_table_rep sg **
      (armv7a_task_continuations abi published.(TskState).(parkedTaskStacks) ** frame)).
  { unfold UCOS2_inv; entailer!. }
  destruct (os_int_exit_selection_raw_frame_post sg published _ heap
    (proj1 (proj1 Hvalid)) (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered
    ltac:(rewrite Hready; discriminate) (Hsplit heap Hheap))
    as [selected [Hselection [Hhighread [Hcurrentread Hselected]]]].
  assert (Hselected_valid : UCOS2_state_inv sg (os_int_exit_selection_state published))
    by (apply os_int_exit_selection_state_preserves_validity; exact Hvalid).
  assert (Hmerge : UCOS2_raw_rep sg (os_int_exit_selection_state published) ** unmap_table_rep sg **
      (armv7a_task_continuations abi published.(TskState).(parkedTaskStacks) ** frame) |--
    UCOS2_inv sg transfer.(os_int_exit_hooked_state) **
      armv7a_task_continuations abi transfer.(os_int_exit_hooked_state).(TskState).(parkedTaskStacks) **
      (unmap_table_rep sg ** frame)).
  { unfold transfer, task_create_initial_selection_transfer; cbn [os_int_exit_hooked_state].
    unfold UCOS2_inv; entailer!. }
  pose proof (task_create_selected_initial_destination external platform port abi initial_abi
    sg region args task_return lower upper initial_name invocation origin acquired current slot
    image lease tail Hlayout Hregion Hcommit Hcreation Hready) as Hdestination.
  destruct (armv7a_install_take_task_continuation external platform port abi sg transfer _ selected
    Hdestination Haddress (Hmerge selected Hselected))
    as [final [saved [Hinstall [Hbinding [Hstack [Hfragments [Hcurrent Hresources]]]]]]].
  change (saved.(armv7a_continuation_stack) = lease) in Hstack.
  change (saved.(armv7a_continuation_fragments) = initial.(armv7a_continuation_fragments)) in Hfragments.
  rewrite Hstack, Hfragments in Hresources; rewrite Hstack in Hcurrent.
  assert (Hreorder : UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep lease.(stackLeaseRegion) initial.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource abi saved ** (unmap_table_rep sg ** frame) |--
    task_stack_fragments_rep initial.(armv7a_continuation_stack).(stackLeaseRegion)
      initial.(armv7a_continuation_fragments) **
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
      armv7a_task_continuation_resource abi saved ** unmap_table_rep sg ** frame)).
  { unfold initial; cbn [armv7a_initial_continuation armv7a_continuation_stack]; entailer!. }
  assert (Hinitial : armv7a_initial_frame_binding initial)
    by (apply task_create_initial_frame_binding with (region := region); assumption).
  exists selected, final, saved; split; [exact Hselection|]. split; [exact Hinstall|].
  split; [exact (armv7a_initial_frame_restore_reads initial _ final Hinitial (Hreorder final Hresources))|].
  split; [exact Hcurrent|].
  assert (Hassoc : UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep lease.(stackLeaseRegion) initial.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource abi saved ** (unmap_table_rep sg ** frame) |--
    UCOS2_inv sg (os_int_exit_installed_state transfer) **
      armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
      task_stack_fragments_rep lease.(stackLeaseRegion) initial.(armv7a_continuation_fragments) **
      armv7a_task_continuation_resource abi saved ** unmap_table_rep sg ** frame) by entailer!.
  exact (Hassoc final Hresources).
Qed.

(** Direct consumer of the actual publication cut.  The initialized stack
    is absent from the postcondition's parked map after the selected take;
    its single physical owner supplies all sixteen frame reads instead.
    This theorem is not an OS_Sched call proof: any source interval between
    these fragments must transport this produced world on its real heap. *)
Lemma task_create_publication_selection_takes_initial_frame :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    (initial_abi : Armv7aInitialEntryABI external platform port abi)
    sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease flags tail (frame : Assertion) heap,
  UCOS2_state_inv sg current ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  let actual := task_create_tcb_args args
    (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node actual acquired slot image).(tcbTaskName) chars) ->
  let published := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  let initial := armv7a_initial_continuation lease args.(createStackTop) args.(createEntry)
    args.(createArgument) task_return lower upper in
  let transfer := task_create_initial_selection_transfer published initial in
  published.(SchedState).(readyList) = lease.(stackLeaseSlot) :: tail ->
  tcb_field_address (task_slot_addr sg lease.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg lease.(stackLeaseSlot) ->
  (task_create_publication_storage sg actual invocation acquired current slot image **
   task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
   armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame) heap ->
  exists selected final saved,
    os_int_exit_selection_heap_fragment sg heap selected /\
    sched_install_heap_fragment sg selected final (task_slot_addr sg lease.(stackLeaseSlot))
      initial.(armv7a_continuation_sp) /\
    armv7a_continuation_restore_reads initial final /\
    task_current_at (os_int_exit_installed_state transfer)
      lease.(stackLeaseSlot) lease.(stackLeaseGeneration) /\
    (UCOS2_inv sg (os_int_exit_installed_state transfer) **
     armv7a_task_continuations abi (os_int_exit_installed_state transfer).(TskState).(parkedTaskStacks) **
     task_stack_fragments_rep lease.(stackLeaseRegion) initial.(armv7a_continuation_fragments) **
     armv7a_task_continuation_resource abi saved ** unmap_table_rep sg ** frame) final.
Proof.
  intros external platform port abi initial_abi sg region args task_return lower upper initial_name
    invocation origin acquired current slot image lease flags tail frame heap Hvalid Hlayout Hregion
    actual Hcommit Hcreation Hflags Hname published initial transfer Hready Haddress Hheap.
  pose proof (task_create_publication_stack_merge external platform port abi sg region args
    task_return lower upper initial_name invocation origin acquired current slot image lease flags
    Hvalid Hlayout Hregion Hcommit Hcreation Hflags Hname) as Hpublish.
  cbv zeta in Hpublish; fold actual in Hpublish; fold published in Hpublish.
  assert (Hmerge : task_create_publication_storage sg actual invocation acquired current slot image **
      task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
      armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame |--
    UCOS2_inv sg published ** armv7a_task_continuations abi published.(TskState).(parkedTaskStacks) **
      unmap_table_rep sg ** frame).
  { sep_apply_l_atomic Hpublish; entailer!. }
  exact (task_create_selection_takes_initial_frame external platform port abi initial_abi sg region args
    task_return lower upper initial_name invocation origin acquired current slot image lease tail frame heap
    Hlayout Hregion Hcommit Hcreation Hready Haddress (Hmerge heap Hheap)).
Qed.
