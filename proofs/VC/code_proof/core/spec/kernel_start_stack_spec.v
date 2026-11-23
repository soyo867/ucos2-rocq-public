Require Import Coq.Lists.List Coq.ZArith.ZArith.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.timer.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_start.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Resource endpoints for Task publication and first start. The completed
    TCB/ready writes use task_sched_commit_state; the stack is transferred
    in the SAME protected phase before publication becomes observable.
    This rule is not permission to leave a public task without its stack
    across Restore, nor to retain its initial bytes after it has run. *)
Lemma task_commit_park_global_resources : forall sg s priority invocation origin lease node words,
  UCOS2_state_inv sg s ->
  task_commit_identity s.(TskState) priority invocation node ->
  task_stack_creation_binding s.(TskState) priority invocation origin lease ->
  valid_task_stack_region lease.(stackLeaseRegion) ->
  task_stack_saved_pointer_in_range lease.(stackLeaseRegion) node.(tcbStkPtr) ->
  let committed := task_sched_commit_state sg s priority invocation node in
  let parked := task_stack_park s.(TskState).(parkedTaskStacks) lease words in
  task_stack_storage lease.(stackLeaseRegion) words ** UCOS2_inv sg committed |--
    UCOS2_inv sg (replace_TskS (glob_task_set_parked_stacks committed.(TskState) parked) committed).
Proof.
  intros sg s priority invocation origin lease node words Hvalid Hidentity Hbinding Hregion Hsp
    committed parked.
  assert (Hconsistent : parked_stacks_consistent s.(TskState) s.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  destruct (task_stack_creation_binding_commit_identity s.(TskState) priority invocation origin
    lease node Hbinding Hidentity) as [Hslot Hgen].
  assert (Hfresh : s.(TskState).(parkedTaskStacks) (task_stack_key lease) = None).
  { unfold task_stack_key; rewrite <- Hslot, <- Hgen.
    eapply task_commit_stack_key_absent; [exact (proj1 (proj2 Hvalid))|exact Hidentity|exact Hconsistent]. }
  rewrite (UCOS2_inv_split_parked_stacks sg committed); Intros.
  match goal with H : UCOS2_state_inv sg committed |- _ => rename H into Hcommitted end.
  change (task_stack_storage lease.(stackLeaseRegion) words **
    (store_parked_stacks s.(TskState).(parkedTaskStacks) **
     UCOS2_raw_rep_missing_parked_stacks sg committed) |--
    UCOS2_inv sg (replace_TskS (glob_task_set_parked_stacks committed.(TskState) parked) committed)).
  eapply derivable1_trans with (y :=
    (task_stack_storage lease.(stackLeaseRegion) words ** store_parked_stacks s.(TskState).(parkedTaskStacks)) **
    UCOS2_raw_rep_missing_parked_stacks sg committed); [entailer!|].
  sep_apply_l_atomic (task_stack_commit_park_consistent_resources s.(TskState) priority invocation
    origin lease node words s.(TskState).(parkedTaskStacks)
    Hconsistent Hfresh Hbinding Hidentity Hregion Hsp).
  Intros.
  match goal with H : parked_stacks_consistent (task_commit _ _ _ _) _ |- _ =>
    rename H into Hparked end.
  apply UCOS2_inv_merge_updated_parked_stacks; [exact Hcommitted|exact Hparked].
Qed.

(** Consume TCBInit's actual publication writes together with the caller's
    current stack. Post-validity, private-generation freshness and the
    committed stack map are derived, not supplied as new postconditions.
    StackInit/clear supply [words] at this protected cutpoint; this rule
    never promises that the initial bytes survive a later scheduling call. *)
Lemma task_tcb_init_publication_stack_merge :
  forall sg args invocation origin acquired current slot image flags lease words,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node args acquired slot image).(tcbTaskName) chars) ->
  task_stack_creation_binding current.(TskState) args.(initPrio) invocation origin lease ->
  valid_task_stack_region lease.(stackLeaseRegion) ->
  task_stack_saved_pointer_in_range lease.(stackLeaseRegion) args.(initStkPtr) ->
  let post := task_tcb_init_published_state sg args invocation acquired current slot image in
  task_stack_storage lease.(stackLeaseRegion) words **
    (task_slot_storage_rep sg slot
       (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
         (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
           sg.(osKernelConfig).(cfgTaskProfile) args image)) **
     task_tcb_init_used_with_head_prev sg current slot **
     sg.(g_OSTCBList) # Ptr |-> task_slot_addr sg slot **
     sg.(g_OSTaskCtr) # UChar |-> (task_tcb_init_count current + 1) **
     sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group post **
     UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows post) **
     PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg post) **
     task_tcb_init_publication_other sg current) |--
  UCOS2_inv sg
    (replace_TskS (glob_task_set_parked_stacks post.(TskState)
      (task_stack_park current.(TskState).(parkedTaskStacks) lease words)) post).
Proof.
  intros sg args invocation origin acquired current slot image flags lease words
    Hvalid Hcommit Hflags Hname Hbinding Hregion Hsp post.
  unfold post.
  pose proof (task_tcb_init_publication_storage_merge__publication_and_returns
    sg args invocation origin acquired current slot image flags Hvalid Hcommit Hflags Hname) as Hpublish.
  cbv zeta in Hpublish; sep_apply_l_atomic Hpublish.
  eapply derivable1_trans with (y := task_stack_storage lease.(stackLeaseRegion) words **
    UCOS2_inv sg (task_tcb_init_published_state sg args invocation acquired current slot image));
    [entailer!|].
  apply task_commit_park_global_resources with (origin := origin).
  - exact Hvalid.
  - eapply task_tcb_init_commit_binding_identity; exact Hcommit.
  - exact Hbinding.
  - exact Hregion.
  - exact Hsp.
Qed.

(** The initial continuation is transferred at the SAME actual protected
    publication cut as the existing TCB/ready storage consumer. The input
    below is the actual written TCB/link/table heap, not a pure endpoint
    or a resource generated by CPU Save. The source StackInit producer in
    task_create_stack_spec supplies its current buffer before this cut. *)
Lemma task_tcb_init_publication_initial_continuation_merge :
  forall external platform port (abi : Armv7aContinuationABI external platform port)
    sg region args task_return lower upper initial_name invocation origin acquired current slot image flags lease,
  let actual := task_create_tcb_args args (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) initial_name in
  let post := task_tcb_init_published_state sg actual invocation acquired current slot image in
  let after := task_create_stack_published_state sg actual invocation acquired current slot image lease
    (task_create_stack_image TaskStackNoVFP args task_return lower upper) in
  UCOS2_state_inv sg current ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  lease.(stackLeaseRegion) = region ->
  task_tcb_init_commit_binding actual invocation origin acquired current slot ->
  task_stack_creation_binding current.(TskState) actual.(initPrio) invocation origin lease ->
  image (TCBCommonField TCBFlagsRdy) = Some flags ->
  (sg.(osKernelConfig).(cfgTaskNames) = true ->
    exists chars, readable_name current.(NameState)
      (task_tcb_init_commit_node actual acquired slot image).(tcbTaskName) chars) ->
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    (task_slot_storage_rep sg slot
       (task_tcb_init_linked_layout_image sg current.(TskState).(tcbListHead)
         (task_tcb_init_layout_image sg.(osKernelConfig).(cfgEventMultiEnabled)
           sg.(osKernelConfig).(cfgTaskProfile) actual image)) **
     task_tcb_init_used_with_head_prev sg current slot **
     sg.(g_OSTCBList) # Ptr |-> task_slot_addr sg slot **
     sg.(g_OSTaskCtr) # UChar |-> (task_tcb_init_count current + 1) **
     sg.(g_OSRdyGrp) # UChar |-> task_tcb_init_ready_group post **
     UCharArray.full sg.(g_OSRdyTbl) 8 (task_tcb_init_ready_rows post) **
     PtrArray.full sg.(g_OSTCBPrioTbl) 64 (task_tcb_init_priority_table sg post) **
     task_tcb_init_publication_other sg current) **
    armv7a_task_continuations abi current.(TskState).(parkedTaskStacks) |--
  UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks).
Proof.
  intros external platform port abi sg region args task_return lower upper initial_name invocation origin
    acquired current slot image flags lease actual post after
    Hvalid Hlayout Hregion Hcommit Hcreation Hflags Hname.
  pose proof (task_tcb_init_publication_storage_merge__publication_and_returns
    sg actual invocation origin acquired current slot image flags Hvalid Hcommit Hflags Hname) as Hpublish.
  cbv zeta in Hpublish; unfold post; sep_apply_l_atomic Hpublish.
  eapply derivable1_trans with (y :=
    task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    UCOS2_inv sg post ** armv7a_task_continuations abi current.(TskState).(parkedTaskStacks));
    [entailer!|].
  rewrite (UCOS2_inv_split_parked_stacks sg post); Intros.
  match goal with H : UCOS2_state_inv sg post |- _ => rename H into Hpost end.
  change (task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
    (store_parked_stacks current.(TskState).(parkedTaskStacks) **
     (UCOS2_raw_rep_missing_parked_stacks sg post **
      armv7a_task_continuations abi current.(TskState).(parkedTaskStacks))) |--
    UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
  pose proof (task_create_stack_park_initial_continuation external platform port abi sg region args
    task_return lower upper initial_name invocation origin acquired current slot image lease
    Hvalid Hlayout Hregion Hcommit Hcreation) as Hpark.
  cbv zeta in Hpark; sep_apply_l_atomic Hpark.
  Intros.
  match goal with H : parked_stacks_consistent _ _ |- _ => rename H into Hstacks end.
  change (parked_stacks_consistent post.(TskState) after.(TskState).(parkedTaskStacks)) in Hstacks.
  change (store_parked_stacks after.(TskState).(parkedTaskStacks) **
    (armv7a_task_continuations abi after.(TskState).(parkedTaskStacks) **
     UCOS2_raw_rep_missing_parked_stacks sg post) |--
    UCOS2_inv sg after ** armv7a_task_continuations abi after.(TskState).(parkedTaskStacks)).
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg post
    after.(TskState).(parkedTaskStacks) Hpost Hstacks).
  unfold after, task_create_stack_published_state; entailer!.
Qed.

Definition kernel_start_take_stack_state (s : UCOS2_Verify_State) (lease : TaskStackLease)
  : UCOS2_Verify_State :=
  replace_TskS (glob_task_set_parked_stacks s.(TskState)
    (task_stack_take s.(TskState).(parkedTaskStacks) lease)) s.

(** V2.93.01 ARMv7-A/GNU OSStartHighRdy calls OSTaskSwHook, writes
    OSRunning, then RELOADS OSTCBHighRdy and its saved SP before restoring.
    [s] is this actual post-hook observation, not a frozen pre-hook state.
    The hook/port contract must establish the selected live instance and
    supply its saved register frame. The theorem transfers existing bytes;
    it proves no ARM instructions, entry-code contract or ordinary return
    to the caller of OSStart. A retired/reused generation is not accepted. *)
Lemma kernel_start_take_stack_resources : forall sg s lease words node,
  sched_current_ready_at s.(TskState) s.(SchedState) lease.(stackLeaseSlot) node ->
  s.(SchedState).(isRunning) = true ->
  s.(SchedState).(highRdyTid) = Some lease.(stackLeaseSlot) ->
  node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  s.(TskState).(parkedTaskStacks) (task_stack_key lease) =
    Some (lease.(stackLeaseRegion), task_stack_complete_fragments lease.(stackLeaseRegion) words) ->
  UCOS2_inv sg s |--
    coq_prop (task_stack_live_binding (kernel_start_take_stack_state s lease).(TskState) lease /\
      sched_task_call_boundary (kernel_start_take_stack_state s lease).(TskState)
        (kernel_start_take_stack_state s lease).(SchedState) /\
      (kernel_start_take_stack_state s lease).(SchedState).(highRdyTid) = Some lease.(stackLeaseSlot) /\
      (kernel_start_take_stack_state s lease).(TskState).(parkedTaskStacks) (task_stack_key lease) = None) &&
    (task_stack_storage lease.(stackLeaseRegion) words **
      UCOS2_inv sg (kernel_start_take_stack_state s lease)).
Proof.
  intros sg s lease words node Hready Hrunning Hhigh Hgen Hentry.
  rewrite (UCOS2_inv_split_parked_stacks sg s); Intros.
  match goal with H : UCOS2_state_inv sg s |- _ => rename H into Hvalid end.
  assert (Hconsistent : parked_stacks_consistent s.(TskState) s.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  assert (Hlease : task_stack_lease_matches_task lease node).
  { destruct (Hconsistent lease.(stackLeaseSlot) lease.(stackLeaseGeneration)
      lease.(stackLeaseRegion) (task_stack_complete_fragments lease.(stackLeaseRegion) words) Hentry)
      as [_ [_ [_ Hmatching]]].
    destruct lease; apply Hmatching; [exact (proj1 Hready)|exact Hgen]. }
  assert (Hlive : task_stack_live_binding (kernel_start_take_stack_state s lease).(TskState) lease).
  { exists node; split; [exact (proj1 Hready)|exact Hlease]. }
  assert (Hboundary : sched_task_call_boundary (kernel_start_take_stack_state s lease).(TskState)
    (kernel_start_take_stack_state s lease).(SchedState)).
  { split; [exact Hrunning|]. exists lease.(stackLeaseSlot), node; exact Hready. }
  assert (Hremoved : (kernel_start_take_stack_state s lease).(TskState).(parkedTaskStacks)
    (task_stack_key lease) = None) by apply task_stack_take_lookup.
  sep_apply_l_atomic (store_parked_stacks_take s.(TskState).(parkedTaskStacks) lease words Hentry).
  sep_apply_l_atomic (UCOS2_inv_merge_updated_parked_stacks sg s
    (task_stack_take s.(TskState).(parkedTaskStacks) lease) Hvalid
    (task_stack_take_preserves_consistency _ _ lease Hconsistent));
    unfold kernel_start_take_stack_state in *; entailer!.
Qed.

(** Actual post-hook Scheduler cells include the OSRunning store. The
    other modules are framed from that SAME post-hook state; no equality
    with a pre-hook snapshot or no-op hook contract is silently used. *)
Lemma kernel_start_running_stack_resources : forall sg s lease words node,
  UCOS2_state_inv sg s -> task_idle_tail sg s.(TskState) ->
  (sg.(osKernelConfig).(cfgTimerEnabled) = true -> timer_api_initialized s.(TimerState)) ->
  sched_current_ready_at s.(TskState) s.(SchedState) lease.(stackLeaseSlot) node ->
  s.(SchedState).(highRdyTid) = Some lease.(stackLeaseSlot) ->
  node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  s.(TskState).(parkedTaskStacks) (task_stack_key lease) =
    Some (lease.(stackLeaseRegion), task_stack_complete_fragments lease.(stackLeaseRegion) words) ->
  let running := kernel_running_store s in
  let after := kernel_start_take_stack_state running lease in
  sched_raw_rep sg running.(TskState) running.(SchedState) **
    UCOS2_raw_rep_missing_sched sg s |--
  coq_prop (task_stack_live_binding after.(TskState) lease /\
    sched_task_call_boundary after.(TskState) after.(SchedState) /\
    after.(SchedState).(highRdyTid) = Some lease.(stackLeaseSlot) /\
    after.(TskState).(parkedTaskStacks) (task_stack_key lease) = None) &&
    (task_stack_storage lease.(stackLeaseRegion) words ** UCOS2_inv sg after).
Proof.
  intros sg s lease words node Hvalid Hidle Htimer Hready Hhigh Hgen Hentry running after.
  eapply derivable1_trans with (y := UCOS2_inv sg running).
  - apply (UCOS2_inv_merge_updated_module sg s running SchedModule).
    + apply kernel_running_store_preserves_validity; assumption.
    + reflexivity.
  - apply kernel_start_take_stack_resources with (node := node).
    + exact Hready.
    + reflexivity.
    + exact Hhigh.
    + exact Hgen.
    + exact Hentry.
Qed.

Lemma kernel_start_selection_stack_binding : forall sg s head tail node lease words,
  UCOS2_state_inv sg s -> s.(SchedState).(isRunning) = false ->
  s.(SchedState).(readyList) = head :: tail -> s.(TskState).(inUsedTaskStates) head = Some node ->
  lease.(stackLeaseSlot) = head -> node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  s.(TskState).(parkedTaskStacks) (task_stack_key lease) =
    Some (lease.(stackLeaseRegion), task_stack_complete_fragments lease.(stackLeaseRegion) words) ->
  (kernel_start_ready_state s).(SchedState).(curTaskID) = Some lease.(stackLeaseSlot) /\
  task_stack_live_binding (kernel_start_ready_state s).(TskState) lease /\
  (kernel_start_ready_state s).(TskState).(parkedTaskStacks) (task_stack_key lease) =
    Some (lease.(stackLeaseRegion), task_stack_complete_fragments lease.(stackLeaseRegion) words).
Proof.
  intros sg s head tail node lease words Hvalid Hrunning Hlist Hnode Hslot Hgen Hentry.
  split.
  - rewrite Hslot.
    exact (proj1 (proj2 (kernel_start_ready_selection sg s head tail node Hvalid Hrunning Hlist Hnode))).
  - split; [|exact Hentry].
    exists node; split; [rewrite Hslot; exact Hnode|].
    assert (Hconsistent : parked_stacks_consistent s.(TskState) s.(TskState).(parkedTaskStacks)).
    { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
    destruct (Hconsistent lease.(stackLeaseSlot) lease.(stackLeaseGeneration)
      lease.(stackLeaseRegion) (task_stack_complete_fragments lease.(stackLeaseRegion) words) Hentry)
      as [_ [_ [_ Hmatching]]].
    destruct lease; apply Hmatching; [rewrite Hslot; exact Hnode|exact Hgen].
Qed.
