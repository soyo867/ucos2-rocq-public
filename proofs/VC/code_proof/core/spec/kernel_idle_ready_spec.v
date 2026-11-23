Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.task_idle_ready Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.kernel_start.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_start_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_InitTaskIdle supplies OS_LOWEST_PRIO to CreateExt. The actual
    OS_TCBInit stores set Stat and Dly to zero before publication. *)
Lemma task_tcb_init_published_idle_ready : forall sg args invocation acquired current slot image,
  args.(initPrio) = sg.(osLowestPrio) ->
  task_idle_ready sg
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState).
Proof.
  intros sg args invocation acquired current slot image Hprio.
  apply task_commit_establishes_idle_ready; [exact Hprio|reflexivity].
Qed.

(** A later creation publishes a fresh private slot. Its writes to the old
    head only change links, so the live Idle TCB retains Stat/Dly/Prio. *)
Lemma task_tcb_init_publication_preserves_idle_ready :
  forall sg args invocation origin acquired current slot image,
  UCOS2_state_inv sg current ->
  task_tcb_init_commit_binding args invocation origin acquired current slot ->
  task_idle_ready sg current.(TskState) ->
  task_idle_ready sg
    (task_tcb_init_published_state sg args invocation acquired current slot image).(TskState).
Proof.
  intros sg args invocation origin acquired current slot image Hvalid Hbinding Hidle.
  pose proof (task_tcb_init_commit_binding_identity args invocation origin
    acquired current slot image Hbinding) as Hidentity.
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  destruct (task_private_excludes_public sg current.(TskState) slot
    (proj1 (proj1 (proj2 Hvalid))) Hprivate) as [Hfresh _].
  apply task_commit_preserves_idle_ready; assumption.
Qed.

(** Consume the same written TCB, links, bitmap, priority table and initial
    stack as the existing publication rule. The ready witness is attached
    at this physical publication cut; it is not a promise about a later
    arbitrary interference interval. This covers both Idle's own creation
    and subsequent creations retaining the established Idle witness. *)
Lemma task_tcb_init_publication_idle_stack_merge :
  forall sg args invocation origin acquired current slot image flags lease words,
  (args.(initPrio) = sg.(osLowestPrio) \/ task_idle_ready sg current.(TskState)) ->
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
  let parked := replace_TskS (glob_task_set_parked_stacks post.(TskState)
    (task_stack_park current.(TskState).(parkedTaskStacks) lease words)) post in
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
  coq_prop (task_idle_ready sg parked.(TskState) /\ parked.(SchedState).(readyList) <> []) &&
  UCOS2_inv sg parked.
Proof.
  intros sg args invocation origin acquired current slot image flags lease words
    Hsource Hvalid Hcommit Hflags Hname Hbinding Hregion Hsp post parked.
  assert (Hidle : task_idle_ready sg parked.(TskState)).
  { change (task_idle_ready sg post.(TskState)).
    destruct Hsource as [Hprio | Hidle].
    - apply task_tcb_init_published_idle_ready; exact Hprio.
    - eapply task_tcb_init_publication_preserves_idle_ready; eauto. }
  pose proof (task_tcb_init_publication_stack_merge sg args invocation origin acquired current slot
    image flags lease words Hvalid Hcommit Hflags Hname Hbinding Hregion Hsp) as Hmerge.
  cbv zeta in Hmerge; fold post parked in Hmerge.
  eapply derivable1_trans; [exact Hmerge|].
  unfold UCOS2_inv; Intros.
  assert (Hnonempty : parked.(SchedState).(readyList) <> []).
  { eapply sched_idle_ready_nonempty; [|exact Hidle].
    match goal with H : UCOS2_state_inv sg parked |- _ =>
      exact (proj1 (proj1 (proj2 (proj2 H)))) end. }
  entailer!.
Qed.
