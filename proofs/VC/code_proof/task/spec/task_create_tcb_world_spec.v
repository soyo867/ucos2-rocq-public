Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_sched_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Publication changes links of an existing head. Transport precisely
    generation/priority/status/delay from the real commit, then use the
    new global ready invariant for membership. Neither whole-node equality
    nor current-implies-ready is assumed. Boot and nonzero-nesting stages
    remain supported. The new child's private slot cannot be the live
    executing caller, so its park does not occupy the caller's taken key. *)
Lemma task_create_publication_preserves_call_stage : forall sg publication state call,
  UCOS2_state_inv sg state ->
  task_create_stack_publication_input sg publication state ->
  task_create_call_stage call state ->
  task_create_call_stage call (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state call Hvalid Hinput [Horigin Hstage].
  unfold task_create_call_stage.
  destruct call.(os_sched_call_origin) as [|slot generation] eqn:Hcall.
  - split; [exact Horigin|exact I].
  - destruct Horigin as [Hrunning [Hcurrent [old [Hold Hgen]]]].
    destruct Hstage as [Hslot [Hgeneration [Habsent Hready]]].
    set (args := task_create_stack_publication_args publication).
    set (new := task_tcb_init_commit_node args publication.(stack_publication_acquired)
      publication.(stack_publication_slot) publication.(stack_publication_image)).
    set (published := task_create_stack_publication_state sg publication state).
    assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
      publication.(stack_publication_invocation) new).
    { eapply task_tcb_init_commit_binding_identity; exact (proj1 (proj2 (proj2 Hinput))). }
    assert (Hfresh : state.(TskState).(inUsedTaskStates) new.(taskID) = None).
    { exact (proj1 (task_private_excludes_public sg state.(TskState) new.(taskID)
        (proj1 (proj1 (proj2 Hvalid))) (task_commit_identity_private _ _ _ _ Hidentity))). }
    assert (Hdifferent : slot <> new.(taskID)) by congruence.
    destruct (task_commit_transports_old_fields state.(TskState) args.(initPrio)
      publication.(stack_publication_invocation) new slot old Hfresh Hold)
      as [updated [Hupdated Hfields]].
    assert (Hgen_updated : updated.(taskGeneration) = old.(taskGeneration))
      by exact (f_equal taskGeneration Hfields).
    assert (Hlookup : published.(TskState).(inUsedTaskStates) slot = Some updated) by exact Hupdated.
    split.
    + split; [exact Hrunning|]. split; [exact Hcurrent|].
      exists updated; split; [exact Hlookup|congruence].
    + split; [exact Hslot|]. split; [exact Hgeneration|]. split.
      * destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _
          (proj1 (proj2 (proj2 (proj2 Hinput)))) Hidentity) as [Hnewslot Hnewgen].
        change ((task_stack_park state.(TskState).(parkedTaskStacks)
          publication.(stack_publication_lease) (task_create_stack_publication_words publication))
          (task_stack_key call.(os_sched_call_stack)) = None).
        rewrite task_stack_park_lookup_other; [exact Habsent|].
        intro Heq; apply Hdifferent; rewrite Hslot, Hnewslot; exact (f_equal fst Heq).
      * intros Hnest.
        destruct (Hready Hnest) as [ready [Hready_old Hg]].
        assert (ready = old) by (destruct Hready_old as [Hready_node _]; congruence); subst ready.
        destruct Hready_old as [_ [Hcur [Hpriority [Hin Heffective]]]].
        assert (Hpriority_updated : updated.(curPrio) = old.(curPrio))
          by exact (f_equal curPrio Hfields).
        assert (Hstatus_updated : updated.(stat) = old.(stat))
          by exact (f_equal stat Hfields).
        assert (Hdelay_updated : updated.(dly) = old.(dly))
          by exact (f_equal dly Hfields).
        assert (Heffective_updated : is_effectively_ready updated.(stat) updated.(dly) = true).
        { rewrite Hstatus_updated, Hdelay_updated; exact Heffective. }
        assert (Hpost : UCOS2_state_inv sg published).
        { eapply task_create_stack_publication_preserves_validity; [exact Hvalid|].
          split; [exact Hinput|reflexivity]. }
        assert (Hmember : In slot published.(SchedState).(readyList)).
        { exact (proj1 (proj2 (proj2 (proj1 (proj1 (proj2 (proj2 Hpost))))))
            _ _ Hlookup Heffective_updated). }
        exists updated; split; [|congruence].
        unfold sched_current_ready_at; split; [exact Hlookup|]. split; [exact Hcur|].
        split.
        -- change (state.(SchedState).(curSchedPrio) = Some updated.(curPrio)).
           rewrite Hpriority_updated; exact Hpriority.
        -- split; assumption.
Qed.

(** Actual TCBInit publication stores retain the API-stage source facts
    and produce the SAME current strong world needed by its final Restore
    and TaskCreate's next Save. The child's initialized stack is consumed
    by the existing proved publication merge; no old weak capsule post is
    upgraded, and the masked CPU owner is framed only through these stores. *)
Lemma task_create_tcb_publication_world_source :
  forall environment critical sg publication state call saved acquired before (frame : Assertion),
  let args := task_create_stack_publication_args publication in
  let published := task_create_stack_publication_state sg publication state in
  UCOS2_state_inv sg state ->
  task_create_stack_publication_input sg publication state ->
  task_create_call_stage call state ->
  task_stack_live_coverage state.(TskState) (task_stack_call_active_key call) ->
  0 <= args.(initPrio) < 64 ->
  0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296 ->
  (task_tcb_init_publication_tail_storage sg args state
     publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_stack_continuations environment.(task_stack_call_continuations)
     state.(TskState) state.(TskState).(parkedTaskStacks) **
   (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) saved acquired **
    task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame)) before ->
  exists after,
    task_tcb_init_publication_tail_fragment sg args.(initPrio)
      (task_slot_addr sg publication.(stack_publication_slot)) before after /\
    kernel_client_step (task_create_stack_publication_client publication) sg state published /\
    task_create_call_stage call published /\
    (kernel_stack_call_masked environment.(task_stack_call_continuations) kernel_program_inv
       critical sg (task_stack_call_active_key call) call saved acquired published ** frame) after.
Proof.
  intros environment critical sg publication state call saved acquired before frame args published
    Hvalid Hinput Hstage Hcoverage Hpriority Hpointer Hpre.
  assert (Horder : task_tcb_init_publication_tail_storage sg args state
      publication.(stack_publication_slot) publication.(stack_publication_image) **
    task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
    armv7a_task_stack_continuations environment.(task_stack_call_continuations)
      state.(TskState) state.(TskState).(parkedTaskStacks) **
    (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
       call.(os_sched_call_origin) saved acquired **
     task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame) |--
    task_tcb_init_publication_tail_storage sg args state
      publication.(stack_publication_slot) publication.(stack_publication_image) **
    (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
     armv7a_task_stack_continuations environment.(task_stack_call_continuations)
       state.(TskState) state.(TskState).(parkedTaskStacks) **
     (critical_region_masked environment.(task_stack_call_platform) critical sg call.(os_sched_call_invocation)
        call.(os_sched_call_origin) saved acquired **
      task_tcb_init_stack_context environment call ** unmap_table_rep sg ** frame))) by entailer!.
  destruct (task_tcb_init_publication_tail_store_execution sg args
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid (proj1 (proj2 (proj2 Hinput))) Hpriority Hpointer
    (Horder before Hpre)) as [after [Hrun Hafter]].
  pose proof (task_create_publication_covered_stack_merge _ _ _
    environment.(task_stack_call_continuations) sg publication state (task_stack_call_active_key call)
    Hvalid Hinput Hcoverage) as Hmerge; cbv zeta in Hmerge.
  fold args in Hmerge.
  pose proof (task_create_publication_preserves_call_stage sg publication state call Hvalid Hinput Hstage)
    as Hstage_after.
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg state published)
    by (split; [exact Hinput|reflexivity]).
  exists after; split; [exact Hrun|]. split; [exact Hstep|]. split; [exact Hstage_after|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sepcon_assoc_change; sep_apply_l_atomic Hmerge; Intros.
    unfold kernel_stack_call_masked, kernel_stack_inv, task_tcb_init_stack_context.
    rewrite kernel_program_inv_split_unmap; entailer!. }
  exact (Hclose after Hafter).
Qed.
