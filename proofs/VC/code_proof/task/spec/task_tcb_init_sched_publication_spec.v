Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_source_entry_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Facts at the real final publication cut, consumed by its C annotation.
    No fact concerns a future Restore. The child supplies a ready entry;
    the live caller's key is distinct from the private child, so this C
    publication preserves an already established available-key fact.
    Boot needs no task-key or ready-caller premise. *)
Definition task_tcb_init_publication_call_observation sg publication call current : Prop :=
  task_create_stack_publication_input sg publication current /\
  (task_create_stack_publication_state sg publication current).(SchedState).(readyList) <> [] /\
  (kernel_call_stack_available call current ->
    kernel_call_stack_available call (task_create_stack_publication_state sg publication current)).

(** The actual post-store cells, initialized buffer and capsule map are
    consumed once by the existing merge. Its established publication
    input is now retained for the next call, rather than reconstructed
    from a weaker existential result or assumed as a new public premise. *)
Lemma task_tcb_init_continuation_publication_sched_output :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin initial acquired current slot rest image call,
  call.(os_sched_call_invocation) = invocation -> call.(os_sched_call_origin) = origin ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired ->
  task_tcb_init_call_preserved sg invocation initial acquired ->
  task_tcb_init_detach_observation (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired slot rest image ->
  task_tcb_init_call_preserved sg invocation
    (task_tcb_init_detached_state (task_tcb_init_stack_call_args args initial_name)
      invocation origin acquired slot rest image) current ->
  task_tcb_init_commit_binding (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired current slot ->
  UCOS2_state_inv sg current ->
  task_stack_live_coverage current.(TskState) (task_stack_call_active_key call) ->
  task_create_publication_storage sg (task_tcb_init_stack_call_args args initial_name)
    invocation acquired current slot image **
  task_stack_storage region (task_create_stack_image TaskStackNoVFP args task_return lower upper) **
  task_tcb_init_continuation_capsules environment saved_local current |--
  EX lease,
    let publication := task_tcb_init_stack_publication region args task_return lower upper initial_name
      invocation origin acquired slot image lease in
    coq_prop (task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
      invocation origin initial 0 (task_create_stack_publication_state sg publication current) /\
      task_stack_live_coverage (task_create_stack_publication_state sg publication current).(TskState)
        (task_stack_call_active_key call) /\
      (forall observer, task_tcb_init_stack_source_preserved observer current
        (task_create_stack_publication_state sg publication current)) /\
      task_tcb_init_publication_call_observation sg publication call current) &&
    (UCOS2_inv sg (task_create_stack_publication_state sg publication current) **
     task_tcb_init_continuation_capsules environment saved_local
       (task_create_stack_publication_state sg publication current)).
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin initial acquired current slot rest image call Hi Ho Hlayout Hentry Hfirst
    Hdetach Hinterval Hcommit Hvalid Hcoverage.
  destruct (task_tcb_init_call_preserves_allocation sg (task_tcb_init_stack_call_args args initial_name)
    invocation origin acquired slot rest image current Hentry Hdetach Hinterval)
    as [_ [_ Hactive]].
  assert (Hactive_call : task_invocation_active current.(TskState)
    call.(os_sched_call_invocation) call.(os_sched_call_origin))
    by (rewrite Hi, Ho; exact Hactive).
  sep_apply_l_atomic (task_tcb_init_continuation_publication_output environment critical saved_local
    sg region args task_return lower upper initial_name invocation origin initial acquired current slot
    rest image (task_stack_call_active_key call) Hlayout Hentry Hfirst Hdetach Hinterval Hcommit Hvalid Hcoverage).
  Intros lease; cbv zeta; Intros.
  set (publication := task_tcb_init_stack_publication region args task_return lower upper initial_name
    invocation origin acquired slot image lease).
  assert (Hinput : task_create_stack_publication_input sg publication current)
    by (unfold publication; tauto).
  assert (Havailable : kernel_call_stack_available call current ->
    kernel_call_stack_available call (task_create_stack_publication_state sg publication current)).
  { intro Hnone.
    pose proof (proj2 (proj2 Hactive_call)) as Hlive.
    unfold kernel_call_stack_available in Hnone |- *.
    destruct call.(os_sched_call_origin) as [|tid generation] eqn:Hcall; [exact I|].
    unfold task_invocation_origin_live in Hlive.
    destruct Hlive as [caller_node [Hcaller Hgeneration]].
    pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
    pose proof (proj1 (proj2 (proj2 (proj2 Hinput)))) as Hcreation.
    set (node := task_tcb_init_commit_node (task_create_stack_publication_args publication)
      publication.(stack_publication_acquired) publication.(stack_publication_slot)
      publication.(stack_publication_image)).
    assert (Hidentity : task_commit_identity current.(TskState)
      (task_create_stack_publication_args publication).(initPrio)
      publication.(stack_publication_invocation) node)
      by (eapply task_tcb_init_commit_binding_identity; exact Hbinding).
    destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity)
      as [Hslot Hgeneration_child].
    pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
    pose proof (proj1 (task_private_excludes_public sg current.(TskState) node.(taskID)
      (proj1 (proj1 (proj2 Hvalid))) Hprivate)) as Hnot_used.
    assert (Hdifferent : (tid, generation) <> task_stack_key publication.(stack_publication_lease)).
    { intro Hequal; pose proof (f_equal fst Hequal) as Htid.
      change (tid = publication.(stack_publication_lease).(stackLeaseSlot)) in Htid.
      rewrite <- Hslot in Htid; subst tid; rewrite Hnot_used in Hcaller; discriminate. }
    change (task_stack_park current.(TskState).(parkedTaskStacks)
      publication.(stack_publication_lease) (task_create_stack_publication_words publication)
      (tid, generation) = None).
    rewrite task_stack_park_lookup_other by exact Hdifferent; exact Hnone. }
  assert (Hobservation : task_tcb_init_publication_call_observation sg publication call current).
  { split; [exact Hinput|]. split; [apply task_create_stack_publication_ready_nonempty|exact Havailable]. }
  Exists lease; fold publication; entailer!.
Qed.
