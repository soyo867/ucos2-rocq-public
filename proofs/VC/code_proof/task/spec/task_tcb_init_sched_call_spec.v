Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_call_protocol_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same full result and failure buffer as the canonical TCB call.
    The additional observations refer to THIS returned/current pair.
    Successful publication establishes a ready entry; completed returns
    transport it under the registered C-module obligations. Availability
    belongs only to a successful ordinary return that may call Scheduler;
    the no-free branch retains its original complete result and buffer.

    This source-aware summary still needs the returning producers below;
    changing a declaration to this post alone does not verify its callee. *)
Definition task_tcb_init_continuation_sched_call_post environment critical saved_local sg
  region args task_return lower upper initial_name invocation origin mask initial original result : Assertion :=
  EX released,
    coq_prop (task_tcb_init_stack_call_result critical sg region args task_return lower upper
      initial_name invocation origin initial result released) &&
    coq_prop (UCOS2_state_inv sg released /\
      task_tcb_init_stack_source_preserved original initial released) &&
    ((EX returned current,
      coq_prop (task_tcb_init_stack_same_call returned original /\
        task_tcb_init_stack_return_preserved original released current /\
        (result = 0 -> current.(SchedState).(readyList) <> []) /\
        (result = 0 -> kernel_call_stack_available original initial ->
          kernel_call_stack_available returned current)) &&
      task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current) **
     task_tcb_init_stack_buffer_result region args task_return lower upper result).

Lemma task_tcb_init_stack_success_ready : forall critical sg region args task_return lower upper
  initial_name invocation origin initial released,
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial 0 released ->
  released.(SchedState).(readyList) <> [].
Proof.
  intros critical sg region args task_return lower upper initial_name invocation origin initial released Hresult.
  inversion Hresult; subst; apply task_create_stack_publication_ready_nonempty.
Qed.

(** Publication parks the newly allocated child's initial stack, not the
    currently executing creator's key. Their separation follows from the
    real private/public pool partition, rather than a ghost freshness law. *)
Lemma task_create_stack_publication_preserves_call_available : forall sg publication state call,
  UCOS2_state_inv sg state -> task_create_stack_publication_input sg publication state ->
  kernel_call_task_source call state -> kernel_call_stack_available call state ->
  kernel_call_stack_available call (task_create_stack_publication_state sg publication state).
Proof.
  intros sg publication state call Hvalid Hinput Hsource Havailable.
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hcommit.
  pose proof (proj1 (proj2 (proj2 (proj2 Hinput)))) as Hcreation.
  set (args := task_create_stack_publication_args publication).
  set (node := task_tcb_init_commit_node args publication.(stack_publication_acquired)
    publication.(stack_publication_slot) publication.(stack_publication_image)).
  assert (Hidentity : task_commit_identity state.(TskState) args.(initPrio)
    publication.(stack_publication_invocation) node)
    by (eapply task_tcb_init_commit_binding_identity; exact Hcommit).
  destruct (task_stack_creation_binding_commit_identity _ _ _ _ _ _ Hcreation Hidentity)
    as [Hslot Hgeneration].
  pose proof (task_commit_identity_private _ _ _ _ Hidentity) as Hprivate.
  pose proof (proj1 (task_private_excludes_public sg state.(TskState) node.(taskID)
    (proj1 (proj1 (proj2 Hvalid))) Hprivate)) as Hnone.
  destruct (kernel_call_task_source_current_at call state Hsource)
    as [Hcurrent [current_node [Hused Hgen]]].
  assert (Hdifferent : task_stack_key call.(os_sched_call_stack) <>
    task_stack_key publication.(stack_publication_lease)).
  { intro Hkey; pose proof (f_equal fst Hkey) as Hsame_slot.
    change (call.(os_sched_call_stack).(stackLeaseSlot) =
      publication.(stack_publication_lease).(stackLeaseSlot)) in Hsame_slot.
    rewrite <- Hslot in Hsame_slot; rewrite Hsame_slot, Hnone in Hused; discriminate. }
  unfold kernel_call_stack_available in Havailable |- *.
  rewrite (proj1 Hsource) in Havailable |- *.
  change (task_stack_park state.(TskState).(parkedTaskStacks)
    publication.(stack_publication_lease) (task_create_stack_publication_words publication)
    (task_stack_key call.(os_sched_call_stack)) = None).
  rewrite task_stack_park_lookup_other by exact Hdifferent; exact Havailable.
Qed.

(** Existing callers that need no Scheduler protocol can keep their old
    post. This direction forgets only pure observations, never local map
    ownership, a failed buffer, or one of the result alternatives. *)
Lemma task_tcb_init_continuation_sched_call_post_weaken : forall environment critical saved_local sg
  region args task_return lower upper initial_name invocation origin mask initial original result,
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result |--
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros; unfold task_tcb_init_continuation_sched_call_post; Intros released returned current.
  unfold task_tcb_init_continuation_call_post; Exists released.
  unfold task_tcb_init_continuation_call_return_post; Exists returned current; entailer!.
Qed.

(** A failed allocation returns immediately through TaskCreate's rollback
    branch. No Scheduler call consumes its stack availability, so the
    existing full no-free post already supplies every required fact.
    This preserves both the returned execution resources and failed buffer. *)
Lemma task_tcb_init_continuation_no_free_sched_call_post :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original,
  task_tcb_init_continuation_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 66 |--
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 66.
Proof.
  intros; unfold task_tcb_init_continuation_call_post,
    task_tcb_init_continuation_call_return_post; Intros released returned current.
  unfold task_tcb_init_continuation_sched_call_post; Exists released returned current.
  entailer!; intros; discriminate.
Qed.

(** Consume a completed, registered C return with its actual resource
    endpoint. Only the real trace transports ready and source facts; the
    availability observation must be supplied by its last take or its
    uninterrupted source. No future return or flat IRQ trace is invented. *)
Lemma task_tcb_init_continuation_registered_sched_call_post :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result released returned current,
  kernel_sched_ready_clients critical ->
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_stack_same_call returned original ->
  kernel_resumption_task_source_trace environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    original.(os_sched_call_invocation) None original.(os_sched_call_origin)
    released false returned.(os_sched_call_origin) current ->
  (result = 0 -> kernel_call_stack_available original initial ->
    kernel_call_stack_available returned current) ->
  task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current **
    task_tcb_init_stack_buffer_result region args task_return lower upper result |--
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result released returned current
    Hmodules Hresult Hvalid Hprefix Hsame Htrace Havailable.
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)) as Hinterval.
  destruct (critical_region_interval_transports_resources critical sg original.(os_sched_call_invocation)
    released current Hinterval Hvalid) as [Hvalid_after [Hframe Hactive]].
  pose proof (task_tcb_init_stack_registered_source_preserved _ _ _ _ _ _ _ _
    Hvalid Hsame Htrace) as Hsource.
  assert (Hreturn : task_tcb_init_stack_return_preserved original released current).
  { split; [exact Hframe|]. split; [apply Hactive|exact Hsource]. }
  assert (Hready : result = 0 -> current.(SchedState).(readyList) <> []).
  { intro Hsuccess; subst result.
    eapply critical_region_interval_preserves_sched_ready; [exact Hmodules|exact Hinterval|exact Hvalid|].
    eapply task_tcb_init_stack_success_ready; exact Hresult. }
  unfold task_tcb_init_continuation_sched_call_post; Exists released returned current; entailer!.
Qed.

(** The no-interference instance consumes the SAME released state and
    buffer. Its availability premise concerns the TCB body's own updates;
    it cannot be manufactured from a weak public Restore post. *)
Lemma task_tcb_init_continuation_uninterrupted_sched_call_post :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result released,
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  (result = 0 -> kernel_call_stack_available original initial ->
    kernel_call_stack_available original released) ->
  task_tcb_init_continuation_save_input environment critical saved_local sg original mask released **
    task_tcb_init_stack_buffer_result region args task_return lower upper result |--
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original result released Hresult Hvalid Hsource Havailable.
  assert (Hready : result = 0 -> released.(SchedState).(readyList) <> []).
  { intros ->; eapply task_tcb_init_stack_success_ready; exact Hresult. }
  assert (Hreturn : task_tcb_init_stack_return_preserved original released released).
  { split; [reflexivity|]. split; [auto|apply task_tcb_init_stack_source_preserved_refl]. }
  unfold task_tcb_init_continuation_sched_call_post; Exists released original released.
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.

(** A concrete success source: the C publication updates the real child
    slot and parks its initial buffer; an uninterrupted completed Restore
    owns this very published world. The two publication properties above
    therefore reach the full TCB post used by the caller below. *)
Lemma task_tcb_init_continuation_publication_sched_call_post :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original acquired current slot image lease,
  let publication := task_tcb_init_stack_publication region args task_return lower upper initial_name
    invocation origin acquired slot image lease in
  let released := task_create_stack_publication_state sg publication current in
  task_tcb_init_call_result sg (task_tcb_init_stack_call_args args initial_name) invocation origin
    initial 0 (task_tcb_init_published_state sg (task_tcb_init_stack_call_args args initial_name)
      invocation acquired current slot image) ->
  UCOS2_state_inv sg current -> task_create_stack_publication_input sg publication current ->
  kernel_call_task_source original initial ->
  task_tcb_init_stack_source_preserved original initial current ->
  (kernel_call_stack_available original initial -> kernel_call_stack_available original current) ->
  task_tcb_init_continuation_save_input environment critical saved_local sg original mask released |--
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 0.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original acquired current slot image lease publication released
    Hresult Hvalid Hinput Hsource Hprefix Havailable.
  assert (Hsource_current : kernel_call_task_source original current) by (apply Hprefix; exact Hsource).
  assert (Hstep : kernel_client_step (task_create_stack_publication_client publication) sg current released).
  { split; [exact Hinput|reflexivity]. }
  pose proof (kernel_client_certificate_preserves_selected_resources _
    (task_create_stack_publication_certificate publication) sg current released Hvalid Hstep) as [Hreleased _].
  assert (Hpublished : task_tcb_init_stack_call_result critical sg region args task_return lower upper
    initial_name invocation origin initial 0 released).
  { unfold released, publication; econstructor; [exact Hresult|exact Hinput]. }
  assert (Hsource_released : task_tcb_init_stack_source_preserved original initial released).
  { intro Hinitial; apply task_create_stack_publication_preserves_call_source;
      [exact Hvalid|exact Hinput|apply Hprefix; exact Hinitial]. }
  assert (Havailable_released : kernel_call_stack_available original initial ->
    kernel_call_stack_available original released).
  { intro Hinitial; apply task_create_stack_publication_preserves_call_available;
      [exact Hvalid|exact Hinput|exact Hsource_current|apply Havailable; exact Hinitial]. }
  eapply derivable1_trans; [|apply (task_tcb_init_continuation_uninterrupted_sched_call_post
    environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin mask initial original 0 released Hpublished Hreleased Hsource_released
    (fun _ => Havailable_released))].
  unfold task_tcb_init_stack_buffer_result; destruct (Z.eq_dec 0 66); [discriminate|entailer!].
Qed.

(** The counter-only Closed-to-Closed IRQ family has an actual generic-map
    heap interpretation. Its completed return observations are composed
    across deposit, the registered interval, and take; no single flattened
    trace across the physical deposit/take is required here. Publication
    has its separate actual source instance above; this closed-start trace
    cannot manufacture a private publication cut or an arbitrary handler.

    [Hreturn] is the existing three-part observation produced by those
    same edges. The heap input is the restored owner's actual current
    world, not an independently chosen existential Scheduler post. *)
Lemma task_tcb_init_continuation_builtin_take_sched_call_post :
  forall environment critical saved_local Extra sg region args task_return lower upper initial_name
    invocation origin mask initial original result released returned sp fragments registry_return,
  let parked := armv7a_irq_live_parked_state released returned sp fragments in
  let current := os_int_exit_wrapper_restored_state registry_return returned.(os_sched_call_stack) in
  task_tcb_init_stack_call_result critical sg region args task_return lower upper initial_name
    invocation origin initial result released ->
  UCOS2_state_inv sg released ->
  task_tcb_init_stack_source_preserved original initial released ->
  task_tcb_init_stack_same_call returned original ->
  returned.(os_sched_call_origin) = RunningInvocation
    returned.(os_sched_call_stack).(stackLeaseSlot) returned.(os_sched_call_stack).(stackLeaseGeneration) ->
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
    KernelClientHeapClosed parked KernelClientHeapClosed registry_return ->
  task_tcb_init_stack_return_preserved original released current ->
  task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current **
    task_tcb_init_stack_buffer_result region args task_return lower upper result |--
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original result.
Proof.
  intros environment critical saved_local Extra sg region args task_return lower upper initial_name
    invocation origin mask initial original result released returned sp fragments registry_return
    parked current Hresult Hvalid Hprefix Hsame Horigin Htrace Hreturn.
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg KernelClientHeapClosed parked
    KernelClientHeapClosed registry_return Htrace eq_refl) as [Hclosed [Htasks Hsched]].
  assert (Hparked_sched : parked.(SchedState) = released.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      os_sched_save_current_sp, armv7a_irq_entry_counter_state.
    destruct released.(SchedState).(isRunning); reflexivity. }
  assert (Hready : result = 0 -> current.(SchedState).(readyList) <> []).
  { intro Hsuccess; subst result.
    change (registry_return.(SchedState).(readyList) <> []).
    rewrite Hsched, Hparked_sched; eapply task_tcb_init_stack_success_ready; exact Hresult. }
  assert (Havailable : kernel_call_stack_available returned current).
  { unfold current; apply kernel_call_stack_available_after_take; exact Horigin. }
  unfold task_tcb_init_continuation_sched_call_post; Exists released returned current; entailer!.
Qed.

(** Actual TaskCreate success consumer. The ordinary source and entry
    availability come from the approved runtime-entry contract; publication
    and the returned source establish all new Scheduler facts on exactly
    the world owned here. No readiness of the caller itself is required. *)
Lemma task_create_tcb_success_sched_call_pre :
  forall environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial,
  kernel_call_task_source original initial -> kernel_call_stack_available original initial ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_tcb_init_continuation_sched_call_post environment critical saved_local sg region args task_return
    lower upper initial_name invocation origin mask initial original 0 ** unmap_table_rep sg |--
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      kernel_call_task_source returned current /\ kernel_call_stack_available returned current) &&
    os_sched_continuation_call_pre environment saved_local kernel_program_inv sg returned mask current.
Proof.
  intros environment critical saved_local sg region args task_return lower upper initial_name
    invocation origin original mask initial Hinitial Havailable Haddress.
  unfold task_tcb_init_continuation_sched_call_post; Intros released returned current.
  assert (Hsame : task_tcb_init_stack_same_call returned original) by tauto.
  assert (Hprefix : task_tcb_init_stack_source_preserved original initial released) by tauto.
  assert (Htail : task_tcb_init_stack_source_preserved original released current)
    by (unfold task_tcb_init_stack_return_preserved in *; tauto).
  assert (Hsource : kernel_call_task_source returned current).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original current Hsame)).
    apply Htail, Hprefix; exact Hinitial. }
  assert (Hcurrent_available : kernel_call_stack_available returned current) by tauto.
  assert (Hready : current.(SchedState).(readyList) <> []) by tauto.
  unfold task_tcb_init_stack_buffer_result; destruct (Z.eq_dec 0 66); [discriminate|].
  assert (Hobserve : task_tcb_init_continuation_save_input environment critical saved_local
      sg returned mask current |--
    coq_prop (UCOS2_state_inv sg current) &&
    task_tcb_init_continuation_save_input environment critical saved_local sg returned mask current).
  { unfold task_tcb_init_continuation_save_input, task_create_continuation_input; entailer!. }
  sep_apply_l_atomic Hobserve; Intros.
  assert (Hvalid : UCOS2_state_inv sg current) by assumption.
  assert (Hcut : os_sched_call_cut sg returned current).
  { eapply os_sched_call_cut_from_source; try eassumption.
    rewrite (proj2 (proj2 Hsame)); exact Haddress. }
  sep_apply_l_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg returned mask current)).
  Exists returned current; unfold os_sched_continuation_call_pre, os_sched_continuation_pre; entailer!.
Qed.

(** Link boundary: the old source-preserved field does not itself transport
    key absence, and an arbitrary old Restore output does not establish
    ready preservation. The registered and builtin source instances above
    consume precisely these observations at a fixed actual endpoint.
    The canonical callee must retain them at that earliest source boundary;
    the stronger post is not claimed for a weak or uninstantiated registry. *)

