Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched Ucos2Verify.lib.interrupt Ucos2Verify.lib.helpers.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_continuation_call_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A property of the real ready list, carried in the existing region.
    It neither requires the outgoing caller to be ready nor identifies a
    permanently lowest-priority task. Publication establishes it directly.
    Each registered C module must prove its own preservation instance. *)
Definition kernel_sched_ready_inv sg state : Prop :=
  UCOS2_state_inv sg state /\ state.(SchedState).(readyList) <> [].

Definition kernel_sched_ready_clients (critical : CriticalRegionResources) : Prop :=
  forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources kernel_sched_ready_inv action.

(** This observation belongs to a completed running-call cut. It is NOT
    invariant throughout an interrupt: the interrupted key is genuinely
    parked and is removed by the real final take. Boot has no task key. *)
Definition kernel_call_stack_available call state : Prop :=
  match call.(os_sched_call_origin) with
  | BootInvocation => True
  | RunningInvocation slot generation =>
      state.(TskState).(parkedTaskStacks) (slot, generation) = None
  end.

(** Minimal requirements of the actual C guards. In the ISR/locked branch
    neither a nonempty ready list nor current-task storage is demanded.
    There is no universal future-acquire or future-hook condition. *)
Definition os_sched_call_cut sg call state : Prop :=
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) /\
  (os_sched_requests_switch state = true ->
    os_sched_current_storage_binding sg call state /\
    state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None).

Definition os_sched_continuation_call_pre environment saved_local resources
  sg call mask state : Assertion :=
  coq_prop (os_sched_call_cut sg call state) &&
  os_sched_continuation_pre environment saved_local resources sg call mask state.

(** A source-aware C Save-wrapper summary. Its source producers below use
    the actual acquired endpoint; this is not an added ARM/BSP Ensure.
    The shared module/return-source obligations must be instantiated before
    this summary may be used as a complete implementation contract. *)
Definition os_sched_continuation_call_save_output environment critical saved_local
  sg original mask saved before : Assertion :=
  EX returned acquired,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      interrupt_saved_value mask saved /\
      task_tcb_init_stack_source_preserved original before acquired /\
      os_sched_call_cut sg returned acquired) &&
    task_tcb_init_continuation_restore_input environment critical saved_local
      sg returned saved acquired acquired.

Lemma task_create_stack_publication_ready_nonempty : forall sg publication state,
  (task_create_stack_publication_state sg publication state).(SchedState).(readyList) <> [].
Proof.
  intros sg publication state Hempty.
  assert (Hin : In publication.(stack_publication_slot)
    (task_create_stack_publication_state sg publication state).(SchedState).(readyList)).
  { change (In publication.(stack_publication_slot)
      (insert_sorted_by
        (sched_task_key sg (task_commit state.(TskState)
          (task_create_stack_publication_args publication).(initPrio)
          publication.(stack_publication_invocation)
          (task_tcb_init_commit_node (task_create_stack_publication_args publication)
            publication.(stack_publication_acquired) publication.(stack_publication_slot)
            publication.(stack_publication_image))))
        publication.(stack_publication_slot) state.(SchedState).(readyList))).
    apply insert_sorted_by_in; left; reflexivity. }
  rewrite Hempty in Hin; contradiction.
Qed.

Lemma task_create_stack_publication_preserves_sched_ready : forall publication,
  kernel_client_preserves_resources kernel_sched_ready_inv
    (task_create_stack_publication_client publication).
Proof.
  intros publication sg before after [Hvalid Hready] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources _
    (task_create_stack_publication_certificate publication) sg before after Hvalid Hstep)
    as [Hafter Hresources].
  split; [split; [exact Hafter|]|exact Hresources].
  destruct Hstep as [Hinput ->]; apply task_create_stack_publication_ready_nonempty.
Qed.

(** Concrete registered counter cuts. These do not certify an arbitrary
    handler, a scheduling suffix, or an unregistered Extra action. *)
Lemma kernel_int_enter_preserves_sched_ready :
  kernel_client_preserves_resources kernel_sched_ready_inv
    (kernel_full_profile_cut_client KernelFullIntEnter).
Proof.
  intros sg before after [Hvalid Hready] [_ ->].
  split; [split; assumption|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|intros; assumption].
Qed.

Lemma kernel_int_exit_counter_preserves_sched_ready : forall running,
  kernel_client_preserves_resources kernel_sched_ready_inv
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running)).
Proof.
  intros running sg before after [Hvalid Hready] [_ ->].
  split; [split; assumption|].
  split; [intros; reflexivity|]. split; [intros; reflexivity|intros; assumption].
Qed.

Lemma critical_region_interval_preserves_sched_ready : forall critical sg invocation before after,
  kernel_sched_ready_clients critical ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg before -> before.(SchedState).(readyList) <> [] ->
  after.(SchedState).(readyList) <> [].
Proof.
  intros critical sg invocation before after Hmodules Htrace Hvalid Hready.
  pose proof (critical_region_interval_transports_invariant kernel_sched_ready_inv
    critical sg invocation before after Hmodules Htrace (conj Hvalid Hready)) as Htransport.
  exact (proj2 (proj1 Htransport)).
Qed.

(** Current storage is derived from the established invocation/current
    source, the live map and the actual C-field layout bridge. A raw CPU
    resource alone does not imply it. This has no caller-ready premise. *)
Lemma kernel_call_task_source_current_storage : forall sg call state,
  UCOS2_state_inv sg state -> kernel_call_task_source call state ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_current_storage_binding sg call state.
Proof.
  intros sg call state Hvalid Hsource Haddress.
  destruct (kernel_call_task_source_current_at call state Hsource)
    as [Hcurrent [node [Hnode Hgeneration]]].
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  destruct Htasks as [Hpool [Hclosure Hrest]].
  assert (Hrange : task_slot_in_range sg call.(os_sched_call_stack).(stackLeaseSlot)).
  { apply (proj2 (proj1 Hpool call.(os_sched_call_stack).(stackLeaseSlot))).
    left; exists node; exact Hnode. }
  destruct Hclosure as [Hnodup [Hhead [Hcount [Hmembership Hlinks]]]].
  assert (Hin : In call.(os_sched_call_stack).(stackLeaseSlot)
    state.(TskState).(taskLifecycle).(taskActiveOrder)).
  { apply (proj2 (Hmembership _)); exists node; exact Hnode. }
  assert (Hid : forall ids previous,
    task_active_links state.(TskState).(inUsedTaskStates) previous ids ->
    In call.(os_sched_call_stack).(stackLeaseSlot) ids ->
    node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot)).
  { intro ids; induction ids as [|head tail IH]; intros previous Hactive Hin'; [contradiction|].
    destruct Hactive as [first [Hfirst [Hfirst_id [_ [_ Htail]]]]].
    destruct Hin' as [Heq|Hin'].
    - rewrite Heq in Hfirst, Hfirst_id.
      assert (Hfirst_eq : first = node) by congruence.
      rewrite Hfirst_eq in Hfirst_id; exact Hfirst_id.
    - exact (IH (Some head) Htail Hin'). }
  unfold os_sched_current_storage_binding; cbv zeta.
  split; [exact (proj1 Hsource)|]. split; [exact Hcurrent|].
  split; [exact Hrange|]. split; [exact Haddress|].
  left; exists node; split; [exact Hnode|]. split; [exact (Hid _ None Hlinks Hin)|exact Hgeneration].
Qed.

Lemma os_sched_call_cut_from_source : forall sg call state,
  UCOS2_state_inv sg state -> kernel_call_task_source call state ->
  state.(SchedState).(readyList) <> [] -> kernel_call_stack_available call state ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  os_sched_call_cut sg call state.
Proof.
  intros sg call state Hvalid Hsource Hready Havailable Haddress.
  split; [intros; exact Hready|]. intros _; split.
  - eapply kernel_call_task_source_current_storage; eassumption.
  - unfold kernel_call_stack_available in Havailable; rewrite (proj1 Hsource) in Havailable.
    exact Havailable.
Qed.

Lemma os_sched_call_cut_disabled : forall sg call state,
  os_sched_selection_enabled state = false -> os_sched_call_cut sg call state.
Proof.
  intros sg call state Hdisabled; split; [intros Hen; congruence|].
  intro Hswitch; unfold os_sched_requests_switch in Hswitch.
  rewrite Hdisabled in Hswitch; discriminate.
Qed.

(** The actual last take establishes absence. It does not transport an
    old absence assertion through the parked interval. The same lemma
    applies to the exact endpoint returned by the existing IRQ producer. *)
Lemma kernel_call_stack_available_after_take : forall call state,
  call.(os_sched_call_origin) = RunningInvocation
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  kernel_call_stack_available call
    (os_int_exit_wrapper_restored_state state call.(os_sched_call_stack)).
Proof.
  intros call state Horigin; unfold kernel_call_stack_available; rewrite Horigin.
  change (task_stack_take state.(TskState).(parkedTaskStacks)
    call.(os_sched_call_stack) (task_stack_key call.(os_sched_call_stack)) = None).
  apply task_stack_take_lookup.
Qed.

(** Source-facing Save consumer: ready comes from the already established
    shared invariant and the registered C trace on the SAME acquired state.
    [Havailable] is the completed last-take/uninterrupted cut observation;
    it is deliberately separate from the global R/G invariant. *)
Lemma os_sched_registered_save_call_output :
  forall environment critical saved_local sg original returned mask saved before acquired,
  kernel_sched_ready_clients critical ->
  UCOS2_state_inv sg before -> before.(SchedState).(readyList) <> [] ->
  kernel_call_task_source original before ->
  kernel_call_save_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical sg original returned mask saved before acquired ->
  kernel_call_stack_available returned acquired ->
  tcb_field_address (task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg original.(os_sched_call_stack).(stackLeaseSlot) ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg returned saved acquired acquired |--
  os_sched_continuation_call_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros environment critical saved_local sg original returned mask saved before acquired
    Hmodules Hvalid Hready Hsource Hsave Havailable Haddress.
  pose proof (kernel_call_save_source_region_interval _ _ _ _ _ _ _ _ _ _ Hsave) as Hinterval.
  pose proof (critical_region_interval_preserves_sched_ready critical sg
    original.(os_sched_call_invocation) before acquired Hmodules Hinterval Hvalid Hready) as Hready_after.
  pose proof Hsave as [Htrace [Hi [Ho [Hs Hsaved]]]].
  assert (Hsame : task_tcb_init_stack_same_call returned original) by (repeat split; assumption).
  assert (Hpreserved : task_tcb_init_stack_source_preserved original before acquired).
  { eapply task_tcb_init_stack_registered_source_preserved; eassumption. }
  assert (Hcurrent : kernel_call_task_source returned acquired).
  { apply (proj2 (task_tcb_init_stack_same_call_source_iff returned original acquired Hsame)).
    apply Hpreserved; exact Hsource. }
  pose proof (critical_region_interval_transports_resources critical sg
    original.(os_sched_call_invocation) before acquired Hinterval Hvalid) as [Hvalid_after Hrest].
  assert (Hcut : os_sched_call_cut sg returned acquired).
  { eapply os_sched_call_cut_from_source; try eassumption.
    rewrite Hs; exact Haddress. }
  unfold os_sched_continuation_call_save_output; Exists returned acquired; entailer!.
Qed.

(** A disabled ACTUAL acquired cut needs none of the selection facts.
    The source/guard observation must come from the completed C wrapper;
    no assertion here says every disabled entry remains disabled. *)
Lemma os_sched_disabled_save_call_output : forall environment critical saved_local sg
  original returned mask saved before acquired,
  task_tcb_init_stack_same_call returned original -> interrupt_saved_value mask saved ->
  task_tcb_init_stack_source_preserved original before acquired ->
  os_sched_selection_enabled acquired = false ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg returned saved acquired acquired |--
  os_sched_continuation_call_save_output environment critical saved_local sg original mask saved before.
Proof.
  intros; assert (Hcut : os_sched_call_cut sg returned acquired)
    by (apply os_sched_call_cut_disabled; assumption).
  unfold os_sched_continuation_call_save_output; Exists returned acquired; entailer!.
Qed.

(** The uninterrupted instance keeps exactly the initial guarded cut;
    the existing Save producer supplies the real masked owner and saved
    word. Thus ISR/locked states with an empty ready list remain admitted. *)
Lemma os_sched_uninterrupted_save_call_output : forall environment critical saved_local sg
  call mask saved state,
  os_sched_call_cut sg call state -> interrupt_saved_value mask saved ->
  task_tcb_init_continuation_restore_input environment critical saved_local
    sg call saved state state |--
  os_sched_continuation_call_save_output environment critical saved_local sg call mask saved state.
Proof.
  intros; unfold os_sched_continuation_call_save_output; Exists call state.
  unfold task_tcb_init_stack_same_call, task_tcb_init_stack_source_preserved; entailer!.
Qed.

(** The actual annotation consumer. All four C branches and the same
    generic map are delegated to the already proved common prefix. *)
Lemma os_sched_call_save_output_prefix : forall environment critical saved_local sg
  original mask saved before heap (frame : Assertion),
  (os_sched_continuation_call_save_output environment critical saved_local sg
     original mask saved before ** unmap_table_rep sg ** frame) heap ->
  exists returned acquired after,
    task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
    task_tcb_init_stack_source_preserved original before acquired /\
    os_sched_call_cut sg returned acquired /\
    os_sched_modular_prefix_execution sg acquired heap after /\
    ((if os_sched_requests_switch acquired
      then os_sched_continuation_switch_pre environment critical saved_local kernel_program_inv
        sg returned saved acquired acquired
      else os_sched_continuation_body_post environment critical saved_local kernel_program_inv
        sg returned saved acquired acquired) ** frame) after.
Proof.
  intros environment critical saved_local sg original mask saved before heap frame Hpre.
  assert (Hopen : os_sched_continuation_call_save_output environment critical saved_local sg
      original mask saved before ** unmap_table_rep sg ** frame |--
    EX returned acquired,
      coq_prop (task_tcb_init_stack_same_call returned original /\ interrupt_saved_value mask saved /\
        task_tcb_init_stack_source_preserved original before acquired /\ os_sched_call_cut sg returned acquired) &&
      (task_tcb_init_continuation_restore_input environment critical saved_local
        sg returned saved acquired acquired ** unmap_table_rep sg ** frame)).
  { unfold os_sched_continuation_call_save_output; Intros returned acquired.
    Exists returned acquired; entailer!. }
  destruct (Hopen heap Hpre) as [returned [acquired [[Hsame [Hsaved [Hsource Hcut]]] Howned]]].
  destruct (os_sched_continuation_c_prefix environment critical saved_local sg returned saved acquired
    acquired heap frame (proj1 Hcut) (proj2 Hcut) Howned) as [after [Hrun Hpost]].
  exists returned, acquired, after.
  split; [exact Hsame|]. split; [exact Hsaved|]. split; [exact Hsource|].
  split; [exact Hcut|]. split; [exact Hrun|exact Hpost].
Qed.

(** The record [CriticalRegionResources] and every platform ABI are
    unchanged. The existing selected registry still needs the explicit
    module instances above (and instances for its other real C actions).
    No global instance for arbitrary wait/suspend/delete/ISR code is claimed.
    General disabled-entry guard transport and the actual take/source
    endpoints remain implementation-linking obligations, not new laws. *)
