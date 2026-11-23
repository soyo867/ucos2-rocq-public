Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.ucos2_spatial Ucos2Verify.lib.task Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** StackInit has reserved a priority but has not allocated the child's TCB.
    IRQ entry changes the running caller's saved SP, nesting and parked map,
    not that reservation or name storage. Validity below is the result of the
    actual spatial save/store producer, not an extra public precondition. *)
Lemma task_create_stack_init_park_preserves_entry : forall sg args call state node sp fragments,
  state.(SchedState).(isRunning) = true ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  UCOS2_state_inv sg (armv7a_irq_live_parked_state state call sp fragments) ->
  task_create_stack_init_entry_preserved sg args call state
    (armv7a_irq_live_parked_state state call sp fragments).
Proof.
  intros sg args call state node sp fragments Hrunning Hnode Hvalid initial_name
    [Hbefore [Hpriority [Hactive [Hpending Hname]]]].
  split; [exact Hvalid|]. split; [exact Hpriority|]. split.
  - unfold armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state, os_sched_save_current_sp.
    rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode.
    change (task_invocation_active
      (glob_task_set_usedtask state.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node sp)) call.(os_sched_call_invocation) call.(os_sched_call_origin)).
    eapply task_set_saved_sp_preserves_invocation_active; eassumption.
  - split.
    + unfold task_tcb_init_pending, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
        armv7a_irq_entry_counter_state, os_sched_save_current_sp.
      rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; exact Hpending.
    + unfold task_tcb_init_name_valid, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
        armv7a_irq_entry_counter_state, os_sched_save_current_sp.
      rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode; exact Hname.
Qed.

Lemma task_create_stack_init_take_preserves_entry : forall sg args call state,
  UCOS2_state_inv sg (os_int_exit_wrapper_restored_state state call.(os_sched_call_stack)) ->
  task_create_stack_init_entry_preserved sg args call state
    (os_int_exit_wrapper_restored_state state call.(os_sched_call_stack)).
Proof.
  intros sg args call state Hvalid initial_name
    [Hbefore [Hpriority [Hactive [Hpending Hname]]]].
  exact (conj Hvalid (conj Hpriority (conj Hactive (conj Hpending Hname)))).
Qed.

(** An IRQ at a StackInit source cut: the child's unpublished buffer may
    be partly written and stays in [frame], whereas the current OS world
    and parked map move through the actual handler registry. The returned
    next-TCB entry property is derived from those same source states.
    The selected return and false-stop guard are explicit finite-branch
    conditions; this is neither termination nor arbitrary-handler coverage. *)
Lemma task_create_stack_init_irq_source : forall environment critical Extra
  extra_resources extra_step extra_effect sg args state node handler suspended publication mask
  before saved_heap (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  handler.(os_int_exit_interrupted_mask) = mask ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None extra_effect ->
  (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  armv7a_save_transition abi handler suspended before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap, kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg call.(os_sched_call_invocation)
          None call.(os_sched_call_origin) parked stopped returned_origin returned /\
        (stopped = false -> returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
         exists selected,
           armv7a_irq_restore_pointer_reads sg closed_heap (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           (forall final, armv7a_restore_transition abi handler selected closed_heap final ->
             let resumed := armv7a_continuation_resumed_call selected call in
             let current := os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack) in
             task_tcb_init_stack_same_call resumed call /\
             task_create_stack_init_entry_preserved sg args call state current /\
             task_tcb_init_stack_source_preserved call state current /\
             (task_tcb_init_stack_save_input environment critical sg resumed mask current ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) final))).
Proof.
  intros environment critical Extra extra_resources extra_step extra_effect sg args state node handler suspended
    publication mask before saved_heap frame call abi parked focus payload Horigin Hslice Hrunning Hnesting Hcurrent
    Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hmask Hextension Hextra Henter Hexit Hpublish
    Hsource Hpre Hsave.
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
     (UCOS2_inv sg state ** armv7a_task_stack_continuations abi state.(TskState) state.(TskState).(parkedTaskStacks) **
      (unmap_table_rep sg ** frame)))) end.
  { unfold task_tcb_init_stack_save_input, critical_region_outside, task_tcb_init_stack_capsules,
      task_stack_call_active_key, os_int_exit_frame_save_pre.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running, Horigin, Hmask.
    unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (armv7a_irq_source_save_parks_call _ _ _ abi sg state node handler suspended publication
    (unmap_table_rep sg ** frame) before saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone
    Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Howned Hsave)
    as [registry_heap [Hwrites [Hstores [Hcovered Hregistry]]]].
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hsaved_mask [Hpc [Hsavedsp Hfragments]]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hlease; rewrite Hcall in Hlease; symmetry; exact Hlease. }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask state.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments state.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state.
    rewrite Hrunning; unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hpointer : task_saved_pointer_at parked suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)).
  { unfold task_saved_pointer_at; rewrite Hlease, Htasks.
    exists (task_set_saved_sp node suspended.(armv7a_continuation_sp)); split.
    - cbn [glob_task_set_parked_stacks glob_task_set_usedtask inUsedTaskStates]; rewrite Z.eqb_refl; reflexivity.
    - change (node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) /\
        suspended.(armv7a_continuation_sp) = suspended.(armv7a_continuation_sp)); auto. }
  assert (Hlookup : parked.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload).
  { unfold payload; rewrite Htasks, Hlease; apply task_stack_park_fragments_lookup. }
  match type of Hregistry with ?P registry_heap => assert (Hworld : P |--
    coq_prop (UCOS2_state_inv sg parked) &&
    (kernel_client_call_stack_world abi sg focus payload parked **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler ** frame))) end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts, focus.
    rewrite kernel_program_inv_split_unmap, Hpc; unfold UCOS2_inv; entailer!. }
  destruct (Hworld registry_heap Hregistry) as [Hvalid Hworld_owned].
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (task_create_registered_call_stack_restore _ _ _ Extra abi extra_resources extra_step extra_effect
    critical.(critical_region_clients) sg call suspended Hbinding Hcall Hslice Hextension Hextra Henter Hexit Hpublish
    Hsource KernelClientHeapClosed registry_heap closed_heap parked handler frame Hvalid Hpointer Htrace I Hworld_owned)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_current.
  destruct (Hreturn Hreturned_current Haddress)
    as [selected [Hpointers [Hfocus [Hselected_lease [Hselected_sp [Hcpsr [Hregisters [Hcoverage_return Hresume]]]]]]]].
  exists selected; split; [exact Hpointers|].
  intros final Hrestore resumed current.
  destruct (Hresume final Hrestore) as [Hmemory Hfinal].
  assert (Hvalid_current : UCOS2_state_inv sg current).
  { match type of Hfinal with ?P final => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve final Hfinal)). }
  pose proof (proj1 (kernel_resumption_task_source_trace_erases _ _ critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None call.(os_sched_call_origin) parked stopped returned_origin returned Hsources))
    as Hinterval; rewrite Hnormal in Hinterval.
  assert (Hpreserved : task_create_stack_init_entry_preserved sg args call state current).
  { intros initial_name Hinitial.
    apply (task_create_stack_init_take_preserves_entry sg args call returned Hvalid_current initial_name).
    eapply task_tcb_init_acquire_entry; [|exact Hinterval].
    exact (task_create_stack_init_park_preserves_entry sg args call state node _ _
      Hrunning Hnode Hvalid initial_name Hinitial). }
  assert (Hordinary : task_tcb_init_stack_source_preserved call state current).
  { intros [Hcall_origin [Hactive Hcall_current]].
    destruct (critical_region_interval_transports_resources critical sg call.(os_sched_call_invocation)
      parked returned Hinterval Hvalid) as [_ [_ Hactive_return]].
    split; [exact Hcall_origin|]. split.
    - change (task_invocation_active returned.(TskState) call.(os_sched_call_invocation) call.(os_sched_call_origin)).
      apply Hactive_return; rewrite Htasks.
      change (task_invocation_active (glob_task_set_usedtask state.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
        (task_set_saved_sp node suspended.(armv7a_continuation_sp))) call.(os_sched_call_invocation) call.(os_sched_call_origin)).
      eapply task_set_saved_sp_preserves_invocation_active; eassumption.
    - unfold task_execution_current; rewrite Horigin; exact Hreturned_current. }
  assert (Hsame : task_tcb_init_stack_same_call resumed call).
  { unfold task_tcb_init_stack_same_call, resumed, armv7a_continuation_resumed_call; cbn; auto. }
  split; [exact Hsame|]. split; [exact Hpreserved|]. split; [exact Hordinary|].
  match type of Hfinal with ?P final => match goal with |- ?Q final => assert (Hclose : P |-- Q) end end.
  { unfold task_tcb_init_stack_save_input, critical_region_outside, task_tcb_init_stack_capsules,
      task_stack_call_active_key, resumed, armv7a_continuation_resumed_call.
    cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running, Horigin, Hselected_lease.
    rewrite Hmask in Hsaved_mask; rewrite Hsaved_mask.
    unfold UCOS2_inv; entailer!. }
  exact (Hclose final Hfinal).
Qed.

(** Actual sixteen-store initializer followed by its final returning IRQ cut.
    The source result is immediately consumed by the unchanged TCBInit entry
    interface. This finite suffix does not cover IRQs between the stores. *)
Lemma task_create_stack_init_stores_irq_tcb_pre : forall environment critical Extra
  extra_resources extra_step extra_effect sg args state node handler suspended publication mask
  region task_return lower old_frame upper initial_name before (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let parked := armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
  let focus := armv7a_call_focus call suspended.(armv7a_continuation_pc)
    suspended.(armv7a_continuation_lr) in
  let payload := (suspended.(armv7a_continuation_stack).(stackLeaseRegion),
    suspended.(armv7a_continuation_fragments)) in
  call.(os_sched_call_origin) = RunningInvocation call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  armv7a_task_frame_slice suspended ->
  state.(SchedState).(isRunning) = true -> state.(IntrState).(intNesting) = 0 ->
  state.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    suspended.(armv7a_continuation_fragments) ->
  task_publication_happened state.(TskState) publication call.(os_sched_call_stack).(stackLeaseSlot)
    call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    suspended.(armv7a_continuation_sp) ->
  handler.(os_int_exit_interrupted_mask) = mask ->
  @kernel_client_call_stack_extension_valid _ _ _ Extra abi
    extra_resources focus payload extra_step extra_effect ->
  (forall cut initial next returned, extra_effect sg cut initial next returned ->
    UCOS2_state_inv sg initial ->
    task_saved_pointer_at initial suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp) ->
    UCOS2_state_inv sg returned /\
    task_saved_pointer_at returned suspended.(armv7a_continuation_stack) suspended.(armv7a_continuation_sp)) ->
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source environment.(task_stack_call_external)
    environment.(task_stack_call_port) critical.(critical_region_clients) sg
    call.(os_sched_call_invocation) None extra_effect ->
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) state ->
  (task_create_stack_init_input environment critical sg region args task_return lower old_frame upper
     call mask state ** unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) before ->
  exists initialized,
    kernel_heap_execution (task_stack_init_no_vfp_writes args.(createStackTop)
      args.(createEntry) args.(createArgument) task_return) before initialized /\
    (forall saved_heap, armv7a_save_transition abi handler suspended initialized saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      initialized.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap, kernel_client_heap_trace extra_step sg KernelClientHeapClosed registry_heap
      KernelClientHeapClosed closed_heap ->
      exists returned stopped returned_origin,
        kernel_client_heap_state_trace extra_effect sg KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg call.(os_sched_call_invocation)
          None call.(os_sched_call_origin) parked stopped returned_origin returned /\
        (stopped = false -> returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
         exists selected,
           armv7a_irq_restore_pointer_reads sg closed_heap (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot))
             selected.(armv7a_continuation_sp) /\
           (forall final, armv7a_restore_transition abi handler selected closed_heap final ->
             let resumed := armv7a_continuation_resumed_call selected call in
             let current := os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack) in
             (task_create_stack_init_output environment critical sg region args task_return lower upper
                call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) final /\
             ((EX context checkpoint,
               coq_prop (task_tcb_init_stack_same_call context call /\
                 task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
                   call.(os_sched_call_invocation) call.(os_sched_call_origin) checkpoint /\
                 task_tcb_init_stack_source_preserved call state checkpoint) &&
               task_tcb_init_stack_call_pre environment critical sg region args task_return lower upper initial_name
                 call.(os_sched_call_invocation) call.(os_sched_call_origin) mask checkpoint context) ** unmap_table_rep sg **
              task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) final)))).
Proof.
  intros environment critical Extra extra_resources extra_step extra_effect sg args state node handler suspended
    publication mask region task_return lower old_frame upper initial_name before frame call abi parked focus payload
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp
    Hmask Hextension Hextra Henter Hexit Hpublish Hsource Hlayout Hentry Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame)) end.
  { unfold task_create_stack_init_input; entailer!. }
  destruct (task_stack_init_no_vfp_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower old_frame upper _ before (Horder before Hpre)) as [initialized [Hinit Hinitialized]].
  exists initialized; split; [exact Hinit|].
  intros saved_heap Hsave.
  set (buffer := task_stack_init_post TaskStackNoVFP region.(stackRegionBase) args.(createStackTop)
    args.(createEntry) args.(createArgument) task_return (task_create_options args)
    lower upper (task_stack_init_sp TaskStackNoVFP args.(createStackTop))).
  match type of Hinitialized with ?P initialized => assert (Hirq_input : P |--
    task_tcb_init_stack_save_input environment critical sg call mask state ** unmap_table_rep sg **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
    (buffer ** frame)) end.
  { unfold buffer; entailer!. }
  destruct (task_create_stack_init_irq_source environment critical Extra extra_resources extra_step extra_effect
    sg args state node handler suspended publication mask initialized saved_heap (buffer ** frame)
    Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp
    Hmask Hextension Hextra Henter Hexit Hpublish Hsource (Hirq_input initialized Hinitialized) Hsave)
    as [registry_heap [Hwrites [Hstores Htrace_return]]].
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (Htrace_return closed_heap Htrace)
    as [returned [stopped [returned_origin [Hstates [Hsources Hreturn]]]]].
  exists returned, stopped, returned_origin; split; [exact Hstates|]. split; [exact Hsources|].
  intros Hnormal Hreturned_current.
  destruct (Hreturn Hnormal Hreturned_current) as [selected [Hpointers Hresume]].
  exists selected; split; [exact Hpointers|].
  intros final Hrestore resumed current.
  destruct (Hresume final Hrestore) as [Hsame [Hpreserved [Hordinary Hfinal]]].
  assert (Houtput : (task_create_stack_init_output environment critical sg region args task_return lower upper
    call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) ** unmap_table_rep sg **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) final).
  { match type of Hfinal with ?P final => match goal with |- ?Q final => assert (Hpack : P |-- Q) end end.
    { unfold task_create_stack_init_output; Exists resumed current; unfold buffer; entailer!. }
    exact (Hpack final Hfinal). }
  split; [exact Houtput|].
  match type of Houtput with ?P final => match goal with |- ?Q final => assert (Hconsume : P |-- Q) end end.
  { sep_apply_l_atomic (task_create_stack_init_output_tcb_pre environment critical sg region args task_return
      lower upper initial_name call mask state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) Hlayout Hentry).
    Intros context checkpoint; Exists context checkpoint; entailer!; tauto. }
  exact (Hconsume final Houtput).
Qed.
