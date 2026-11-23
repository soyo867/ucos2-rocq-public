Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_call_history_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_return_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_interleaving_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_init_repeated_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_calls_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** An ordinary unmasked source cut has no outstanding C Save/inside
    pair. The real IRQ Save consumes its current execution resources;
    the exact IRQ descriptor is retained only at that parked key. The
    source return transports all other local owners and the private
    caller frame, including a partly initialized child buffer.

    This is the built-in counter-only returning subfamily. It does not
    assign a preservation law to Extra clients, nested handlers, or
    switching paths. Save and Restore below are actual transitions. *)
Lemma task_create_continuation_irq_source : forall environment critical saved_local Extra
  sg state node handler suspended publication mask before saved_heap (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let abi := environment.(task_stack_call_continuations) in
  let local := task_tcb_init_irq_local saved_local suspended in
  let parked := armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
    suspended.(armv7a_continuation_fragments) in
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
  critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, critical.(critical_region_clients)
    (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
  (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
   unmap_table_rep sg **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
   frame) before ->
  armv7a_save_transition abi handler suspended before saved_heap ->
  exists registry_heap,
    kernel_heap_writes (armv7a_continuation_save_writes suspended)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg state
      call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp)) saved_heap registry_heap /\
    (forall closed_heap,
      @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
        KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
      exists returned,
        @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
          KernelClientHeapClosed parked KernelClientHeapClosed returned /\
        kernel_resumption_task_source_trace environment.(task_stack_call_external)
          environment.(task_stack_call_port) critical.(critical_region_clients) sg
          call.(os_sched_call_invocation) None call.(os_sched_call_origin)
          parked false call.(os_sched_call_origin) returned /\
        armv7a_irq_restore_pointer_reads sg closed_heap
          (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
        (forall final, armv7a_restore_transition abi handler suspended closed_heap final ->
          let resumed := armv7a_continuation_resumed_call suspended call in
          let current := os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack) in
          task_tcb_init_stack_same_call resumed call /\
          task_tcb_init_call_preserved sg call.(os_sched_call_invocation) state current /\
          task_tcb_init_stack_return_preserved call state current /\
          (task_tcb_init_continuation_save_input environment critical saved_local sg resumed mask current **
           unmap_table_rep sg **
           task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
           frame) final)).
Proof.
  intros environment critical saved_local Extra sg state node handler suspended publication mask before saved_heap
    frame call abi local parked Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hmask Henter Hexit Hpublish Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler suspended before saved_heap Hsave)
    as [Hentry [Hcall [Hbinding [Hsaved_mask [Hpc [Hsavedsp Hfragments]]]]]].
  assert (Hlease : suspended.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hbound; rewrite Hcall in Hbound; symmetry; exact Hbound. }
  assert (Habsent : state.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  match type of Hpre with ?P before => assert (Hopen : P |--
    coq_prop (task_stack_live_coverage state.(TskState) (Some (task_stack_key call.(os_sched_call_stack)))) &&
    (os_int_exit_frame_save_pre environment.(task_stack_call_external) environment.(task_stack_call_platform) handler **
     (UCOS2_inv sg state **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** local suspended ** (unmap_table_rep sg ** frame)))) end.
  { unfold task_tcb_init_continuation_save_input, task_create_continuation_input.
    fold abi; Intros.
    sep_apply_l_atomic (proj1 (task_tcb_init_irq_map_absent _ _ _ abi state.(TskState)
      state.(TskState).(parkedTaskStacks) saved_local suspended Habsent)).
    unfold local, os_int_exit_frame_save_pre; rewrite task_tcb_init_irq_local_saved_eq, Hmask.
    unfold critical_region_outside.
    rewrite critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
    unfold task_stack_call_active_key in *; rewrite Horigin in *.
    unfold UCOS2_inv; entailer!. }
  destruct (Hopen before Hpre) as [Hcoverage Howned].
  destruct (kernel_irq_save_continuation_resources _ _ _ abi sg state node handler suspended publication
    local (unmap_table_rep sg ** frame) before saved_heap Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen
    Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage Howned Hsave)
    as [registry_heap [Hsave_call [Hsave_pc [Hsave_mask [Hwrites [Hstores [Hcovered Hparked]]]]]]].
  fold parked in Hcovered, Hparked.
  assert (Hparked_valid : UCOS2_state_inv sg parked).
  { match type of Hparked with ?P registry_heap => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg parked) && TT) end.
    { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
    exact (proj1 (Hobserve registry_heap Hparked)). }
  assert (Htasks : parked.(TskState) = glob_task_set_parked_stacks
    (glob_task_set_usedtask state.(TskState) call.(os_sched_call_stack).(stackLeaseSlot)
      (task_set_saved_sp node suspended.(armv7a_continuation_sp)))
    (task_stack_park_fragments state.(TskState).(parkedTaskStacks) call.(os_sched_call_stack)
      suspended.(armv7a_continuation_fragments))).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  assert (Hparked_sched : parked.(SchedState) = state.(SchedState)).
  { unfold parked, armv7a_irq_live_parked_state, armv7a_irq_live_entry_state,
      armv7a_irq_entry_counter_state; rewrite Hrunning.
    unfold os_sched_save_current_sp; cbn [replace_IntrS TskState]; rewrite Hnode; reflexivity. }
  match type of Hparked with ?P registry_heap => assert (Hregistry : P |--
    kernel_client_continuation_world abi local sg parked **
    (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
     frame)) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  exists registry_heap; split; [exact Hwrites|]. split; [exact Hstores|].
  intros closed_heap Htrace.
  destruct (kernel_client_continuation_trace_resources _ _ _ Extra abi local critical.(critical_region_clients)
    sg call.(os_sched_call_invocation) None Henter Hexit Hpublish
    KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap _ Htrace parked
    call.(os_sched_call_origin) I (Hregistry registry_heap Hparked))
    as [returned [Hstates [Hsources [Hobserver Hworld]]]].
  destruct (kernel_client_builtin_closed_trace_task_fields Extra sg _ _ _ _ Hstates eq_refl)
    as [Hclosed [Hreturned_tasks Hreturned_sched]].
  assert (Hreturned_current : returned.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot)).
  { rewrite Hreturned_sched, Hparked_sched; exact Hcurrent. }
  assert (Hreturned_node : returned.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))).
  { rewrite Hreturned_tasks, Htasks; cbn [glob_task_set_parked_stacks inUsedTaskStates glob_task_set_usedtask].
    rewrite Z.eqb_refl; reflexivity. }
  assert (Hreturned_lookup : returned.(TskState).(parkedTaskStacks)
    (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments))).
  { rewrite Hreturned_tasks, Htasks, Hlease; apply task_stack_park_fragments_lookup. }
  match type of Hworld with ?P closed_heap => assert (Htake_input : P |--
    coq_prop (task_stack_live_coverage returned.(TskState) None) &&
    (UCOS2_inv sg returned **
     store_parked_continuations (kernel_saved_continuation_entry abi returned.(TskState)
       (task_tcb_init_irq_local saved_local suspended)) returned.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      unmap_table_rep sg ** frame))) end.
  { unfold kernel_client_continuation_resources, kernel_client_continuation_world, local;
      rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Htake_input closed_heap Hworld) as [Hreturned_coverage Htake_owned].
  assert (Htake_current : returned.(SchedState).(curTaskID) =
    Some suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Hreturned_current).
  assert (Htake_node : returned.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) =
    Some (task_set_saved_sp node suspended.(armv7a_continuation_sp))) by (rewrite Hlease; exact Hreturned_node).
  assert (Htake_gen : (task_set_saved_sp node suspended.(armv7a_continuation_sp)).(taskGeneration) =
    suspended.(armv7a_continuation_stack).(stackLeaseGeneration)) by (rewrite Hlease; exact Hgen).
  assert (Htake_address : tcb_field_address
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) by (rewrite Hlease; exact Haddress).
  destruct (task_tcb_init_irq_take_resources _ _ _ abi sg returned saved_local suspended call
    (task_set_saved_sp node suspended.(armv7a_continuation_sp)) _ closed_heap Hcall Htake_current Htake_node
    Htake_gen Hreturned_lookup Htake_address Hreturned_coverage Htake_owned)
    as [Hpointers [Hreads [Hfinal_coverage Htake_resources]]].
  exists returned; split; [exact Hstates|]. split; [exact Hsources|]. split.
  - rewrite Hlease in Hpointers; exact Hpointers.
  - intros final Hrestore resumed current.
    match type of Htake_resources with ?P closed_heap => assert (Hrestore_input : P |--
      interrupt_platform_running environment.(task_stack_call_platform) handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources environment.(task_stack_call_port) handler **
      task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
        suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
      (UCOS2_inv sg (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       task_tcb_init_continuation_capsules environment saved_local
         (os_int_exit_wrapper_restored_state returned suspended.(armv7a_continuation_stack)) **
       unmap_table_rep sg ** frame)) end.
    { unfold task_tcb_init_continuation_capsules; fold abi; entailer!. }
    destruct (armv7a_restore_call_resources _ _ _ abi handler suspended call _ closed_heap final
      Hcall Hreads (Hrestore_input closed_heap Htake_resources) Hrestore) as [Hmemory Hfinal].
    rewrite Hsaved_mask, Hmask, Hlease in Hfinal.
    fold resumed current in Hfinal.
    assert (Hcurrent_valid : UCOS2_state_inv sg current).
    { match type of Hfinal with ?P final => assert (Hobserve : P |-- coq_prop (UCOS2_state_inv sg current) && TT) end.
      { unfold UCOS2_inv; entailer!; intros ? ?; exact I. }
      exact (proj1 (Hobserve final Hfinal)). }
    assert (Hpreserved : task_tcb_init_stack_return_preserved call state current).
    { unfold current; eapply task_tcb_init_stack_irq_return_preserved; eassumption. }
    assert (Hcall_preserved : task_tcb_init_call_preserved sg call.(os_sched_call_invocation) state current).
    { unfold current; eapply task_tcb_init_irq_preserves_call; eassumption. }
    assert (Hsame : task_tcb_init_stack_same_call resumed call).
    { unfold task_tcb_init_stack_same_call, resumed, armv7a_continuation_resumed_call; cbn;
        rewrite Hlease; auto. }
    split; [exact Hsame|]. split; [exact Hcall_preserved|]. split; [exact Hpreserved|].
    match type of Hfinal with ?P final => match goal with |- ?Q final => assert (Hclose : P |-- Q) end end.
    { unfold task_tcb_init_continuation_save_input, task_create_continuation_input,
        task_stack_call_active_key, resumed, armv7a_continuation_resumed_call, critical_region_outside.
      cbn [os_sched_call_invocation os_sched_call_origin os_sched_call_stack].
      rewrite Hlease, Horigin, critical_region_outside_without_running_rep, <- UCOS2_raw_rep_split_running.
      rewrite Hlease in Hfinal_coverage.
      fold current in Hfinal_coverage.
      unfold task_tcb_init_continuation_capsules, UCOS2_inv; fold abi; entailer!. }
    exact (Hclose final Hfinal).
Qed.

(** A finite source continuation of the real sixteen typed stores. Each
    number chooses the next store chunk before one actual IRQ; firstn
    clips beyond the final store. The induction carries the current map,
    the written prefix, and the still-private unwritten child buffer.
    Its empty case supplies the EXISTING public init_output and consumes
    that output into the next real TCBInit precondition on the same heap.

    The per-cut handler facts describe observed first-level IRQs with an
    owned handler stack. The theorem neither promises that an IRQ occurs
    nor that an arbitrary handler returns. Extra and switching handlers
    remain separate source-proof obligations. *)
Fixpoint task_create_continuation_init_irq_execution (schedule : list nat)
  (environment : TaskStackCallEnvironment) (critical : CriticalRegionResources)
  (saved_local : Armv7aContinuation -> Assertion)
  (sg : StableGlobVars) (args : TaskCreateArgs) (region handler_region : TaskStackRegion)
  (handler_fragments : TaskStackFragments) (task_return : Z)
  (lower upper : list (option Z)) (initial_name : Z)
  (original : OsSchedCallContext) (mask : Z) (initial_state : UCOS2_Verify_State)
  (call : OsSchedCallContext) (state : UCOS2_Verify_State) (prefix suffix : list Z)
  (before : model) (frame : Assertion) {struct schedule} : Prop :=
  match schedule with
  | [] =>
      exists initialized,
        kernel_heap_execution (task_stack_push_writes
          (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) suffix) before initialized /\
        (task_create_continuation_init_output environment critical saved_local sg region args task_return lower upper
           original mask initial_state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) **
         unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) initialized /\
        ((EX context checkpoint,
          coq_prop (task_tcb_init_stack_same_call context original /\
            task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
              original.(os_sched_call_invocation) original.(os_sched_call_origin) checkpoint /\
            task_tcb_init_stack_source_preserved original initial_state checkpoint) &&
          task_tcb_init_continuation_call_pre environment critical saved_local sg region args task_return lower upper
            initial_name original.(os_sched_call_invocation) original.(os_sched_call_origin) mask checkpoint context) **
         unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) initialized
  | count :: remaining =>
      let chunk := firstn count suffix in
      let rest := skipn count suffix in
      let abi := environment.(task_stack_call_continuations) in
      exists cut,
        kernel_heap_execution (task_stack_push_writes
          (task_stack_init_aligned_top args.(createStackTop) - 4 * Zlength prefix) chunk) before cut /\
        (forall Extra node handler suspended publication saved_heap,
          let parked := armv7a_irq_live_parked_state state call suspended.(armv7a_continuation_sp)
            suspended.(armv7a_continuation_fragments) in
          handler.(os_int_exit_interrupted_call) = call ->
          handler.(os_int_exit_handler_stack) = handler_region ->
          handler.(os_int_exit_handler_fragments) = handler_fragments ->
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
          critical.(critical_region_clients) (kernel_full_profile_cut_client KernelFullIntEnter) ->
          (forall running, critical.(critical_region_clients)
            (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
          (forall publication, critical.(critical_region_clients) (task_create_stack_publication_client publication)) ->
          armv7a_save_transition abi handler suspended cut saved_heap ->
          exists registry_heap,
            kernel_heap_writes (armv7a_continuation_save_writes suspended)
              cut.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
            kernel_heap_execution (armv7a_irq_live_entry_writes sg state
              call.(os_sched_call_stack).(stackLeaseSlot) suspended.(armv7a_continuation_sp))
              saved_heap registry_heap /\
            (forall closed_heap,
              @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
                KernelClientHeapClosed registry_heap KernelClientHeapClosed closed_heap ->
              exists returned,
                @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
                  KernelClientHeapClosed parked KernelClientHeapClosed returned /\
                kernel_resumption_task_source_trace environment.(task_stack_call_external)
                  environment.(task_stack_call_port) critical.(critical_region_clients) sg
                  call.(os_sched_call_invocation) None call.(os_sched_call_origin)
                  parked false call.(os_sched_call_origin) returned /\
                armv7a_irq_restore_pointer_reads sg closed_heap
                  (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) suspended.(armv7a_continuation_sp) /\
                (forall final, armv7a_restore_transition abi handler suspended closed_heap final ->
                  task_create_continuation_init_irq_execution remaining environment critical saved_local sg args region
                    handler_region handler_fragments task_return lower upper initial_name original mask
                    initial_state (armv7a_continuation_resumed_call suspended call)
                    (os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack))
                    (prefix ++ chunk) rest final frame)))
  end.

Lemma task_create_continuation_init_irq_execution_source :
  forall schedule environment critical saved_local sg args region
    handler_region handler_fragments task_return lower upper initial_name original mask initial_state,
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    original.(os_sched_call_invocation) original.(os_sched_call_origin) initial_state ->
  forall call state prefix suffix before (frame : Assertion),
  task_tcb_init_stack_same_call call original ->
  task_create_stack_init_entry_preserved sg args original initial_state state ->
  task_tcb_init_stack_source_preserved original initial_state state ->
  prefix ++ suffix = task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return ->
  Forall (fun value => 0 <= value < 4294967296) suffix ->
  (task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
   task_tcb_init_continuation_save_input environment critical saved_local sg call mask state **
   unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  task_create_continuation_init_irq_execution schedule environment critical saved_local sg args region handler_region
    handler_fragments task_return lower upper initial_name original mask initial_state
    call state prefix suffix before frame.
Proof.
  induction schedule as [|count remaining IH]; intros environment critical saved_local sg args region handler_region
    handler_fragments task_return lower upper initial_name original mask initial_state Hlayout Hentry
    call state prefix suffix before frame Hsame Hpreserved Hordinary Hwords Hranges Hpre.
  - cbn [task_create_continuation_init_irq_execution].
    match type of Hpre with ?P before => assert (Horder : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix suffix **
      (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** unmap_table_rep sg **
       task_stack_fragments_rep handler_region handler_fragments ** frame)) by entailer! end.
    destruct (task_stack_init_suffix_store_execution region.(stackRegionBase) args.(createStackTop)
      args.(createEntry) args.(createArgument) task_return (task_create_options args)
      lower upper prefix suffix _ before Hwords Hranges (Horder before Hpre))
      as [initialized [Hrun Hinitialized]].
    exists initialized; split; [exact Hrun|].
    assert (Houtput : (task_create_continuation_init_output environment critical saved_local sg region args task_return
      lower upper original mask initial_state (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) **
      unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) initialized).
    { match type of Hinitialized with ?P initialized => match goal with |- ?Q initialized =>
        assert (Hpack : P |-- Q) end end.
      { unfold task_create_continuation_init_output; Exists call state; entailer!. }
      exact (Hpack initialized Hinitialized). }
    split; [exact Houtput|].
    match type of Houtput with ?P initialized => match goal with |- ?Q initialized =>
      assert (Hconsume : P |-- Q) end end.
    { sep_apply_l_atomic (task_create_continuation_init_output_tcb_pre environment critical saved_local sg
        region args task_return lower upper initial_name original mask initial_state
        (task_stack_init_sp TaskStackNoVFP args.(createStackTop)) Hlayout Hentry).
      Intros context checkpoint; Exists context checkpoint; entailer!; tauto. }
    exact (Hconsume initialized Houtput).
  - cbn [task_create_continuation_init_irq_execution].
    set (chunk := firstn count suffix).
    set (rest := skipn count suffix).
    assert (Hsplit : chunk ++ rest = suffix) by (unfold chunk, rest; apply firstn_skipn).
    assert (Hlength : Zlength prefix + Zlength chunk + Zlength rest = 16).
    { rewrite <- Z.add_assoc, <- Zlength_app, Hsplit, <- Zlength_app, Hwords; reflexivity. }
    assert (Hchunk : Forall (fun value => 0 <= value < 4294967296) chunk).
    { rewrite <- Hsplit, Forall_app in Hranges; tauto. }
    assert (Hrest : Forall (fun value => 0 <= value < 4294967296) rest).
    { rewrite <- Hsplit, Forall_app in Hranges; tauto. }
    match type of Hpre with ?P before => assert (Horder : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop) lower upper prefix (chunk ++ rest) **
      (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** unmap_table_rep sg **
       task_stack_fragments_rep handler_region handler_fragments ** frame)) end.
    { rewrite Hsplit; entailer!. }
    destruct (task_stack_init_partial_store_execution region.(stackRegionBase) args.(createStackTop)
      lower upper prefix chunk rest _ before Hlength Hchunk (Horder before Hpre))
      as [cut [Hstores Hcut]].
    exists cut; split; [exact Hstores|].
    intros Extra node handler suspended publication saved_heap
      Hhandler_call Hhandler_region Hhandler_fragments Horigin Hslice Hrunning
      Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hmask
      Henter Hexit Hpublish Hsave.
    set (buffer := task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
      lower upper (prefix ++ chunk) rest).
    match type of Hcut with ?P cut => assert (Hirq_input : P |--
      task_tcb_init_continuation_save_input environment critical saved_local sg
        handler.(os_int_exit_interrupted_call) mask state **
      unmap_table_rep sg **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
      (buffer ** frame)) end.
    { rewrite Hhandler_call, Hhandler_region, Hhandler_fragments; unfold buffer; entailer!. }
    pose proof (task_create_continuation_irq_source environment critical saved_local Extra
      sg state node handler suspended publication mask cut saved_heap (buffer ** frame)) as Hirq.
    cbv zeta in Hirq.
    rewrite Hhandler_call in Hirq.
    destruct (Hirq Horigin Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
      Hpublication Hsp Hmask Henter Hexit Hpublish
      ltac:(rewrite Hhandler_call in Hirq_input; exact (Hirq_input cut Hcut)) Hsave)
      as [registry_heap [Hwrites [Hentry_stores Hreturned]]].
    exists registry_heap; split; [exact Hwrites|]. split; [exact Hentry_stores|].
    intros closed_heap Htrace.
    destruct (Hreturned closed_heap Htrace) as [returned [Hstates [Hsources [Hpointers Hresume]]]].
    exists returned; split; [exact Hstates|]. split; [exact Hsources|]. split; [exact Hpointers|].
    intros final Hrestore.
    destruct (Hresume final Hrestore) as [Hresumed_same [Hstep_call [Hstep_return Hfinal]]].
    pose proof (proj2 (proj2 Hstep_return)) as Hstep_source.
    set (resumed := armv7a_continuation_resumed_call suspended call).
    set (current := os_int_exit_wrapper_restored_state returned call.(os_sched_call_stack)).
    assert (Hsame_next : task_tcb_init_stack_same_call resumed original).
    { unfold resumed; unfold task_tcb_init_stack_same_call in *; destruct Hsame as [Hi [Ho Hs]];
        destruct Hresumed_same as [Hri [Hro Hrs]]; split; [congruence|]; split; congruence. }
    assert (Hentry_next : task_create_stack_init_entry_preserved sg args original initial_state current).
    { intros name Hinitial.
      specialize (Hpreserved name Hinitial).
      destruct Hsame as [Hi [Ho Hs]].
      rewrite Hi in Hstep_call.
      eapply task_tcb_init_call_preserves_entry; [exact Hpreserved|exact Hstep_call]. }
    assert (Hsource_next : task_tcb_init_stack_source_preserved original initial_state current).
    { intros Hinitial.
      apply (proj1 (task_tcb_init_stack_same_call_source_iff call original current Hsame)).
      apply Hstep_source.
      apply (proj2 (task_tcb_init_stack_same_call_source_iff call original state Hsame)).
      exact (Hordinary Hinitial). }
    match type of Hfinal with ?P final => assert (Hnext : P |--
      task_stack_init_partial_frame region.(stackRegionBase) args.(createStackTop)
        lower upper (prefix ++ chunk) rest **
      task_tcb_init_continuation_save_input environment critical saved_local sg resumed mask current **
      unmap_table_rep sg ** task_stack_fragments_rep handler_region handler_fragments ** frame) end.
    { rewrite Hhandler_region, Hhandler_fragments; unfold buffer; entailer!. }
    apply (IH environment critical saved_local sg args region handler_region handler_fragments task_return lower upper
      initial_name original mask initial_state Hlayout Hentry resumed current (prefix ++ chunk) rest final frame
      Hsame_next Hentry_next Hsource_next).
    + rewrite <- app_assoc, Hsplit; exact Hwords.
    + exact Hrest.
    + exact (Hnext final Hfinal).
Qed.

(** The canonical initializer input itself establishes the induction's
    first partial buffer and current generic map. No IRQ post or future
    successful publication is assumed by this producer. *)
Lemma task_create_continuation_init_repeated_irq_tcb_pre :
  forall schedule environment critical saved_local sg args state call mask region handler_region handler_fragments
    task_return lower old_frame upper initial_name before (frame : Assertion),
  task_create_stack_layout TaskStackNoVFP region args lower upper ->
  task_tcb_init_entry sg (task_tcb_init_stack_call_args args initial_name)
    call.(os_sched_call_invocation) call.(os_sched_call_origin) state ->
  (task_create_continuation_init_input environment critical saved_local sg region args task_return lower old_frame upper
     call mask state ** unmap_table_rep sg **
   task_stack_fragments_rep handler_region handler_fragments ** frame) before ->
  exists prepared,
    kernel_heap_execution [] before prepared /\
    task_create_continuation_init_irq_execution schedule environment critical saved_local sg args region handler_region
      handler_fragments task_return lower upper initial_name call mask state call state []
      (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) prepared frame.
Proof.
  intros schedule environment critical saved_local sg args state call mask region handler_region handler_fragments
    task_return lower old_frame upper initial_name before frame Hlayout Hentry Hpre.
  match type of Hpre with ?P before => assert (Horder : P |--
    task_stack_init_pre TaskStackNoVFP region.(stackRegionBase) region.(stackRegionWords)
      args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper **
    (task_tcb_init_continuation_save_input environment critical saved_local sg call mask state ** unmap_table_rep sg **
     task_stack_fragments_rep handler_region handler_fragments ** frame)) end.
  { unfold task_create_continuation_init_input; entailer!. }
  destruct (task_stack_init_prefix_store_execution region.(stackRegionBase) region.(stackRegionWords)
    args.(createStackTop) args.(createEntry) args.(createArgument) task_return lower old_frame upper []
    (task_stack_init_core_push_words args.(createEntry) args.(createArgument) task_return) _ before eq_refl
    (Horder before Hpre)) as [prepared [Hrun [Hranges Hprepared]]].
  exists prepared; split; [exact Hrun|].
  eapply task_create_continuation_init_irq_execution_source.
  - exact Hlayout.
  - exact Hentry.
  - repeat split; reflexivity.
  - intros name Hinitial; exact Hinitial.
  - apply task_tcb_init_stack_source_preserved_refl.
  - reflexivity.
  - exact Hranges.
  - match type of Hprepared with ?P prepared => match goal with |- ?Q prepared =>
      assert (Hclose : P |-- Q) by entailer! end end.
    exact (Hclose prepared Hprepared).
Qed.
