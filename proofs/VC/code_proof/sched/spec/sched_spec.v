Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import SumLib.ZRange.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Export Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.kernel_execution.
Require Export Ucos2Verify.lib.interrupt.
Require Export Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.mutex.
Require Export Ucos2Verify.lib.task_context.
Require Export Ucos2Verify.VC.code.sched.spec.sched_new_spec.

Import ListNotations UCOS2_C_Rules.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OS_Sched, Source/os_core.c:1702--1733, V2.93.01.  These are the kernel's
    masked preparation steps, not a complete context-switch/return model.
    The current profile disables per-task profiling and TLS; their extra
    writes/calls must be added before using a profile that enables them.
    Save/Restore and OS_TASK_SW retain their separate platform contracts. *)
Definition os_sched_selection_enabled (entry : UCOS2_Verify_State) : bool :=
  (Z.eqb entry.(IntrState).(intNesting) 0 &&
   Z.eqb entry.(IntrState).(lockNesting) 0)%bool.

(** Neither OSRunning, ready-list nonemptiness nor a live current TCB is a
    source guard.  The comparison reads the physical current-priority byte. *)
Definition os_sched_requests_switch (entry : UCOS2_Verify_State) : bool :=
  if os_sched_selection_enabled entry then
    sched_switch_byte_guard
      (sched_selected_priority entry.(TskState) entry.(SchedState))
      (sched_priority_byte entry.(SchedState).(curSchedPrio))
  else false.

Definition os_sched_counter_stage (entry : UCOS2_Verify_State) : SchedAbstractState :=
  if os_sched_requests_switch entry
  then sched_increment_switch_counter entry.(SchedState) else entry.(SchedState).

(** Source-level physical endpoint, including empty ready bitmaps and raw
    NULL/reserved priority-table entries.  No no-op fallback hides these
    cases.  This owns the actual writes but does not assert that a raw
    selected pointer is a valid platform switch destination. *)
Definition os_sched_prefix_physical_rep (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) : Assertion :=
  if os_sched_selection_enabled entry then
    sched_cache_cells sg
      (sched_selected_priority entry.(TskState) entry.(SchedState))
      (sched_selected_pointer sg entry.(TskState) entry.(SchedState)) **
    sched_physical_without_high sg (os_sched_counter_stage entry)
  else sched_physical_rep sg entry.(SchedState).

Definition os_sched_prefix_rep (sg : StableGlobVars) (entry : UCOS2_Verify_State) : Assertion :=
  sg.(g_OSRdyGrp) # UChar |-> encode_ready_grp entry.(SchedState).(readyList) entry.(TskState) **
  sched_rows_rep sg entry.(TskState) entry.(SchedState).(readyList) [0;1;2;3;4;5;6;7] **
  os_sched_prefix_physical_rep sg entry.

(** A LOGICAL checkpoint used only through the source-correspondence theorem
    below.  That theorem requires nonempty ready when selection is enabled;
    it is not an extra C test.  Empty/raw cases retain the physical endpoint
    above instead of being silently mapped to a fictitious successful state. *)
Definition os_sched_ready_checkpoint (entry : UCOS2_Verify_State) : SchedAbstractState :=
  if os_sched_selection_enabled entry then
    let selected := sched_refresh_high entry.(TskState) entry.(SchedState) in
    if os_sched_requests_switch entry
    then sched_increment_switch_counter selected else selected
  else entry.(SchedState).

Lemma os_sched_selection_enabled_iff : forall entry,
  os_sched_selection_enabled entry = true <->
  entry.(IntrState).(intNesting) = 0 /\ entry.(IntrState).(lockNesting) = 0.
Proof. intros; unfold os_sched_selection_enabled; rewrite Bool.andb_true_iff, !Z.eqb_eq; reflexivity. Qed.

Lemma os_sched_requests_switch_iff : forall entry,
  os_sched_requests_switch entry = true <-> os_sched_selection_enabled entry = true /\
  sched_selected_priority entry.(TskState) entry.(SchedState) <>
    sched_priority_byte entry.(SchedState).(curSchedPrio).
Proof.
  intros; unfold os_sched_requests_switch; destruct (os_sched_selection_enabled entry).
  - rewrite sched_switch_byte_guard_iff; tauto.
  - split; [discriminate|intros [H _]; discriminate].
Qed.

(** The full-call relation below separates C preparation, the contracted
    port operation, and a possible later return of THIS invocation.  The
    port boundary is external: these definitions are not an ARM executor
    or an implementation of App_TaskSwHook. *)
Definition os_sched_prefix_state (entry : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_SchedS (os_sched_ready_checkpoint entry) entry.

(** The executing stack is not duplicated in the public parked-stack map.
    Fragments may leave holes lent to the compiler's live typed C locals.
    A reused pool address does not change this saved invocation's generation. *)
Record OsSchedCallContext : Type := {
  os_sched_call_invocation : nat;
  os_sched_call_origin : TaskInvocationOrigin;
  os_sched_call_stack : TaskStackLease;
  os_sched_call_fragments : TaskStackFragments;
}.

(** A view of the CURRENT execution, independent of a task's allocation
    lease. A handler executes on its exception-stack region; it must not
    invent a task slot/generation for that region. The source context keeps
    KernelInterrupt distinct from KernelCaller. This pure descriptor grants
    no bytes, CPU token, source transition or calling-convention guarantee. *)
Record OsExecutionView : Type := {
  os_execution_invocation : nat;
  os_execution_origin : TaskInvocationOrigin;
  os_execution_context : KernelExecutionContext;
  os_execution_stack : TaskStackRegion;
  os_execution_fragments : TaskStackFragments
}.

Definition os_sched_execution_view (call : OsSchedCallContext) : OsExecutionView :=
  {| os_execution_invocation := call.(os_sched_call_invocation);
     os_execution_origin := call.(os_sched_call_origin);
     os_execution_context :=
       KernelCaller call.(os_sched_call_invocation) call.(os_sched_call_origin);
     os_execution_stack := call.(os_sched_call_stack).(stackLeaseRegion);
     os_execution_fragments := call.(os_sched_call_fragments) |}.

Coercion os_sched_execution_view : OsSchedCallContext >-> OsExecutionView.

(** Actual TCB-SP source write.  The map test selects the logical owner of
    the already observed pointer, not an additional C guard.  The absent
    free-image totalization of task_save_free_sp is NEVER a memory-safety
    premise: os_sched_current_storage_binding separately requires an owner. *)
Definition os_sched_save_current_sp (entry : UCOS2_Verify_State)
  (slot : TaskID) (sp : Z) : UCOS2_Verify_State :=
  replace_TskS
    (match entry.(TskState).(inUsedTaskStates) slot with
     | Some node => glob_task_set_usedtask entry.(TskState) slot (task_set_saved_sp node sp)
     | None => task_save_free_sp entry.(TskState) slot sp
     end) entry.

Definition os_sched_current_storage_binding (sg : StableGlobVars)
  (context : OsSchedCallContext) (entry : UCOS2_Verify_State) : Prop :=
  let lease := context.(os_sched_call_stack) in
  context.(os_sched_call_origin) =
    RunningInvocation lease.(stackLeaseSlot) lease.(stackLeaseGeneration) /\
  entry.(SchedState).(curTaskID) = Some lease.(stackLeaseSlot) /\
  task_slot_in_range sg lease.(stackLeaseSlot) /\
  tcb_field_address (task_slot_addr sg lease.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg lease.(stackLeaseSlot) /\
  ((exists node, entry.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node /\
      node.(taskID) = lease.(stackLeaseSlot) /\
      node.(taskGeneration) = lease.(stackLeaseGeneration)) \/
   (entry.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = None /\
    exists image, entry.(TskState).(taskLifecycle).(taskFreeStorage) lease.(stackLeaseSlot) = Some image)).

(** The callback source action and architecture-frame relation are explicit
    parameters of the approved EXTERNAL contract.  A concrete callback/port
    linking proof must supply their source binding.  The frame relation is
    not allowed to stand for an arbitrary kernel poststate: it talks only
    about the executing register/stack frame.  The caller's other typed
    cells are protected by the same disjoint-frame contract as the C ABI. *)
Record OsSchedExternalResources : Type := {
  os_sched_arch_running : OsExecutionView -> Assertion;
  os_sched_arch_save_source : OsSchedCallContext -> Z -> TaskStackFragments -> Prop;
  os_sched_arch_restore_source : TaskStackLease -> Z -> TaskStackFragments -> Prop;
  os_sched_arch_resume_source : OsSchedCallContext -> OsSchedCallContext -> Prop;
  os_sched_hook_action : KernelClientAction;
  os_sched_hook_certificate : KernelClientCertificate os_sched_hook_action;
}.

Definition os_execution_view_resources (external : OsSchedExternalResources)
  (context : OsExecutionView) : Assertion :=
  task_stack_fragments_rep context.(os_execution_stack)
    context.(os_execution_fragments) ** external.(os_sched_arch_running) context.

(** Preserve the task-call interface and its literal lease projections.
    Its interpretation is definitionally the shared execution view, so
    old task proofs need no new resource premise or representation law. *)
Definition os_sched_context_resources (external : OsSchedExternalResources)
  (context : OsSchedCallContext) : Assertion :=
  task_stack_fragments_rep context.(os_sched_call_stack).(stackLeaseRegion)
    context.(os_sched_call_fragments) ** external.(os_sched_arch_running) context.

(** Only the source's high-pointer/high-byte reads after the hook select
    the destination.  The slot/generation/parked context below are platform
    safety obligations; they are not tests inserted into OS_Sched.  The
    architecture restore relation receives that TCB's actual saved SP and
    the exact fragments taken from its parked-stack entry. *)
Definition os_sched_destination_binding (external : OsSchedExternalResources)
  (context : OsSchedCallContext)
  (saved : TaskStackFragments) (hooked : UCOS2_Verify_State)
  (incoming : TaskStackLease) (resumed : TaskStackFragments) : Prop :=
  hooked.(SchedState).(highRdyTid) = Some incoming.(stackLeaseSlot) /\
  (exists node, hooked.(TskState).(inUsedTaskStates) incoming.(stackLeaseSlot) = Some node /\
     node.(taskGeneration) = incoming.(stackLeaseGeneration) /\
     hooked.(SchedState).(highRdyPrio) = Some node.(curPrio) /\
     external.(os_sched_arch_restore_source) incoming node.(tcbStkPtr) resumed) /\
  task_stack_live_binding hooked.(TskState) incoming /\
  (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
     context.(os_sched_call_stack) saved) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), resumed).

Definition os_sched_install_context (context : OsSchedCallContext)
  (saved : TaskStackFragments) (incoming : TaskStackLease)
  (hooked : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_SchedS (sched_install_selected hooked.(SchedState))
    (replace_TskS
      (glob_task_set_parked_stacks hooked.(TskState)
        (task_stack_take (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
          context.(os_sched_call_stack) saved) incoming)) hooked).

(** This relation is independent of a preservation certificate.  In order:
    save the original stack/register continuation, store outgoing SP, run
    the supported hook, reread high caches, then install/take that context.
    In the alias case park/take uses one key and one TCB owner, not two. *)
Definition os_sched_switch_source (external : OsSchedExternalResources)
  (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (context : OsSchedCallContext) (installed : UCOS2_Verify_State) : Prop :=
  os_sched_requests_switch entry = true /\
  exists sp saved hooked incoming resumed,
    external.(os_sched_arch_save_source) context sp saved /\
    kernel_client_step external.(os_sched_hook_action) sg
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) sp) hooked /\
    os_sched_destination_binding external context saved hooked incoming resumed /\
    installed = os_sched_install_context context saved incoming hooked.

Inductive OsSchedSwitchOutcome : Type :=
| OsSchedOriginalResumed (context : OsSchedCallContext) (state : UCOS2_Verify_State)
| OsSchedOriginalRetired (state : UCOS2_Verify_State).

(** Return is a later event of the original lifetime, not the destination
    installation event.  Retirement is also represented; it is not erased
    by endpoint-validity or live-invocation guards in the raw transformer. *)
Definition os_sched_switch_outcome (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (context : OsSchedCallContext)
  (outcome : OsSchedSwitchOutcome) : Prop :=
  exists installed,
    os_sched_switch_source external sg entry context installed /\
    match outcome with
    | OsSchedOriginalResumed returned final =>
        (exists stopped, kernel_client_trace critical.(critical_region_clients) sg
          context.(os_sched_call_invocation) installed stopped final /\
          orb (kernel_client_stops external.(os_sched_hook_action)
            context.(os_sched_call_invocation)) stopped = false) /\
        external.(os_sched_arch_resume_source) context returned /\
        returned.(os_sched_call_invocation) = context.(os_sched_call_invocation) /\
        returned.(os_sched_call_origin) = context.(os_sched_call_origin) /\
        returned.(os_sched_call_stack) = context.(os_sched_call_stack) /\
        task_invocation_active final.(TskState) context.(os_sched_call_invocation)
          context.(os_sched_call_origin) /\
        final.(SchedState).(curTaskID) = Some context.(os_sched_call_stack).(stackLeaseSlot) /\
        final.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None
    | OsSchedOriginalRetired final =>
        exists stopped, kernel_client_trace critical.(critical_region_clients) sg
          context.(os_sched_call_invocation) installed stopped final /\
          orb (kernel_client_stops external.(os_sched_hook_action)
            context.(os_sched_call_invocation)) stopped = true
    end.

Lemma os_sched_save_current_sp_scheduler_frame : forall entry slot sp,
  (os_sched_save_current_sp entry slot sp).(SchedState) = entry.(SchedState).
Proof. reflexivity. Qed.

Lemma os_sched_save_current_sp_live_value : forall entry slot sp node,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  (os_sched_save_current_sp entry slot sp).(TskState).(inUsedTaskStates) slot =
    Some (task_set_saved_sp node sp).
Proof.
  intros entry slot sp node Hnode; unfold os_sched_save_current_sp; rewrite Hnode.
  cbn [replace_TskS TskState glob_task_set_usedtask inUsedTaskStates].
  rewrite Z.eqb_refl; reflexivity.
Qed.

(** Explicit supported callback/frame conditions, stated as source atoms
    rather than a post-validity test.  A saved free-slot generation need not
    be live: only a matching live generation constrains its SP.  A callback
    may affect kernel and application resources, but must preserve the
    retained outgoing frame and select an installable destination if it
    returns to this port continuation. *)
Definition os_sched_saved_stack_binding (context : OsSchedCallContext)
  (saved : TaskStackFragments) (hooked : UCOS2_Verify_State) : Prop :=
  let lease := context.(os_sched_call_stack) in
  valid_task_stack_region lease.(stackLeaseRegion) /\
  task_stack_fragments_in_range lease.(stackLeaseRegion).(stackRegionWords) 0 saved /\
  (exists publication, task_publication_happened hooked.(TskState) publication
     lease.(stackLeaseSlot) lease.(stackLeaseGeneration)) /\
  (forall node, hooked.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
     node.(taskGeneration) = lease.(stackLeaseGeneration) -> task_stack_lease_matches_task lease node) /\
  hooked.(TskState).(parkedTaskStacks) (task_stack_key lease) = None.

Definition os_sched_switch_input (external : OsSchedExternalResources)
  (sg : StableGlobVars) (context : OsSchedCallContext)
  (entry : UCOS2_Verify_State) : Prop :=
  os_sched_current_storage_binding sg context entry /\
  entry.(TskState).(parkedTaskStacks) (task_stack_key context.(os_sched_call_stack)) = None /\
  (forall sp saved hooked,
    external.(os_sched_arch_save_source) context sp saved ->
    kernel_client_step external.(os_sched_hook_action) sg
      (os_sched_save_current_sp (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) sp) hooked ->
    os_sched_saved_stack_binding context saved hooked /\
    exists incoming resumed, os_sched_destination_binding external context saved hooked incoming resumed).

(** These are INTERNAL caller/platform safety obligations, not executable
    guards and not unconditional guarantees for arbitrary raw pointers.
    The critical source interval must preserve them until acquisition.
    In particular no premise demands that the outgoing slot is live. *)
Definition os_sched_acquire_safety (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (context : OsSchedCallContext) (before : UCOS2_Verify_State) : Prop :=
  forall entry, critical_region_interval critical sg context.(os_sched_call_invocation) before entry ->
    (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) /\
    (os_sched_requests_switch entry = true -> os_sched_switch_input external sg context entry).

Definition os_sched_entry_safety (external : OsSchedExternalResources)
  (sg : StableGlobVars) (context : OsSchedCallContext) (entry : UCOS2_Verify_State) : Prop :=
  (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) /\
  (os_sched_requests_switch entry = true -> os_sched_switch_input external sg context entry).

Definition os_sched_switch_requested (entry : UCOS2_Verify_State) : Prop :=
  os_sched_requests_switch entry = true.

Definition os_sched_global_addresses (sg : StableGlobVars)
  (ints locks high current high_tcb table counter unmap group rows : Z) : Prop :=
  ints = sg.(g_OSIntNesting) /\ locks = sg.(g_OSLockNesting) /\
  high = sg.(g_OSPrioHighRdy) /\ current = sg.(g_OSPrioCur) /\
  high_tcb = sg.(g_OSTCBHighRdy) /\ table = sg.(g_OSTCBPrioTbl) /\
  counter = sg.(g_OSCtxSwCtr) /\
  sched_new_global_addresses sg unmap group rows high.

Definition os_sched_pre (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext)
  (mask : Z) (before : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg before /\
    os_sched_acquire_safety external critical sg context before) &&
  (interrupt_platform_running platform context.(os_sched_call_invocation)
     context.(os_sched_call_origin) mask **
   critical_region_outside critical sg context.(os_sched_call_invocation) before **
   os_sched_context_resources external context ** unmap_table_rep sg).

Definition os_sched_c_return (external : OsSchedExternalResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (entry : UCOS2_Verify_State) (context returned : OsSchedCallContext)
  (final : UCOS2_Verify_State) : Prop :=
  if os_sched_requests_switch entry then
    os_sched_switch_outcome external critical sg entry context (OsSchedOriginalResumed returned final)
  else returned = context /\ final = os_sched_prefix_state entry.

Definition os_sched_post (external : OsSchedExternalResources)
  (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (context : OsSchedCallContext)
  (mask : Z) (before : UCOS2_Verify_State) : Assertion :=
  EX entry, EX final, EX returned,
    coq_prop (critical_region_interval critical sg context.(os_sched_call_invocation) before entry /\
      os_sched_c_return external critical sg entry context returned final) &&
    (interrupt_platform_running platform context.(os_sched_call_invocation)
       context.(os_sched_call_origin) mask **
     critical_region_outside critical sg context.(os_sched_call_invocation) final **
     os_sched_context_resources external returned ** unmap_table_rep sg).

Lemma os_sched_save_current_sp_free_value : forall entry slot sp image,
  entry.(TskState).(inUsedTaskStates) slot = None ->
  entry.(TskState).(taskLifecycle).(taskFreeStorage) slot = Some image ->
  (os_sched_save_current_sp entry slot sp).(TskState).(taskLifecycle).(taskFreeStorage) slot =
    Some (tcb_saved_sp_image image sp).
Proof.
  intros entry slot sp image Hnone Himage; unfold os_sched_save_current_sp; rewrite Hnone.
  apply task_free_saved_sp_storage_target; exact Himage.
Qed.

Lemma os_sched_install_context_current_cache : forall context saved incoming hooked,
  (os_sched_install_context context saved incoming hooked).(SchedState).(curTaskID) =
      hooked.(SchedState).(highRdyTid) /\
  (os_sched_install_context context saved incoming hooked).(SchedState).(curSchedPrio) =
      hooked.(SchedState).(highRdyPrio).
Proof. intros; split; reflexivity. Qed.

Lemma os_sched_install_context_frame : forall context saved incoming hooked,
  (os_sched_install_context context saved incoming hooked).(IntrState) = hooked.(IntrState) /\
  (os_sched_install_context context saved incoming hooked).(EventState) = hooked.(EventState) /\
  (os_sched_install_context context saved incoming hooked).(SchedState).(readyList) = hooked.(SchedState).(readyList) /\
  (os_sched_install_context context saved incoming hooked).(SchedState).(ctxSwCtr) = hooked.(SchedState).(ctxSwCtr).
Proof. intros; repeat split; reflexivity. Qed.

Lemma os_sched_save_live_sp_preserves_cross_module_consistency : forall sg entry slot node sp,
  entry.(TskState).(inUsedTaskStates) slot = Some node ->
  cross_module_consistency sg entry ->
  cross_module_consistency sg
    (replace_TskS (glob_task_set_usedtask entry.(TskState) slot (task_set_saved_sp node sp)) entry).
Proof.
  intros sg entry slot node sp Hnode
    [Htable [Hsnapshot [Hwait [Hprotocol [Hunique [Hflag Htimer]]]]]].
  split.
  - eapply task_mutex_priotbl_consistency_update_task; [exact Hnode|reflexivity|exact Htable].
  - split; [eapply mutex_owner_snapshot_update_task; eauto|].
    split.
    + eapply event_wait_object_update_task;
        [exact Hnode|reflexivity|reflexivity|reflexivity| |exact Hwait].
      intros kind Hphase; exact Hphase.
    + split; [exact Hprotocol|]; split; [exact Hunique|]; split; [|exact Htimer].
      eapply task_flag_waiter_consistency_update_task;
        [exact Hnode|reflexivity|reflexivity|reflexivity|reflexivity| | |exact Hflag]; auto.
Qed.

Lemma os_sched_save_live_sp_preserves_validity : forall sg entry node sp lease,
  UCOS2_state_inv sg entry ->
  entry.(TskState).(inUsedTaskStates) lease.(stackLeaseSlot) = Some node ->
  node.(taskID) = lease.(stackLeaseSlot) ->
  node.(taskGeneration) = lease.(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key lease) = None ->
  UCOS2_state_inv sg
    (replace_TskS (glob_task_set_usedtask entry.(TskState) lease.(stackLeaseSlot)
      (task_set_saved_sp node sp)) entry).
Proof.
  intros sg entry node sp lease
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus
      [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hparked Hpending]]]]]]]]]]]]]]]
    Hnode Hslot Hgeneration Hnone.
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_TskS (glob_task_set_usedtask entry.(TskState) lease.(stackLeaseSlot)
      (task_set_saved_sp node sp)) entry)).
  { eapply kernel_names_valid_frame; [exact Hreferences|reflexivity| | | | |].
    - eapply task_update_name_references; [exact Hnode|reflexivity].
    - intros; assumption.
    - intros; assumption.
    - intros; assumption.
    - intros; assumption. }
  split; [exact Hprofile|].
  split; [eapply task_set_saved_sp_preserves_in_range; eauto|].
  split; [eapply sched_update_task_preserves_in_range; eauto; reflexivity|].
  split.
  - eapply event_update_task_preserves_in_range;
      [exact Hnode|reflexivity|reflexivity|reflexivity| |exact Hevents].
    intros kind Hphase; exact Hphase.
  - split; [eapply os_sched_save_live_sp_preserves_cross_module_consistency; eauto|].
    split; [intro Hrunning; eapply task_update_preserves_idle_tail; eauto; reflexivity|].
    split.
    + apply task_reserved_bits_clear_update_task; [exact Hstatus|].
      exact (Hstatus lease.(stackLeaseSlot) node Hnode).
    + split; [exact Hflags|]; split; [exact Hmemory|]; split; [exact Htimer|].
      split; [exact Hstats|]; split; [exact Hcontrol|]; split; [exact Hnames|].
      split; [exact HreferencesAfter|].
      split.
      * exact (task_set_saved_sp_preserves_parked_stacks_consistency
        entry.(TskState) node sp lease entry.(TskState).(parkedTaskStacks)
        Hparked Hnode Hslot Hgeneration Hnone).
      * eapply pending_mutex_consistency_table_transport;
          [intros; reflexivity|intros; reflexivity|exact Hpending].
Qed.

Lemma os_sched_save_free_sp_preserves_validity : forall sg entry slot sp,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (replace_TskS (task_save_free_sp entry.(TskState) slot sp) entry).
Proof.
  intros sg entry slot sp
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus
      [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences Hparked]]]]]]]]]]]]]].
  split; [exact Hprofile|].
  split; [apply task_save_free_sp_preserves_in_range; exact Htasks|].
  split; [exact Hsched|]; split; [exact Hevents|]; split; [exact Hcross|].
  split; [exact Hidle|]; split; [exact Hstatus|]; split; [exact Hflags|].
  split; [exact Hmemory|]; split; [exact Htimer|]; split; [exact Hstats|].
  split; [exact Hcontrol|]; split; [exact Hnames|].
  split; [exact Hreferences|exact Hparked].
Qed.

Lemma os_sched_disabled_checkpoint_eq : forall entry,
  os_sched_selection_enabled entry = false ->
  os_sched_requests_switch entry = false /\ os_sched_ready_checkpoint entry = entry.(SchedState).
Proof. intros; unfold os_sched_requests_switch, os_sched_ready_checkpoint; rewrite H; split; reflexivity. Qed.

Lemma os_sched_no_switch_refreshes_high : forall entry,
  os_sched_selection_enabled entry = true -> os_sched_requests_switch entry = false ->
  os_sched_ready_checkpoint entry = sched_refresh_high entry.(TskState) entry.(SchedState).
Proof. intros; unfold os_sched_ready_checkpoint; rewrite H, H0; reflexivity. Qed.

Lemma os_sched_empty_selection : forall entry,
  os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) = [] ->
  os_sched_requests_switch entry =
    sched_switch_byte_guard 0 (sched_priority_byte entry.(SchedState).(curSchedPrio)).
Proof.
  intros; unfold os_sched_requests_switch; rewrite H.
  rewrite sched_empty_selected_priority by exact H0; reflexivity.
Qed.

Lemma os_sched_ready_checkpoint_frame : forall entry,
  (os_sched_ready_checkpoint entry).(readyList) = entry.(SchedState).(readyList) /\
  (os_sched_ready_checkpoint entry).(curTaskID) = entry.(SchedState).(curTaskID) /\
  (os_sched_ready_checkpoint entry).(curSchedPrio) = entry.(SchedState).(curSchedPrio) /\
  (os_sched_ready_checkpoint entry).(isRunning) = entry.(SchedState).(isRunning).
Proof.
  intro entry; unfold os_sched_ready_checkpoint; destruct (os_sched_selection_enabled entry);
    [destruct (os_sched_requests_switch entry)|]; repeat split; reflexivity.
Qed.

Lemma os_sched_ready_checkpoint_counter_eq : forall entry,
  (os_sched_ready_checkpoint entry).(ctxSwCtr) = (os_sched_counter_stage entry).(ctxSwCtr).
Proof.
  intro entry; unfold os_sched_ready_checkpoint, os_sched_counter_stage.
  destruct (os_sched_selection_enabled entry) eqn:Hen.
  - destruct (os_sched_requests_switch entry); reflexivity.
  - unfold os_sched_requests_switch; rewrite Hen; reflexivity.
Qed.

Lemma os_sched_same_task_stale_cache_requests_switch : forall sg entry head tail t,
  valid_stable_glob_vars sg -> sched_ready_in_range sg entry.(TskState) entry.(SchedState) ->
  entry.(SchedState).(readyList) = head :: tail -> entry.(TskState).(inUsedTaskStates) head = Some t ->
  entry.(SchedState).(curTaskID) = Some head ->
  sched_priority_byte entry.(SchedState).(curSchedPrio) <> t.(curPrio) ->
  os_sched_selection_enabled entry = true -> os_sched_requests_switch entry = true.
Proof.
  intros sg entry head tail t Hsg Hready Hlist Hlookup Hcurrent Hstale Hen.
  apply os_sched_requests_switch_iff; split; [exact Hen|].
  rewrite (sched_selected_priority_eq_head sg _ _ _ _ _ Hsg Hready Hlist Hlookup); congruence.
Qed.

Lemma os_sched_ready_checkpoint_preserves_in_range : forall sg entry,
  task_pool_partition sg entry.(TskState) ->
  sched_in_range sg entry.(TskState) entry.(SchedState) ->
  sched_in_range sg entry.(TskState) (os_sched_ready_checkpoint entry).
Proof.
  intros sg entry Hpool Hsched; unfold os_sched_ready_checkpoint.
  destruct (os_sched_selection_enabled entry); [|exact Hsched].
  pose proof (sched_refresh_high_preserves_in_range sg _ _ Hpool Hsched) as Hselected.
  destruct (os_sched_requests_switch entry); [apply sched_increment_switch_counter_preserves_in_range|];
    exact Hselected.
Qed.

Lemma os_sched_ready_checkpoint_high_consistency : forall sg entry,
  sched_ready_in_range sg entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true ->
  sched_high_ready_consistency entry.(TskState) (os_sched_ready_checkpoint entry).
Proof.
  intros sg entry Hready Hen; unfold os_sched_ready_checkpoint; rewrite Hen.
  destruct (os_sched_requests_switch entry);
    exact (sched_refresh_high_establishes_consistency sg _ _ Hready).
Qed.

(** A destination-state consequence of the already explicit platform cache
    installation contract.  It does NOT prove the assembly, its stack/TCB
    writes, or that OS_Sched returns in the newly selected task's context. *)
Lemma os_sched_installed_destination_boundary : forall sg entry,
  sched_ready_in_range sg entry.(TskState) entry.(SchedState) ->
  os_sched_selection_enabled entry = true -> entry.(SchedState).(isRunning) = true ->
  entry.(SchedState).(readyList) <> [] ->
  sched_task_call_boundary entry.(TskState)
    (sched_install_selected (os_sched_ready_checkpoint entry)).
Proof.
  intros sg entry Hready Hen Hrunning Hnonempty.
  apply sched_install_selected_task_boundary with (sg := sg).
  - unfold sched_ready_in_range in *.
    rewrite (proj1 (os_sched_ready_checkpoint_frame entry)); exact Hready.
  - apply os_sched_ready_checkpoint_high_consistency with (sg := sg); assumption.
  - rewrite (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame entry)))); exact Hrunning.
  - rewrite (proj1 (os_sched_ready_checkpoint_frame entry)); exact Hnonempty.
Qed.

Lemma os_sched_prefix_physical_eq_checkpoint : forall sg entry,
  valid_stable_glob_vars sg -> sched_ready_in_range sg entry.(TskState) entry.(SchedState) ->
  task_current_prio_registered entry.(TskState) ->
  (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) ->
  os_sched_prefix_physical_rep sg entry --||-- sched_physical_rep sg (os_sched_ready_checkpoint entry).
Proof.
  intros sg entry Hsg Hready Hregistered Hnonempty.
  unfold os_sched_prefix_physical_rep, os_sched_ready_checkpoint.
  destruct (os_sched_selection_enabled entry) eqn:Hen; [|split; entailer!].
  specialize (Hnonempty eq_refl).
  destruct entry.(SchedState).(readyList) as [|head tail] eqn:Hlist; [contradiction|].
  destruct (proj1 Hready head ltac:(rewrite Hlist; left; reflexivity)) as [t [Ht _]].
  unfold os_sched_counter_stage; destruct (os_sched_requests_switch entry).
  - exact (sched_selection_written_head_eq sg entry.(TskState)
      (sched_increment_switch_counter entry.(SchedState)) head tail t
      Hsg Hready Hregistered Hlist Ht).
  - exact (sched_selection_written_head_eq sg entry.(TskState) entry.(SchedState)
      head tail t Hsg Hready Hregistered Hlist Ht).
Qed.

Lemma os_sched_prefix_rep_eq_checkpoint : forall sg entry,
  valid_stable_glob_vars sg -> sched_ready_in_range sg entry.(TskState) entry.(SchedState) ->
  task_current_prio_registered entry.(TskState) ->
  (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) ->
  os_sched_prefix_rep sg entry --||--
    sched_raw_rep sg entry.(TskState) (os_sched_ready_checkpoint entry).
Proof.
  intros sg entry Hsg Hready Hregistered Hnonempty.
  destruct (os_sched_prefix_physical_eq_checkpoint sg entry Hsg Hready Hregistered Hnonempty) as [Hto Hfrom].
  unfold os_sched_prefix_rep, sched_raw_rep.
  rewrite (proj1 (os_sched_ready_checkpoint_frame entry)); split.
  - sep_apply_l_atomic Hto; entailer!.
  - sep_apply_l_atomic Hfrom; entailer!.
Qed.

Lemma os_sched_ready_checkpoint_preserves_validity : forall sg entry,
  UCOS2_state_inv sg entry ->
  UCOS2_state_inv sg (replace_SchedS (os_sched_ready_checkpoint entry) entry).
Proof.
  intros sg entry Hvalid; apply UCOS2_replace_sched_preserves_validity; [exact Hvalid| |].
  - apply os_sched_ready_checkpoint_preserves_in_range.
    + exact (proj1 (proj1 (proj2 Hvalid))).
    + exact (proj1 (proj2 (proj2 Hvalid))).
  - exact (proj2 (proj2 (proj2 (os_sched_ready_checkpoint_frame entry)))).
Qed.

Lemma os_sched_prefix_merge_inv : forall sg entry,
  UCOS2_state_inv sg entry ->
  (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) ->
  task_public_storage sg entry.(TskState) ** os_sched_prefix_rep sg entry **
  UCOS2_raw_rep_missing_task_storage_sched sg entry |--
    UCOS2_inv sg (replace_SchedS (os_sched_ready_checkpoint entry) entry).
Proof.
  intros sg entry Hvalid Hnonempty.
  pose proof (proj1 Hvalid) as Hprofile.
  assert (Hsg : valid_stable_glob_vars sg) by (unfold selected_kernel_profile in Hprofile; tauto).
  pose proof (proj1 (proj2 Hvalid)) as Htasks.
  assert (Hregistered : task_current_prio_registered entry.(TskState)).
  { unfold task_in_range in Htasks; tauto. }
  pose proof (proj1 (os_sched_prefix_rep_eq_checkpoint sg entry Hsg
    (proj1 (proj1 (proj2 (proj2 Hvalid)))) Hregistered Hnonempty)) as Hphysical.
  pose proof (UCOS2_inv_merge_updated_task_storage_sched sg entry
    (replace_SchedS (os_sched_ready_checkpoint entry) entry)
    (os_sched_ready_checkpoint_preserves_validity sg entry Hvalid) eq_refl) as Hmerge.
  sep_apply_l_atomic Hphysical.
  cbn [replace_SchedS TskState SchedState] in Hmerge.
  sep_apply_l_atomic Hmerge.
  entailer!.
Qed.

Definition os_sched_ints (entry : UCOS2_Verify_State) : Z := entry.(IntrState).(intNesting).
Definition os_sched_locks (entry : UCOS2_Verify_State) : Z := entry.(IntrState).(lockNesting).
Definition os_sched_group (entry : UCOS2_Verify_State) : Z :=
  encode_ready_grp entry.(SchedState).(readyList) entry.(TskState).
Definition os_sched_rows (entry : UCOS2_Verify_State) : list Z :=
  sched_row_values entry.(TskState) entry.(SchedState).(readyList).
Definition os_sched_old_high (entry : UCOS2_Verify_State) : Z :=
  sched_priority_byte entry.(SchedState).(highRdyPrio).
Definition os_sched_current (entry : UCOS2_Verify_State) : Z :=
  sched_priority_byte entry.(SchedState).(curSchedPrio).
Definition os_sched_old_pointer (sg : StableGlobVars) (entry : UCOS2_Verify_State) : Z :=
  encode_task_link sg entry.(SchedState).(highRdyTid).
Definition os_sched_counter (entry : UCOS2_Verify_State) : Z := entry.(SchedState).(ctxSwCtr).
Definition os_sched_table (sg : StableGlobVars) (entry : UCOS2_Verify_State) : list Z :=
  map (fun p => prio_tbl_entry_to_addr sg (entry.(TskState).(prioTbl) p)) (Zrange 0 64).
Definition os_sched_selected (entry : UCOS2_Verify_State) : Z :=
  sched_selected_priority entry.(TskState) entry.(SchedState).
Definition os_sched_selected_tcb (sg : StableGlobVars) (entry : UCOS2_Verify_State) : Z :=
  sched_selected_pointer sg entry.(TskState) entry.(SchedState).

(** Structural complement of this C prefix's exact field footprint.  It
    retains every unrelated native module and every parked stack.  It is
    reassembled before the external switch; it is not a whole-Task frame
    carried across the TCB-SP write or the hook. *)
Definition os_sched_work_frame (sg : StableGlobVars) (entry : UCOS2_Verify_State) : Assertion :=
  task_public_storage_without_prio_tbl sg entry.(TskState) **
  store_parked_stacks entry.(TskState).(parkedTaskStacks) **
  UCOS2_selected_rep sg entry (fun m => match m with
    | TaskModule | SchedModule | InterruptModule => false | _ => true end) **
  sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg entry.(SchedState).(curTaskID) **
  sg.(g_OSRunning) # UChar |-> (if entry.(SchedState).(isRunning) then 1 else 0).

Definition os_sched_work_cells (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (high pointer counter : Z) : Assertion :=
  sg.(g_OSIntNesting) # UChar |-> os_sched_ints entry **
  sg.(g_OSLockNesting) # UChar |-> os_sched_locks entry **
  sched_new_rep sg (os_sched_group entry) (os_sched_rows entry) high **
  PtrArray.full sg.(g_OSTCBPrioTbl) 64 (os_sched_table sg entry) **
  sg.(g_OSPrioCur) # UChar |-> os_sched_current entry **
  sg.(g_OSTCBHighRdy) # Ptr |-> pointer **
  sg.(g_OSCtxSwCtr) # UInt |-> counter ** os_sched_work_frame sg entry.

Lemma os_sched_work_cells_entry_equiv : forall sg entry,
  UCOS2_raw_rep sg entry ** unmap_table_rep sg --||--
  os_sched_work_cells sg entry (os_sched_old_high entry)
    (os_sched_old_pointer sg entry) (os_sched_counter entry).
Proof.
  intros; unfold os_sched_work_cells, os_sched_work_frame,
    os_sched_ints, os_sched_locks, os_sched_group, os_sched_rows,
    os_sched_old_high, os_sched_old_pointer, os_sched_current, os_sched_counter,
    os_sched_table, UCOS2_raw_rep, UCOS2_selected_rep,
    task_shared_rep, sched_raw_rep,
    sched_new_rep, sched_physical_rep, task_public_storage,
    task_public_storage_without_prio_tbl, store_prio_tbl.
  cbn [UCOS2_module_rep].
  rewrite sched_rows_array_equiv.
  split.
  - unfold interrupt_inv, store_int_state; entailer!.
  - pose proof (interrupt_inv_merge_counters sg entry.(IntrState)) as Hmerge.
    unfold store_int_state in Hmerge.
    sep_apply_l_atomic Hmerge; entailer!.
Qed.

Lemma os_sched_selected_eq_callee_result : forall entry,
  os_sched_selected entry = sched_new_priority (os_sched_group entry) (os_sched_rows entry).
Proof. intros; symmetry; apply sched_new_priority_eq_selected. Qed.

Lemma os_sched_selected_table_value : forall sg entry,
  Znth (os_sched_selected entry) (os_sched_table sg entry) 0 =
    os_sched_selected_tcb sg entry.
Proof.
  intros; unfold os_sched_table, os_sched_selected_tcb, sched_selected_pointer.
  apply prio_table_values_Znth; apply sched_selected_priority_in_range.
Qed.

Lemma os_sched_hook_preserves_validity : forall external sg before after,
  UCOS2_state_inv sg before ->
  kernel_client_step external.(os_sched_hook_action) sg before after ->
  UCOS2_state_inv sg after.
Proof.
  intros external sg before after Hvalid Hstep.
  exact (kernel_client_preserves_validity external.(os_sched_hook_action)
    external.(os_sched_hook_certificate) sg before after Hvalid Hstep).
Qed.

Lemma os_sched_park_saved_context_preserves_consistency : forall context saved hooked,
  parked_stacks_consistent hooked.(TskState) hooked.(TskState).(parkedTaskStacks) ->
  os_sched_saved_stack_binding context saved hooked ->
  parked_stacks_consistent hooked.(TskState)
    (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
      context.(os_sched_call_stack) saved).
Proof.
  intros context saved hooked Hconsistent [Hregion [Hgeometry [Hhistory [Hbinding Habsent]]]].
  destruct context as [invocation origin [region slot generation] fragments].
  cbn [os_sched_call_stack stackLeaseRegion stackLeaseSlot stackLeaseGeneration] in *.
  intros other other_generation other_region other_fragments Hentry.
  destruct (task_stack_key_eq_dec (other, other_generation) (slot, generation)) as [Heq|Hneq].
  - injection Heq as Hslot Hgeneration; subst other other_generation.
    change (task_stack_park_fragments hooked.(TskState).(parkedTaskStacks)
      {| stackLeaseRegion := region; stackLeaseSlot := slot; stackLeaseGeneration := generation |}
      saved (task_stack_key
      {| stackLeaseRegion := region; stackLeaseSlot := slot; stackLeaseGeneration := generation |}) =
      Some (other_region, other_fragments)) in Hentry.
    rewrite task_stack_park_fragments_lookup in Hentry.
    injection Hentry as Hregion_eq Hfragments_eq; subst other_region other_fragments.
    split; [exact Hregion|]. split; [exact Hgeometry|]. split; assumption.
  - rewrite task_stack_park_fragments_lookup_other in Hentry by exact Hneq.
    exact (Hconsistent other other_generation other_region other_fragments Hentry).
Qed.

Lemma os_sched_install_context_preserves_validity : forall sg context saved incoming hooked,
  UCOS2_state_inv sg hooked -> os_sched_saved_stack_binding context saved hooked ->
  (forall p, hooked.(SchedState).(highRdyPrio) = Some p -> task_priority_in_range sg p) ->
  UCOS2_state_inv sg (os_sched_install_context context saved incoming hooked).
Proof.
  intros sg context saved incoming hooked Hvalid Hsaved Hindex.
  assert (Hparked : parked_stacks_consistent hooked.(TskState) hooked.(TskState).(parkedTaskStacks)).
  { unfold UCOS2_state_inv, UCOS2_state_inv_with_ready in Hvalid; tauto. }
  pose proof (task_stack_take_preserves_consistency _ _ incoming
    (os_sched_park_saved_context_preserves_consistency context saved hooked Hparked Hsaved)) as Htake.
  pose proof (UCOS2_replace_parked_stacks_preserves_validity sg hooked _ Hvalid Htake) as Hstackstate.
  unfold os_sched_install_context; apply UCOS2_replace_sched_preserves_validity.
  - exact Hstackstate.
  - apply sched_install_selected_preserves_in_range.
    + exact (proj1 (proj2 (proj2 Hvalid))).
    + exact Hindex.
  - reflexivity.
Qed.

Lemma os_sched_switch_source_preserves_validity : forall external sg entry context installed,
  UCOS2_state_inv sg (os_sched_prefix_state entry) ->
  os_sched_switch_input external sg context entry ->
  os_sched_switch_source external sg entry context installed ->
  UCOS2_state_inv sg installed.
Proof.
  intros external sg entry context installed Hprefix
    [Hbinding [Hnone Hhook]] [Hrequested [sp [saved [hooked [incoming [resumed
      [Hsave [Hstep [Hdestination Hinstalled]]]]]]]]].
  subst installed.
  assert (Hsaved : UCOS2_state_inv sg
    (os_sched_save_current_sp (os_sched_prefix_state entry)
      context.(os_sched_call_stack).(stackLeaseSlot) sp)).
  { destruct Hbinding as [Horigin [Hcurrent [Hslot [Haddress [Hlive|Hfree]]]]].
    - destruct Hlive as [node [Hnode [Hid Hgeneration]]].
      unfold os_sched_save_current_sp; cbn [os_sched_prefix_state replace_SchedS TskState].
      rewrite Hnode.
      exact (os_sched_save_live_sp_preserves_validity sg (os_sched_prefix_state entry)
        node sp context.(os_sched_call_stack) Hprefix Hnode Hid Hgeneration Hnone).
    - destruct Hfree as [Hnode Himage].
      unfold os_sched_save_current_sp; cbn [os_sched_prefix_state replace_SchedS TskState].
      rewrite Hnode.
      exact (os_sched_save_free_sp_preserves_validity sg (os_sched_prefix_state entry)
        context.(os_sched_call_stack).(stackLeaseSlot) sp Hprefix). }
  assert (Hhooked : UCOS2_state_inv sg hooked).
  { eapply os_sched_hook_preserves_validity; eauto. }
  apply os_sched_install_context_preserves_validity.
  - exact Hhooked.
  - exact (proj1 (Hhook sp saved hooked Hsave Hstep)).
  - destruct Hdestination as [_ [[node [Hnode [_ [Hpriority _]]]] _]].
    intros p Hp; assert (p = node.(curPrio)) by congruence; subst p.
    pose proof (proj1 (proj2 Hhooked)) as Htasks.
    assert (Hpriorities : forall tid t,
      hooked.(TskState).(inUsedTaskStates) tid = Some t ->
      task_priority_in_range sg t.(curPrio))
      by (unfold task_in_range in Htasks; tauto).
    eapply Hpriorities; exact Hnode.
Qed.

Lemma os_sched_switch_outcome_preserves_validity : forall external critical sg entry context outcome,
  UCOS2_state_inv sg (os_sched_prefix_state entry) ->
  os_sched_switch_input external sg context entry ->
  os_sched_switch_outcome external critical sg entry context outcome ->
  match outcome with
  | OsSchedOriginalResumed _ final | OsSchedOriginalRetired final => UCOS2_state_inv sg final
  end.
Proof.
  intros external critical sg entry context outcome Hvalid Hinput [installed [Hsource Houtcome]].
  pose proof (os_sched_switch_source_preserves_validity external sg entry context installed
    Hvalid Hinput Hsource) as Hinstalled.
  destruct outcome as [returned final|final]; simpl in Houtcome |- *.
  - destruct Houtcome as [[stopped [Htrace Hnormal]] _].
    exact (proj1 (kernel_client_trace_transports_resources _ _ _ _ _ _
      critical.(critical_region_client_certificates) Htrace Hinstalled)).
  - destruct Houtcome as [stopped [Htrace Hretired]].
    exact (proj1 (kernel_client_trace_transports_resources _ _ _ _ _ _
      critical.(critical_region_client_certificates) Htrace Hinstalled)).
Qed.
