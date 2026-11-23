Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_stack_call_source_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_selection_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_program_clients_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_private_type_source_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_handler_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_public_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_restore_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_stack_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_del_critical_stack_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Only the already checked counter-handler family is lifted here. Its
    local steps obey the EXISTING private-frame contract and its kernel
    bodies do not create/delete tasks or ECBs. The physical parked bytes
    stay in the one program world. The initially absent active key owns
    no dormant token in the old strong table, so retaining the other
    descriptors does not duplicate the temporary saved continuation. *)
Lemma mutex_del_restore_clients_event_eq : forall clients state,
  (mutex_del_restore_clients_state clients state).(EventState) = state.(EventState).
Proof.
  induction clients as [|kind rest IH]; intros state; [reflexivity|].
  cbn [mutex_del_restore_clients_state]; rewrite IH; destruct kind; reflexivity.
Qed.

Lemma mutex_del_restore_irq_tasks_event_eq : forall sg state handler saved node publication clients kind,
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  let call := handler.(os_int_exit_interrupted_call) in
  let final := mutex_del_restore_irq_state state handler saved clients kind in
  final.(TskState) = glob_task_set_usedtask state.(TskState)
    call.(os_sched_call_stack).(stackLeaseSlot)
    (task_set_saved_sp node saved.(armv7a_continuation_sp)) /\
  final.(EventState) = state.(EventState).
Proof.
  intros sg state handler saved node publication clients kind Hsafe call final.
  destruct Hsafe as [Hrunning [Hnesting [Hcurrent [Hnode [Hid [Hgen [Hnone Hrest]]]]]]].
  pose proof (proj1 (mutex_del_restore_clients_task_sched_eq clients
    (mutex_del_restore_irq_parked state handler saved))) as Htasks.
  pose proof (mutex_del_restore_clients_event_eq clients
    (mutex_del_restore_irq_parked state handler saved)) as Hevent.
  assert (Hexit_tasks : (mutex_del_restore_exit_state kind
      (mutex_del_restore_clients_state clients (mutex_del_restore_irq_parked state handler saved))).(TskState) =
    (mutex_del_restore_irq_parked state handler saved).(TskState)).
  { unfold mutex_del_restore_exit_state; destruct kind; exact Htasks. }
  assert (Hexit_event : (mutex_del_restore_exit_state kind
      (mutex_del_restore_clients_state clients (mutex_del_restore_irq_parked state handler saved))).(EventState) =
    (mutex_del_restore_irq_parked state handler saved).(EventState)).
  { unfold mutex_del_restore_exit_state; destruct kind; exact Hevent. }
  unfold final, mutex_del_restore_irq_state, os_int_exit_wrapper_restored_state.
  cbn [replace_TskS TskState EventState]; rewrite Hexit_tasks, Hexit_event.
  unfold mutex_del_restore_irq_parked, armv7a_irq_live_parked_state,
    armv7a_irq_live_entry_state, armv7a_irq_entry_counter_state, os_sched_save_current_sp.
  rewrite Hrunning; cbn [replace_IntrS TskState]; rewrite Hnode.
  cbn [replace_TskS TskState EventState glob_task_set_usedtask parkedTaskStacks].
  split; [|reflexivity].
  rewrite glob_task_set_parked_stacks_last_write.
  cbn [glob_task_set_parked_stacks parkedTaskStacks].
  assert (Hmap : task_stack_take
    (task_stack_park_fragments state.(TskState).(parkedTaskStacks)
      call.(os_sched_call_stack) saved.(armv7a_continuation_fragments))
    call.(os_sched_call_stack) = state.(TskState).(parkedTaskStacks)).
  { apply functional_extensionality; intros key.
    destruct (task_stack_key_eq_dec key (task_stack_key call.(os_sched_call_stack)));
      [subst key; rewrite task_stack_take_lookup; symmetry; exact Hnone|].
    rewrite task_stack_take_lookup_other, task_stack_park_fragments_lookup_other by assumption.
    reflexivity. }
  unfold call in Hmap; rewrite Hmap; reflexivity.
Qed.

(** This is a proved reindexing of existing ownership, not an IRQ
    preservation assumption. Only the live caller's saved-SP field has
    changed; a descriptor at an older generation remains unconstrained by
    that live SP exactly as in the existing strong representation. *)
Lemma mutex_del_restore_irq_merge_stack_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg active state handler saved
  node publication clients kind,
  mutex_del_restore_irq_input sg state handler saved node publication kind ->
  kernel_program_inv sg (mutex_del_restore_irq_state state handler saved clients kind) **
    mutex_del_stack_critical_frame abi sg active state |--
  kernel_stack_inv abi mutex_del_stack_resources sg active
    (mutex_del_restore_irq_state state handler saved clients kind).
Proof.
  intros external platform port abi sg active state handler saved node publication clients kind Hsafe.
  destruct (mutex_del_restore_irq_tasks_event_eq sg state handler saved node publication clients kind Hsafe)
    as [Htasks Hevent].
  destruct Hsafe as [Hrunning [Hnesting [Hcurrent [Hnode [Hid [Hgen [Hnone Hrest]]]]]]].
  set (final := mutex_del_restore_irq_state state handler saved clients kind) in *.
  unfold mutex_del_stack_critical_frame; Intros_p Hfacts.
  destruct Hfacts as [Hhistory [Htypes Hcoverage]].
  assert (Hcoverage' : task_stack_live_coverage final.(TskState) active).
  { rewrite Htasks; eapply task_stack_save_sp_preserves_coverage; eassumption. }
  assert (Hhistory' : mutex_program_selected_reachable sg final).
  { eapply mutex_program_source_history_reachable; [exact Hhistory|].
    eapply mutex_program_task_fields_source with
      (tid := handler.(os_int_exit_interrupted_call).(os_sched_call_stack).(stackLeaseSlot))
      (old := node) (new := task_set_saved_sp node saved.(armv7a_continuation_sp));
      [exact Hnode|reflexivity|reflexivity|rewrite Htasks; reflexivity|rewrite Hevent; reflexivity]. }
  assert (Hcapsules : armv7a_task_stack_continuations abi state.(TskState)
      state.(TskState).(parkedTaskStacks) |--
    armv7a_task_stack_continuations abi final.(TskState) final.(TskState).(parkedTaskStacks)).
  { rewrite Htasks; cbn [glob_task_set_usedtask parkedTaskStacks].
    eapply armv7a_task_stack_continuations_save_sp; eassumption. }
  sep_apply_l_atomic Hcapsules.
  unfold kernel_stack_inv, mutex_del_stack_resources; rewrite Hevent; entailer!.
Qed.

Section RepeatedIRQResources.
Context (external : OsSchedExternalResources) (platform : InterruptPlatformResources)
  (port : OsIntExitPlatformResources) (abi : Armv7aContinuationABI external platform port)
  (sg : StableGlobVars) (Local : Type).
Variable local_step : OsIntExitCallContext ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable normal_return : OsIntExitCallContext -> StableGlobVars ->
  RestoreHandlerCursor Local -> model -> RestoreHandlerCursor Local -> model -> Prop.
Variable handler_contract : forall handler,
  RestoreHandlerContract
    (fun (_ : RestoreHandlerCall) (_ : Local) => mutex_del_restore_handler_owner platform port handler)
    (local_step handler) (normal_return handler).
Variable handler_stack : TaskStackRegion.
Variable handler_fragments : TaskStackFragments.

Lemma mutex_del_restore_irq_execution_stack_resources : forall active mask pc lr
  call state before returned final after (frame : Assertion),
  mutex_del_restore_irq_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments mask pc lr call state before returned final after ->
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros active mask pc lr call state before returned final after frame Hrun Hpre.
  assert (Hopen : kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame) |--
    kernel_call_execution_owned external platform call mask **
      (kernel_program_inv sg state ** task_stack_fragments_rep handler_stack handler_fragments **
       (mutex_del_stack_critical_frame abi sg active state ** frame))).
  { unfold kernel_stack_call_closed; rewrite mutex_del_stack_world_split_critical_frame; entailer!. }
  destruct (mutex_del_restore_irq_execution_resources external platform port abi sg Local local_step normal_return
    handler_contract handler_stack handler_fragments mask pc lr call state before returned final after
    (mutex_del_stack_critical_frame abi sg active state ** frame) Hrun (Hopen before Hpre))
    as [Hi [Ho [Hs Howned]]].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|].
  destruct Hrun as [state handler saved node publication clients kind before saved_heap handler_heap handler_cursor
    returned_cursor returned_heap exit_cursor exit_heap exited_heap after Hsafe Hpc Hmask Hlr Hstack Hfragments
    Hsave Hentry Hreturn Hsame Hreturn_pc Htrace Hwrapper Hexit Hreads Hrestore].
  match type of Howned with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { eapply derivable1_trans with (y :=
      (kernel_program_inv sg (mutex_del_restore_irq_state state handler saved clients kind) **
       mutex_del_stack_critical_frame abi sg active state) **
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved handler.(os_int_exit_interrupted_call)) mask **
       task_stack_fragments_rep handler_stack handler_fragments ** frame)).
    - entailer!.
    - sep_apply_l_atomic
        (mutex_del_restore_irq_merge_stack_world external platform port abi sg active state handler saved
          node publication clients kind Hsafe).
      unfold kernel_stack_call_closed; entailer!. }
  exact (Hclose after Howned).
Qed.

(** No bound on IRQ count is assumed. Induction is on the supplied
    normally-returning physical execution, with a separate actual save,
    deposit, private/client trace, take and CPU restore in every round. *)
Lemma mutex_del_restore_irqs_execution_stack_resources : forall active mask pc lr
  call state before returned final after (frame : Assertion),
  mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments mask pc lr call state before returned final after ->
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active call mask state **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned mask final **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros active mask pc lr call state before returned final after frame Hrun; induction Hrun; intros Hpre.
  - split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|exact Hpre].
  - destruct (mutex_del_restore_irq_execution_stack_resources active _ _ _ _ _ _ _ _ _ _ H Hpre)
      as [Hi [Ho [Hs Hmiddle]]].
    destruct (IHHrun Hmiddle) as [Hi' [Ho' [Hs' Hpost]]].
    split; [congruence|]. split; [congruence|]. split; [congruence|exact Hpost].
Qed.

(** One real Restore prefix, the unbounded-finite counter IRQ family at
    its BX cut, and one real BX. [restore_entry] is a caller-supplied code
    address: the existing Restore ABI has no linker-address field, so this
    theorem does not establish that external binding. Boot/current=None
    remains admitted by the zero-round branch. No flat interval erases
    the SP/park/take history. *)
Lemma mutex_del_stack_repeated_restore_resources : forall critical arch
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  active call saved acquired checkpoint restore_entry cursor before written released
  returned final resumed final_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (mutex_del_stack_restore_input abi critical sg active call saved acquired checkpoint **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before ->
  armv7a_restore_prefix_transition restore cursor before written released ->
  mutex_del_restore_irqs_execution external platform port abi sg Local local_step normal_return
    handler_stack handler_fragments (armv7a_irq_fiq_mask saved) (restore_entry + 8)
    cursor.(kernel_restore_lr) call checkpoint released returned final resumed ->
  armv7a_restore_suffix_transition restore written resumed final_cursor after ->
  returned.(os_sched_call_invocation) = call.(os_sched_call_invocation) /\
  returned.(os_sched_call_origin) = call.(os_sched_call_origin) /\
  returned.(os_sched_call_stack) = call.(os_sched_call_stack) /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (kernel_stack_call_closed abi mutex_del_stack_resources sg active returned
    (armv7a_irq_fiq_mask saved) final **
    (task_stack_fragments_rep handler_stack handler_fragments ** frame)) after.
Proof.
  intros critical arch restore active call saved acquired checkpoint restore_entry cursor before written released
    returned final resumed final_cursor after frame Hr0 Hmask Hpre Hprefix Hirqs Hsuffix.
  assert (Hmasked : (kernel_stack_call_masked abi mutex_del_stack_resources critical sg active call
      saved acquired checkpoint ** (task_stack_fragments_rep handler_stack handler_fragments ** frame)) before).
  { match type of Hpre with ?P before => match goal with |- ?Q before => assert (Hopen : P |-- Q) end end.
    { sep_apply_l_atomic (mutex_del_stack_restore_input_masked external platform port abi critical sg active
        call saved acquired checkpoint); entailer!. }
    exact (Hopen before Hpre). }
  destruct (kernel_stack_call_restore_prefix _ _ _ _ _ abi restore mutex_del_stack_resources sg active
    call saved acquired checkpoint cursor before written released _ Hr0 Hmask Hmasked Hprefix)
    as [Hwritten [Hmemory Hreleased]].
  destruct (mutex_del_restore_irqs_execution_stack_resources active _ _ _ _ _ _ _ _ _ _ Hirqs Hreleased)
    as [Hi [Ho [Hs Hresumed]]].
  set (word := armv7a_cpsr_restore_direct cursor.(kernel_restore_current_cpsr) cursor.(kernel_restore_r0)).
  assert (Hword : written.(kernel_restore_msr_word) = Some word) by (rewrite Hwritten; reflexivity).
  assert (Hword_mask : armv7a_irq_fiq_mask word = armv7a_irq_fiq_mask saved).
  { unfold word; rewrite armv7a_cpsr_restore_mask_eq, Hr0; reflexivity. }
  rewrite <- Hword_mask in Hresumed.
  assert (Hsuffix_pre : (kernel_call_execution_owned external platform returned (armv7a_irq_fiq_mask word) **
    (kernel_stack_inv abi mutex_del_stack_resources sg active final **
      (task_stack_fragments_rep handler_stack handler_fragments ** frame))) resumed).
  { match type of Hresumed with ?P resumed => match goal with |- ?Q resumed =>
      assert (Horder : P |-- Q) end end.
    { unfold kernel_stack_call_closed; entailer!. }
    exact (Horder resumed Hresumed). }
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore
    returned word written resumed final_cursor after _ Hword Hsuffix_pre Hsuffix)
    as [Hcursor [Hafter_memory Hclosed]].
  split; [exact Hi|]. split; [exact Ho|]. split; [exact Hs|]. split.
  - rewrite Hcursor, Hwritten; reflexivity.
  - rewrite Hword_mask in Hclosed.
    match type of Hclosed with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { unfold kernel_stack_call_closed; entailer!. }
    exact (Hclose after Hclosed).
Qed.
End RepeatedIRQResources.
