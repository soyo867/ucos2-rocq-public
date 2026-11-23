Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.VC.code.flag.spec.flag_source_resources_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_irq_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_irq_spec.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_continuation_resources_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.lib.flag.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.VC.code.flag.spec.flag_task_rdy_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source-facing component interfaces, not a replacement public callee
    declaration. [current_local] is the owned cut of the actual invocation.
    The uninterrupted instructions preserve the same heap world and local.
    General interrupted/switched traces still need the Flag source registry
    interpreter and Pend's real local-declaration/call-site producer. *)
Definition flag_source_save_input {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources local
  sg active call mask state (current_local : Assertion) : Assertion :=
  kernel_continuation_call_closed abi resources local sg active call mask state ** current_local.

Definition flag_source_restore_input {external platform port}
  (abi : Armv7aContinuationABI external platform port) resources local critical
  sg active call saved acquired state (current_local : Assertion) : Assertion :=
  kernel_continuation_call_masked abi resources local critical sg active call saved acquired state **
    current_local.

Lemma flag_source_uninterrupted_save_resources : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (save : Armv7aSaveSuffixABI external platform critical arch)
  resources local sg active call state mask registers before final_registers acquired after
  (current_local frame : Assertion),
  registers.(kernel_save_return_word) = None -> valid_os_cpu_sr registers.(kernel_save_cpsr) ->
  armv7a_irq_fiq_mask registers.(kernel_save_cpsr) = mask ->
  (flag_source_save_input abi resources local sg active call mask state current_local ** frame) before ->
  armv7a_save_suffix_transition save (kernel_save_read_cpsr registers) state before
    final_registers acquired after ->
  acquired = state /\ final_registers.(kernel_save_r0) = registers.(kernel_save_cpsr) /\
  kernel_call_save_uninterrupted_execution arch registers state before final_registers acquired after /\
  (flag_source_restore_input abi resources local critical sg active call
    final_registers.(kernel_save_r0) state state current_local ** frame) after.
Proof.
  intros external platform port critical arch abi save resources local sg active call state mask registers
    before final_registers acquired after current_local frame Hreturn Hvalid Hmask Hpre Hsource.
  assert (Hopen : flag_source_save_input abi resources local sg active call mask state current_local ** frame |--
    kernel_continuation_call_closed abi resources local sg active call mask state ** (current_local ** frame)).
  { unfold flag_source_save_input; entailer!. }
  destruct (kernel_continuation_call_uninterrupted_save external platform port critical arch abi save
    resources local sg active call state mask registers before final_registers acquired after
    (current_local ** frame) Hreturn Hvalid Hmask (Hopen before Hpre) Hsource)
    as [Hstate [Hr0 [Hrun Hafter]]].
  split; [exact Hstate|]. split; [exact Hr0|]. split; [exact Hrun|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold flag_source_restore_input; entailer!. }
  exact (Hclose after Hafter).
Qed.

Lemma flag_source_uninterrupted_restore_resources : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  resources local sg active call saved acquired state cursor before written middle final_cursor after
  (current_local frame : Assertion),
  cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (flag_source_restore_input abi resources local critical sg active call saved acquired state current_local ** frame) before ->
  armv7a_restore_prefix_transition restore cursor before written middle ->
  armv7a_restore_suffix_transition restore written middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  (flag_source_save_input abi resources local sg active call (armv7a_irq_fiq_mask saved)
    state current_local ** frame) after.
Proof.
  intros external platform port critical arch abi restore resources local sg active call saved acquired state
    cursor before written middle final_cursor after current_local frame Hr0 Hmask Hpre Hprefix Hsuffix.
  assert (Hopen : flag_source_restore_input abi resources local critical sg active call saved acquired state
      current_local ** frame |--
    kernel_continuation_call_masked abi resources local critical sg active call saved acquired state **
      (current_local ** frame)).
  { unfold flag_source_restore_input; entailer!. }
  destruct (kernel_continuation_call_uninterrupted_restore external platform port critical arch abi restore
    resources local sg active call saved acquired state cursor before written middle final_cursor after
    (current_local ** frame) Hr0 Hmask (Hopen before Hpre) Hprefix Hsuffix) as [Hrun [Hreturn Hafter]].
  split; [exact Hrun|]. split; [exact Hreturn|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold flag_source_save_input; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** The existing precise IRQ descriptor adapter is extended with the
    ACTUAL interrupted local resource. The extra owner is held once in
    the same existing map entry. Other keys retain their original locals;
    no initial None descriptor is relabelled as a saved call. *)
Definition flag_source_irq_local saved_local suspended (interrupted_local : Assertion) :=
  flag_continuation_local_node suspended.(armv7a_continuation_stack) interrupted_local
    (task_tcb_init_irq_local saved_local suspended).

Lemma flag_source_irq_local_selected : forall saved_local suspended interrupted_local,
  flag_source_irq_local saved_local suspended interrupted_local suspended --||--
    (coq_prop (suspended = suspended) && interrupted_local).
Proof.
  intros; unfold flag_source_irq_local.
  rewrite flag_continuation_local_node_selected by reflexivity.
  rewrite task_tcb_init_irq_local_saved_eq; split; entailer!.
Qed.

Lemma flag_source_irq_map_absent : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks saved_local suspended interrupted_local,
  stacks (task_stack_key suspended.(armv7a_continuation_stack)) = None ->
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (task_create_continuation_local saved_local)) stacks --||--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks (flag_source_irq_local saved_local suspended interrupted_local)) stacks.
Proof.
  intros external platform port abi tasks stacks saved_local suspended interrupted_local Hnone.
  pose proof (task_tcb_init_irq_map_absent external platform port abi tasks stacks saved_local suspended Hnone) as Hirq.
  pose proof (flag_continuation_map_node_absent external platform port abi tasks
    suspended.(armv7a_continuation_stack) interrupted_local (task_tcb_init_irq_local saved_local suspended)
    stacks Hnone) as Hlocal.
  unfold flag_source_irq_local; split.
  - intros heap Howned; exact (proj1 Hlocal heap (proj1 Hirq heap Howned)).
  - intros heap Howned; exact (proj2 Hirq heap (proj2 Hlocal heap Howned)).
Qed.

(** The Some-call observation is PRODUCED by the real IRQ save. The
    current local need only be owned before that save. No source guarantee,
    enhanced post or descriptor-call fact is assumed as its replacement. *)
Lemma flag_source_irq_save_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler descriptor publication saved_local
  (interrupted_local frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let parked := armv7a_irq_live_parked_state entry call descriptor.(armv7a_continuation_sp)
    descriptor.(armv7a_continuation_fragments) in
  armv7a_task_frame_slice descriptor ->
  entry.(SchedState).(isRunning) = true -> entry.(IntrState).(intNesting) = 0 ->
  entry.(SchedState).(curTaskID) = Some call.(os_sched_call_stack).(stackLeaseSlot) ->
  entry.(TskState).(inUsedTaskStates) call.(os_sched_call_stack).(stackLeaseSlot) = Some node ->
  node.(taskID) = call.(os_sched_call_stack).(stackLeaseSlot) ->
  node.(taskGeneration) = call.(os_sched_call_stack).(stackLeaseGeneration) ->
  entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None ->
  tcb_field_address (task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg call.(os_sched_call_stack).(stackLeaseSlot) ->
  valid_task_stack_region call.(os_sched_call_stack).(stackLeaseRegion) ->
  task_stack_fragments_in_range call.(os_sched_call_stack).(stackLeaseRegion).(stackRegionWords) 0
    descriptor.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    descriptor.(armv7a_continuation_sp) ->
  task_stack_live_coverage entry.(TskState) (Some (task_stack_key call.(os_sched_call_stack))) ->
  (os_int_exit_frame_save_pre external platform handler **
   (UCOS2_inv sg entry **
    store_parked_continuations
      (kernel_saved_continuation_entry abi entry.(TskState) (task_create_continuation_local saved_local))
      entry.(TskState).(parkedTaskStacks) ** interrupted_local ** frame)) before ->
  armv7a_save_transition abi handler descriptor before saved_heap ->
  exists final,
    descriptor.(armv7a_continuation_call) = Some call /\
    descriptor.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    armv7a_irq_fiq_mask descriptor.(armv7a_continuation_cpsr) = handler.(os_int_exit_interrupted_mask) /\
    kernel_heap_writes (armv7a_continuation_save_writes descriptor)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution (armv7a_irq_live_entry_writes sg entry
      call.(os_sched_call_stack).(stackLeaseSlot) descriptor.(armv7a_continuation_sp)) saved_heap final /\
    task_stack_live_coverage parked.(TskState) None /\
    (UCOS2_inv sg parked **
     store_parked_continuations
       (kernel_saved_continuation_entry abi parked.(TskState)
         (flag_source_irq_local saved_local descriptor interrupted_local))
       parked.(TskState).(parkedTaskStacks) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler descriptor publication saved_local interrupted_local
    frame before saved_heap call parked Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress
    Hregion Hgeometry Hpublication Hsp Hcoverage Hpre Hsave.
  destruct (armv7a_save_transition_observations _ _ _ abi handler descriptor before saved_heap Hsave)
    as [Hsource [Hcall [Hbinding Hobservations]]].
  assert (Hlease : descriptor.(armv7a_continuation_stack) = call.(os_sched_call_stack)).
  { pose proof (proj2 Hbinding) as Hstack; rewrite Hcall in Hstack; symmetry; exact Hstack. }
  assert (Habsent : entry.(TskState).(parkedTaskStacks)
    (task_stack_key descriptor.(armv7a_continuation_stack)) = None) by (rewrite Hlease; exact Hnone).
  match type of Hpre with ?P before => assert (Hopen : P |--
    os_int_exit_frame_save_pre external platform handler **
      (UCOS2_inv sg entry **
       store_parked_continuations
         (kernel_saved_continuation_entry abi entry.(TskState)
           (flag_source_irq_local saved_local descriptor interrupted_local))
         entry.(TskState).(parkedTaskStacks) **
       flag_source_irq_local saved_local descriptor interrupted_local descriptor ** frame)) end.
  { sep_apply_l_atomic (proj1 (flag_source_irq_map_absent external platform port abi entry.(TskState)
      entry.(TskState).(parkedTaskStacks) saved_local descriptor interrupted_local Habsent)).
    sep_apply_r_atomic (proj2 (flag_source_irq_local_selected saved_local descriptor interrupted_local)); entailer!. }
  exact (kernel_irq_save_continuation_resources external platform port abi sg entry node handler descriptor
    publication (flag_source_irq_local saved_local descriptor interrupted_local) frame before saved_heap
    Hslice Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry Hpublication Hsp Hcoverage
    (Hopen before Hpre) Hsave).
Qed.

(** The concrete pointer reads and selected take recover the exact saved
    descriptor and its local owner. The receipt extraction is a linear
    split of that SAME entry; there is no second copy of node or stack. *)
Lemma flag_source_irq_take_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state saved_local suspended call node
  (interrupted_local frame : Assertion) heap,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState)
       (flag_source_irq_local saved_local suspended interrupted_local))
     state.(TskState).(parkedTaskStacks) ** frame) heap ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot))
    suspended.(armv7a_continuation_sp) /\
  armv7a_continuation_restore_reads suspended heap /\
  task_stack_live_coverage restored.(TskState) (Some (task_stack_key suspended.(armv7a_continuation_stack))) /\
  (UCOS2_inv sg restored ** store_parked_continuations
     (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
     restored.(TskState).(parkedTaskStacks) **
   task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
     suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
   (interrupted_local ** frame)) heap.
Proof.
  intros external platform port abi sg state saved_local suspended call node interrupted_local frame heap
    Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre restored.
  match type of Hpre with ?P heap => assert (Hopen : P |--
    UCOS2_inv sg state ** store_parked_continuations
      (kernel_saved_continuation_entry abi state.(TskState) (task_tcb_init_irq_local saved_local suspended))
      state.(TskState).(parkedTaskStacks) ** (interrupted_local ** frame)) end.
  { unfold flag_source_irq_local.
    sep_apply_l_atomic (flag_continuation_map_take_node external platform port abi state.(TskState)
      suspended.(armv7a_continuation_stack) interrupted_local (task_tcb_init_irq_local saved_local suspended)
      state.(TskState).(parkedTaskStacks) suspended.(armv7a_continuation_fragments) Hparked); entailer!. }
  exact (task_tcb_init_irq_take_resources external platform port abi sg state saved_local suspended call node
    (interrupted_local ** frame) heap Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage (Hopen heap Hpre)).
Qed.

(** A real restore consumes the selected dormant authority and restores
    its interrupted invocation. The actual local is returned to that same
    call, with the now-absent key and the remaining ordinary map. This is
    the final IRQ edge; an intervening registry path is not inferred. *)
Lemma flag_source_irq_restore_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state saved_local suspended call node handler
  (interrupted_local frame : Assertion) before after,
  suspended.(armv7a_continuation_call) = Some call ->
  state.(SchedState).(curTaskID) = Some suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  state.(TskState).(inUsedTaskStates) suspended.(armv7a_continuation_stack).(stackLeaseSlot) = Some node ->
  node.(taskGeneration) = suspended.(armv7a_continuation_stack).(stackLeaseGeneration) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), suspended.(armv7a_continuation_fragments)) ->
  tcb_field_address (task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg suspended.(armv7a_continuation_stack).(stackLeaseSlot) ->
  task_stack_live_coverage state.(TskState) None ->
  (UCOS2_inv sg state ** store_parked_continuations
     (kernel_saved_continuation_entry abi state.(TskState)
       (flag_source_irq_local saved_local suspended interrupted_local))
     state.(TskState).(parkedTaskStacks) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) before ->
  armv7a_restore_transition abi handler suspended before after ->
  let restored := os_int_exit_wrapper_restored_state state suspended.(armv7a_continuation_stack) in
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  restored.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) = None /\
  (flag_source_save_input abi (fun sg state => UCOS2_inv sg state)
     (task_create_continuation_local saved_local) sg
     (Some (task_stack_key suspended.(armv7a_continuation_stack)))
     (armv7a_continuation_resumed_call suspended call)
     (armv7a_irq_fiq_mask suspended.(armv7a_continuation_cpsr)) restored interrupted_local **
   task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) ** frame) after.
Proof.
  intros external platform port abi sg state saved_local suspended call node handler interrupted_local frame
    before after Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre Hrestore restored.
  destruct (flag_source_irq_take_resources external platform port abi sg state saved_local suspended call node
    interrupted_local _ before Hcall Hcurrent Hnode Hgen Hparked Haddress Hcoverage Hpre)
    as [Hpointers [Hreads [Hcovered Htaken]]].
  fold restored in Hcovered, Htaken.
  match type of Htaken with ?P before => assert (Hopen : P |--
    interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler **
    task_stack_fragments_rep suspended.(armv7a_continuation_stack).(stackLeaseRegion)
      suspended.(armv7a_continuation_fragments) ** armv7a_dormant_continuation abi suspended **
    (UCOS2_inv sg restored ** store_parked_continuations
       (kernel_saved_continuation_entry abi restored.(TskState) (task_create_continuation_local saved_local))
       restored.(TskState).(parkedTaskStacks) ** interrupted_local ** frame)) by entailer! end.
  destruct (armv7a_restore_transition_resources external platform port abi handler suspended _ before after
    Hreads (Hopen before Htaken) Hrestore) as [Hmemory Hafter].
  rewrite Hcall in Hafter.
  split; [exact Hmemory|]. split.
  - unfold restored, os_int_exit_wrapper_restored_state;
      cbn [replace_TskS TskState glob_task_set_parked_stacks parkedTaskStacks].
    apply task_stack_take_lookup.
  - match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
    { unfold flag_source_save_input, kernel_continuation_call_closed, kernel_continuation_inv; entailer!. }
    exact (Hclose after Hafter).
Qed.


(** A Post ISR may wake the very Pend invocation it interrupted. Its
    detached node is added AFTER the actual Next assignment, retaining
    both the original interrupted local and the precise IRQ descriptor. *)
Lemma flag_source_irq_local_add_receipt : forall saved_local suspended interrupted_local receipt descriptor,
  flag_continuation_local_node suspended.(armv7a_continuation_stack) receipt
    (flag_source_irq_local saved_local suspended interrupted_local) descriptor --||--
  flag_source_irq_local saved_local suspended (interrupted_local ** receipt) descriptor.
Proof.
  intros; unfold flag_source_irq_local, flag_continuation_local_node.
  destruct task_stack_key_eq_dec; split; entailer!.
Qed.

Lemma flag_source_irq_map_add_receipt : forall external platform port
  (abi : Armv7aContinuationABI external platform port) tasks stacks saved_local suspended interrupted_local receipt,
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (flag_continuation_local_node suspended.(armv7a_continuation_stack) receipt
        (flag_source_irq_local saved_local suspended interrupted_local))) stacks |--
  store_parked_continuations
    (kernel_saved_continuation_entry abi tasks
      (flag_source_irq_local saved_local suspended (interrupted_local ** receipt))) stacks.
Proof.
  intros; unfold store_parked_continuations; apply TaskFieldStorage.store_map_mono.
  intros key payload Hlookup; unfold kernel_saved_continuation_entry; Intros descriptor.
  sep_apply_l_atomic (proj1 (flag_source_irq_local_add_receipt saved_local suspended
    interrupted_local receipt descriptor)); Exists descriptor; entailer!.
Qed.

Lemma flag_source_irq_task_rdy_next_publish : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg state node waiter old bits result returned
  saved_local suspended fragments pnode (interrupted_local frame : Assertion) before middle after observed,
  UCOS2_state_inv sg state -> flag_task_rdy_domain sg state node waiter old bits ->
  waiter.(flagNodeAddr) = node ->
  task_stack_key suspended.(armv7a_continuation_stack) = (waiter.(flagTask), waiter.(flagTaskGeneration)) ->
  state.(TskState).(parkedTaskStacks) (task_stack_key suspended.(armv7a_continuation_stack)) =
    Some (suspended.(armv7a_continuation_stack).(stackLeaseRegion), fragments) ->
  flag_pend_sched_task_rdy_call sg node bits result returned before middle ->
  flag_source_next_assignment pnode node observed middle after ->
  (flag_task_rdy_pre sg state node waiter old bits **
    (UCOS2_raw_rep_missing_task_storage_sched_flag sg state **
     store_parked_continuations
       (kernel_saved_continuation_entry abi state.(TskState)
         (flag_source_irq_local saved_local suspended interrupted_local))
       state.(TskState).(parkedTaskStacks) ** (pnode # Ptr |-> node ** frame))) before ->
  exists post schedule,
    flag_task_rdy sg state node bits result = Some (schedule, post) /\
    returned = (if schedule then 1 else 0) /\
    observed = waiter.(flagWaitImage).(flagNodeNext) /\
    (pnode # Ptr |-> observed ** UCOS2_inv sg post **
     store_parked_continuations
       (kernel_saved_continuation_entry abi post.(TskState)
         (flag_source_irq_local saved_local suspended
           (interrupted_local ** flag_pend_sched_node_rep sg node post)))
       post.(TskState).(parkedTaskStacks) ** frame) after.
Proof.
  intros external platform port abi sg state node waiter old bits result returned saved_local suspended
    fragments pnode interrupted_local frame before middle after observed Hvalid Hdomain Hnode Hkey Hentry
    Hcall Hnext Hpre.
  destruct (flag_source_task_rdy_next_publish external platform port abi sg state node waiter old bits result
    returned suspended.(armv7a_continuation_stack)
    (flag_source_irq_local saved_local suspended interrupted_local) fragments pnode frame before middle after
    observed Hvalid Hdomain Hnode Hkey Hentry Hcall Hnext Hpre)
    as [post [schedule [Hstep [Hreturned [Hobserved Hafter]]]]].
  exists post, schedule; split; [exact Hstep|]. split; [exact Hreturned|]. split; [exact Hobserved|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { sep_apply_l_atomic (flag_source_irq_map_add_receipt external platform port abi post.(TskState)
      post.(TskState).(parkedTaskStacks) saved_local suspended interrupted_local
      (flag_pend_sched_node_rep sg node post)); entailer!. }
  exact (Hclose after Hafter).
Qed.

(** This is the actual masked C prefix, with all its selector/guard and
    cache/counter writes. The unchanged task/Flag projections permit the
    actual caller locals to stay in the source frame at this segment. *)
Lemma flag_source_sched_prefix_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  local critical sg active call saved acquired state before (current_local frame : Assertion),
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (flag_source_restore_input abi kernel_program_inv local critical sg active call saved acquired state
    current_local ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg state before after /\
    (os_sched_requests_switch state = true ->
      sched_high_ready_consistency (os_sched_prefix_state state).(TskState)
        (os_sched_prefix_state state).(SchedState)) /\
    (flag_source_restore_input abi kernel_program_inv local critical sg active call saved acquired
      (os_sched_prefix_state state) current_local ** frame) after.
Proof.
  intros external platform port abi local critical sg active call saved acquired state before current_local frame
    Hnonempty Hpre.
  match type of Hpre with ?P before => assert (Hopen : P |--
    kernel_continuation_call_masked abi kernel_program_inv local critical sg active call saved acquired state **
      (current_local ** frame)) end.
  { unfold flag_source_restore_input; entailer!. }
  destruct (os_sched_modular_prefix_continuation_resources external platform port abi local critical sg active
    call saved acquired state before (current_local ** frame) Hnonempty (Hopen before Hpre))
    as [after [Hrun [Hhigh Hafter]]].
  exists after; split; [exact Hrun|]. split; [exact Hhigh|].
  match type of Hafter with ?P after => match goal with |- ?Q after => assert (Hclose : P |-- Q) end end.
  { unfold flag_source_restore_input; entailer!. }
  exact (Hclose after Hafter).
Qed.

(** Complete nonswitch body and uninterrupted Restore suffix. Disabled,
    nested, locked and equal-priority cases follow the real prefix guards.
    This does not cover switched/interrupted paths, or infer that an
    arbitrary prefix heap is the returned endpoint of those paths. *)
Lemma flag_source_sched_nonswitch_return_resources : forall external platform port critical arch
  (abi : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  local sg active call saved acquired state before (current_local frame : Assertion),
  os_sched_requests_switch state = false ->
  (os_sched_selection_enabled state = true -> state.(SchedState).(readyList) <> []) ->
  (flag_source_restore_input abi kernel_program_inv local critical sg active call saved acquired state
    current_local ** frame) before ->
  exists prefix_heap,
    os_sched_modular_prefix_execution sg state before prefix_heap /\
    forall cursor written middle final_cursor after,
      cursor.(kernel_restore_r0) = saved -> armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
      armv7a_restore_prefix_transition restore cursor prefix_heap written middle ->
      armv7a_restore_suffix_transition restore written middle final_cursor after ->
      os_sched_c_return external critical sg state call call (os_sched_prefix_state state) /\
      kernel_call_restore_uninterrupted_execution arch cursor prefix_heap final_cursor after /\
      final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
      (flag_source_save_input abi kernel_program_inv local sg active call (armv7a_irq_fiq_mask saved)
        (os_sched_prefix_state state) current_local ** frame) after.
Proof.
  intros external platform port critical arch abi restore local sg active call saved acquired state before
    current_local frame Hnoswitch Hnonempty Hpre.
  destruct (flag_source_sched_prefix_resources external platform port abi local critical sg active call saved
    acquired state before current_local frame Hnonempty Hpre) as [prefix_heap [Hprefix [Hhigh Howned]]].
  exists prefix_heap; split; [exact Hprefix|].
  intros cursor written middle final_cursor after Hr0 Hmask Hwrite Hsuffix.
  split.
  - unfold os_sched_c_return; rewrite Hnoswitch; auto.
  - exact (flag_source_uninterrupted_restore_resources external platform port critical arch abi restore
      kernel_program_inv local sg active call saved acquired (os_sched_prefix_state state) cursor prefix_heap
      written middle final_cursor after current_local frame Hr0 Hmask Howned Hwrite Hsuffix).
Qed.
