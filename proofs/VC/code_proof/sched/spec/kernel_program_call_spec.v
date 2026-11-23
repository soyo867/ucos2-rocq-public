Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task_context Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_install_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_entry_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_counter_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_restore_resource_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** OSUnMapTbl is part of the shared program owner handed to the executing
    handler, not an immutable private loan retained by the interrupted
    caller. This equivalence only opens that one owner for a source fragment;
    it cannot add a table to the old dynamic-only closed assertion. *)
Lemma kernel_program_continuation_world_split_unmap :
  forall external platform port
    (abi : Armv7aContinuationABI external platform port) focus sg state,
  armv7a_continuation_world abi focus (kernel_program_inv sg) state --||--
    armv7a_continuation_world abi focus (UCOS2_inv sg) state **
    unmap_table_rep sg.
Proof.
  intros; unfold armv7a_continuation_world.
  rewrite kernel_program_inv_split_unmap; split; entailer!.
Qed.

(** The source counter fragment has no unspecified heap successor. Equal
    real byte loads choose the same guarded store; its ordered writes are
    deterministic. This supports transport to a SUPPLIED execution result. *)
Lemma os_int_exit_masked_counter_final_eq : forall sg before observed first other second,
  os_int_exit_masked_counter_fragment sg before observed first ->
  os_int_exit_masked_counter_fragment sg before other second -> first = second.
Proof.
  intros sg before observed first other second Hfirst Hsecond.
  destruct Hfirst as [heap Hread1|heap nesting1 first Hread1 Hnest1 Hrun1];
    destruct Hsecond as [heap Hread2|heap nesting2 second Hread2 Hnest2 Hrun2].
  - reflexivity.
  - pose proof (KernelHeapObservation.uchar_load_deterministic _ _ _ _ Hread1 Hread2);
      discriminate.
  - pose proof (KernelHeapObservation.uchar_load_deterministic _ _ _ _ Hread1 Hread2);
      discriminate.
  - assert (nesting1 = nesting2) as Hnest.
    { eapply KernelHeapObservation.uchar_load_deterministic; eassumption. }
    subst nesting2; eapply kernel_heap_execution_deterministic; eassumption.
Qed.

Lemma os_int_exit_masked_no_schedule_final_eq : forall sg before first second,
  os_int_exit_masked_no_schedule_fragment sg before first ->
  os_int_exit_masked_no_schedule_fragment sg before second -> first = second.
Proof.
  intros sg before first second Hfirst Hsecond.
  destruct Hfirst; destruct Hsecond;
    eapply os_int_exit_masked_counter_final_eq; eassumption.
Qed.

(** The masked no-schedule OSIntExit fragment performs its actual ordered
    reads and counter store on the executing handler's program world. The
    table and original focused capsule are retained through those local
    writes, not held privately across arbitrary intervening execution. *)
Lemma kernel_program_irq_no_schedule_keeps_parked_call : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (armv7a_continuation_world abi focus (kernel_program_inv sg) state ** frame) before ->
  exists after,
    os_int_exit_masked_no_schedule_fragment sg before after /\
    (armv7a_continuation_world abi focus (kernel_program_inv sg)
       (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi focus sg state frame before Hbranch Hpre.
  assert (Hsplit : armv7a_continuation_world abi focus (kernel_program_inv sg) state ** frame |--
    armv7a_continuation_world abi focus (UCOS2_inv sg) state **
      (unmap_table_rep sg ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  destruct (armv7a_irq_no_schedule_keeps_parked_call external platform port abi focus
    sg state (unmap_table_rep sg ** frame) before Hbranch (Hsplit before Hpre))
    as [after [Hsource Hpost]].
  exists after; split; [exact Hsource|].
  assert (Hmerge : armv7a_continuation_world abi focus (UCOS2_inv sg)
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
      (unmap_table_rep sg ** frame) |--
    armv7a_continuation_world abi focus (kernel_program_inv sg)
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  exact (Hmerge after Hpost).
Qed.

(** In particular the resource is obtained on the actual supplied final
    heap, not merely on an unrelated existential endpoint. *)
Lemma kernel_program_irq_no_schedule_preserves_world : forall external platform port
  (abi : Armv7aContinuationABI external platform port) focus sg state
  (frame : Assertion) before after,
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  (armv7a_continuation_world abi focus (kernel_program_inv sg) state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (armv7a_continuation_world abi focus (kernel_program_inv sg)
     (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi focus sg state frame before after Hbranch Hpre Hsource.
  destruct (kernel_program_irq_no_schedule_keeps_parked_call external platform port abi
    focus sg state frame before Hbranch Hpre) as [final [Hrun Hpost]].
  pose proof (os_int_exit_masked_no_schedule_final_eq sg before final after Hrun Hsource) as ->.
  exact Hpost.
Qed.

(** Common source cut for an already registered call: actual selected-SP
    load/cache writes and capsule take, followed by the supplied sixteen
    frame reads and register-restore transition on that SAME heap. The
    selected PC/LR are obtained from the focused attachment. No call return
    or equality with the interrupted state is asserted. Save's suffix and
    a Restore/BX caller may consume this resource separately. *)
Lemma kernel_program_selected_call_restore : forall external platform port
  (continuations : Armv7aContinuationABI external platform port)
  sg handler original transfer resume_pc return_pc (frame : Assertion) heap,
  let focus := armv7a_call_focus original resume_pc return_pc in
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) =
    task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
      transfer.(os_int_exit_hooked_state) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = resume_pc /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall restored,
      saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      restored.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved original)
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       (armv7a_continuation_world continuations focus (kernel_program_inv sg)
          (os_int_exit_installed_state transfer) **
        task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) restored).
Proof.
  intros external platform port continuations sg handler original transfer resume_pc
    return_pc frame heap focus Hdestination Hkey Haddress Hpre.
  assert (Hsplit :
    armv7a_continuation_world continuations focus (kernel_program_inv sg)
      transfer.(os_int_exit_hooked_state) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame) |--
    armv7a_continuation_world continuations focus (UCOS2_inv sg)
      transfer.(os_int_exit_hooked_state) **
    (unmap_table_rep sg **
      (interrupt_platform_running platform handler.(os_int_exit_invocation)
         handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame))).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  destruct (armv7a_install_take_continuation external platform port continuations
    focus sg transfer _ heap Hdestination Hkey Haddress (Hsplit heap Hpre))
    as [installed [saved [Hinstall [Hbinding [Hfocused
      [Hstack [Hfragments [Hcurrent Howned]]]]]]]].
  destruct Hfocused as [Hcall [Hpc Hlr]].
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hcall|].
  split; [exact Hpc|]. split; [exact Hlr|].
  intros restored Hsp Hreads Hrestore.
  assert (Hreorder :
    armv7a_continuation_world continuations focus (UCOS2_inv sg)
      (os_int_exit_installed_state transfer) **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (unmap_table_rep sg **
      (interrupt_platform_running platform handler.(os_int_exit_invocation)
         handler.(os_int_exit_origin) 192 **
       os_int_exit_context_resources port handler ** frame)) |--
    interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 ** os_int_exit_context_resources port handler **
    task_stack_fragments_rep saved.(armv7a_continuation_stack).(stackLeaseRegion)
      saved.(armv7a_continuation_fragments) ** armv7a_dormant_continuation continuations saved **
    (armv7a_continuation_world continuations focus (kernel_program_inv sg)
       (os_int_exit_installed_state transfer) ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  destruct (armv7a_restore_call_resources external platform port continuations
    handler saved original _ installed restored Hcall Hreads
    (Hreorder installed Howned) Hrestore) as [Hmemory Hrestored].
  split; [exact Hmemory|].
  assert (Hframe :
    kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call saved original)
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) **
    (armv7a_continuation_world continuations focus (kernel_program_inv sg)
       (os_int_exit_installed_state transfer) ** frame) |--
    kernel_call_execution_owned external platform
      (armv7a_continuation_resumed_call saved original)
      (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
    (armv7a_continuation_world continuations focus (kernel_program_inv sg)
       (os_int_exit_installed_state transfer) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame)) by entailer!.
  exact (Hframe restored Hrestored).
Qed.

(** Actual post-hook install -> selected capsule -> register restore ->
    Save suffix, all on the same successive heaps. In particular, the table
    is present in the executing handler's input world and is returned with
    the ACTUAL resumed state, which need not equal the interrupted state.

    The existing platform ABI is used without new fields. No ready-task
    coverage, Event public-slot property, or arbitrary BSP/hook producer is
    inferred here. This is a source-cut consumer, not a replacement public
    Save Ensure. The loaded-SP and register equations are actual instruction
    joins which a complete caller/source execution must establish. *)
Lemma kernel_program_selected_save_continuation :
  forall external platform port critical arch
    (continuations : Armv7aContinuationABI external platform port)
    (suffix : Armv7aSaveSuffixABI external platform critical arch)
    sg handler original transfer return_pc (frame : Assertion) heap,
  let focus := armv7a_call_focus original
    (armv7a_save_entry_address suffix + 4) return_pc in
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) =
    task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
      transfer.(os_int_exit_hooked_state) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = armv7a_save_entry_address suffix + 4 /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall registers restored final_registers resumed after,
      saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
      registers.(kernel_save_cpsr) = saved.(armv7a_continuation_cpsr) ->
      registers.(kernel_save_r0) = nth 0 saved.(armv7a_continuation_registers) 0 ->
      registers.(kernel_save_lr) = saved.(armv7a_continuation_lr) ->
      interrupt_saved_value (armv7a_irq_fiq_mask registers.(kernel_save_cpsr))
        registers.(kernel_save_r0) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      armv7a_save_suffix_transition suffix registers (os_int_exit_installed_state transfer)
        restored final_registers resumed after ->
      resumed = os_int_exit_installed_state transfer /\
      final_registers.(kernel_save_return_word) = Some return_pc /\
      final_registers.(kernel_save_r0) = registers.(kernel_save_r0) /\
      (critical_region_masked platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) final_registers.(kernel_save_r0)
         (os_int_exit_installed_state transfer) **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       (armv7a_continuation_world continuations focus (kernel_program_inv sg)
          (os_int_exit_installed_state transfer) **
        task_stack_fragments_rep handler.(os_int_exit_handler_stack)
          handler.(os_int_exit_handler_fragments) ** frame)) after).
Proof.
  intros external platform port critical arch continuations suffix sg handler original
    transfer return_pc frame heap focus Hdestination Hkey Haddress Hpre.
  destruct (kernel_program_selected_call_restore external platform port continuations sg
    handler original transfer (armv7a_save_entry_address suffix + 4) return_pc frame heap
    Hdestination Hkey Haddress Hpre)
    as [installed [saved [Hinstall [Hcall [Hpc [Hlr Hconsume]]]]]].
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hcall|].
  split; [exact Hpc|]. split; [exact Hlr|].
  intros registers restored final_registers resumed after
    Hsp Hcpsr Hr0 Hregisterlr Hsaved Hreads Hrestore Hsuffix.
  destruct (Hconsume restored Hsp Hreads Hrestore) as [Hmemory Hrestored].
  assert (Hsuffix_owned :
    (kernel_call_execution_owned external platform
       (armv7a_continuation_resumed_call saved original)
       (armv7a_irq_fiq_mask registers.(kernel_save_cpsr)) **
     (armv7a_continuation_world continuations focus (kernel_program_inv sg)
        (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame)) restored).
  { rewrite Hcpsr; exact Hrestored. }
  destruct (armv7a_save_suffix_preserves_source_heap external platform critical arch suffix
    sg (armv7a_continuation_resumed_call saved original) registers
    (os_int_exit_installed_state transfer) restored final_registers resumed after
    _ Hsaved Hsuffix_owned Hsuffix)
    as [Hstate [Hsame [Hreturn [Hvalue Hpost]]]].
  split; [exact Hstate|]. split; [rewrite Hregisterlr, Hlr in Hreturn; exact Hreturn|].
  split; [exact Hvalue|].
  cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin] in Hpost.
  exact Hpost.
Qed.

(** The matching entry producer consumes the original execution owner:
    actual register/frame writes followed by real counter and TCB-SP stores.
    The same program table enters the resulting handler-owned world. This
    does not assert that an arbitrary intervening BSP or task returns it;
    that middle source execution still needs its own heap/resource proof. *)
Lemma kernel_program_irq_source_save_deposit : forall external platform port
  (abi : Armv7aContinuationABI external platform port)
  sg entry node handler saved publication (frame : Assertion) before saved_heap,
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    saved.(armv7a_continuation_lr) in
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
    saved.(armv7a_continuation_fragments) ->
  task_publication_happened entry.(TskState) publication
    call.(os_sched_call_stack).(stackLeaseSlot) call.(os_sched_call_stack).(stackLeaseGeneration) ->
  task_stack_saved_pointer_in_range call.(os_sched_call_stack).(stackLeaseRegion)
    saved.(armv7a_continuation_sp) ->
  (os_int_exit_frame_save_pre external platform handler **
    (armv7a_continuation_world abi focus
       (kernel_program_inv sg) entry ** frame)) before ->
  armv7a_save_transition abi handler saved before saved_heap ->
  exists final,
    saved.(armv7a_continuation_call) = Some call /\
    saved.(armv7a_continuation_pc) = handler.(os_int_exit_interrupted_pc) /\
    kernel_heap_writes (armv7a_continuation_save_writes saved)
      before.(ConAssertion.s_mem) saved_heap.(ConAssertion.s_mem) /\
    kernel_heap_execution
      (armv7a_irq_live_entry_writes sg entry call.(os_sched_call_stack).(stackLeaseSlot)
        saved.(armv7a_continuation_sp)) saved_heap final /\
    (armv7a_continuation_world abi focus (kernel_program_inv sg)
       (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
         saved.(armv7a_continuation_fragments)) **
     (interrupt_platform_running platform handler.(os_int_exit_invocation)
        handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) final.
Proof.
  intros external platform port abi sg entry node handler saved publication frame before saved_heap
    call focus Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp Hpre Hsave.
  assert (Hsplit :
    os_int_exit_frame_save_pre external platform handler **
      (armv7a_continuation_world abi focus (kernel_program_inv sg) entry ** frame) |--
    os_int_exit_frame_save_pre external platform handler **
      (armv7a_continuation_world abi focus (UCOS2_inv sg) entry **
        (unmap_table_rep sg ** frame))).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  destruct (armv7a_irq_source_save_deposit external platform port abi sg entry node handler
    saved publication (unmap_table_rep sg ** frame) before saved_heap
    Hrunning Hnesting Hcurrent Hnode Hid Hgen Hnone Haddress Hregion Hgeometry
    Hpublication Hsp (Hsplit before Hpre) Hsave)
    as [final [Hcall [Hpc [Hwrites [Hcounter Hpost]]]]].
  exists final; split; [exact Hcall|]. split; [exact Hpc|].
  split; [exact Hwrites|]. split; [exact Hcounter|].
  assert (Hmerge :
    armv7a_continuation_world abi focus (UCOS2_inv sg)
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** (unmap_table_rep sg ** frame)) |--
    armv7a_continuation_world abi focus (kernel_program_inv sg)
      (armv7a_irq_live_parked_state entry call saved.(armv7a_continuation_sp)
        saved.(armv7a_continuation_fragments)) **
    (interrupt_platform_running platform handler.(os_int_exit_invocation)
       handler.(os_int_exit_origin) 192 **
     os_int_exit_context_resources port handler ** frame)).
  { rewrite kernel_program_continuation_world_split_unmap; entailer!. }
  exact (Hmerge final Hpost).
Qed.

(** Actual local MSR cut. The program owner is the existing single shared
    world framed through these two local instructions; it is not supplied
    by the CPU/CSL ABI. An ensuing IRQ must TAKE this owner before using it. *)
Lemma kernel_program_restore_prefix_closed : forall external platform critical arch
  (abi : Armv7aRestoreResourceABI external platform critical arch)
  sg call saved entry checkpoint cursor before written_cursor after (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources external call **
   (kernel_program_inv sg checkpoint ** frame)) before ->
  armv7a_restore_prefix_transition abi cursor before written_cursor after ->
  written_cursor = kernel_restore_write_cpsr cursor /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) checkpoint **
   os_sched_context_resources external call ** frame) after.
Proof.
  intros external platform critical arch abi sg call saved entry checkpoint cursor
    before written_cursor after frame Hr0 Hmask Hpre Hrun.
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch
    abi sg call saved entry cursor before written_cursor after
    (kernel_program_inv sg checkpoint ** frame) Hr0 Hmask Hpre Hrun)
    as [Hcursor [Hmemory Howned]].
  split; [exact Hcursor|]. split; [exact Hmemory|].
  assert (Hclose : kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask saved) ** (kernel_program_inv sg checkpoint ** frame) |--
    kernel_program_closed platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) checkpoint **
    os_sched_context_resources external call ** frame).
  { rewrite kernel_program_closed_equiv; unfold kernel_call_execution_owned; entailer!. }
  exact (Hclose after Howned).
Qed.

(** The no-interruption branch is a real prefix/release/suffix consumer on
    the exact intermediate and final models. The assertion indexed by
    checkpoint is preserved by the local frame laws, not by a new OS-state
    field in the ABI. This theorem does not classify every public call. *)
Lemma kernel_program_restore_uninterrupted_closed : forall external platform critical arch
  (abi : Armv7aRestoreResourceABI external platform critical arch)
  sg call saved entry checkpoint cursor before written_cursor middle final_cursor after
  (frame : Assertion),
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources external call **
   (kernel_program_inv sg checkpoint ** frame)) before ->
  armv7a_restore_prefix_transition abi cursor before written_cursor middle ->
  armv7a_restore_suffix_transition abi written_cursor middle final_cursor after ->
  kernel_call_restore_uninterrupted_execution arch cursor before final_cursor after /\
  final_cursor.(kernel_restore_return_word) = Some cursor.(kernel_restore_lr) /\
  after.(ConAssertion.s_mem) = before.(ConAssertion.s_mem) /\
  (kernel_program_closed platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) checkpoint **
   os_sched_context_resources external call ** frame) after.
Proof.
  intros external platform critical arch abi sg call saved entry checkpoint cursor
    before written_cursor middle final_cursor after frame Hr0 Hmask Hpre Hprefix Hsuffix.
  destruct (armv7a_restore_uninterrupted_transports_owned_execution external platform critical
    arch abi sg call saved entry cursor before written_cursor middle final_cursor after
    (kernel_program_inv sg checkpoint ** frame) Hr0 Hmask Hpre Hprefix Hsuffix)
    as [Hsource [Hreturn [Hmemory Howned]]].
  split; [exact Hsource|]. split; [exact Hreturn|]. split; [exact Hmemory|].
  assert (Hclose : kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask saved) ** (kernel_program_inv sg checkpoint ** frame) |--
    kernel_program_closed platform critical sg call.(os_sched_call_invocation)
      call.(os_sched_call_origin) (armv7a_irq_fiq_mask saved) checkpoint **
    os_sched_context_resources external call ** frame).
  { rewrite kernel_program_closed_equiv; unfold kernel_call_execution_owned; entailer!. }
  exact (Hclose after Howned).
Qed.

(** Interrupted branch's downstream join: real selected-SP/cache writes,
    actual sixteen frame reads and exception restore meet the BX source
    transition on the SAME restored model. The MSR mask and LR are joined
    explicitly to that saved frame. [bx_pc] still needs the caller's actual
    linked Restore address binding. This does not create the intervening
    handler world, tie it to an earlier released checkpoint or prove that
    this task is selected/eventually returns. Saved/inside are NOT needed
    again here, and every parked/handler/frame resource is returned. *)
Lemma kernel_program_selected_restore_suffix : forall external platform port critical arch
  (continuations : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg handler original transfer bx_pc return_pc (frame : Assertion) heap,
  let focus := armv7a_call_focus original bx_pc return_pc in
  os_int_exit_destination_binding external transfer ->
  task_stack_key transfer.(os_int_exit_incoming_stack) =
    task_stack_key original.(os_sched_call_stack) ->
  tcb_field_address (task_slot_addr sg
      transfer.(os_int_exit_incoming_stack).(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot) ->
  (armv7a_continuation_world continuations focus (kernel_program_inv sg)
      transfer.(os_int_exit_hooked_state) **
   (interrupt_platform_running platform handler.(os_int_exit_invocation)
      handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  exists installed saved,
    sched_install_heap_fragment sg heap installed
      (task_slot_addr sg transfer.(os_int_exit_incoming_stack).(stackLeaseSlot))
      transfer.(os_int_exit_incoming_sp) /\
    saved.(armv7a_continuation_call) = Some original /\
    saved.(armv7a_continuation_pc) = bx_pc /\
    saved.(armv7a_continuation_lr) = return_pc /\
    (forall restored cursor written final_cursor after,
      saved.(armv7a_continuation_sp) = transfer.(os_int_exit_incoming_sp) ->
      armv7a_continuation_restore_reads saved installed ->
      armv7a_restore_transition continuations handler saved installed restored ->
      cursor.(kernel_restore_lr) = saved.(armv7a_continuation_lr) ->
      cursor.(kernel_restore_msr_word) = Some written ->
      armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr) = armv7a_irq_fiq_mask written ->
      armv7a_restore_suffix_transition restore cursor restored final_cursor after ->
      final_cursor.(kernel_restore_return_word) = Some return_pc /\
      after.(ConAssertion.s_mem) = installed.(ConAssertion.s_mem) /\
      (kernel_program_closed platform critical sg original.(os_sched_call_invocation)
         original.(os_sched_call_origin) (armv7a_irq_fiq_mask written)
         (os_int_exit_installed_state transfer) **
       os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
       armv7a_parked_continuations continuations focus (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) after).
Proof.
  intros external platform port critical arch continuations restore sg handler original transfer
    bx_pc return_pc frame heap focus Hdestination Hkey Haddress Hpre.
  destruct (kernel_program_selected_call_restore external platform port continuations sg handler
    original transfer bx_pc return_pc frame heap Hdestination Hkey Haddress Hpre)
    as [installed [saved [Hinstall [Hcall [Hpc [Hlr Hconsume]]]]]].
  exists installed, saved; split; [exact Hinstall|]. split; [exact Hcall|].
  split; [exact Hpc|]. split; [exact Hlr|].
  intros restored cursor written final_cursor after Hsp Hreads Hrestore Hcursor_lr Hword Hmask Hsuffix.
  destruct (Hconsume restored Hsp Hreads Hrestore) as [Hmemory Howned].
  rewrite Hmask in Howned.
  destruct (armv7a_restore_suffix_transports_owned_execution external platform critical arch restore
    (armv7a_continuation_resumed_call saved original) written cursor restored final_cursor after
    (armv7a_continuation_world continuations focus (kernel_program_inv sg)
       (os_int_exit_installed_state transfer) **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame) Hword Howned Hsuffix)
    as [Hfinal [Hmemory_final Hpost]].
  split.
  - rewrite Hfinal; cbn [kernel_restore_branch_lr kernel_restore_return_word].
    rewrite Hcursor_lr, Hlr; reflexivity.
  - split; [congruence|].
    assert (Hclose :
      kernel_call_execution_owned external platform (armv7a_continuation_resumed_call saved original)
        (armv7a_irq_fiq_mask written) **
      (armv7a_continuation_world continuations focus (kernel_program_inv sg)
         (os_int_exit_installed_state transfer) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack)
         handler.(os_int_exit_handler_fragments) ** frame) |--
      kernel_program_closed platform critical sg original.(os_sched_call_invocation)
        original.(os_sched_call_origin) (armv7a_irq_fiq_mask written)
        (os_int_exit_installed_state transfer) **
      os_sched_context_resources external (armv7a_continuation_resumed_call saved original) **
      armv7a_parked_continuations continuations focus (os_int_exit_installed_state transfer) **
      task_stack_fragments_rep handler.(os_int_exit_handler_stack)
        handler.(os_int_exit_handler_fragments) ** frame).
    { unfold kernel_call_execution_owned, armv7a_continuation_world.
      rewrite kernel_program_closed_equiv.
      cbn [armv7a_continuation_resumed_call os_sched_call_invocation os_sched_call_origin]; entailer!. }
    exact (Hclose after Hpost).
Qed.

(** Upstream interrupted-branch seam on the actual MSR endpoint. The
    inactive handler stack is an owned input, not manufactured here. The
    existing absent-focus theorem adds only the empty focused rights and
    carries all physical program bytes into the IRQ-save input. To apply
    source_save_deposit next, the caller still joins the actual saved LR
    with cursor.LR and supplies its real entry/frame/publication facts. *)
Lemma kernel_program_restore_prefix_irq_input : forall external platform port critical arch
  (continuations : Armv7aContinuationABI external platform port)
  (restore : Armv7aRestoreResourceABI external platform critical arch)
  sg handler saved entry checkpoint cursor heap written_cursor released (frame : Assertion),
  let call := handler.(os_int_exit_interrupted_call) in
  let focus := armv7a_call_focus call handler.(os_int_exit_interrupted_pc)
    cursor.(kernel_restore_lr) in
  handler.(os_int_exit_interrupted_mask) = armv7a_irq_fiq_mask saved ->
  checkpoint.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = None ->
  cursor.(kernel_restore_r0) = saved ->
  armv7a_irq_fiq_mask cursor.(kernel_restore_current_cpsr) = 192 ->
  (critical_region_masked platform critical sg call.(os_sched_call_invocation)
     call.(os_sched_call_origin) saved entry **
   os_sched_context_resources external call **
   (kernel_program_inv sg checkpoint **
    task_stack_fragments_rep handler.(os_int_exit_handler_stack)
      handler.(os_int_exit_handler_fragments) ** frame)) heap ->
  armv7a_restore_prefix_transition restore cursor heap written_cursor released ->
  written_cursor = kernel_restore_write_cpsr cursor /\
  released.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
  (os_int_exit_frame_save_pre external platform handler **
   (armv7a_continuation_world continuations focus (kernel_program_inv sg) checkpoint **
    frame)) released.
Proof.
  intros external platform port critical arch continuations restore sg handler saved entry checkpoint
    cursor heap written_cursor released frame call focus Hhandler_mask Hnone Hr0 Hmask Hpre Hprefix.
  destruct (armv7a_restore_prefix_releases_critical_region external platform critical arch restore
    sg call saved entry cursor heap written_cursor released
    (kernel_program_inv sg checkpoint **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame) Hr0 Hmask Hpre Hprefix)
    as [Hcursor [Hmemory Howned]].
  split; [exact Hcursor|]. split; [exact Hmemory|].
  assert (Hworld : kernel_program_inv sg checkpoint |--
    armv7a_continuation_world continuations focus (kernel_program_inv sg) checkpoint).
  { rewrite kernel_program_inv_split_unmap, kernel_program_continuation_world_split_unmap.
    intros owned [world [table [Hsplit [Hworld Htable]]]].
    exists world, table; split; [exact Hsplit|]; split; [|exact Htable].
    exact (armv7a_continuation_world_open_absent external platform port continuations
      focus sg checkpoint Hnone world Hworld). }
  assert (Hjoin : kernel_call_execution_owned external platform call
      (armv7a_irq_fiq_mask saved) **
    (kernel_program_inv sg checkpoint **
     task_stack_fragments_rep handler.(os_int_exit_handler_stack)
       handler.(os_int_exit_handler_fragments) ** frame) |--
    os_int_exit_frame_save_pre external platform handler **
    (armv7a_continuation_world continuations focus (kernel_program_inv sg) checkpoint ** frame)).
  { sep_apply_l_atomic Hworld.
    unfold os_int_exit_frame_save_pre; rewrite Hhandler_mask; unfold call; entailer!. }
  exact (Hjoin released Howned).
Qed.
