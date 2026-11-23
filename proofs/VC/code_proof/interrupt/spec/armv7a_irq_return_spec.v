Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.task_storage Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Import UCOS2_C_Rules KernelHeapObservation.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Selected ARMv7-A/non-VFP wrapper, after the masked OSIntExit return:
    LDR R4,[OSTCBCur]; LDR SP,[R4]. The second read really uses the value
    of the first. These reads do not alter memory; restoring registers and
    the saved PC/mask is the already explicit external continuation contract.
    No equality with the earlier IRQ-entry heap is assumed. *)
Definition armv7a_irq_restore_pointer_reads (sg : StableGlobVars)
  (heap : model) (tcb sp : Z) : Prop :=
  pointer_load sg.(g_OSTCBCur) tcb heap /\ pointer_load tcb sp heap.

Lemma armv7a_irq_raw_current_pointer_load : forall sg state heap,
  UCOS2_raw_rep sg state heap ->
  pointer_load sg.(g_OSTCBCur) (encode_task_link sg state.(SchedState).(curTaskID)) heap.
Proof.
  intros sg state heap Hraw.
  assert (Hfocus : UCOS2_raw_rep sg state |--
    sg.(g_OSTCBCur) # Ptr |-> encode_task_link sg state.(SchedState).(curTaskID) ** TT).
  { unfold UCOS2_raw_rep, sched_raw_rep, sched_physical_rep; entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hfocus heap Hraw).
Qed.

(** The joint-feature invariant has the same physical parked-stack owner.
    Taking one frame changes only that map; all real TCB fields, including
    Multi and profiling fields, and all Event/name resources are retained.
    This proof does not try to obtain full validity from the old selected
    profile certificate. *)
Lemma os_int_exit_wrapper_take_full_destination_resources : forall sg state incoming fragments,
  state.(TskState).(parkedTaskStacks) (task_stack_key incoming) =
    Some (incoming.(stackLeaseRegion), fragments) ->
  UCOS2_full_inv sg state |--
  UCOS2_full_inv sg (os_int_exit_wrapper_restored_state state incoming) **
    task_stack_fragments_rep incoming.(stackLeaseRegion) fragments.
Proof.
  intros sg state incoming fragments Hentry.
  unfold UCOS2_full_inv; Intros.
  assert (Hvalid : UCOS2_full_state_inv sg state) by assumption.
  assert (Hconsistent : parked_stacks_consistent state.(TskState)
    (task_stack_take state.(TskState).(parkedTaskStacks) incoming)).
  { apply task_stack_take_preserves_consistency.
    unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready in Hvalid; tauto. }
  assert (Hupdated : UCOS2_full_state_inv sg (os_int_exit_wrapper_restored_state state incoming)).
  { destruct Hvalid as
      [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hstatus
        [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hold Hpending]]]]]]]]]]]]]]].
    unfold os_int_exit_wrapper_restored_state.
    repeat (split; [assumption|]); exact Hpending. }
  assert (Hsplit : forall st, UCOS2_raw_rep sg st --||--
    store_parked_stacks st.(TskState).(parkedTaskStacks) **
    UCOS2_raw_rep_missing_parked_stacks sg st).
  { intros; unfold UCOS2_raw_rep, UCOS2_raw_rep_missing_parked_stacks, task_shared_rep;
      split; entailer!. }
  rewrite (Hsplit state).
  sep_apply_l_atomic (store_parked_stacks_take_fragments _ _ _ Hentry).
  rewrite (Hsplit (os_int_exit_wrapper_restored_state state incoming)).
  unfold os_int_exit_wrapper_restored_state.
  rewrite UCOS2_raw_rep_missing_parked_stacks_replace_eq; entailer!.
Qed.

Lemma armv7a_irq_raw_live_stack_pointer_load : forall sg state slot node heap,
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_raw_rep sg state heap ->
  pointer_load (task_slot_addr sg slot) node.(tcbStkPtr) heap.
Proof.
  intros sg state slot node heap Hnode Haddress Hraw.
  assert (Hfocus : UCOS2_raw_rep sg state |--
    task_slot_addr sg slot # Ptr |-> node.(tcbStkPtr) ** TT).
  { unfold UCOS2_raw_rep, task_shared_rep.
    sep_apply_l_atomic (task_public_storage_split_saved_sp sg state.(TskState) slot node Hnode).
    cbn [tcb_layout_cell tcb_cell]; rewrite Haddress; entailer!; intros ? ?; exact I. }
  eapply framed_pointer_store_load; exact (Hfocus heap Hraw).
Qed.

Lemma armv7a_irq_restore_pointer_reads_live : forall sg state slot node heap,
  state.(SchedState).(curTaskID) = Some slot ->
  state.(TskState).(inUsedTaskStates) slot = Some node ->
  tcb_field_address (task_slot_addr sg slot) TCBStkPtr = task_slot_addr sg slot ->
  UCOS2_raw_rep sg state heap ->
  armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg slot) node.(tcbStkPtr).
Proof.
  intros sg state slot node heap Hcurrent Hnode Haddress Hraw; split.
  - pose proof (armv7a_irq_raw_current_pointer_load sg state heap Hraw) as Hread.
    rewrite Hcurrent in Hread; exact Hread.
  - eapply armv7a_irq_raw_live_stack_pointer_load; eassumption.
Qed.

Lemma armv7a_irq_restore_pointer_reads_deterministic : forall sg heap tcb sp tcb' sp',
  armv7a_irq_restore_pointer_reads sg heap tcb sp ->
  armv7a_irq_restore_pointer_reads sg heap tcb' sp' -> tcb = tcb' /\ sp = sp'.
Proof.
  intros sg heap tcb sp tcb' sp' [Hcurrent Hsp] [Hcurrent' Hsp'].
  assert (tcb = tcb') by (eapply pointer_load_deterministic; eassumption).
  subst tcb'; split; [reflexivity|eapply pointer_load_deterministic; eassumption].
Qed.

Lemma armv7a_irq_restore_pointer_reads_frame : forall sg heap tcb sp frame whole,
  armv7a_irq_restore_pointer_reads sg heap tcb sp -> join heap frame whole ->
  armv7a_irq_restore_pointer_reads sg whole tcb sp.
Proof. intros sg heap tcb sp frame whole [Hcurrent Hsp] Hjoin;
  split; eapply pointer_load_frame; eassumption. Qed.

(** This is a live-current, same-saved-frame return fragment at an ACTUAL
    masked source cut. [task_current_at] and the saved binding must come
    from the intervening source path; they are not new public preconditions
    or consequences of a CPU token. Free-current and switched destinations
    remain separate paths, not silently removed from the general wrapper.

    The pointer/SP observations are read from this heap. Then the exact
    parked bytes leave the global owner and are consumed with the handler's
    CPU/architecture ownership by the entry-issued linear escrow. Handler
    stack bytes remain an inactive frame. No [outside = raw] bridge is used. *)
Lemma armv7a_irq_wrapper_resumes_saved_call :
  forall external platform port sg context state heap restored_pc,
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_inv sg state ** armv7a_irq_handler_frame external platform port context) heap ->
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    context.(os_int_exit_interrupted_sp) /\
  (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
    (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
      context.(os_int_exit_interrupted_mask) **
     UCOS2_inv sg (os_int_exit_wrapper_restored_state state context.(os_int_exit_interrupted_stack)) **
     task_stack_fragments_rep context.(os_int_exit_handler_stack)
       context.(os_int_exit_handler_fragments))) heap.
Proof.
  intros external platform port sg context state heap restored_pc
    [Hcurrent [node [Hnode Hgeneration]]] [Hparked Hsaved] Haddress Hpc Hbefore.
  split.
  - destruct Hbefore as [owned [frame [Hjoin [[Hvalid Hraw] Hframe]]]].
    rewrite <- (Hsaved node Hnode Hgeneration).
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption.
  - assert (Hreturn : UCOS2_inv sg state ** armv7a_irq_handler_frame external platform port context |--
      coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
        context.(os_int_exit_interrupted_mask) **
       UCOS2_inv sg (os_int_exit_wrapper_restored_state state context.(os_int_exit_interrupted_stack)) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments))).
    { sep_apply_l_atomic (os_int_exit_wrapper_take_destination_resources sg state
        context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_fragments) Hparked).
      unfold armv7a_irq_handler_frame, os_int_exit_context_resources.
      pose proof (os_int_exit_consume_continuation_escrow external platform port context restored_pc Hpc)
        as Hresume.
      unfold os_int_exit_resume_register_input in Hresume.
      sepcon_right_assoc; sep_apply_l_atomic Hresume; Intros; entailer!. }
    exact (Hreturn heap Hbefore).
Qed.

(** Compose the physical OSRunning/counter/lock fragment and these exact
    wrapper reads with the saved continuation's resource consumption. The
    no-schedule condition describes only this branch; it does not restrict
    the OSIntExit public contract or infer that every IRQ returns. *)
Lemma armv7a_irq_no_schedule_resumes_saved_call :
  forall external platform port sg context state heap restored_pc,
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_inv sg state ** armv7a_irq_handler_frame external platform port context) heap ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final
      (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
      context.(os_int_exit_interrupted_sp) /\
    (forall observed_tcb observed_sp,
      armv7a_irq_restore_pointer_reads sg final observed_tcb observed_sp ->
      observed_tcb = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) /\
      observed_sp = context.(os_int_exit_interrupted_sp)) /\
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
        context.(os_int_exit_interrupted_mask) **
       UCOS2_inv sg (os_int_exit_wrapper_restored_state
         (os_int_exit_counter_state state.(SchedState).(isRunning) state)
         context.(os_int_exit_interrupted_stack)) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments))) final.
Proof.
  intros external platform port sg context state heap restored_pc
    Hcurrent Hsaved Hnoschedule Haddress Hpc Hbefore.
  destruct (armv7a_irq_no_schedule_heap_post external platform port sg context state heap
    Hsaved Hnoschedule Hbefore) as [final [Hsource [Hbinding Hafter]]].
  destruct (armv7a_irq_wrapper_resumes_saved_call external platform port sg context
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) final
    restored_pc Hcurrent Hbinding Haddress Hpc Hafter) as [Hreads Hpost].
  exists final; split; [exact Hsource|]. split; [exact Hreads|]. split; [|exact Hpost].
  intros observed_tcb observed_sp Hobserved.
  eapply armv7a_irq_restore_pointer_reads_deterministic; eassumption.
Qed.

Lemma armv7a_irq_wrapper_resumes_saved_call_full :
  forall external platform port sg context state heap restored_pc,
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_full_inv sg state ** armv7a_irq_handler_frame external platform port context) heap ->
  armv7a_irq_restore_pointer_reads sg heap
    (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    context.(os_int_exit_interrupted_sp) /\
  (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
    (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
      context.(os_int_exit_interrupted_mask) **
     UCOS2_full_inv sg (os_int_exit_wrapper_restored_state state context.(os_int_exit_interrupted_stack)) **
     task_stack_fragments_rep context.(os_int_exit_handler_stack)
       context.(os_int_exit_handler_fragments))) heap.
Proof.
  intros external platform port sg context state heap restored_pc
    [Hcurrent [node [Hnode Hgeneration]]] [Hparked Hsaved] Haddress Hpc Hbefore.
  split.
  - destruct Hbefore as [owned [frame [Hjoin [[Hvalid Hraw] Hframe]]]].
    rewrite <- (Hsaved node Hnode Hgeneration).
    eapply armv7a_irq_restore_pointer_reads_frame; [|exact Hjoin].
    eapply armv7a_irq_restore_pointer_reads_live; eassumption.
  - assert (Hreturn : UCOS2_full_inv sg state ** armv7a_irq_handler_frame external platform port context |--
      coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
        context.(os_int_exit_interrupted_mask) **
       UCOS2_full_inv sg (os_int_exit_wrapper_restored_state state context.(os_int_exit_interrupted_stack)) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments))).
    { sep_apply_l_atomic (os_int_exit_wrapper_take_full_destination_resources sg state
        context.(os_int_exit_interrupted_stack) context.(os_int_exit_interrupted_fragments) Hparked).
      unfold armv7a_irq_handler_frame, os_int_exit_context_resources.
      pose proof (os_int_exit_consume_continuation_escrow external platform port context restored_pc Hpc)
        as Hresume.
      unfold os_int_exit_resume_register_input in Hresume.
      sepcon_right_assoc; sep_apply_l_atomic Hresume; Intros; entailer!. }
    exact (Hreturn heap Hbefore).
Qed.

Lemma armv7a_irq_no_schedule_resumes_saved_call_full :
  forall external platform port sg context state heap restored_pc,
  task_current_at state context.(os_int_exit_interrupted_stack).(stackLeaseSlot)
    context.(os_int_exit_interrupted_stack).(stackLeaseGeneration) ->
  os_int_exit_saved_exception_binding context state ->
  interrupt_exit_requests_schedule state.(SchedState).(isRunning) state.(IntrState) = false ->
  tcb_field_address (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
    TCBStkPtr = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) ->
  port.(os_int_exit_frame_return_source) context restored_pc ->
  (UCOS2_full_inv sg state ** armv7a_irq_handler_frame external platform port context) heap ->
  exists final,
    os_int_exit_masked_no_schedule_fragment sg heap final /\
    armv7a_irq_restore_pointer_reads sg final
      (task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot))
      context.(os_int_exit_interrupted_sp) /\
    (forall observed_tcb observed_sp,
      armv7a_irq_restore_pointer_reads sg final observed_tcb observed_sp ->
      observed_tcb = task_slot_addr sg context.(os_int_exit_interrupted_stack).(stackLeaseSlot) /\
      observed_sp = context.(os_int_exit_interrupted_sp)) /\
    (coq_prop (restored_pc = context.(os_int_exit_interrupted_pc)) &&
      (kernel_call_execution_owned external platform (os_int_exit_resumed_call context)
        context.(os_int_exit_interrupted_mask) **
       UCOS2_full_inv sg (os_int_exit_wrapper_restored_state
         (os_int_exit_counter_state state.(SchedState).(isRunning) state)
         context.(os_int_exit_interrupted_stack)) **
       task_stack_fragments_rep context.(os_int_exit_handler_stack)
         context.(os_int_exit_handler_fragments))) final.
Proof.
  intros external platform port sg context state heap restored_pc
    Hcurrent Hsaved Hnoschedule Haddress Hpc Hbefore.
  destruct (os_int_exit_masked_no_schedule_full_frame_post sg state _ heap Hnoschedule Hbefore)
    as [final [Hsource Hafter]].
  destruct (armv7a_irq_wrapper_resumes_saved_call_full external platform port sg context
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) final
    restored_pc Hcurrent Hsaved Haddress Hpc Hafter) as [Hreads Hpost].
  exists final; split; [exact Hsource|]. split; [exact Hreads|]. split; [|exact Hpost].
  intros observed_tcb observed_sp Hobserved.
  eapply armv7a_irq_restore_pointer_reads_deterministic; eassumption.
Qed.
