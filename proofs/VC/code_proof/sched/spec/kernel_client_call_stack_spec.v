Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.task_context.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.interrupt Ucos2Verify.lib.sched.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_call_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.armv7a_irq_return_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A pending-call view of the SAME shared program and stack map. Presence
    is established by the earlier save/deposit, not a new API precondition.
    Coverage is retained for all live tasks, not just the focused caller. *)
Definition kernel_client_call_stack_facts focus payload state : Prop :=
  task_stack_live_coverage state.(TskState) None /\
  state.(TskState).(parkedTaskStacks) (armv7a_call_focus_key focus) = Some payload.

Definition kernel_client_call_stack_world {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg focus payload state : Assertion :=
  coq_prop (kernel_client_call_stack_facts focus payload state) &&
  (kernel_program_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
    state.(TskState).(parkedTaskStacks)).

Definition kernel_client_call_stack_publication {external platform port}
  (abi : Armv7aContinuationABI external platform port) sg publication focus payload state : Assertion :=
  coq_prop (kernel_client_call_stack_facts focus payload state /\ UCOS2_state_inv sg state /\
    task_create_stack_publication_input sg publication state /\
    0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
    0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg).

(** Reuse the existing SOURCE cuts and trace, with a stronger linear view.
    An Extra cut is not coerced to Closed; deletion/switching extensions
    need their own proof and may expose a different resource stage. *)
Definition kernel_client_call_stack_resources {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port)
  (extra_resources : StableGlobVars -> Extra -> UCOS2_Verify_State -> Assertion)
  sg focus payload (cut : KernelClientHeapCut Extra) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_client_call_stack_world abi sg focus payload state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_call_stack_publication abi sg publication focus payload state
  | KernelClientHeapExtra extra => extra_resources sg extra state
  end.

Lemma kernel_client_int_enter_keeps_call_stack : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload state (frame : Assertion) before after,
  (kernel_client_call_stack_world abi sg focus payload state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_call_stack_world abi sg focus payload (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi sg focus payload state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_call_stack_world abi sg focus payload state ** frame |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    (UCOS2_inv sg state ** (unmap_table_rep sg **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [Hfacts Hheap].
  pose proof (kernel_client_int_enter_writes sg state _ before after Hheap Hsource) as Hwrites.
  destruct (os_int_enter_source_heap_frames_private sg state _ before Hheap) as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  match type of Hpost with ?P after =>
    assert (Hmerge : P |-- kernel_client_call_stack_world abi sg focus payload (os_int_enter_state state) ** frame)
  end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
    unfold kernel_client_call_stack_facts in *.
    unfold os_int_enter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hpost).
Qed.

Lemma kernel_client_int_exit_keeps_call_stack : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus payload state (frame : Assertion) before after,
  (kernel_client_call_stack_world abi sg focus payload state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_call_stack_world abi sg focus payload
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi sg focus payload state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_call_stack_world abi sg focus payload state ** frame |--
    coq_prop (kernel_client_call_stack_facts focus payload state) &&
    (UCOS2_inv sg state ** (unmap_table_rep sg **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [Hfacts [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw) as [middle [Hcounter Hraw_after]].
  destruct (os_int_exit_masked_counter_fragment_frame sg owned _ middle rest before Hcounter Hjoin)
    as [produced [Hwhole Hjoined]].
  assert (produced = after).
  { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
  subst produced.
  assert (Hafter : (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
    (unmap_table_rep sg ** armv7a_task_call_stacks abi state.(TskState) focus
      state.(TskState).(parkedTaskStacks) ** frame)) after).
  { exists middle, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
  match type of Hafter with ?P after =>
    assert (Hmerge : P |-- kernel_client_call_stack_world abi sg focus payload
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame)
  end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap.
    unfold kernel_client_call_stack_facts in *.
    unfold os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hafter).
Qed.

(** The five actual publication stores, with their ordered field reads,
    produce the successor world on the supplied execution endpoint. This
    is not a post-state supplied by a handler/ABI contract. *)
Lemma kernel_client_publication_keeps_call_stack : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg publication focus payload state
  (frame : Assertion) before after,
  (kernel_client_call_stack_publication abi sg publication focus payload state ** frame) before ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  kernel_client_step (task_create_stack_publication_client publication) sg state
    (task_create_stack_publication_state sg publication state) /\
  (kernel_client_call_stack_world abi sg focus payload
    (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi sg publication focus payload state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_call_stack_publication abi sg publication focus payload state ** frame |--
    coq_prop (kernel_client_call_stack_facts focus payload state /\ UCOS2_state_inv sg state /\
      task_create_stack_publication_input sg publication state /\
      0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
      0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
    (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
       state publication.(stack_publication_slot) publication.(stack_publication_image) **
     (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
      armv7a_task_call_stacks abi state.(TskState) focus state.(TskState).(parkedTaskStacks) **
      unmap_table_rep sg ** frame))).
  { unfold kernel_client_call_stack_publication; entailer!. }
  destruct (Hsplit before Hpre) as [[[Hcoverage Hfocus] [Hvalid [Hinput [Hpriority Hpointer]]]] Hheap].
  pose proof (proj1 (proj2 (proj2 Hinput))) as Hbinding.
  destruct (task_tcb_init_publication_tail_store_execution sg (task_create_stack_publication_args publication)
    publication.(stack_publication_invocation) publication.(stack_publication_origin)
    publication.(stack_publication_acquired) state publication.(stack_publication_slot)
    publication.(stack_publication_image) _ before Hvalid Hbinding Hpriority Hpointer Hheap)
    as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_client_publication_final_eq; eassumption); subst produced.
  pose proof (task_create_publication_call_stack_merge external platform port abi sg publication state
    focus None payload Hvalid Hinput Hcoverage Hfocus) as Hclose; cbv zeta in Hclose.
  match type of Hpost with ?P after =>
    assert (Hmerge : P |-- kernel_client_call_stack_world abi sg focus payload
      (task_create_stack_publication_state sg publication state) ** frame)
  end.
  { unfold kernel_client_call_stack_world, kernel_client_call_stack_facts.
    rewrite kernel_program_inv_split_unmap; sepcon_assoc_change.
    sep_apply_l_atomic Hclose; Intros; entailer!. }
  split; [split; [exact Hinput|reflexivity]|exact (Hmerge after Hpost)].
Qed.

Definition kernel_client_call_stack_extension_valid {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) : Prop :=
  forall sg (cut : KernelClientHeapCut Extra) before next after state (frame : Assertion),
    extra_step sg cut before next after ->
    (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
    exists returned, extra_effect sg cut state next returned /\
      (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.

Lemma kernel_client_call_stack_step_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload extra_step extra_effect,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  forall sg cut before next after state (frame : Assertion),
  kernel_client_heap_step extra_step sg cut before next after ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned, kernel_client_heap_state_step extra_effect sg cut state next returned /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect Hextra
    sg cut before next after state frame Hsource Hpre; destruct Hsource.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_keeps_call_stack; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    eapply kernel_client_int_exit_keeps_call_stack; eassumption.
  - exists (task_create_stack_publication_state sg publication state).
    destruct (kernel_client_publication_keeps_call_stack external platform port abi sg publication
      focus payload state frame before after Hpre H) as [[Hinput Hstate] Hpost].
    split; [constructor; exact Hinput|exact Hpost].
  - destruct (Hextra sg cut before next after state frame H Hpre) as [returned [Heffect Hpost]].
    exists returned; split; [constructor; exact Heffect|exact Hpost].
Qed.

(** Same concrete endpoints and source actions as the existing registry;
    no weak-map result is upgraded to a focused entry. *)
Lemma kernel_client_call_stack_trace_source_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload extra_step extra_effect
  clients sg observer event_observer,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  forall cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect clients sg observer
    event_observer Hspatial Henter Hexit Hpublish Hextra cut before next after frame Htrace.
  induction Htrace; intros state origin Hcompatible Hpre.
  - exists state, false, origin; split; [constructor|].
    split; [constructor|]. split; assumption.
  - destruct (kernel_client_call_stack_step_resources external platform port Extra abi extra_resources focus payload extra_step
      extra_effect Hspatial sg cut before middle_cut middle state frame H Hpre)
      as [middle_state [Hstep Hmiddle]].
    destruct (kernel_client_heap_state_step_source external port Extra clients sg observer event_observer
      extra_effect Henter Hexit Hpublish Hextra cut state middle_cut middle_state origin Hcompatible Hstep)
      as [Hmiddle_compatible [stop1 [middle_origin Hsource]]].
    destruct (IHHtrace middle_state middle_origin Hmiddle_compatible Hmiddle)
      as [returned [stop2 [returned_origin [Htail [Htail_source [Hfinal_compatible Hpost]]]]]].
    exists returned, (orb stop1 stop2), returned_origin; split.
    + econstructor; eassumption.
    + split.
      * eapply kernel_resumption_task_source_trace_trans; eassumption.
      * split; assumption.
Qed.

(** Thread the actual execution origin through the same finite physical
    trace.  The pending observer is independent of that origin.  A cut
    binding is established at entry and by each concrete extension; the
    theorem does not require the final origin to be the observer or claim
    eventual selection.  Original caller-local Save/inside resources may
    remain in [frame] throughout. *)
Lemma kernel_client_call_stack_trace_execution_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload extra_source
  extra_step extra_effect clients sg observer event_observer,
  @kernel_client_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_execution_source external port clients sg observer event_observer
    extra_source extra_effect ->
  forall cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_source_cut extra_source cut origin state ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    kernel_client_heap_source_cut extra_source next returned_origin returned /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_source extra_step extra_effect
    clients sg observer event_observer Hspatial Henter Hexit Hpublish Hextra
    cut before next after frame Htrace.
  induction Htrace; intros state origin Hobserver Hcurrent Hpre.
  - exists state, false, origin; split; [constructor|].
    split; [constructor|]. split; [exact Hobserver|].
    split; [exact Hcurrent|exact Hpre].
  - destruct (kernel_client_call_stack_step_resources external platform port Extra abi extra_resources focus payload
      extra_step extra_effect Hspatial sg cut before middle_cut middle state frame H Hpre)
      as [middle_state [Hstep Hmiddle]].
    destruct (kernel_client_heap_state_step_execution_source external port Extra clients sg observer event_observer
      extra_source extra_effect Henter Hexit Hpublish Hextra
      cut state middle_cut middle_state origin Hobserver Hcurrent Hstep)
      as [Hmiddle_observer [stop1 [middle_origin [Hsource Hmiddle_current]]]].
    destruct (IHHtrace middle_state middle_origin Hmiddle_observer Hmiddle_current Hmiddle)
      as [returned [stop2 [returned_origin [Htail [Htail_source [Hfinal_observer [Hfinal_current Hpost]]]]]]].
    exists returned, (orb stop1 stop2), returned_origin; split.
    + econstructor; eassumption.
    + split.
      * eapply kernel_resumption_task_source_trace_trans; eassumption.
      * split; [exact Hfinal_observer|]. split; [exact Hfinal_current|exact Hpost].
Qed.

(** Local handler steps use their real private-heap frame rule. Registered
    segments use the concrete OS producers above, retaining one pending
    call and the whole map throughout the same source cursor trace. *)
Lemma kernel_client_handler_call_stack_resources : forall external platform port Cursor Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload extra_step extra_effect
  (private : Cursor -> Assertion) local_step segment,
  @kernel_client_call_stack_extension_valid external platform port Extra abi extra_resources focus payload extra_step extra_effect ->
  (forall sg cursor cut before returned_cursor next after,
    segment sg cursor cut before returned_cursor next after ->
    kernel_client_heap_step extra_step sg cut before next after) ->
  (forall sg cursor cut before returned_cursor next after,
    segment sg cursor cut before returned_cursor next after -> private cursor = private returned_cursor) ->
  (forall cursor before returned_cursor after (frame : Assertion),
    local_step cursor before returned_cursor after ->
    (private cursor ** frame) before -> (private returned_cursor ** frame) after) ->
  forall sg cursor cut before returned_cursor next after (frame : Assertion),
  kernel_client_handler_trace local_step segment sg cursor cut before returned_cursor next after ->
  forall state,
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** private cursor ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned ** private returned_cursor ** frame) after.
Proof.
  intros external platform port Cursor Extra abi extra_resources focus payload extra_step extra_effect private
    local_step segment Hextra Hsegment Hprivate Hlocal sg cursor cut before returned_cursor next after frame Hrun.
  induction Hrun; intros state Hpre.
  - exists state; split; [constructor|exact Hpre].
  - assert (Horder : kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** private cursor ** frame |--
      private cursor ** (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame)) by entailer!.
    pose proof (Hlocal _ _ _ _ _ H (Horder before Hpre)) as Hmiddle.
    assert (Hback : private middle_cursor ** (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** frame) |--
      kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** private middle_cursor ** frame) by entailer!.
    exact (IHHrun state (Hback middle Hmiddle)).
  - assert (Horder : kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** private cursor ** frame |--
      kernel_client_call_stack_resources abi extra_resources sg focus payload cut state ** (private cursor ** frame)) by entailer!.
    destruct (kernel_client_call_stack_step_resources external platform port Extra abi extra_resources focus payload extra_step extra_effect
      Hextra sg cut before middle_cut middle state (private cursor ** frame)
      (Hsegment sg cursor cut before middle_cursor middle_cut middle H) (Horder before Hpre))
      as [middle_state [Heffect Hmiddle]].
    rewrite (Hprivate sg cursor cut before middle_cursor middle_cut middle H) in Hmiddle.
    assert (Hback : kernel_client_call_stack_resources abi extra_resources sg focus payload middle_cut middle_state **
        (private middle_cursor ** frame) |--
      kernel_client_call_stack_resources abi extra_resources sg focus payload middle_cut middle_state ** private middle_cursor ** frame)
      by entailer!.
    destruct (IHHrun middle_state (Hback middle Hmiddle)) as [returned [Htail Hpost]].
    exists returned; split; [econstructor; eassumption|exact Hpost].
Qed.

(** At the actual wrapper selection boundary, read and consume the call
    retained through the handler. The live-current condition describes
    THIS branch; neither this lemma nor the registry says every exit
    selects the interrupted task. OSUnMapTbl remains owned exactly once. *)
Lemma kernel_client_call_stack_resume : forall external platform port
  (abi : Armv7aContinuationABI external platform port) sg focus fragments state handler
  (frame : Assertion) heap,
  let incoming := focus.(armv7a_focus_call).(os_sched_call_stack) in
  task_current_at state incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
  tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
    task_slot_addr sg incoming.(stackLeaseSlot) ->
  (kernel_client_call_stack_world abi sg focus (incoming.(stackLeaseRegion), fragments) state **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) heap ->
  let restored := os_int_exit_wrapper_restored_state state incoming in
  exists saved,
    armv7a_irq_restore_pointer_reads sg heap (task_slot_addr sg incoming.(stackLeaseSlot))
      saved.(armv7a_continuation_sp) /\
    armv7a_continuation_focus_binding focus saved /\
    task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
    (forall final, armv7a_restore_transition abi handler saved heap final ->
      final.(ConAssertion.s_mem) = heap.(ConAssertion.s_mem) /\
      (kernel_call_execution_owned external platform
         (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
         (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
       task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
       (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
         restored.(TskState) restored.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) final).
Proof.
  intros external platform port abi sg focus fragments state handler frame heap incoming
    [Hcurrent [node [Hnode Hgen]]] Haddress Hpre restored.
  match type of Hpre with ?P heap =>
    assert (Hsplit : P |--
      coq_prop (kernel_client_call_stack_facts focus (incoming.(stackLeaseRegion), fragments) state) &&
      (UCOS2_inv sg state ** armv7a_task_call_stacks abi state.(TskState) focus
        state.(TskState).(parkedTaskStacks) **
       (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
        os_int_exit_context_resources port handler ** (unmap_table_rep sg ** frame))))
  end.
  { unfold kernel_client_call_stack_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit heap Hpre) as [[Hcoverage Hlookup] Hheap].
  exact (armv7a_irq_wrapper_resume_call external platform port abi sg state focus incoming fragments
    node handler (unmap_table_rep sg ** frame) heap Hcurrent Hnode Hgen Hlookup eq_refl
    Haddress Hcoverage Hheap).
Qed.

(** Real finite client execution followed by the selected original-call
    return. The resource and state traces use the SAME heap endpoints.
    The final branch must actually select the live generation of this
    call. Other selections, deleting clients and switching intervals stay
    separate; they are not ruled out by a stronger public API contract. *)
Lemma kernel_client_call_stack_trace_return : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus fragments extra_step extra_effect,
  let incoming := focus.(armv7a_focus_call).(os_sched_call_stack) in
  @kernel_client_call_stack_extension_valid external platform port Extra abi extra_resources focus
    (incoming.(stackLeaseRegion), fragments) extra_step extra_effect ->
  forall sg cut before after state handler (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before KernelClientHeapClosed after ->
  (kernel_client_call_stack_resources abi extra_resources sg focus (incoming.(stackLeaseRegion), fragments)
      cut state **
   (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
    os_int_exit_context_resources port handler ** frame)) before ->
  exists returned,
    kernel_client_heap_state_trace extra_effect sg cut state KernelClientHeapClosed returned /\
    (kernel_client_call_stack_world abi sg focus (incoming.(stackLeaseRegion), fragments) returned **
     (interrupt_platform_running platform handler.(os_int_exit_invocation) handler.(os_int_exit_origin) 192 **
      os_int_exit_context_resources port handler ** frame)) after /\
    (task_current_at returned incoming.(stackLeaseSlot) incoming.(stackLeaseGeneration) ->
     tcb_field_address (task_slot_addr sg incoming.(stackLeaseSlot)) TCBStkPtr =
       task_slot_addr sg incoming.(stackLeaseSlot) ->
     let restored := os_int_exit_wrapper_restored_state returned incoming in
     exists saved,
       armv7a_irq_restore_pointer_reads sg after (task_slot_addr sg incoming.(stackLeaseSlot))
         saved.(armv7a_continuation_sp) /\
       armv7a_continuation_focus_binding focus saved /\
       task_stack_live_coverage restored.(TskState) (Some (task_stack_key incoming)) /\
       (forall final, armv7a_restore_transition abi handler saved after final ->
         final.(ConAssertion.s_mem) = after.(ConAssertion.s_mem) /\
         (kernel_call_execution_owned external platform
            (armv7a_continuation_resumed_call saved focus.(armv7a_focus_call))
            (armv7a_irq_fiq_mask saved.(armv7a_continuation_cpsr)) **
          task_stack_fragments_rep handler.(os_int_exit_handler_stack) handler.(os_int_exit_handler_fragments) **
          (UCOS2_inv sg restored ** armv7a_task_stack_continuations abi
            restored.(TskState) restored.(TskState).(parkedTaskStacks) ** (unmap_table_rep sg ** frame))) final)).
Proof.
  intros external platform port Extra abi extra_resources focus fragments extra_step extra_effect
    incoming Hextra sg cut before after state handler frame Htrace Hpre.
  assert (Htransport : forall first_cut first next_cut last,
    kernel_client_heap_trace extra_step sg first_cut first next_cut last ->
    forall initial (rest : Assertion),
    (kernel_client_call_stack_resources abi extra_resources sg focus (incoming.(stackLeaseRegion), fragments)
      first_cut initial ** rest) first ->
    exists final_state, kernel_client_heap_state_trace extra_effect sg first_cut initial next_cut final_state /\
      (kernel_client_call_stack_resources abi extra_resources sg focus (incoming.(stackLeaseRegion), fragments)
        next_cut final_state ** rest) last).
  { intros first_cut first next_cut last Hrun; induction Hrun; intros initial rest Howned.
    - exists initial; split; [constructor|exact Howned].
    - destruct (kernel_client_call_stack_step_resources external platform port Extra abi extra_resources
        focus (incoming.(stackLeaseRegion), fragments) extra_step extra_effect Hextra sg cut0 before0
        middle_cut middle initial rest H Howned) as [middle_state [Hstep Hmiddle]].
      destruct (IHHrun middle_state rest Hmiddle) as [final_state [Htail Hpost]].
      exists final_state; split; [econstructor; eassumption|exact Hpost]. }
  destruct (Htransport _ _ _ _ Htrace state _ Hpre) as [returned [Hstate Hpost]].
  exists returned; split; [exact Hstate|]. split; [exact Hpost|].
  intros Hcurrent Haddress.
  eapply kernel_client_call_stack_resume; eassumption.
Qed.

