Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_program_call_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The same parked map retains every descriptor's existing local owner.
    Publication consumes its new descriptor's local explicitly; the actual
    initial-entry instance below its caller supplies None = emp. No law is
    imposed on [local], and historical entries need not remain active. *)
Definition kernel_client_continuation_world {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg state : Assertion :=
  coq_prop (task_stack_live_coverage state.(TskState) None) &&
  (kernel_program_inv sg state **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks)).

Definition kernel_client_continuation_publication {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg publication state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) None /\
    task_create_stack_publication_input sg publication state /\
    0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
    0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
  (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
     state publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
   local (task_create_stack_publication_continuation publication) **
   store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
     state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg).

(** This file checks the existing built-in SOURCE subfamily. Extra cuts
    retain their place in the registry type, but have no execution rule in
    this subfamily. Extending it requires the corresponding actual source
    producer, not a universal local-preservation ABI/environment law. *)
Definition kernel_client_continuation_resources {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) local sg
  (cut : KernelClientHeapCut Extra) state : Assertion :=
  match cut with
  | KernelClientHeapClosed => kernel_client_continuation_world abi local sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_publication abi local sg publication state
  | KernelClientHeapExtra _ => coq_prop False && emp
  end.

Lemma kernel_client_int_enter_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg state (frame : Assertion) before after,
  (kernel_client_continuation_world abi local sg state ** frame) before ->
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_continuation_world abi local sg (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi local sg state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_continuation_world abi local sg state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) None) &&
    (UCOS2_inv sg state ** (unmap_table_rep sg **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [Hcoverage Hheap].
  pose proof (kernel_client_int_enter_writes sg state _ before after Hheap Hsource) as Hwrites.
  destruct (os_int_enter_source_heap_frames_private sg state _ before Hheap)
    as [produced [Hrun Hpost]].
  assert (produced = after) by (eapply kernel_heap_execution_deterministic; eassumption); subst produced.
  match type of Hpost with ?P after => assert (Hmerge : P |--
    kernel_client_continuation_world abi local sg (os_int_enter_state state) ** frame) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap.
    unfold os_int_enter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hpost).
Qed.

Lemma kernel_client_int_exit_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg state (frame : Assertion) before after,
  (kernel_client_continuation_world abi local sg state ** frame) before ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_continuation_world abi local sg
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi local sg state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_continuation_world abi local sg state ** frame |--
    coq_prop (task_stack_live_coverage state.(TskState) None) &&
    (UCOS2_inv sg state ** (unmap_table_rep sg **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** frame))).
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap; entailer!. }
  destruct (Hsplit before Hpre) as [Hcoverage [owned [rest [Hjoin [[Hvalid Hraw] Hrest]]]]].
  destruct (os_int_exit_masked_counter_raw_post sg state owned Hraw) as [middle [Hcounter Hraw_after]].
  destruct (os_int_exit_masked_counter_fragment_frame sg owned _ middle rest before Hcounter Hjoin)
    as [produced [Hwhole Hjoined]].
  assert (produced = after).
  { destruct Hsource; eapply os_int_exit_masked_counter_final_eq; eassumption. }
  subst produced.
  assert (Hafter : (UCOS2_inv sg (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
    (unmap_table_rep sg **
     store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
       state.(TskState).(parkedTaskStacks) ** frame)) after).
  { exists middle, rest; split; [exact Hjoined|]. split; [split; assumption|exact Hrest]. }
  match type of Hafter with ?P after => assert (Hmerge : P |--
    kernel_client_continuation_world abi local sg
      (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) end.
  { unfold kernel_client_continuation_world; rewrite kernel_program_inv_split_unmap.
    unfold os_int_exit_counter_state; cbn [replace_IntrS TskState]; entailer!. }
  exact (Hmerge after Hafter).
Qed.

Lemma kernel_client_publication_continuation_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) local sg publication state
  (frame : Assertion) before after,
  (kernel_client_continuation_publication abi local sg publication state ** frame) before ->
  task_tcb_init_publication_tail_fragment sg (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  kernel_client_step (task_create_stack_publication_client publication) sg state
    (task_create_stack_publication_state sg publication state) /\
  (kernel_client_continuation_world abi local sg
    (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi local sg publication state frame before after Hpre Hsource.
  assert (Hsplit : kernel_client_continuation_publication abi local sg publication state ** frame |--
    coq_prop (UCOS2_state_inv sg state /\ task_stack_live_coverage state.(TskState) None /\
      task_create_stack_publication_input sg publication state /\
      0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
      0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
    (task_tcb_init_publication_tail_storage sg (task_create_stack_publication_args publication)
       state publication.(stack_publication_slot) publication.(stack_publication_image) **
     (task_stack_storage publication.(stack_publication_region) (task_create_stack_publication_words publication) **
      local (task_create_stack_publication_continuation publication) **
      store_parked_continuations (kernel_saved_continuation_entry abi state.(TskState) local)
        state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
  { unfold kernel_client_continuation_publication; entailer!. }
  destruct (Hsplit before Hpre) as [[Hvalid [Hcoverage [Hinput [Hpriority Hpointer]]]] Hheap].
  destruct (kernel_task_publication_continuation_source external platform port abi sg publication state
    local None frame before after Hvalid Hinput Hcoverage Hpriority Hpointer Hheap Hsource)
    as [Hstep [Hcovered Howned]].
  split; [exact Hstep|].
  match type of Howned with ?P after => match goal with |- ?Q after =>
    assert (Hmerge : P |-- Q) end end.
  { unfold kernel_client_continuation_world; entailer!. }
  exact (Hmerge after Howned).
Qed.

Lemma kernel_client_continuation_step_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) local sg cut before next after state (frame : Assertion),
  @kernel_client_heap_step Extra (fun _ _ _ _ _ => False) sg cut before next after ->
  (kernel_client_continuation_resources abi local sg cut state ** frame) before ->
  exists returned, kernel_client_heap_state_step (fun _ _ _ _ _ => False) sg cut state next returned /\
    (kernel_client_continuation_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port Extra abi local sg cut before next after state frame Hstep Hpre.
  destruct Hstep.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_continuation_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    eapply kernel_client_int_exit_continuation_resources; eassumption.
  - destruct (kernel_client_publication_continuation_resources external platform port abi local sg
      publication state frame before after Hpre H) as [[Hinput Hstate] Hpost].
    exists (task_create_stack_publication_state sg publication state); split; [constructor; exact Hinput|exact Hpost].
  - contradiction.
Qed.

Lemma kernel_client_builtin_step_task_source : forall external port Extra clients sg observer event_observer,
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  forall cut state next returned origin,
  kernel_client_heap_observer_cut observer cut ->
  @kernel_client_heap_state_step Extra (fun _ _ _ _ _ => False) sg cut state next returned ->
  kernel_client_heap_observer_cut observer next /\
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin state false origin returned.
Proof.
  intros external port Extra clients sg observer event_observer Henter Hexit Hpublish
    cut state next returned origin Hobserver Hstep; destruct Hstep.
  - split; [exact I|].
    change (kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state (kernel_client_stops (kernel_full_profile_cut_client KernelFullIntEnter) observer)
      origin (os_int_enter_state state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + exact Henter.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + reflexivity.
  - split; [exact I|].
    change (kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state (kernel_client_stops
        (kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))) observer)
      origin (os_int_exit_counter_state state.(SchedState).(isRunning) state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + apply Hexit.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + reflexivity.
  - split; [exact I|].
    change (kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state (kernel_client_stops (task_create_stack_publication_client publication) observer)
      origin (task_create_stack_publication_state sg publication state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := task_create_stack_publication_client publication).
    + apply Hpublish.
    + cbn [task_create_stack_publication_client kernel_client_actor].
      cbn [kernel_client_heap_observer_cut] in Hobserver; congruence.
    + intros; discriminate.
    + split; [exact H|reflexivity].
    + apply task_create_stack_publication_current_pointer_eq.
    + reflexivity.
  - contradiction.
Qed.

(** The heap proof produces the state trace, and THAT SAME trace produces
    the source observation. No endpoint resource or future return is
    postulated. Publication is supported at its real prepared source cut. *)
Lemma kernel_client_continuation_trace_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) local clients sg observer event_observer,
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  forall cut before next after (frame : Assertion),
  @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (kernel_client_continuation_resources abi local sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace (fun _ _ _ _ _ => False) sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state false origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_continuation_resources abi local sg next returned ** frame) after.
Proof.
  intros external platform port Extra abi local clients sg observer event_observer Henter Hexit Hpublish
    cut before next after frame Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state; split; [constructor|]. split; [constructor|]. split; assumption.
  - destruct (kernel_client_continuation_step_resources external platform port Extra abi local sg
      cut before middle_cut middle state frame H Hpre) as [middle_state [Hstep Hmiddle]].
    destruct (kernel_client_builtin_step_task_source external port Extra clients sg observer event_observer
      Henter Hexit Hpublish cut state middle_cut middle_state origin Hobserver Hstep)
      as [Hmiddle_observer Hsource].
    destruct (IHHtrace middle_state origin Hmiddle_observer Hmiddle)
      as [returned [Hstates [Htail [Hfinal_observer Hpost]]]].
    exists returned; split; [econstructor; eassumption|]. split.
    + change (kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin state (orb false false) origin returned).
      eapply kernel_resumption_task_source_trace_trans; eassumption.
    + split; assumption.
Qed.

(** With no Extra source transition, a Closed-start trace cannot invent a
    private publication cut. The actual IRQ consumer below uses this
    counter-only subcase; the publication producer above is separately
    available at a real TCBInit publication cut. *)
Lemma kernel_client_builtin_closed_trace_task_fields : forall Extra sg cut state next returned,
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg cut state next returned ->
  cut = KernelClientHeapClosed ->
  next = KernelClientHeapClosed /\ returned.(TskState) = state.(TskState) /\
    returned.(SchedState) = state.(SchedState).
Proof.
  intros Extra sg cut state next returned Htrace; induction Htrace; intros Hclosed.
  - subst cut; repeat split; reflexivity.
  - destruct H; try discriminate; try contradiction.
    + destruct (IHHtrace eq_refl) as [Hnext [Htasks Hsched]].
      split; [exact Hnext|]. split; [rewrite Htasks|rewrite Hsched]; reflexivity.
    + destruct (IHHtrace eq_refl) as [Hnext [Htasks Hsched]].
      split; [exact Hnext|]. split; [rewrite Htasks|rewrite Hsched]; reflexivity.
Qed.
