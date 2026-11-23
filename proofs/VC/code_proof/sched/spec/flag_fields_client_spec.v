Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.kernel_program_storage Ucos2Verify.lib.kernel_heap_storage.
Require Import Ucos2Verify.lib.kernel_heap_execution.
Require Import Ucos2Verify.lib.kernel_heap_observation.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.flag_fields_resources.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_saved_continuation_publication_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_coverage_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_sched_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_stack_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.flag_fields_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_irq_source_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.flag_fields_counter_heap_spec.
(* The publication companion is an installed checked dependency in this workspace. *)
Require Import Ucos2Verify.VC.code.task.spec.flag_fields_publication_spec.
Import UCOS2_C_Rules TaskStateDef KernelHeapStorage KernelHeapObservation ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** The checked counter companion owns the fields Closed world and its
    OSIntEnter/OSIntExit resource transports.  Reuse that exact world here
    so the client trace and the counter proof share one spatial object. *)

(** The prepared publication cut uses the checked six-field publication
    producer.  The publication branch is a real TCBInit tail cut; it is not
    inferred from a closed cut and it does not allocate a whole registry. *)
Definition kernel_client_continuation_fields_publication {external platform port}
  (abi : Armv7aContinuationABI external platform port) local sg publication state : Assertion :=
  coq_prop (UCOS2_state_inv sg state /\
    task_stack_live_coverage state.(TskState) None /\
    task_create_stack_publication_input sg publication state /\
    0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
    0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
  (task_tcb_init_publication_fields_tail_storage sg
      (task_create_stack_publication_args publication) state
      publication.(stack_publication_slot) publication.(stack_publication_image) **
   task_stack_storage publication.(stack_publication_region)
      (task_create_stack_publication_words publication) **
   local (task_create_stack_publication_continuation publication) **
   store_parked_continuations
      (kernel_saved_continuation_entry abi state.(TskState) local)
      state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg).

(** [Extra=False] is the built-in instance only.  This interpretation keeps
    the registry's extra-cut type available without asserting that every
    public client is covered by this candidate. *)
Definition kernel_client_continuation_fields_resources {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) local sg
  (cut : KernelClientHeapCut Extra) state : Assertion :=
  match cut with
  | KernelClientHeapClosed =>
      kernel_client_continuation_fields_world abi local sg state
  | KernelClientHeapTaskPublication publication =>
      kernel_client_continuation_fields_publication abi local sg publication state
  | KernelClientHeapExtra _ => coq_prop False && emp
  end.

(** This is the exact one-step resource obligation consumed by the trace
    theorem below.  The checked counter companion discharges the first two constructors with
    the real OSIntEnter/OSIntExit fields transports; the checked publication
    companion discharges the third constructor. *)
Definition kernel_client_fields_resource_guarantee {Extra}
  (resources : StableGlobVars -> KernelClientHeapCut Extra ->
    UCOS2_Verify_State -> Assertion)
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
    KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra ->
    UCOS2_Verify_State -> KernelClientHeapCut Extra ->
    UCOS2_Verify_State -> Prop) : Prop :=
  forall sg cut before next after state (frame : Assertion),
    kernel_client_heap_step extra_step sg cut before next after ->
    (resources sg cut state ** frame) before ->
    exists returned,
      kernel_client_heap_state_step extra_effect sg cut state next returned /\
      (resources sg next returned ** frame) after.

(** Built-in one-step transport.  The Enter and Exit branches call the
    checked counter companion's actual fields resource consumers; the
    publication branch calls the checked TCB publication source.  Extra=False
    remains this candidate's builtin instance and does not close the public
    registry. *)
Definition kernel_client_builtin_fields_resource_guarantee
  {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) local : Prop :=
  @kernel_client_fields_resource_guarantee Extra
    (fun sg cut state =>
      kernel_client_continuation_fields_resources abi local sg cut state)
    (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False).

Lemma kernel_client_builtin_fields_resource_guarantee_proof :
  forall external platform port Extra
    (abi : Armv7aContinuationABI external platform port) local,
  @kernel_client_fields_resource_guarantee Extra
    (fun sg cut state =>
      kernel_client_continuation_fields_resources abi local sg cut state)
    (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False).
Proof.
  intros external platform port Extra abi local sg cut before next after state frame Hstep Hpre.
  destruct Hstep.
  - exists (os_int_enter_state state); split; [constructor|].
    eapply kernel_client_int_enter_continuation_fields_resources; eassumption.
  - exists (os_int_exit_counter_state state.(SchedState).(isRunning) state).
    split; [constructor|].
    eapply kernel_client_int_exit_continuation_fields_resources; eassumption.
  - assert (Hsplit :
      kernel_client_continuation_fields_publication abi local sg publication state ** frame |--
      coq_prop (UCOS2_state_inv sg state /\
        task_stack_live_coverage state.(TskState) None /\
        task_create_stack_publication_input sg publication state /\
        0 <= (task_create_stack_publication_args publication).(initPrio) < 64 /\
        0 <= task_slot_addr sg publication.(stack_publication_slot) < 4294967296) &&
      (task_tcb_init_publication_fields_tail_storage sg
          (task_create_stack_publication_args publication) state
          publication.(stack_publication_slot) publication.(stack_publication_image) **
       (task_stack_storage publication.(stack_publication_region)
          (task_create_stack_publication_words publication) **
        local (task_create_stack_publication_continuation publication) **
        store_parked_continuations
          (kernel_saved_continuation_entry abi state.(TskState) local)
          state.(TskState).(parkedTaskStacks) ** unmap_table_rep sg ** frame))).
    { unfold kernel_client_continuation_fields_publication; entailer!. }
    destruct (Hsplit before Hpre)
      as [[Hvalid [Hcoverage [Hinput [Hpriority Hpointer]]]] Hheap].
    destruct (kernel_task_publication_continuation_fields_source
      external platform port abi sg publication state local None frame before after
      Hvalid Hinput Hcoverage Hpriority Hpointer Hheap H)
      as [Hstep [Hcovered Howned]].
    exists (task_create_stack_publication_state sg publication state); split.
    + constructor; exact Hinput.
    + match type of Howned with ?P after =>
        assert (Hmerge : P |--
          kernel_client_continuation_fields_world abi local sg
            (task_create_stack_publication_state sg publication state) ** frame)
      end.
      { unfold kernel_client_continuation_fields_world, kernel_continuation_inv.
        entailer!. }
      exact (Hmerge after Howned).
  - contradiction.
Qed.

(** Same-heap trace transport for the fields resource family.  The state
    trace and returned heap are generated from the identical [kernel_client_heap_trace]
    path; no endpoint or future return is postulated. *)
Lemma kernel_client_fields_trace_resource_guarantee :
  forall Extra resources extra_step extra_effect,
  @kernel_client_fields_resource_guarantee Extra resources extra_step extra_effect ->
  forall sg cut before next after (frame : Assertion),
  @kernel_client_heap_trace Extra extra_step sg cut before next after ->
  forall state,
  (resources sg cut state ** frame) before ->
  exists returned,
    @kernel_client_heap_state_trace Extra extra_effect sg cut state next returned /\
    (resources sg next returned ** frame) after.
Proof.
  intros Extra resources extra_step extra_effect Hmodules sg cut before next after frame Htrace.
  induction Htrace; intros state Hpre.
  - exists state; split; [constructor|exact Hpre].
  - destruct (Hmodules sg cut before middle_cut middle state frame H Hpre)
      as [middle_state [Hstep Hmiddle]].
    destruct (IHHtrace middle_state Hmiddle) as [returned [Htail Hpost]].
    exists returned; split; [econstructor; eassumption|exact Hpost].
Qed.

(** Closed-start builtin trace consumer.  Its one-step premise is the
    concrete counter/publication guarantee above; [Extra=False] only expresses
    this candidate's builtin subfamily and says nothing about the complete
    client registry. *)
Lemma kernel_client_builtin_closed_fields_trace_resources :
  forall external platform port Extra
    (abi : Armv7aContinuationABI external platform port) local,
  @kernel_client_builtin_fields_resource_guarantee external platform port Extra abi local ->
  forall sg before after (frame : Assertion),
  @kernel_client_heap_trace Extra (fun _ _ _ _ _ => False) sg
    KernelClientHeapClosed before KernelClientHeapClosed after ->
  forall state,
  (@kernel_client_continuation_fields_resources external platform port Extra abi local sg
      (@KernelClientHeapClosed Extra) state ** frame) before ->
  exists returned,
    @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
      KernelClientHeapClosed state KernelClientHeapClosed returned /\
    (@kernel_client_continuation_fields_resources external platform port Extra abi local sg
      (@KernelClientHeapClosed Extra) returned ** frame) after.
Proof.
  intros external platform port Extra abi local Hmodules sg before after frame Htrace.
  intros state Hpre.
  eapply kernel_client_fields_trace_resource_guarantee; eassumption.
Qed.

(** A closed trace cannot manufacture a publication or extra cut when its
    effect is [False].  This pure projection is useful to callers that keep
    the actual IRQ save/take/restore source conditions outside this candidate. *)
Lemma kernel_client_builtin_closed_fields_trace_task_projection :
  forall Extra sg cut state next returned,
  @kernel_client_heap_state_trace Extra (fun _ _ _ _ _ => False) sg
    cut state next returned ->
  cut = KernelClientHeapClosed ->
  next = KernelClientHeapClosed /\
    returned.(TskState) = state.(TskState) /\
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

(** IRQ-chain dependency boundary.  The real save endpoint, same-heap
    counter trace, and take/restore endpoint remain the source conditions in
    [flag_fields_irq_source_spec] (notably
    [flag_source_fields_irq_save_resources],
    [flag_source_fields_irq_take_resources], and
    [flag_source_fields_irq_restore_resources]).  The checked counter
    companion supplies [os_int_enter_source_heap_fields_raw_post], its
    frame/private continuation, and [os_int_exit_counter_heap_fields_raw_post]
    plus its frame/private continuation, and the builtin proof above consumes
    its continuation resource lemmas.  This candidate deliberately leaves
    that dependency explicit and does not claim a complete registry or public
    API closure. *)
