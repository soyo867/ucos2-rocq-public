Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.timer_execution.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_masked_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_publication_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_spec.
Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** A non-switching source fragment has one registered action on the SAME
    state edge as its concrete heap proof. This lemma is not an assertion
    that arbitrary registered clients frame OSTCBCur. Switching clients
    must instead supply the ordered transfer constructors in task_resume.
    Actor and stop information is retained, not inferred from validity. *)
Lemma kernel_client_framed_step_resumption_source :
  forall external port clients sg observer event_observer origin action before after,
  clients action ->
  kernel_client_actor action <> Some observer ->
  (forall invocation, event_observer = Some invocation ->
    kernel_client_event_actor action <> Some invocation) ->
  kernel_client_step action sg before after ->
  before.(SchedState).(curTaskID) = after.(SchedState).(curTaskID) ->
  before.(TimerState) = after.(TimerState) ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin before (kernel_client_stops action observer) origin after.
Proof.
  intros external port clients sg observer event_observer origin action before after
    Hin Hactor Hevent Hstep Hcurrent Htimer.
  rewrite <- (Bool.orb_false_r (kernel_client_stops action observer)).
  eapply KernelResumptionTaskSourceSegment.
  - rewrite <- (Bool.orb_false_r (kernel_client_stops action observer)).
    eapply KernelClientTaskSourceStep; try eassumption.
    + eapply TaskExecutionClientFrame; eassumption.
    + constructor.
  - rewrite Htimer; constructor.
  - constructor.
Qed.

(** The observer names the invocation whose resources are being retained.
    The source origin instead names the task actually selected at this cut.
    Extra cuts can retain the more precise call/phase binding established
    by their source producer.  Closed and publication cuts only observe
    the existing current-pointer relation; Boot remains admissible. *)
Definition kernel_client_heap_source_cut {Extra}
  (extra_source : Extra -> TaskStateDef.TaskInvocationOrigin -> UCOS2_Verify_State -> Prop)
  (cut : KernelClientHeapCut Extra) origin state : Prop :=
  task_execution_current origin state /\
  match cut with
  | KernelClientHeapExtra extra => extra_source extra origin state
  | _ => True
  end.

(** Only a publication cut carries a Task actor in the built-in registry.
    The real caller/handler source must identify that actor. This predicate
    filters neither C error paths nor allocations: it is the existing
    observer condition of the registered trace, made explicit at that cut. *)
Definition kernel_client_heap_observer_cut {Extra} (observer : nat)
  (cut : KernelClientHeapCut Extra) : Prop :=
  match cut with
  | KernelClientHeapTaskPublication publication =>
      publication.(stack_publication_invocation) <> observer
  | _ => True
  end.

(** An OS extension must prove this from its own source effects, in
    addition to its spatial extension theorem. It is NOT a new ABI field.
    In particular this does not grant an arbitrary client an unchanged
    current task, false stop bit, or return to the observing invocation. *)
Definition kernel_client_heap_extension_source {Extra} external port clients sg observer event_observer
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) : Prop :=
  forall cut state next returned origin,
    kernel_client_heap_observer_cut observer cut ->
    extra_effect sg cut state next returned ->
    kernel_client_heap_observer_cut observer next /\
    exists stopped returned_origin,
      kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin state stopped returned_origin returned.

(** This is an OS proof obligation for registered source steps, not a
    platform law.  Unlike the older unindexed interface, a switching
    producer need only handle the actual incoming execution origin.  It
    must establish the successor binding on the same state edge. *)
Definition kernel_client_heap_extension_execution_source {Extra}
  external port clients sg observer event_observer extra_source
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) : Prop :=
  forall cut state next returned origin,
    kernel_client_heap_observer_cut observer cut ->
    kernel_client_heap_source_cut extra_source cut origin state ->
    extra_effect sg cut state next returned ->
    kernel_client_heap_observer_cut observer next /\
    exists stopped returned_origin,
      kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin state stopped returned_origin returned /\
      kernel_client_heap_source_cut extra_source next returned_origin returned.

(** Every already proved counter/publication extension remains usable.
    Its current-pointer consequence comes from its source trace, rather
    than from a new assumption on a public caller or exception wrapper. *)
Lemma kernel_client_heap_extension_source_execution : forall Extra external port
  clients sg observer event_observer
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop),
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  kernel_client_heap_extension_execution_source external port clients sg observer event_observer
    (fun _ _ _ => True) extra_effect.
Proof.
  intros Extra external port clients sg observer event_observer extra_effect Hsource
    cut state next returned origin Hobserver [Hcurrent Hcut] Heffect.
  destruct (Hsource cut state next returned origin Hobserver Heffect)
    as [Hnext [stopped [returned_origin Htrace]]].
  split; [exact Hnext|]. exists stopped, returned_origin; split; [exact Htrace|].
  split.
  - eapply task_execution_source_trace_preserves_current; [|exact Hcurrent].
    exact (proj2 (kernel_resumption_task_source_trace_erases _ _ _ _ _ _ _ _ _ _ _ Htrace)).
  - destruct next; exact I.
Qed.

(** The named counter actions already have concrete memory producers.
    They are reused here without importing a full-profile validity premise:
    their state/field effects are the same for the selected64 input owner. *)
Lemma kernel_client_int_enter_source_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients sg observer event_observer
  origin state (frame : Assertion) before after,
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  kernel_client_int_enter_fragment sg before after ->
  (kernel_client_heap_world abi sg state ** frame) before ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin state false origin (os_int_enter_state state) /\
  (kernel_client_heap_world abi sg (os_int_enter_state state) ** frame) after.
Proof.
  intros external platform port abi clients sg observer event_observer origin state frame
    before after Hin Hsource Hpre; split.
  - change (kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state (kernel_client_stops (kernel_full_profile_cut_client KernelFullIntEnter) observer)
      origin (os_int_enter_state state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := kernel_full_profile_cut_client KernelFullIntEnter).
    + exact Hin.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + reflexivity.
  - eapply kernel_client_int_enter_resources; eassumption.
Qed.

Lemma kernel_client_int_exit_source_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients sg observer event_observer
  origin state (frame : Assertion) before after,
  clients (kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))) ->
  os_int_exit_masked_no_schedule_fragment sg before after ->
  (kernel_client_heap_world abi sg state ** frame) before ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin state false origin (os_int_exit_counter_state state.(SchedState).(isRunning) state) /\
  (kernel_client_heap_world abi sg
    (os_int_exit_counter_state state.(SchedState).(isRunning) state) ** frame) after.
Proof.
  intros external platform port abi clients sg observer event_observer origin state frame
    before after Hin Hsource Hpre; split.
  - change (kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state (kernel_client_stops
        (kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))) observer)
      origin (os_int_exit_counter_state state.(SchedState).(isRunning) state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := kernel_full_profile_cut_client (KernelFullIntExitCounter state.(SchedState).(isRunning))).
    + exact Hin.
    + discriminate.
    + intros; discriminate.
    + split; [exact I|reflexivity].
    + reflexivity.
    + reflexivity.
  - eapply kernel_client_int_exit_resources; eassumption.
Qed.

Lemma task_create_stack_publication_current_pointer_eq : forall sg publication state,
  state.(SchedState).(curTaskID) =
    (task_create_stack_publication_state sg publication state).(SchedState).(curTaskID).
Proof. reflexivity. Qed.

(** The five real publication stores consume the initialized PRIVATE cut,
    not a Closed world. The resulting trace and whole capsule map refer to
    exactly the publication state proved by that same heap execution.
    The acting invocation must be supplied by actual source classification;
    it is not silently relabelled None or identified with the observer. *)
Lemma kernel_client_publication_source_resources : forall external platform port
  (abi : Armv7aContinuationABI external platform port) clients sg observer event_observer
  origin publication state (frame : Assertion) before after,
  clients (task_create_stack_publication_client publication) ->
  publication.(stack_publication_invocation) <> observer ->
  task_tcb_init_publication_tail_fragment sg
    (task_create_stack_publication_args publication).(initPrio)
    (task_slot_addr sg publication.(stack_publication_slot)) before after ->
  (kernel_client_heap_publication abi sg publication state ** frame) before ->
  kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin state false origin (task_create_stack_publication_state sg publication state) /\
  (kernel_client_heap_world abi sg (task_create_stack_publication_state sg publication state) ** frame) after.
Proof.
  intros external platform port abi clients sg observer event_observer origin publication state
    frame before after Hin Hforeign Hsource Hpre.
  destruct (kernel_client_publication_resources external platform port abi sg publication state
    frame before after Hpre Hsource) as [Hstep Hpost].
  split; [|exact Hpost].
  change (kernel_resumption_task_source_trace external port clients sg observer event_observer
    origin state (kernel_client_stops (task_create_stack_publication_client publication) observer)
    origin (task_create_stack_publication_state sg publication state)).
  eapply kernel_client_framed_step_resumption_source with
    (action := task_create_stack_publication_client publication).
  - exact Hin.
  - cbn [task_create_stack_publication_client kernel_client_actor]; congruence.
  - intros; discriminate.
  - exact Hstep.
  - apply task_create_stack_publication_current_pointer_eq.
  - symmetry; eapply task_create_stack_publication_timer_state_eq; exact Hstep.
Qed.

Lemma kernel_client_heap_state_step_source : forall external port Extra clients sg observer event_observer
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop),
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  forall cut state next returned origin,
  kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_state_step extra_effect sg cut state next returned ->
  kernel_client_heap_observer_cut observer next /\
  exists stopped returned_origin,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned.
Proof.
  intros external port Extra clients sg observer event_observer extra_effect Henter Hexit Hpublish Hextra
    cut state next returned origin Hcompatible Hstep; destruct Hstep.
  - split; [exact I|]. exists false, origin.
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
  - split; [exact I|]. exists false, origin.
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
  - split; [exact I|]. exists false, origin.
    change (kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state (kernel_client_stops (task_create_stack_publication_client publication) observer)
      origin (task_create_stack_publication_state sg publication state)).
    eapply kernel_client_framed_step_resumption_source with
      (action := task_create_stack_publication_client publication).
    + apply Hpublish.
    + cbn [task_create_stack_publication_client kernel_client_actor].
      cbn [kernel_client_heap_observer_cut] in Hcompatible; congruence.
    + intros; discriminate.
    + split; [exact H|reflexivity].
    + apply task_create_stack_publication_current_pointer_eq.
    + reflexivity.
  - eapply Hextra; eassumption.
Qed.

(** Counter/nesting/publication steps keep their existing source proof,
    including Boot and nested non-switching exits.  Only an Extra step
    consumes the more precise execution-cut obligation. *)
Lemma kernel_client_heap_state_step_execution_source : forall external port Extra
  clients sg observer event_observer extra_source
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop),
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_execution_source external port clients sg observer event_observer
    extra_source extra_effect ->
  forall cut state next returned origin,
  kernel_client_heap_observer_cut observer cut ->
  kernel_client_heap_source_cut extra_source cut origin state ->
  kernel_client_heap_state_step extra_effect sg cut state next returned ->
  kernel_client_heap_observer_cut observer next /\
  exists stopped returned_origin,
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_source_cut extra_source next returned_origin returned.
Proof.
  intros external port Extra clients sg observer event_observer extra_source extra_effect
    Henter Hexit Hpublish Hextra.
  assert (Hempty : kernel_client_heap_extension_source external port clients sg observer event_observer
    (fun (_ : StableGlobVars) (_ : KernelClientHeapCut Extra) (_ : UCOS2_Verify_State)
      (_ : KernelClientHeapCut Extra) (_ : UCOS2_Verify_State) => False)).
  { intros ? ? ? ? ? ? Hfalse; contradiction. }
  assert (Hbuiltin_source : kernel_client_heap_extension_source external port clients sg observer event_observer
    (@kernel_client_heap_state_step Extra (fun _ _ _ _ _ => False))).
  { intros cut state next returned origin Hobserver Hstep.
    eapply kernel_client_heap_state_step_source; eassumption. }
  pose proof (kernel_client_heap_extension_source_execution Extra external port clients sg observer event_observer
    (@kernel_client_heap_state_step Extra (fun _ _ _ _ _ => False)) Hbuiltin_source) as Hbuiltin_execution.
  assert (Hbuiltin : forall cut state next returned origin,
    kernel_client_heap_observer_cut observer cut ->
    kernel_client_heap_source_cut extra_source cut origin state ->
    kernel_client_heap_state_step (fun _ _ _ _ _ => False) sg cut state next returned ->
    kernel_client_heap_observer_cut observer next /\
    exists stopped returned_origin,
      kernel_resumption_task_source_trace external port clients sg observer event_observer
        origin state stopped returned_origin returned /\
      kernel_client_heap_source_cut extra_source next returned_origin returned).
  { intros cut state next returned origin Hobserver [Hcurrent Hcut] Hstep.
    assert (Hinput : kernel_client_heap_source_cut (fun _ _ _ => True) cut origin state).
    { split; [exact Hcurrent|destruct cut; exact I]. }
    destruct (Hbuiltin_execution cut state next returned origin Hobserver Hinput Hstep)
      as [Hnext [stopped [returned_origin [Htrace Hreturned]]]].
    split; [exact Hnext|]. exists stopped, returned_origin; split; [exact Htrace|].
    split.
    - exact (proj1 Hreturned).
    - destruct Hstep; simpl; tauto. }
  intros cut state next returned origin Hobserver Hcurrent Hstep.
  destruct Hstep.
  - eapply Hbuiltin; [exact Hobserver|exact Hcurrent|constructor].
  - eapply Hbuiltin; [exact Hobserver|exact Hcurrent|constructor].
  - eapply Hbuiltin; [exact Hobserver|exact Hcurrent|constructor; exact H].
  - eapply Hextra; eassumption.
Qed.

(** Lift the SAME concrete trace and its proved state projection together.
    No two unrelated existential traces are joined just by their endpoints.
    The current cut and entire existing capsule map stay in the returned
    resource predicate; Extra is never replaced by Closed. This generic
    rule retains actual stops and possible origin changes from extensions. *)
Lemma kernel_client_heap_trace_source_resources : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect
  clients sg observer event_observer,
  @kernel_client_heap_extension_valid external platform port Extra
    abi extra_resources extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  forall cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (kernel_client_heap_resources abi extra_resources sg cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_heap_resources abi extra_resources sg next returned ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect clients sg observer
    event_observer Hspatial Henter Hexit Hpublish Hextra cut before next after frame Htrace.
  induction Htrace; intros state origin Hcompatible Hpre.
  - exists state, false, origin; split; [constructor|].
    split; [constructor|]. split; assumption.
  - destruct (kernel_client_heap_step_resources external platform port Extra abi extra_resources extra_step
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
