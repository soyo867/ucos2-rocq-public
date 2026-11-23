Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_call_stack_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_enter_spec.
Require Import Ucos2Verify.VC.code.interrupt.spec.int_exit_heap_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_private_pool_spec.
Import UCOS2_C_Rules EventStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Reuse the SAME registry, cut type, and strong call-stack owner. The
    extension obligation now consumes the current pool and must produce
    its successor on the actual heap edge. This does not register a new
    family, filter clients, or treat pure map facts as bytes. *)
Definition event_private_pool_call_stack_extension_valid {external platform port Extra}
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model -> KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) : Prop :=
  forall sg (cut : KernelClientHeapCut Extra) before next after state (frame : Assertion),
    extra_step sg cut before next after ->
    (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
      event_private_pool_rep sg state.(EventState) ** frame) before ->
    exists returned, extra_effect sg cut state next returned /\
      (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned **
        event_private_pool_rep sg returned.(EventState) ** frame) after.

(** The built-in IntEnter, non-scheduling IntExit and Task publication
    source rules were already proved with the focused call identity.
    Their Event component is unchanged, so their REAL instruction frame
    carries the pool. No analogous frame is asserted for arbitrary
    clients, scheduling exits, or an entire Restore. *)
Lemma event_private_pool_call_stack_step : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload extra_step extra_effect,
  @event_private_pool_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  forall sg cut before next after state (frame : Assertion),
  kernel_client_heap_step extra_step sg cut before next after ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned, kernel_client_heap_state_step extra_effect sg cut state next returned /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned **
      event_private_pool_rep sg returned.(EventState) ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect Hextra
    sg cut before next after state frame Hsource Hpre.
  assert (Horder : kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
      event_private_pool_rep sg state.(EventState) ** frame |--
    kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
      (event_private_pool_rep sg state.(EventState) ** frame)) by entailer!.
  pose proof (Horder before Hpre) as Howned.
  destruct Hsource.
  - pose proof (kernel_client_int_enter_keeps_call_stack external platform port abi sg focus payload
      state (event_private_pool_rep sg state.(EventState) ** frame) before after Howned H) as Hafter.
    exists (os_int_enter_state state); split; [constructor|].
    assert (Hclose : kernel_client_call_stack_world abi sg focus payload (os_int_enter_state state) **
        (event_private_pool_rep sg state.(EventState) ** frame) |--
      kernel_client_call_stack_resources abi extra_resources sg focus payload KernelClientHeapClosed
        (os_int_enter_state state) **
        event_private_pool_rep sg (os_int_enter_state state).(EventState) ** frame)
      by (cbn [kernel_client_call_stack_resources os_int_enter_state replace_IntrS EventState]; entailer!).
    exact (Hclose after Hafter).
  - pose proof (kernel_client_int_exit_keeps_call_stack external platform port abi sg focus payload
      state (event_private_pool_rep sg state.(EventState) ** frame) before after Howned H) as Hafter.
    exists (os_int_exit_counter_state state.(SchedState).(isRunning) state); split; [constructor|].
    match type of Hafter with ?P after =>
      assert (Hclose : P |-- kernel_client_call_stack_resources abi extra_resources sg focus payload
        KernelClientHeapClosed (os_int_exit_counter_state state.(SchedState).(isRunning) state) **
        event_private_pool_rep sg
          (os_int_exit_counter_state state.(SchedState).(isRunning) state).(EventState) ** frame)
    end.
    { cbn [kernel_client_call_stack_resources os_int_exit_counter_state replace_IntrS EventState]; entailer!. }
    exact (Hclose after Hafter).
  - destruct (kernel_client_publication_keeps_call_stack external platform port abi sg publication
      focus payload state (event_private_pool_rep sg state.(EventState) ** frame) before after Howned H)
      as [[Hinput Hstate] Hafter].
    exists (task_create_stack_publication_state sg publication state); split; [constructor; exact Hinput|].
    assert (Hevent : (task_create_stack_publication_state sg publication state).(EventState) = state.(EventState))
      by reflexivity.
    match type of Hafter with ?P after =>
      assert (Hclose : P |-- kernel_client_call_stack_resources abi extra_resources sg focus payload
        KernelClientHeapClosed (task_create_stack_publication_state sg publication state) **
        event_private_pool_rep sg (task_create_stack_publication_state sg publication state).(EventState) ** frame)
    end.
    { rewrite Hevent; cbn [kernel_client_call_stack_resources]; entailer!. }
    exact (Hclose after Hafter).
  - destruct (Hextra sg cut before next after state frame H Hpre) as [returned [Heffect Hafter]].
    exists returned; split; [constructor; exact Heffect|exact Hafter].
Qed.

(** Source history and heap ownership use the same state returned by each
    actual producer. Extension classification remains explicit for every
    extra action. This is a compositional theorem, not a certificate that
    any unspecified enabled source family satisfies its obligations. *)
Lemma event_private_pool_call_stack_trace_source : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources focus payload extra_step extra_effect
  clients sg observer event_observer,
  @event_private_pool_call_stack_extension_valid external platform port Extra
    abi extra_resources focus payload extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  forall cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (kernel_client_call_stack_resources abi extra_resources sg focus payload cut state **
    event_private_pool_rep sg state.(EventState) ** frame) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (kernel_client_call_stack_resources abi extra_resources sg focus payload next returned **
      event_private_pool_rep sg returned.(EventState) ** frame) after.
Proof.
  intros external platform port Extra abi extra_resources focus payload extra_step extra_effect clients sg observer
    event_observer Hspatial Henter Hexit Hpublish Hextra cut before next after frame Htrace.
  induction Htrace; intros state origin Hcompatible Hpre.
  - exists state, false, origin; split; [constructor|]. split; [constructor|]. split; assumption.
  - destruct (event_private_pool_call_stack_step external platform port Extra abi extra_resources focus payload
      extra_step extra_effect Hspatial sg cut before middle_cut middle state frame H Hpre)
      as [middle_state [Hstep Hmiddle]].
    destruct (kernel_client_heap_state_step_source external port Extra clients sg observer event_observer
      extra_effect Henter Hexit Hpublish Hextra cut state middle_cut middle_state origin Hcompatible Hstep)
      as [Hmiddle_compatible [stop1 [middle_origin Hsource]]].
    destruct (IHHtrace middle_state middle_origin Hmiddle_compatible Hmiddle)
      as [returned [stop2 [returned_origin [Htail [Htail_source [Hfinal_compatible Hpost]]]]]].
    exists returned, (orb stop1 stop2), returned_origin; split.
    + econstructor; eassumption.
    + split; [eapply kernel_resumption_task_source_trace_trans; eassumption|]. split; assumption.
Qed.
