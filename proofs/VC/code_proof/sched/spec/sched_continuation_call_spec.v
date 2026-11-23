Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem ConAssertion.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_verify_inv Ucos2Verify.lib.kernel_program_storage.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.task_stack Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.task_resume_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_source_return_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_modular_prefix_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_save_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_heap_source_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_client_continuation_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_continuation_interface_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_continuation_sched_spec.
Require Import Ucos2Verify.VC.code.core.spec.kernel_stack_world_spec.
Import UCOS2_C_Rules TaskStateDef ListNotations.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Module-level resource interpretation of the EXISTING C-client registry.
    [resources] is an interpretation of its existing cuts, not a second
    kernel world or a new history. At a shared closed cut it may be the
    existing [kernel_continuation_inv abi resources local sg active state].

    Each registered C module discharges this one-step guarantee from its
    own actual precondition, C effect and returned resources. Its callers
    reuse the certificate below instead of replaying foreign C statements.
    Pure [KernelClientCertificate] is still required for the relevant
    state/R/G facts; it cannot manufacture the spatial guarantee.

    This is a theorem parameter/OS module obligation. It is NOT a new ARM,
    BSP, interrupt, fairness, or eventual-return law. In particular it is
    never concluded merely from membership in [critical_region_clients]. *)
Definition kernel_client_heap_resource_guarantee {Extra}
  (resources : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State -> Assertion)
  (extra_step : StableGlobVars -> KernelClientHeapCut Extra -> model ->
    KernelClientHeapCut Extra -> model -> Prop)
  (extra_effect : StableGlobVars -> KernelClientHeapCut Extra -> UCOS2_Verify_State ->
    KernelClientHeapCut Extra -> UCOS2_Verify_State -> Prop) : Prop :=
  forall sg cut before next after state (frame : Assertion),
    kernel_client_heap_step extra_step sg cut before next after ->
    (resources sg cut state ** frame) before ->
    exists returned,
      kernel_client_heap_state_step extra_effect sg cut state next returned /\
      (resources sg next returned ** frame) after.

(** The already existing extension certificate supplies the same module
    interface for its original resource interpretation. No old certificate
    is silently upgraded to a stronger continuation/local interpretation. *)
Lemma kernel_client_heap_extension_resource_guarantee : forall external platform port Extra
  (abi : Armv7aContinuationABI external platform port) extra_resources extra_step extra_effect,
  @kernel_client_heap_extension_valid external platform port Extra
    abi extra_resources extra_step extra_effect ->
  kernel_client_heap_resource_guarantee
    (fun sg cut state => kernel_client_heap_resources abi extra_resources sg cut state)
    extra_step extra_effect.
Proof.
  intros external platform port Extra abi extra_resources extra_step extra_effect Hextension.
  intros sg cut before next after state frame Hstep Hpre.
  eapply kernel_client_heap_step_resources; eassumption.
Qed.

(** A nonempty, already proved generic-local instance: actual IntEnter,
    IntExitCounter and a prepared TCB publication. The publication cut owns
    the real initial buffer and its required local; None=emp is supplied
    by the caller's existing local family. Extra=False describes ONLY this
    instance, and does not restrict the public registry or public API. *)
Lemma kernel_client_builtin_continuation_resource_guarantee :
  forall external platform port Extra
    (abi : Armv7aContinuationABI external platform port) local,
  @kernel_client_heap_resource_guarantee Extra
    (fun sg cut state => kernel_client_continuation_resources abi local sg cut state)
    (fun _ _ _ _ _ => False) (fun _ _ _ _ _ => False).
Proof.
  intros external platform port Extra abi local sg cut before next after state frame Hstep Hpre.
  eapply kernel_client_continuation_step_resources; eassumption.
Qed.

(** Reuse the existing trace constructors. The final state and its owner
    are produced together by the module guarantees on the SAME heap path.
    The theorem is shared by callers; it does not ask any caller to inspect
    or inline another module's implementation. *)
Lemma kernel_client_heap_trace_resource_guarantee : forall Extra resources extra_step extra_effect,
  @kernel_client_heap_resource_guarantee Extra resources extra_step extra_effect ->
  forall sg cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  forall state,
  (resources sg cut state ** frame) before ->
  exists returned,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
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

(** The pure registered R/G projection is checked against the resource
    interpreter's very same state edges. This rules out pairing an unrelated
    successful heap endpoint with a desired task/owner history. The existing
    extension-source obligation belongs to the C modules, not the port. *)
Lemma kernel_client_heap_trace_registered_resources :
  forall external port Extra resources extra_step extra_effect clients sg observer event_observer,
  @kernel_client_heap_resource_guarantee Extra resources extra_step extra_effect ->
  clients (kernel_full_profile_cut_client KernelFullIntEnter) ->
  (forall running, clients (kernel_full_profile_cut_client (KernelFullIntExitCounter running))) ->
  (forall publication, clients (task_create_stack_publication_client publication)) ->
  kernel_client_heap_extension_source external port clients sg observer event_observer extra_effect ->
  forall cut before next after (frame : Assertion),
  kernel_client_heap_trace extra_step sg cut before next after ->
  forall state origin,
  kernel_client_heap_observer_cut observer cut ->
  (resources sg cut state ** frame) before ->
  exists returned stopped returned_origin,
    kernel_client_heap_state_trace extra_effect sg cut state next returned /\
    kernel_resumption_task_source_trace external port clients sg observer event_observer
      origin state stopped returned_origin returned /\
    kernel_client_heap_observer_cut observer next /\
    (resources sg next returned ** frame) after.
Proof.
  intros external port Extra resources extra_step extra_effect clients sg observer event_observer
    Hmodules Henter Hexit Hpublication Hextra cut before next after frame Htrace.
  induction Htrace; intros state origin Hobserver Hpre.
  - exists state, false, origin; split; [constructor|].
    split; [constructor|]. split; assumption.
  - destruct (Hmodules sg cut before middle_cut middle state frame H Hpre)
      as [middle_state [Hstep Hmiddle]].
    destruct (kernel_client_heap_state_step_source external port Extra clients sg observer event_observer
      extra_effect Henter Hexit Hpublication Hextra cut state middle_cut middle_state origin Hobserver Hstep)
      as [Hmiddle_observer [stop1 [middle_origin Hsource]]].
    destruct (IHHtrace middle_state middle_origin Hmiddle_observer Hmiddle)
      as [returned [stop2 [returned_origin [Htail [Htail_source [Hfinal_observer Hpost]]]]]].
    exists returned, (orb stop1 stop2), returned_origin; split; [econstructor; eassumption|].
    split; [eapply kernel_resumption_task_source_trace_trans; eassumption|].
    split; assumption.
Qed.

(** OSCtxSw's C-level call-site contract. The same [resources] and local
    policy cross the call. The ordinary C prefix has ALREADY run, hence
    the input heap is indexed by [os_sched_prefix_state entry]. The source
    guard and storage/selection facts remain kernel obligations.

    This interface is not automatically a consequence of the old fixed
    UCOS2_inv OSCtxSw declaration. Linking it requires the port's approved
    execution-authority contract and the registered C modules' shared-world
    guarantees above. It does not ask the port to preserve arbitrary C
    state or prove the C clients. *)
Definition os_sched_continuation_switch_pre environment critical saved_local resources
  sg call saved acquired entry : Assertion :=
  coq_prop (os_sched_requests_switch entry = true /\
    os_sched_current_storage_binding sg call entry /\
    entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None) &&
  kernel_continuation_call_masked environment.(task_stack_call_continuations)
    resources (task_create_continuation_local saved_local) critical sg
    (task_stack_call_active_key call) call saved acquired (os_sched_prefix_state entry).

(** Common protected endpoint of the actual C branch, before the final
    Restore. In the switching branch the normal-return source clause is
    [os_sched_switch_outcome]; the no-switch branch has the exact prefix
    state. The parameter names are the same in both branches and in all
    three current callers. No termination or future selection is asserted. *)
Definition os_sched_continuation_body_post environment critical saved_local resources
  sg call saved acquired entry : Assertion :=
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical
      sg entry call returned current) &&
    kernel_continuation_call_masked environment.(task_stack_call_continuations)
      resources (task_create_continuation_local saved_local) critical sg
      (task_stack_call_active_key returned) returned saved acquired current.

(** The actual C prefix is shared, rather than reimplemented per caller.
    The input is the real acquired cut produced by Save. Its selection
    safety must be established by the shared invariant/source entry and R/G
    obligations. It is not obtained from coverage alone or installed as a
    new platform law. This lemma keeps every C guard/cache/counter write. *)
Lemma os_sched_continuation_c_prefix : forall environment critical saved_local sg call saved acquired
  entry before (frame : Assertion),
  (os_sched_selection_enabled entry = true -> entry.(SchedState).(readyList) <> []) ->
  (os_sched_requests_switch entry = true ->
    os_sched_current_storage_binding sg call entry /\
    entry.(TskState).(parkedTaskStacks) (task_stack_key call.(os_sched_call_stack)) = None) ->
  (task_tcb_init_continuation_restore_input environment critical saved_local sg call
    saved acquired entry ** unmap_table_rep sg ** frame) before ->
  exists after,
    os_sched_modular_prefix_execution sg entry before after /\
    ((if os_sched_requests_switch entry
      then os_sched_continuation_switch_pre environment critical saved_local kernel_program_inv
        sg call saved acquired entry
      else os_sched_continuation_body_post environment critical saved_local kernel_program_inv
        sg call saved acquired entry) ** frame) after.
Proof.
  intros environment critical saved_local sg call saved acquired entry before frame
    Hnonempty Hswitch_input Hpre.
  assert (Hopen :
    task_tcb_init_continuation_restore_input environment critical saved_local sg call saved acquired entry **
      unmap_table_rep sg ** frame |--
    kernel_continuation_call_masked environment.(task_stack_call_continuations) kernel_program_inv
      (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key call)
      call saved acquired entry ** frame).
  { sep_apply_l_atomic (proj1 (task_tcb_init_continuation_restore_input_masked_world
      environment critical saved_local sg call saved acquired entry)); entailer!. }
  destruct (os_sched_modular_prefix_continuation_resources _ _ _ environment.(task_stack_call_continuations)
    (task_create_continuation_local saved_local) critical sg (task_stack_call_active_key call)
    call saved acquired entry before frame Hnonempty (Hopen before Hpre))
    as [after [Hrun [Hhigh Hafter]]].
  exists after; split; [exact Hrun|].
  destruct (os_sched_requests_switch entry) eqn:Hswitch.
  - specialize (Hswitch_input eq_refl).
    match type of Hafter with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { unfold os_sched_continuation_switch_pre; entailer!. }
    exact (Hclose after Hafter).
  - assert (Hreturn : os_sched_c_return environment.(task_stack_call_external) critical
        sg entry call call (os_sched_prefix_state entry)).
    { unfold os_sched_c_return; rewrite Hswitch; auto. }
    match type of Hafter with ?P after => match goal with |- ?Q after =>
      assert (Hclose : P |-- Q) end end.
    { unfold os_sched_continuation_body_post; Exists call (os_sched_prefix_state entry); entailer!. }
    exact (Hclose after Hafter).
Qed.

(** Source identity is a consequence of the exact C return relation. The
    switching case uses the already proved storage/source bridge; the
    no-switch case uses the unchanged task projection of the real prefix. *)
Lemma os_sched_continuation_c_return_source : forall external critical sg entry original returned current,
  (os_sched_requests_switch entry = true -> os_sched_current_storage_binding sg original entry) ->
  os_sched_c_return external critical sg entry original returned current ->
  kernel_call_task_source original entry -> kernel_call_task_source returned current.
Proof.
  intros external critical sg entry original returned current Hsafe Hreturn Hsource.
  destruct (os_sched_requests_switch entry) eqn:Hswitch.
  - pose proof (proj1 (Hsafe eq_refl)) as Horigin.
    unfold os_sched_c_return in Hreturn; rewrite Hswitch in Hreturn.
    destruct Hreturn as [installed [Hrun [Htrace [Harch [Hi [Ho [Hs
      [Hactive [Hcurrent Hparked]]]]]]]]].
    unfold kernel_call_task_source; rewrite Hi, Ho, Hs.
    split; [exact Horigin|]. split; [exact Hactive|].
    unfold task_execution_current; rewrite Horigin; exact Hcurrent.
  - unfold os_sched_c_return in Hreturn; rewrite Hswitch in Hreturn.
    destruct Hreturn as [-> ->]; apply os_sched_prefix_preserves_task_source; exact Hsource.
Qed.

(** Literal consumer for OS_Sched's final C Restore declaration. No local
    owner is forgotten when leaving the shared generic world. Del's extra
    private pool uses the same parameterized body interface, with its own
    already proved resource split/merge at this call site. *)
Lemma os_sched_continuation_body_restore_input : forall environment critical saved_local
  sg call saved acquired entry,
  os_sched_continuation_body_post environment critical saved_local kernel_program_inv
    sg call saved acquired entry |--
  EX returned current,
    coq_prop (os_sched_c_return environment.(task_stack_call_external) critical
      sg entry call returned current /\ UCOS2_state_inv sg current) &&
    (task_tcb_init_continuation_restore_input environment critical saved_local sg
       returned saved acquired current ** unmap_table_rep sg).
Proof.
  intros; unfold os_sched_continuation_body_post; Intros returned current.
  Exists returned current.
  sep_apply_l_atomic (proj2 (task_tcb_init_continuation_restore_input_masked_world
    environment critical saved_local sg returned saved acquired current)).
  unfold task_tcb_init_continuation_restore_input, UCOS2_inv; entailer!.
Qed.

(** Actual continuation after the modular Restore call. The body relation
    refers to the SAME released state that indexes Restore's pre/post. The
    returned generic map comes from that call's output, not from a pure R/G
    relation or the old weak scheduler postcondition. Save's already proved
    source observation supplies [Hentry_source]; no future safety is needed.

    This is the common public return consumed unchanged by TaskCreate and
    by Sem's generic interface. Sem wait-selection and Del owner/private-pool
    consequences remain their own C-module R/G obligations. *)
Lemma os_sched_continuation_restore_output_return : forall environment critical saved_local sg
  original scheduled returned mask saved before entry released,
  task_tcb_init_stack_same_call scheduled original ->
  (kernel_call_task_source original before -> kernel_call_task_source scheduled entry) ->
  (os_sched_requests_switch entry = true ->
    os_sched_current_storage_binding sg scheduled entry) ->
  os_sched_c_return environment.(task_stack_call_external) critical sg entry scheduled returned released ->
  UCOS2_state_inv sg released -> interrupt_saved_value mask saved ->
  task_tcb_init_continuation_restore_output environment critical saved_local sg returned saved released **
    unmap_table_rep sg |--
  os_sched_continuation_return_post environment saved_local kernel_program_inv sg original mask before.
Proof.
  intros environment critical saved_local sg original scheduled returned mask saved before entry released
    Hscheduled Hentry_source Hsafe Hbody Hvalid Hsaved.
  pose proof (os_sched_c_return_execution_identity _ _ _ _ _ _ _ Hbody) as Hreturned.
  unfold task_tcb_init_continuation_restore_output; Intros final current.
  assert (Hfinal : task_tcb_init_stack_same_call final returned) by tauto.
  assert (Hsource : task_tcb_init_stack_source_preserved returned released current) by tauto.
  assert (Hsame : task_tcb_init_stack_same_call final original).
  { unfold task_tcb_init_stack_same_call in *; intuition congruence. }
  assert (Hfinal_source : kernel_call_task_source original before -> kernel_call_task_source final current).
  { intro Hinitial.
    pose proof (os_sched_continuation_c_return_source _ _ _ _ _ _ _ Hsafe Hbody
      (Hentry_source Hinitial)) as Hreleased.
    apply (proj2 (task_tcb_init_stack_same_call_source_iff final returned current Hfinal)).
    apply Hsource; exact Hreleased. }
  sep_apply_l_atomic (proj1 (task_tcb_init_continuation_save_input_closed_world
    environment critical saved_local sg final (armv7a_irq_fiq_mask saved) current)).
  rewrite (proj2 Hsaved).
  unfold os_sched_continuation_return_post; Exists final current; entailer!.
Qed.

(** Linking boundary still to discharge for a complete C callee:
    - actual Save must provide its acquired world and source/entry safety;
    - OSCtxSw must use the approved execution contract plus the registered
      modules' resource guarantee to provide [body_post] on normal return;
    - final Restore uses the same generic region and returns its real map.
    No field of an existing ABI is strengthened by this file. The built-in
    instance above is checked separately from yet-unregistered creator,
    wait/wake, retirement and switched source instances. Their existing
    proved C producers are reusable module evidence, not caller obligations
    to re-enact each possible foreign execution.

    The switch input above contains only actual entry observations. It
    does not quantify over arbitrary future save/hook states as the old
    [os_sched_switch_input] did. The destination must instead be produced
    by the real switch module's capture, hook, selector and owned map.

    The existing resource-only [os_sched_continuation_pre] does not entail
    enabled-selection nonemptiness or current storage binding. In
    particular, [UCOS2_state_inv] contains [task_idle_tail], not idle
    readiness, and its current-cache clause bounds pointers without tying
    them to this execution owner. These are real C source/protocol facts
    to carry through Save, not facts to add to a platform Ensure. This
    file consequently does not claim the complete Scheduler theorem from
    that still-unrepaired public precondition. *)
