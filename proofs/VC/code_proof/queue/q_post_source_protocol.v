From Ucos2Verify.VC.code.queue.spec Require Import q_post_api_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.ucos2_verify_state_def Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.task Ucos2Verify.lib.event Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_client_invariants.
Import UCOS2_C_Rules TaskStateDef EventStateDef SchedStateDef ListNotations.
Local Open Scope Z_scope.

(** Both pre-Save error paths discharge the conditional protocol without
    any ready, no-wait or completed-client premise. *)
Lemma q_post_schedule_protocol_null : forall environment critical sg caller mask eid message before,
  q_post_schedule_protocol environment critical sg caller mask 0 eid message before.
Proof.
  intros environment critical sg caller mask eid message before returned restored error Hprefix.
  unfold q_post_prefix_program in Hprefix; cbn in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

Lemma q_post_schedule_protocol_wrong_type : forall environment critical sg caller mask pe eid message before,
  pe <> 0 -> event_slot_type_value before.(EventState) eid <> 2 ->
  q_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros environment critical sg caller mask pe eid message before Hpe Htype returned restored error Hprefix.
  unfold q_post_prefix_program in Hprefix.
  rewrite (proj2 (Z.eqb_neq _ _) Hpe), (proj2 (Z.eqb_neq _ _) Htype) in Hprefix.
  destruct Hprefix as [Heq _]; discriminate.
Qed.

(** The API Require and both CPU contracts are unchanged. The no-wait
    premise below concerns the exact acquired node of the actual Save relation. *)
Lemma q_post_schedule_protocol_acquired_no_waiters : forall environment critical sg caller mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg caller pe before eid observed ->
  (forall active saved acquired node,
    q_post_save_facts environment critical sg caller active mask saved before acquired ->
    q_post_acquire_facts environment critical sg caller active mask saved before acquired eid observed node ->
    node.(waitList) = []) ->
  q_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros environment critical sg caller mask pe eid message before observed Hvalid Hinput Hempty
    returned restored error Hprefix.
  unfold q_post_prefix_program in Hprefix.
  destruct (Z.eqb pe 0) eqn:Hpe; [destruct Hprefix as [Heq _]; discriminate|].
  destruct (Z.eqb (event_slot_type_value before.(EventState) eid) 2) eqn:Htype;
    [|destruct Hprefix as [Heq _]; discriminate].
  apply Z.eqb_neq in Hpe; apply Z.eqb_eq in Htype.
  destruct Hprefix as [active [saved [acquired [code [schedule [released [next
    [Hsave [Hstep [Hrestore Hresult]]]]]]]]]].
  injection Hresult as Hcode Hschedule Hcaller; subst schedule next.
  pose proof (q_post_save_program_facts _ _ _ _ _ _ _ _ _ Hvalid Hsave) as Hfacts.
  destruct (q_post_acquire_identity environment critical sg caller active mask saved pe before acquired eid observed
    Hvalid Hpe Hinput Htype Hfacts) as [node Hacquire].
  pose proof Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  pose proof (proj1 (q_post_critical_requests_schedule_iff sg QueuePostBack acquired eid node message
    (code, true) released Hnode Hstep) eq_refl) as [Hgroup Hrequest].
  rewrite (Hempty active saved acquired node Hfacts Hacquire) in Hgroup.
  exfalso; exact (Hgroup eq_refl).
Qed.

Definition q_post_queues_no_waiters (state : UCOS2_Verify_State) : Prop :=
  forall eid node, state.(EventState).(inUsedEventStates) eid = Some node ->
    node.(eventType) = OS_EVENT_TYPE_Q -> node.(waitList) = [].

Definition q_post_no_waiters_inv sg state : Prop :=
  UCOS2_state_inv sg state /\ q_post_queues_no_waiters state.

(** Explicit module-level C rely, not a claim that all arbitrary clients or
    all states satisfying UCOS2_state_inv have no Queue waiters. *)
Definition q_post_no_waiters_clients (critical : CriticalRegionResources) : Prop :=
  forall action, critical.(critical_region_clients) action ->
    kernel_client_preserves_resources q_post_no_waiters_inv action.

Lemma q_post_interval_preserves_no_waiters : forall critical sg invocation before after,
  q_post_no_waiters_clients critical -> UCOS2_state_inv sg before ->
  q_post_queues_no_waiters before ->
  critical_region_interval critical sg invocation before after ->
  UCOS2_state_inv sg after /\ q_post_queues_no_waiters after.
Proof.
  intros critical sg invocation before after Hclients Hvalid Hempty Hinterval.
  exact (proj1 (critical_region_interval_transports_invariant q_post_no_waiters_inv
    critical sg invocation before after Hclients Hinterval (conj Hvalid Hempty))).
Qed.

Lemma q_post_schedule_protocol_no_waiters : forall environment critical sg caller mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before -> q_post_no_waiters_clients critical ->
  q_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros environment critical sg caller mask pe eid message before observed Hvalid Hinput Hempty Hclients.
  eapply q_post_schedule_protocol_acquired_no_waiters; [exact Hvalid|exact Hinput|].
  intros active saved acquired node Hfacts Hacquire.
  destruct Hfacts as [Hacquired [Hinterval Hrest]].
  destruct Hacquire as [_ [_ [_ [Hnode [Hqueue Hgeneration]]]]].
  destruct (q_post_interval_preserves_no_waiters critical sg
    (task_resume_view caller).(os_execution_invocation) before acquired
    Hclients Hvalid Hempty Hinterval) as [_ Hempty_acquired].
  exact (Hempty_acquired eid node Hnode Hqueue).
Qed.

(** Source instances for the existing C-module protocol. No new public
    Require, CPU law, registered client or state field is introduced. The
    initializer endpoint is UCOS2_boot_state (64-byte TCB), not the separate
    extended-profile kernel_full_boot_state. *)
Require Import Ucos2Verify.VC.code.queue.spec.q_create_lifecycle_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_create_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_full_profile_client_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_create_stack_client_spec.

Lemma q_post_boot_queues_no_waiters : forall sg task_name flag_name memory_name names,
  q_post_queues_no_waiters (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof. intros sg task_name flag_name memory_name names eid node Hget; discriminate. Qed.

Lemma q_post_published_map_preserves_no_waiters : forall before after,
  after.(EventState).(inUsedEventStates) = before.(EventState).(inUsedEventStates) ->
  q_post_queues_no_waiters before -> q_post_queues_no_waiters after.
Proof.
  intros before after Hmap Hempty eid node Hget Htype.
  rewrite Hmap in Hget; exact (Hempty eid node Hget Htype).
Qed.

Lemma q_post_event_publish_preserves_no_waiters : forall state eid node,
  q_post_queues_no_waiters state ->
  (node.(eventType) = OS_EVENT_TYPE_Q -> node.(waitList) = []) ->
  q_post_queues_no_waiters
    (replace_EventS (event_publish state.(EventState) eid node) state).
Proof.
  intros state eid node Hempty Hnew other current Hget Htype.
  change (kernel_map_set state.(EventState).(inUsedEventStates) eid (Some node) other =
    Some current) in Hget.
  unfold kernel_map_set in Hget.
  destruct (Z.eq_dec other eid).
  - injection Hget as Heq; subst current; apply Hnew; exact Htype.
  - exact (Hempty other current Hget Htype).
Qed.

Lemma q_post_create_publish_preserves_no_waiters :
  forall state eid allocation qid start size name slots,
  q_post_queues_no_waiters state ->
  q_post_queues_no_waiters
    (replace_EventS (queue_publish state.(EventState) eid
      (q_create_initialized_event allocation qid start size name) qid slots) state).
Proof.
  intros state eid allocation qid start size name slots Hempty.
  eapply q_post_published_map_preserves_no_waiters with
    (before := replace_EventS (event_publish state.(EventState) eid
      (q_create_initialized_event allocation qid start size name)) state).
  - reflexivity.
  - apply q_post_event_publish_preserves_no_waiters; [exact Hempty|].
    intros; reflexivity.
Qed.

Lemma q_post_queue_update_preserves_no_waiters : forall state eid node queue slots,
  state.(EventState).(inUsedEventStates) eid = Some node ->
  q_post_queues_no_waiters state ->
  q_post_queues_no_waiters
    (replace_EventS (queue_update state.(EventState) eid node queue slots) state).
Proof.
  intros state eid node queue slots Hnode Hempty other current Hget Htype.
  change ((if Z.eqb other eid then Some (event_set_queue_fields node queue)
    else state.(EventState).(inUsedEventStates) other) = Some current) in Hget.
  destruct (Z.eqb other eid) eqn:Heq.
  - injection Hget as Hcurrent; subst current.
    change (node.(waitList) = []).
    apply (Hempty eid node Hnode); exact Htype.
  - exact (Hempty other current Hget Htype).
Qed.

(** These source transformers alter private bytes or Task/counter state,
    while leaving the actual published ECB map unchanged. *)
Lemma q_post_event_detach_preserves_no_waiters : forall state eid rest image,
  q_post_queues_no_waiters state ->
  q_post_queues_no_waiters
    (replace_EventS (event_detach_head state.(EventState) eid rest image) state).
Proof.
  intros; eapply q_post_published_map_preserves_no_waiters; [reflexivity|eassumption].
Qed.

Lemma q_post_private_store_preserves_no_waiters : forall state eid allocation field value,
  q_post_queues_no_waiters state ->
  q_post_queues_no_waiters
    (replace_EventS (event_private_write state.(EventState) eid allocation field value) state).
Proof.
  intros; eapply q_post_published_map_preserves_no_waiters; [reflexivity|eassumption].
Qed.

Lemma q_post_task_publication_preserves_no_waiters : forall sg publication state,
  q_post_queues_no_waiters state ->
  q_post_queues_no_waiters (task_create_stack_publication_state sg publication state).
Proof.
  intros; eapply q_post_published_map_preserves_no_waiters; [reflexivity|eassumption].
Qed.

Lemma q_post_counter_cut_preserves_no_waiters : forall cut state,
  q_post_queues_no_waiters state ->
  q_post_queues_no_waiters (kernel_full_profile_cut_state cut state).
Proof.
  intros cut state Hempty.
  eapply q_post_published_map_preserves_no_waiters with (before := state).
  - destruct cut; reflexivity.
  - exact Hempty.
Qed.

(** Lift a proved source step and its existing certificate. This does not
    register the action, enlarge a critical-region family, or assert that
    arbitrary clients preserve this extra property. *)
Lemma q_post_no_waiters_client_from_certificate : forall action,
  KernelClientCertificate action ->
  (forall sg before after,
    UCOS2_state_inv sg before -> q_post_queues_no_waiters before ->
    kernel_client_step action sg before after -> q_post_queues_no_waiters after) ->
  kernel_client_preserves_resources q_post_no_waiters_inv action.
Proof.
  intros action Hcertificate Hempty_step sg before after [Hvalid Hempty] Hstep.
  destruct (kernel_client_certificate_preserves_selected_resources action Hcertificate
    sg before after Hvalid Hstep) as [Hafter Hframes].
  split; [split; [exact Hafter|exact (Hempty_step sg before after Hvalid Hempty Hstep)]|exact Hframes].
Qed.

Lemma q_post_task_publication_client_preserves_no_waiters : forall publication,
  kernel_client_preserves_resources q_post_no_waiters_inv
    (task_create_stack_publication_client publication).
Proof.
  intro publication; apply q_post_no_waiters_client_from_certificate.
  - apply task_create_stack_publication_certificate.
  - intros sg before after Hvalid Hempty [Hinput ->].
    apply q_post_task_publication_preserves_no_waiters; exact Hempty.
Qed.

Lemma q_post_private_store_client_preserves_no_waiters :
  forall actor eid allocation field stored,
  kernel_client_preserves_resources q_post_no_waiters_inv
    (event_create_private_store_client actor eid allocation field stored).
Proof.
  intros; apply q_post_no_waiters_client_from_certificate.
  - apply event_create_private_store_client_certificate.
  - intros sg before after Hvalid Hempty [Hget ->].
    apply q_post_private_store_preserves_no_waiters; exact Hempty.
Qed.

(** A finite union of existing source-action shapes. This is an admission
    example for a supplied C registry, not a new registry and not a claim
    that every kernel/environment action belongs to this family. *)
Definition q_post_no_waiters_source_client (action : KernelClientAction) : Prop :=
  (exists publication, action = task_create_stack_publication_client publication) \/
  (exists cut,
    (cut = KernelFullIntEnter \/ exists observed, cut = KernelFullIntExitCounter observed) /\
    action = kernel_full_profile_cut_client cut) \/
  (exists actor invocation, action = event_create_allocate_client actor invocation) \/
  (exists actor eid allocation field stored,
    action = event_create_private_store_client actor eid allocation field stored) \/
  (exists actor eid allocation free,
    action = q_create_reserve_client actor eid allocation free) \/
  (exists actor eid allocation qid start size slots name,
    action = q_create_publication_client actor eid allocation qid start size slots name) \/
  (exists actor eid allocation node,
    node.(waitList) = [] /\ action = event_create_publication_client actor eid allocation node).

Lemma q_post_no_waiters_source_client_step : forall action sg before after,
  q_post_no_waiters_source_client action ->
  q_post_queues_no_waiters before -> kernel_client_step action sg before after ->
  q_post_queues_no_waiters after.
Proof.
  intros action sg before after Hsource Hempty Hstep.
  destruct Hsource as [Htask|[Hcounter|[Hallocate|[Hprivate|[Hreserve|[Hpublish|Hevent]]]]]].
  - destruct Htask as [publication ->]. destruct Hstep as [Hinput ->].
    apply q_post_task_publication_preserves_no_waiters; exact Hempty.
  - destruct Hcounter as [cut [Hselected ->]]. destruct Hstep as [Hinput ->].
    apply q_post_counter_cut_preserves_no_waiters; exact Hempty.
  - destruct Hallocate as [actor [invocation ->]].
    destruct Hstep as [_ [result Hallocate]].
    unfold event_create_allocate_critical in Hallocate.
    destruct before.(EventState).(unUsedEventStates) as [|eid rest].
    + destruct Hallocate as [_ ->]; exact Hempty.
    + destruct Hallocate as [image [_ [_ ->]]].
      apply q_post_event_detach_preserves_no_waiters; exact Hempty.
  - destruct Hprivate as [actor [eid [allocation [field [stored ->]]]]].
    destruct Hstep as [Hget ->].
    apply q_post_private_store_preserves_no_waiters; exact Hempty.
  - destruct Hreserve as [actor [eid [allocation [free ->]]]].
    destruct Hstep as [_ [_ [_ [_ [result [actual [Hget Hreserve]]]]]]].
    destruct free as [|qid rest]; destruct Hreserve as [_ ->].
    all: eapply q_post_published_map_preserves_no_waiters with (before := before);
      [reflexivity|exact Hempty].
  - destruct Hpublish as [actor [eid [allocation [qid [start [size [slots [name ->]]]]]]]].
    destruct Hstep as [_ [_ [_ [_ ->]]]].
    apply q_post_create_publish_preserves_no_waiters; exact Hempty.
  - destruct Hevent as [actor [eid [allocation [node [Hnew ->]]]]].
    destruct Hstep as [_ [_ ->]].
    apply q_post_event_publish_preserves_no_waiters; [exact Hempty|intros; exact Hnew].
Qed.

Lemma q_post_no_waiters_source_client_preserves_resources : forall action,
  KernelClientCertificate action -> q_post_no_waiters_source_client action ->
  kernel_client_preserves_resources q_post_no_waiters_inv action.
Proof.
  intros action Hcertificate Hsource.
  apply q_post_no_waiters_client_from_certificate; [exact Hcertificate|].
  intros sg before after Hvalid Hempty Hstep.
  eapply q_post_no_waiters_source_client_step; eassumption.
Qed.

Lemma q_post_no_waiters_clients_from_source_family : forall critical,
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  q_post_no_waiters_clients critical.
Proof.
  intros critical Hfamily action Hin.
  apply q_post_no_waiters_source_client_preserves_resources.
  - exact (critical_region_client_certificates critical action Hin).
  - exact (Hfamily action Hin).
Qed.

Lemma q_post_schedule_protocol_no_waiters_sources : forall environment critical sg caller mask pe eid message before observed,
  UCOS2_state_inv sg before ->
  q_post_call_input critical sg caller pe before eid observed ->
  q_post_queues_no_waiters before ->
  (forall action, critical_region_clients critical action -> q_post_no_waiters_source_client action) ->
  q_post_schedule_protocol environment critical sg caller mask pe eid message before.
Proof.
  intros environment critical sg caller mask pe eid message before observed Hvalid Hinput Hempty Hfamily.
  eapply q_post_schedule_protocol_no_waiters; [exact Hvalid|exact Hinput|exact Hempty|].
  apply q_post_no_waiters_clients_from_source_family; exact Hfamily.
Qed.

(** Post's own successful ring update is a real source case outside the
    above illustrative action union. The full/error alternatives leave the
    state untouched. A no-wait Boot call therefore preserves the property
    for the next call; no wake or scheduling fact is assumed here. *)
Lemma q_post_critical_preserves_no_waiters : forall sg kind eid message before node result after,
  q_post_lookup before eid node -> node.(eventType) = OS_EVENT_TYPE_Q ->
  q_post_queues_no_waiters before ->
  q_post_critical sg kind eid message before result after ->
  q_post_queues_no_waiters after.
Proof.
  intros sg kind eid message before node result after Hnode Htype Hempty
    [actual [Hactual Hstep]].
  assert (actual = node) by congruence; subst actual.
  rewrite (Hempty eid node Hnode Htype) in Hstep.
  cbn [encode_event_wait_grp Z.eqb] in Hstep.
  destruct Hstep as [queue [Hqueue Hstep]].
  destruct (Z.leb queue.(qSize) (queue_entries queue)).
  - destruct Hstep as [_ ->]; exact Hempty.
  - destruct Hstep as [slots [next [_ [_ [_ ->]]]]].
    eapply q_post_queue_update_preserves_no_waiters; eassumption.
Qed.

Require Import Ucos2Verify.VC.code.core.spec.kernel_boot_spec.
Require Import Ucos2Verify.VC.code.task.spec.init_tcb_list_spec.
Local Open Scope sac_scope.

(** Consume the selected initializer's existing spatial post. Its existing
    memory/startup/BSS obligations remain explicit in kernel_boot_spec; this
    consequence is not a new proof of OSInit's implementation or its hooks. *)
Lemma q_post_boot_initializer_establishes_no_waiters :
  forall sg task_name flag_name memory_name names,
  selected_kernel_profile sg -> init_tcb_list_profile sg -> valid_name_resources names ->
  (sg.(osKernelConfig).(cfgMemoryEnabled) = true ->
   sg.(osKernelConfig).(cfgMemoryNames) = true ->
   exists chars, readable_name names memory_name chars) ->
  kernel_boot_initializer_post sg task_name flag_name memory_name names |--
  coq_prop (q_post_no_waiters_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names)) &&
  UCOS2_inv sg (UCOS2_boot_state sg task_name flag_name memory_name names).
Proof.
  intros sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory.
  pose proof (q_post_boot_queues_no_waiters sg task_name flag_name memory_name names) as Hempty.
  sep_apply_l_atomic (kernel_boot_initializer_post_establishes_global_inv
    sg task_name flag_name memory_name names Hprofile Htcb Hnames Hmemory).
  unfold q_post_no_waiters_inv, UCOS2_inv; entailer!.
Qed.
