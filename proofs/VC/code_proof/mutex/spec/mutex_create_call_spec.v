Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.micromega.Lia Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.array_abstraction.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_wait.
Require Import Ucos2Verify.lib.mutex.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.

Import UCOS2_C_Rules ListNotations TaskStateDef EventStateDef.
Import EventFieldStorage.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

(** Source-order composition for the selected names-disabled Create body.
    The private PCP lease refers to the one already reserved physical
    priority slot. Publication consumes this lease and the initialized
    private ECB; it neither reserves a second cell nor initializes bytes. *)
Module MutexCreateCall.

Definition allocation_pcp (sg : StableGlobVars) (pcp : Priority)
  (allocation : EventPrivateAllocation) : Prop :=
  allocation.(eventPrivateMutexPCP) =
    if pcp =? sg.(osPrioMutexCeilDis) then None else Some pcp.

Definition initialized_event (pcp : Priority) (allocation : EventPrivateAllocation)
  : OSEventAbstractState :=
  mutex_create_node pcp allocation.(eventPrivateGeneration) allocation.(eventPrivateStorage).

Lemma publish_lookup_same : forall events eid node,
  (event_publish events eid node).(inUsedEventStates) eid = Some node.
Proof. intros; apply kernel_map_set_same. Qed.

Lemma publish_lookup_other : forall events eid node other,
  other <> eid ->
  (event_publish events eid node).(inUsedEventStates) other = events.(inUsedEventStates) other.
Proof. intros; apply kernel_map_set_other; assumption. Qed.

Lemma publish_lease_view_eq : forall events eid node,
  event_mutex_lease_view (event_publish events eid node) =
    kernel_map_set (event_mutex_lease_view events) eid None.
Proof.
  intros; apply functional_extensionality; intro other.
  unfold event_mutex_lease_view, event_publish; simpl; unfold kernel_map_set.
  destruct (Z.eq_dec other eid); reflexivity.
Qed.

Lemma allocation_enabled_lease : forall sg events eid allocation pcp,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> pcp <> sg.(osPrioMutexCeilDis) ->
  event_mutex_lease_view events eid = Some (pcp, allocation.(eventPrivateQueue)).
Proof.
  intros sg events eid allocation pcp Hget Hpcp Henabled.
  unfold event_mutex_lease_view; rewrite Hget.
  unfold allocation_pcp in Hpcp; rewrite (proj2 (Z.eqb_neq _ _) Henabled) in Hpcp.
  rewrite Hpcp; reflexivity.
Qed.

Lemma allocation_lease_priority : forall sg events eid allocation pcp p queue,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation ->
  event_mutex_lease_view events eid = Some (p, queue) ->
  p = pcp /\ pcp <> sg.(osPrioMutexCeilDis).
Proof.
  intros sg events eid allocation pcp p queue Hget Hpcp Hlease.
  unfold event_mutex_lease_view in Hlease; rewrite Hget in Hlease.
  unfold allocation_pcp in Hpcp; rewrite Hpcp in Hlease.
  destruct (pcp =? sg.(osPrioMutexCeilDis)) eqn:Hdisabled; [discriminate|].
  injection Hlease as Hsame Hqueue; split; [symmetry; exact Hsame|].
  apply Z.eqb_neq; exact Hdisabled.
Qed.

Lemma allocation_enabled_facts : forall sg tasks events eid allocation pcp,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> pending_mutex_consistency sg tasks events ->
  pcp <> sg.(osPrioMutexCeilDis) ->
  tasks.(prioTbl) pcp = PTReserved /\
  tasks.(taskLifecycle).(taskReservations) pcp = None /\
  ~ (exists mid e m, events.(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m pcp) /\
  (forall other queue, event_mutex_lease_view events other = Some (pcp, queue) -> other = eid).
Proof.
  intros sg tasks events eid allocation pcp Hget Hpcp Hpending Henabled.
  pose proof (allocation_enabled_lease sg events eid allocation pcp Hget Hpcp Henabled) as Hlease.
  specialize (Hpending eid pcp allocation.(eventPrivateQueue) Hlease); tauto.
Qed.

Lemma publish_priority_claim_iff : forall sg events eid allocation pcp p,
  events.(inUsedEventStates) eid = None ->
  ((exists mid e m,
      (event_publish events eid (initialized_event pcp allocation)).(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) <->
   (exists mid e m, events.(inUsedEventStates) mid = Some e /\
      e.(eventType) = OS_EVENT_TYPE_MUTEX /\ e.(mutexFields) = Some m /\
      mutex_reserves_priority_slot sg m p) \/
   (pcp <> sg.(osPrioMutexCeilDis) /\ pcp = p)).
Proof.
  intros sg events eid allocation pcp p Hnone; split.
  - intros [mid [e [m [He [Htype [Hm Hclaim]]]]]].
    destruct (Z.eq_dec mid eid) as [->|Hne].
    + rewrite publish_lookup_same in He; injection He as He; subst e.
      cbn [initialized_event mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
      right; exact Hclaim.
    + rewrite publish_lookup_other in He by exact Hne.
      left; exists mid, e, m; exact (conj He (conj Htype (conj Hm Hclaim))).
  - intros [[mid [e [m [He Hrest]]]]|Hclaim].
    + exists mid, e, m; split; [|exact Hrest].
      rewrite publish_lookup_other; [exact He|congruence].
    + exists eid, (initialized_event pcp allocation),
        {| mfPCP := pcp; mfOwner := None; mfOwnerOrigPrio := None |}.
      split; [apply publish_lookup_same|]. split; [reflexivity|].
      split; [reflexivity|exact Hclaim].
Qed.

Lemma publish_preserves_owner_claim : forall sg events eid allocation pcp owner p,
  events.(inUsedEventStates) eid = None ->
  mutex_task_enabled_pcp_claim sg events owner p ->
  mutex_task_enabled_pcp_claim sg (event_publish events eid (initialized_event pcp allocation)) owner p.
Proof.
  intros sg events eid allocation pcp owner p Hnone [mid [e [m [He Hrest]]]].
  exists mid, e, m; split; [|exact Hrest].
  rewrite publish_lookup_other; [exact He|congruence].
Qed.

Lemma publish_preserves_table_consistency : forall sg tasks events eid allocation pcp,
  events.(inUsedEventStates) eid = None ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> pending_mutex_consistency sg tasks events ->
  task_mutex_priotbl_consistency sg tasks events ->
  task_mutex_priotbl_consistency sg tasks (event_publish events eid (initialized_event pcp allocation)).
Proof.
  intros sg tasks events eid allocation pcp Hnone Hget Hpcp Hpending [Hcreator [Hslots Halias]].
  split.
  - intros p entry Hentry Hclaim.
    apply (publish_priority_claim_iff sg events eid allocation pcp p Hnone) in Hclaim.
    destruct Hclaim as [Hclaim|[Henabled <-]].
    + exact (Hcreator p entry Hentry Hclaim).
    + destruct (allocation_enabled_facts sg tasks events eid allocation pcp
        Hget Hpcp Hpending Henabled) as [_ [Hreservation _]]; congruence.
  - split.
    + intros p Hp; specialize (Hslots p Hp).
      destruct (tasks.(prioTbl) p) eqn:Htable.
      * intros Hclaim; apply (publish_priority_claim_iff sg events eid allocation pcp p Hnone) in Hclaim.
        destruct Hclaim as [Hclaim|[Henabled <-]]; [exact (Hslots Hclaim)|].
        destruct (allocation_enabled_facts sg tasks events eid allocation pcp
          Hget Hpcp Hpending Henabled) as [Hreserved _]; congruence.
      * destruct Hslots as [Hreservation|[Hclaim|[other [queue Hlease]]]].
        -- left; exact Hreservation.
        -- right; left; apply (publish_priority_claim_iff sg events eid allocation pcp p Hnone).
           left; exact Hclaim.
        -- destruct (Z.eq_dec other eid) as [->|Hne].
           ++ destruct (allocation_lease_priority sg events eid allocation pcp p queue Hget Hpcp Hlease)
                as [-> Henabled].
              right; left; apply (publish_priority_claim_iff sg events eid allocation pcp pcp Hnone).
              right; split; [exact Henabled|reflexivity].
           ++ right; right; exists other, queue; rewrite publish_lease_view_eq, kernel_map_set_other;
                assumption.
      * exact Hslots.
    + intros tid t Ht; destruct (Halias tid t Ht) as [base [Hbase [Heffective Hclaims]]].
      exists base; split; [exact Hbase|]. split; [exact Heffective|].
      intros p Hp; destruct (Hclaims p Hp) as [Hbasep|[Hlower Hclaim]]; [left; exact Hbasep|].
      right; split; [exact Hlower|]; eapply publish_preserves_owner_claim; eassumption.
Qed.

Lemma publish_preserves_owner_snapshots : forall sg tasks events eid allocation pcp,
  mutex_owner_snapshot_in_range sg tasks events ->
  mutex_owner_snapshot_in_range sg tasks (event_publish events eid (initialized_event pcp allocation)).
Proof.
  intros sg tasks events eid allocation pcp Hvalid mid e m owner He Htype Hm Howner.
  destruct (Z.eq_dec mid eid) as [->|Hne].
  - rewrite publish_lookup_same in He; injection He as He; subst e.
    cbn [initialized_event mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m; discriminate.
  - rewrite publish_lookup_other in He by exact Hne.
    exact (Hvalid mid e m owner He Htype Hm Howner).
Qed.

Lemma publish_preserves_mutex_protocol : forall sg s eid allocation pcp,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> valid_mutex_pcp sg pcp ->
  pending_mutex_consistency sg s.(TskState) s.(EventState) -> mutex_protocol_consistency sg s ->
  mutex_protocol_consistency sg
    (replace_EventS (event_publish s.(EventState) eid (initialized_event pcp allocation)) s).
Proof.
  intros sg s eid allocation pcp Hget Hpcp Hrange Hpending Hvalid mid e m He Htype Hm.
  change ((event_publish s.(EventState) eid (initialized_event pcp allocation)).(inUsedEventStates) mid = Some e) in He.
  destruct (Z.eq_dec mid eid) as [->|Hne].
  - rewrite publish_lookup_same in He; injection He as He; subst e.
    cbn [initialized_event mutex_create_node mutexFields] in Hm; injection Hm as Hm; subst m.
    split; [exact Hrange|]. split; [exact I|].
    destruct (Z.eq_dec pcp sg.(osPrioMutexCeilDis)) as [Hdisabled|Henabled].
    + left; exact Hdisabled.
    + right; split; [exact Henabled|left].
      exact (proj1 (allocation_enabled_facts sg s.(TskState) s.(EventState) eid allocation pcp
        Hget Hpcp Hpending Henabled)).
  - rewrite publish_lookup_other in He by exact Hne.
    exact (Hvalid mid e m He Htype Hm).
Qed.

Lemma allocation_enabled_differs_live_mutex : forall sg tasks events eid allocation pcp mid e m,
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> pending_mutex_consistency sg tasks events ->
  pcp <> sg.(osPrioMutexCeilDis) ->
  events.(inUsedEventStates) mid = Some e -> e.(eventType) = OS_EVENT_TYPE_MUTEX ->
  e.(mutexFields) = Some m -> m.(mfPCP) <> pcp.
Proof.
  intros sg tasks events eid allocation pcp mid e m Hget Hpcp Hpending Henabled He Htype Hm Heq.
  destruct (allocation_enabled_facts sg tasks events eid allocation pcp Hget Hpcp Hpending Henabled)
    as [_ [_ [Hnolive _]]].
  apply Hnolive; exists mid, e, m; split; [exact He|]. split; [exact Htype|].
  split; [exact Hm|]. split; [unfold mutex_pcp_enabled; congruence|exact Heq].
Qed.

Lemma publish_preserves_pcp_unique : forall sg s eid allocation pcp,
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> pending_mutex_consistency sg s.(TskState) s.(EventState) ->
  mutex_enabled_pcp_unique sg s ->
  mutex_enabled_pcp_unique sg
    (replace_EventS (event_publish s.(EventState) eid (initialized_event pcp allocation)) s).
Proof.
  intros sg s eid allocation pcp Hget Hpcp Hpending Hunique mid1 e1 m1 mid2 e2 m2
    He1 Htype1 Hm1 He2 Htype2 Hm2 Hsame Henabled.
  change ((event_publish s.(EventState) eid (initialized_event pcp allocation)).(inUsedEventStates) mid1 = Some e1) in He1.
  change ((event_publish s.(EventState) eid (initialized_event pcp allocation)).(inUsedEventStates) mid2 = Some e2) in He2.
  destruct (Z.eq_dec mid1 eid) as [->|Hne1]; destruct (Z.eq_dec mid2 eid) as [->|Hne2].
  - reflexivity.
  - rewrite publish_lookup_same in He1; injection He1 as He1; subst e1.
    cbn [initialized_event mutex_create_node mutexFields] in Hm1; injection Hm1 as Hm1; subst m1.
    rewrite publish_lookup_other in He2 by exact Hne2.
    exfalso; eapply allocation_enabled_differs_live_mutex;
      [exact Hget|exact Hpcp|exact Hpending|exact Henabled|exact He2|exact Htype2|exact Hm2|symmetry; exact Hsame].
  - rewrite publish_lookup_same in He2; injection He2 as He2; subst e2.
    cbn [initialized_event mutex_create_node mutexFields] in Hm2; injection Hm2 as Hm2; subst m2.
    rewrite publish_lookup_other in He1 by exact Hne1.
    exfalso; eapply allocation_enabled_differs_live_mutex;
      [exact Hget|exact Hpcp|exact Hpending|cbn [mfPCP] in Hsame; congruence|exact He1|exact Htype1|exact Hm1|exact Hsame].
  - rewrite publish_lookup_other in He1 by exact Hne1.
    rewrite publish_lookup_other in He2 by exact Hne2; eapply Hunique; eassumption.
Qed.

Lemma publish_preserves_cross_module_consistency : forall sg s eid allocation pcp,
  s.(EventState).(inUsedEventStates) eid = None ->
  s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> valid_mutex_pcp sg pcp ->
  pending_mutex_consistency sg s.(TskState) s.(EventState) -> cross_module_consistency sg s ->
  cross_module_consistency sg
    (replace_EventS (event_publish s.(EventState) eid (initialized_event pcp allocation)) s).
Proof.
  intros sg s eid allocation pcp Hnone Hget Hpcp Hrange Hpending
    [Htable [Howners [Hwait [Hprotocol [Hunique [Hflags Htimer]]]]]].
  split; [eapply publish_preserves_table_consistency; eassumption|].
  split; [eapply publish_preserves_owner_snapshots; eassumption|].
  split.
  - eapply event_wait_object_consistency_event_publish with (node := initialized_event pcp allocation);
      [exact Hnone|reflexivity|reflexivity|exact Hwait].
  - split; [eapply publish_preserves_mutex_protocol; eassumption|].
    split; [eapply publish_preserves_pcp_unique; eassumption|].
    split; [exact Hflags|exact Htimer].
Qed.

Lemma publish_preserves_pending_consistency : forall sg tasks events eid allocation pcp,
  events.(inUsedEventStates) eid = None ->
  events.(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> pending_mutex_consistency sg tasks events ->
  pending_mutex_consistency sg tasks (event_publish events eid (initialized_event pcp allocation)).
Proof.
  intros sg tasks events eid allocation pcp Hnone Hget Hpcp Hpending other p queue Hlease.
  rewrite publish_lease_view_eq in Hlease.
  destruct (Z.eq_dec other eid) as [->|Hne].
  { rewrite kernel_map_set_same in Hlease; discriminate. }
  rewrite kernel_map_set_other in Hlease by exact Hne.
  destruct (Hpending other p queue Hlease)
    as [Hrange [Henabled [Hqueue [Hreserved [Hcreator [Hnolive Hunique]]]]]].
  split; [exact Hrange|]. split; [exact Henabled|]. split; [exact Hqueue|].
  split; [exact Hreserved|]. split; [exact Hcreator|]. split.
  - intros Hclaim; apply (publish_priority_claim_iff sg events eid allocation pcp p Hnone) in Hclaim.
    destruct Hclaim as [Hclaim|[Hpcpenabled Heq]]; [exact (Hnolive Hclaim)|].
    subst p; destruct (allocation_enabled_facts sg tasks events eid allocation pcp
      Hget Hpcp Hpending Hpcpenabled) as [_ [_ [_ Hsole]]].
    apply Hne; exact (Hsole other queue Hlease).
  - intros slot slot_queue Hslot; rewrite publish_lease_view_eq in Hslot.
    destruct (Z.eq_dec slot eid) as [->|Hdifferent].
    + rewrite kernel_map_set_same in Hslot; discriminate.
    + rewrite kernel_map_set_other in Hslot by exact Hdifferent.
      exact (Hunique slot slot_queue Hslot).
Qed.

Lemma publish_preserves_validity : forall sg s eid allocation pcp,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation_pcp sg pcp allocation -> valid_mutex_pcp sg pcp ->
  UCOS2_state_inv sg
    (replace_EventS (event_publish s.(EventState) eid (initialized_event pcp allocation)) s).
Proof.
  intros sg s eid allocation pcp
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hbits [Hflags
      [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    Hget Hpcp Hrange.
  destruct (event_pool_private_not_free sg s.(EventState) eid allocation (proj1 Hevents) Hget)
    as [_ [_ Hnone]].
  assert (HreferencesAfter : kernel_names_valid sg
    (replace_EventS (event_publish s.(EventState) eid (initialized_event pcp allocation)) s)).
  { eapply kernel_names_valid_replace_event_add_name; [exact Hreferences| |].
    - apply event_name_valid_disabled; unfold selected_kernel_profile in Hprofile; tauto.
    - intros p Hreference; exact (event_publish_name_references s.(EventState) eid
        (initialized_event pcp allocation) p Hreference). }
  unfold UCOS2_state_inv, UCOS2_state_inv_with_ready.
  split; [exact Hprofile|]. split; [exact Htasks|]. split; [exact Hsched|]. split.
  - eapply event_publish_preserves_in_range; [exact Hevents|exact Hget|reflexivity| | | |].
    + unfold event_fields_consistency, initialized_event, mutex_create_node; simpl; intuition discriminate.
    + unfold event_payload_consistency, initialized_event, mutex_create_node, mutex_fields_consistency;
        simpl; intuition.
    + intros other old q Hold Hqueue; discriminate.
    + apply event_wait_entry_consistency_empty; reflexivity.
  - split; [eapply publish_preserves_cross_module_consistency; eassumption|].
    split; [exact Hidle|]. split; [exact Hbits|]. split; [exact Hflags|].
    split; [exact Hmemory|]. split; [exact Htimer|]. split; [exact Hstats|].
    split; [exact Hcontrol|]. split; [exact Hnames|]. split; [exact HreferencesAfter|].
    split; [exact Hstacks|]; eapply publish_preserves_pending_consistency; eassumption.
Qed.

Lemma initialized_image_matches_event : forall sg tasks allocation image pcp,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  allocation.(eventPrivateStorage) = event_create_image false 4 (pcp * 256 + 255) 0 0 image ->
  forall field, In field (event_fields sg.(osKernelConfig).(cfgEventNames)) ->
    allocation.(eventPrivateStorage) field = event_image sg tasks (initialized_event pcp allocation) field.
Proof.
  intros sg tasks allocation image pcp Hnames Himage field Hin.
  rewrite Hnames in Hin; destruct field;
    try (exfalso; unfold event_fields in Hin; simpl in Hin; intuition discriminate);
    unfold event_image, initialized_event, mutex_create_node; rewrite Himage; reflexivity.
Qed.

Lemma publish_merge : forall sg s eid allocation image pcp,
  UCOS2_state_inv sg s -> s.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateQueue) = None -> allocation_pcp sg pcp allocation -> valid_mutex_pcp sg pcp ->
  allocation.(eventPrivateStorage) = event_create_image false 4 (pcp * 256 + 255) 0 0 image ->
  event_private_storage_rep sg eid allocation **
    (event_raw_rep sg s.(TskState) s.(EventState) ** queue_storage_rep sg s.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg s) |--
  UCOS2_inv sg (replace_EventS (event_publish s.(EventState) eid (initialized_event pcp allocation)) s).
Proof.
  intros sg s eid allocation image pcp Hvalid Hget Hqueue Hpcp Hrange Himage.
  pose proof Hvalid as [Hprofile [_ [_ [[Hpool _] _]]]].
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false)
    by (unfold selected_kernel_profile in Hprofile; tauto).
  destruct (event_pool_private_not_free sg s.(EventState) eid allocation Hpool Hget)
    as [_ [_ Hnone]].
  pose proof (publish_preserves_validity sg s eid allocation pcp Hvalid Hget Hpcp Hrange) as Hpost.
  sep_apply_l_atomic (event_publish_reconstructs_raw_rep_on_fields sg s.(TskState) s.(EventState)
    eid allocation (initialized_event pcp allocation) Hpool Hget
    (initialized_image_matches_event sg s.(TskState) allocation image pcp Hnames Himage)).
  sep_apply_l_atomic (queue_event_publish_preserves_storage sg s.(EventState) eid allocation
    (initialized_event pcp allocation) Hnone Hget Hqueue eq_refl).
  eapply derivable1_trans; [|apply UCOS2_inv_merge_updated_event_queue; exact Hpost]; entailer!.
Qed.

Lemma interleaved_publish_merge :
  forall critical sg task_invocation event_invocation eid before initialized allocation final pcp,
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  allocation.(eventPrivateQueue) = None -> allocation_pcp sg pcp allocation -> valid_mutex_pcp sg pcp ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid
    (event_create_initialization_fields false 4 (pcp * 256 + 255) 0 0) before tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  event_private_storage_rep sg eid final **
    (event_raw_rep sg initialized.(TskState) initialized.(EventState) **
     queue_storage_rep sg initialized.(EventState) **
     UCOS2_raw_rep_missing_event_queue sg initialized) |--
  UCOS2_inv sg
    (replace_EventS (event_publish initialized.(EventState) eid (initialized_event pcp final)) initialized).
Proof.
  intros critical sg task_invocation event_invocation eid before initialized allocation final pcp
    Hvalid Hget Hinv Hqueue Hpcp Hrange Hstores Hfinal.
  destruct (sem_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ _ Hvalid Hget Hinv Hstores)
    as [Hinitialized [current [Hcurrent [_ [_ [Hqueue_after Himage]]]]]].
  assert (current = final) by congruence; subst current.
  rewrite event_create_stores_image_initialization_eq in Himage.
  pose proof (sem_create_private_stores_interleaved_mutex_pcp_eq
    _ _ _ _ _ _ _ _ _ _ _ Hvalid Hget Hinv Hstores Hfinal) as Hlease.
  eapply publish_merge; [exact Hinitialized|exact Hfinal| | |exact Hrange|exact Himage].
  - rewrite Hqueue_after; exact Hqueue.
  - unfold allocation_pcp in *; rewrite Hlease; exact Hpcp.
Qed.

Definition priority_rejected (sg : StableGlobVars) (pcp : Priority) : bool :=
  (negb (pcp =? sg.(osPrioMutexCeilDis)) && (sg.(osLowestPrio) <=? pcp))%bool.

Definition priority_slot_busy (sg : StableGlobVars) (pcp : Priority)
  (entry : UCOS2_Verify_State) : bool :=
  if pcp =? sg.(osPrioMutexCeilDis) then false else
  match entry.(TskState).(prioTbl) pcp with PTFree => false | _ => true end.

Lemma priority_accepted_in_range : forall sg pcp,
  0 <= pcp -> priority_rejected sg pcp = false -> valid_mutex_pcp sg pcp.
Proof.
  intros sg pcp Hnonnegative Haccepted; unfold priority_rejected in Haccepted.
  destruct (pcp =? sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - left; apply Z.eqb_eq; exact Hdisabled.
  - right; simpl in Haccepted; apply Z.leb_gt in Haccepted; split; assumption.
Qed.

Lemma priority_slot_available_iff : forall sg pcp entry,
  priority_slot_busy sg pcp entry = false <->
    pcp = sg.(osPrioMutexCeilDis) \/ entry.(TskState).(prioTbl) pcp = PTFree.
Proof.
  intros; unfold priority_slot_busy; destruct (pcp =? sg.(osPrioMutexCeilDis)) eqn:Hdisabled.
  - apply Z.eqb_eq in Hdisabled; split; auto.
  - apply Z.eqb_neq in Hdisabled; destruct (entry.(TskState).(prioTbl) pcp); split;
      intros; try discriminate; intuition congruence.
Qed.

(** This relation ends at the ACTUAL Restore frontier. The empty-pool
    branch includes the source's reservation rollback, hence its endpoint
    is the acquired entry. There is no post-validity guard. *)
Definition allocate_critical (sg : StableGlobVars) (pcp : Priority)
  : program UCOS2_Verify_State (OSErrCode * option (EventID * EventStorage)) :=
  fun entry result after =>
    if priority_slot_busy sg pcp entry then
      result = (OS_ERR_PRIO_EXIST, None) /\ after = entry
    else match entry.(EventState).(unUsedEventStates) with
    | [] => result = (OS_ERR_PEVENT_NULL, None) /\ after = entry
    | eid :: rest => exists image,
        entry.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
        result = (OS_ERR_NONE, Some (eid, image)) /\
        after = mutex_create_detached_state sg pcp eid rest entry
    end.

Lemma allocate_critical_exists : forall sg pcp entry,
  UCOS2_state_inv sg entry -> exists result after, allocate_critical sg pcp entry result after.
Proof.
  intros sg pcp entry Hvalid; unfold allocate_critical.
  destruct (priority_slot_busy sg pcp entry).
  - exists (OS_ERR_PRIO_EXIST, None), entry; split; reflexivity.
  - destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
    + exists (OS_ERR_PEVENT_NULL, None), entry; split; reflexivity.
    + pose proof Hvalid as [_ [_ [_ [[_ [[Hdomain _] _]] _]]]].
      destruct (proj2 (Hdomain eid) ltac:(rewrite Hhead; left; reflexivity)) as [image Himage].
      exists (OS_ERR_NONE, Some (eid, image)), (mutex_create_detached_state sg pcp eid rest entry).
      exists image; split; [exact Himage|]; split; reflexivity.
Qed.

Lemma allocate_critical_preserves_validity : forall sg pcp entry result after,
  UCOS2_state_inv sg entry -> valid_mutex_pcp sg pcp ->
  allocate_critical sg pcp entry result after -> UCOS2_state_inv sg after.
Proof.
  intros sg pcp entry result after Hvalid Hpcp; unfold allocate_critical.
  destruct (priority_slot_busy sg pcp entry) eqn:Hbusy.
  - intros [_ ->]; exact Hvalid.
  - destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
    + intros [_ ->]; exact Hvalid.
    + intros [image [_ [_ ->]]]; apply MutexCreateFull.detached_state_preserves_validity;
        [exact Hvalid|exact Hhead|exact Hpcp|apply priority_slot_available_iff; exact Hbusy].
Qed.

Lemma allocate_critical_private_result : forall sg pcp entry err eid image after,
  allocate_critical sg pcp entry (err, Some (eid, image)) after ->
  err = OS_ERR_NONE /\
  after.(EventState).(eventLifecycle).(eventPrivate) eid =
    Some (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp).
Proof.
  intros sg pcp entry err eid image after; unfold allocate_critical.
  destruct (priority_slot_busy sg pcp entry); [intros [Hbad _]; discriminate|].
  destruct entry.(EventState).(unUsedEventStates) as [|head rest]; [intros [Hbad _]; discriminate|].
  intros [bytes [Hbytes [Hresult ->]]]; injection Hresult as Herr Heid Himage; subst err head bytes.
  split; [reflexivity|].
  cbn [mutex_create_detached_state replace_EventS EventState replace_TskS].
  rewrite MutexCreateFull.detached_private_lookup.
  unfold mutex_create_storage; rewrite Hbytes; reflexivity.
Qed.

Lemma allocate_critical_failure_frame : forall sg pcp entry err after,
  allocate_critical sg pcp entry (err, None) after -> after = entry.
Proof.
  intros sg pcp entry err after; unfold allocate_critical.
  destruct (priority_slot_busy sg pcp entry); [tauto|].
  destruct entry.(EventState).(unUsedEventStates); [tauto|intros [image [_ [Hbad _]]]; discriminate].
Qed.

Definition call_relation (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (before : UCOS2_Verify_State)
  (result : OSErrCode * option EventID) (after : UCOS2_Verify_State) : Prop :=
  if priority_rejected sg pcp then result = (OS_ERR_PRIO_INVALID, None) /\ after = before
  else if 0 <? before.(IntrState).(intNesting) then result = (OS_ERR_CREATE_ISR, None) /\ after = before
  else exists entry allocated critical_result,
    critical_region_interval critical sg invocation before entry /\
    allocate_critical sg pcp entry critical_result allocated /\
    match critical_result with
    | (err, None) => result = (err, None) /\ critical_region_interval critical sg invocation allocated after
    | (err, Some (eid, image)) => exists initialized allocation,
        sem_create_private_stores_interleaved critical sg invocation
          entry.(EventState).(eventLifecycle).(eventNextInvocation) eid
          (event_create_initialization_fields false 4 (pcp * 256 + 255) 0 0) allocated tt initialized /\
        initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
        result = (err, Some eid) /\
        after = replace_EventS
          (event_publish initialized.(EventState) eid (initialized_event pcp allocation)) initialized
    end.

Lemma call_preserves_validity : forall critical sg invocation pcp before result after,
  UCOS2_state_inv sg before -> 0 <= pcp ->
  call_relation critical sg invocation pcp before result after -> UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pcp before result after Hvalid Hnonnegative Hcall.
  unfold call_relation in Hcall; destruct (priority_rejected sg pcp) eqn:Haccepted.
  - destruct Hcall as [_ ->]; exact Hvalid.
  - pose proof (priority_accepted_in_range sg pcp Hnonnegative Haccepted) as Hpcp.
    destruct (0 <? before.(IntrState).(intNesting)); [destruct Hcall as [_ ->]; exact Hvalid|].
    destruct Hcall as [entry [allocated [[err [ [eid image] | ]] [Htrace [Hallocate Hreturn]]]]].
    + pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Htrace Hvalid)) as Hentry.
      pose proof (allocate_critical_preserves_validity sg pcp entry _ allocated Hentry Hpcp Hallocate) as Hallocated.
      destruct (allocate_critical_private_result sg pcp entry err eid image allocated Hallocate) as [Herr Hprivate].
      destruct Hreturn as [initialized [allocation [Hstores [Hget [_ ->]]]]].
      destruct (sem_create_private_stores_interleaved_post
        _ _ _ _ _ _ _ _ _ _ Hallocated Hprivate eq_refl Hstores) as [Hinitialized _].
      pose proof (sem_create_private_stores_interleaved_mutex_pcp_eq
        _ _ _ _ _ _ _ _ _ _ _ Hallocated Hprivate eq_refl Hstores Hget) as Hlease.
      eapply publish_preserves_validity; [exact Hinitialized|exact Hget| |exact Hpcp].
      unfold allocation_pcp; exact Hlease.
    + pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Htrace Hvalid)) as Hentry.
      pose proof (allocate_critical_preserves_validity sg pcp entry _ allocated Hentry Hpcp Hallocate) as Hallocated.
      destruct Hreturn as [_ Hreturn_trace].
      exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hreturn_trace Hallocated)).
Qed.

Lemma call_exists : forall critical sg invocation pcp before,
  UCOS2_state_inv sg before -> exists result after, call_relation critical sg invocation pcp before result after.
Proof.
  intros critical sg invocation pcp before Hvalid; unfold call_relation.
  destruct (priority_rejected sg pcp).
  - exists (OS_ERR_PRIO_INVALID, None), before; split; reflexivity.
  - destruct (0 <? before.(IntrState).(intNesting)).
    + exists (OS_ERR_CREATE_ISR, None), before; split; reflexivity.
    + destruct (allocate_critical_exists sg pcp before Hvalid) as [[err [[eid image]|]] [allocated Hallocate]].
      * destruct (allocate_critical_private_result sg pcp before err eid image allocated Hallocate) as [Herr Hprivate].
        destruct (event_create_private_stores_exists eid
          (event_create_initialization_fields false 4 (pcp * 256 + 255) 0 0) allocated _ Hprivate)
          as [initialized Hstores].
        destruct (event_create_private_stores_post_allocation eid _ allocated tt initialized _ Hprivate Hstores)
          as [allocation [Hget Himage]].
        exists (err, Some eid),
          (replace_EventS (event_publish initialized.(EventState) eid (initialized_event pcp allocation)) initialized).
        exists before, allocated, (err, Some (eid, image)); split; [constructor|].
        split; [exact Hallocate|]; exists initialized, allocation; split.
        -- exact (sem_create_private_stores_without_interference critical sg invocation eid _
             allocated tt initialized _ Hprivate Hstores).
        -- split; [exact Hget|]; split; reflexivity.
      * exists (err, None), allocated; exists before, allocated, (err, None).
        split; [constructor|]; split; [exact Hallocate|]; split; [reflexivity|constructor].
Qed.

Definition call_program (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) : program UCOS2_Verify_State addr :=
  fun before pointer after => exists result,
    call_relation critical sg invocation pcp before result after /\
    pointer = event_encode_pool_link sg (snd result).

Definition result_prop (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (before after : UCOS2_Verify_State)
  (pointer error : Z) : Prop := exists result,
    call_relation critical sg invocation pcp before result after /\
    pointer = event_encode_pool_link sg (snd result) /\ error = encode_os_err_code (fst result).

Lemma result_prop_call_program : forall critical sg invocation pcp before after pointer error,
  result_prop critical sg invocation pcp before after pointer error ->
  call_program critical sg invocation pcp before pointer after.
Proof.
  intros critical sg invocation pcp before after pointer error [result [Hcall [Hpointer Herror]]].
  exists result; split; assumption.
Qed.

Lemma call_program_preserves_validity : forall critical sg invocation pcp before pointer after,
  UCOS2_state_inv sg before -> 0 <= pcp ->
  call_program critical sg invocation pcp before pointer after -> UCOS2_state_inv sg after.
Proof.
  intros critical sg invocation pcp before pointer after Hvalid Hpcp [result [Hcall _]].
  eapply call_preserves_validity; eassumption.
Qed.

Definition closed (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) : Assertion :=
  coq_prop (UCOS2_state_inv sg state) &&
    (interrupt_platform_running platform invocation origin mask ** critical_region_outside critical sg invocation state).

Lemma closed_equiv : forall platform critical sg invocation origin mask state,
  closed platform critical sg invocation origin mask state --||--
    (interrupt_platform_running platform invocation origin mask ** UCOS2_inv sg state).
Proof.
  intros; unfold closed; rewrite sem_create_closed_region_equiv.
  unfold UCOS2_inv; split; entailer!.
Qed.

Definition acquire_facts (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (mask saved : Z) (before entry : UCOS2_Verify_State) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_state_inv sg entry /\ interrupt_saved_value mask saved.

Lemma save_consequence : forall critical sg invocation mask saved before entry,
  UCOS2_state_inv sg before -> critical_region_interval critical sg invocation before entry ->
  interrupt_saved_value mask saved ->
  UCOS2_raw_rep sg entry |--
    coq_prop (acquire_facts critical sg invocation mask saved before entry) && UCOS2_inv sg entry.
Proof.
  intros critical sg invocation mask saved before entry Hvalid Hinterval Hsaved.
  pose proof (proj1 (critical_region_interval_transports_resources _ _ _ _ _ Hinterval Hvalid)) as Hentry.
  assert (Hfacts : acquire_facts critical sg invocation mask saved before entry)
    by (unfold acquire_facts; auto).
  unfold UCOS2_inv; entailer!.
Qed.

(** Restore receives the already established current invariant, including
    the pending lease on success. The detached physical ECB is framed by
    the caller, not hidden or initialized inside the wrapper contract. *)
Definition restore_pre (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin) (saved : Z)
  (entry checkpoint : UCOS2_Verify_State) : Assertion :=
  critical_region_masked platform critical sg invocation origin saved entry ** UCOS2_inv sg checkpoint.

Lemma restore_pre_exposes_saved_token : forall platform critical sg invocation origin saved entry checkpoint,
  restore_pre platform critical sg invocation origin saved entry checkpoint --||--
    (interrupt_platform_running platform invocation origin 192 **
     interrupt_platform_saved platform (save_token saved invocation origin) **
     critical_region_inside critical sg invocation entry ** UCOS2_inv sg checkpoint).
Proof. intros; unfold restore_pre, critical_region_masked; split; entailer!. Qed.

Lemma restore_consequence : forall platform critical sg invocation origin mask checkpoint,
  UCOS2_state_inv sg checkpoint ->
  interrupt_platform_running platform invocation origin mask **
    critical_region_outside critical sg invocation checkpoint |--
  closed platform critical sg invocation origin mask checkpoint.
Proof. intros; unfold closed; entailer!. Qed.

End MutexCreateCall.

Module MutexCreateSpatial.

Definition priority_value (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pcp : Priority) : addr := prio_tbl_entry_to_addr sg (entry.(TskState).(prioTbl) pcp).

Definition priority_table (sg : StableGlobVars) (entry : UCOS2_Verify_State) : Assertion :=
  store_prio_tbl sg entry.(TskState).(prioTbl).

Definition priority_table_missing (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pcp : Priority) : Assertion := store_prio_tbl_missing_i sg entry.(TskState).(prioTbl) pcp.

Definition reserved_priority_table (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pcp : Priority) : Assertion := store_prio_tbl sg
    (mutex_create_priority_state sg pcp entry.(TskState)).(prioTbl).

Definition reserved_priority_table_missing (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pcp : Priority) : Assertion := store_prio_tbl_missing_i sg
    (mutex_create_priority_state sg pcp entry.(TskState)).(prioTbl) pcp.

Definition slot_available (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pcp : Priority) : Prop := pcp = sg.(osPrioMutexCeilDis) \/ entry.(TskState).(prioTbl) pcp = PTFree.

Definition free_head (sg : StableGlobVars) (entry : UCOS2_Verify_State) : addr :=
  event_encode_pool_link sg (hd_error entry.(EventState).(unUsedEventStates)).

(** Preserve the actual C pointer through the frontend's local-store
    normalization; its physical pool equality is opened by the spatial
    proof, not used to rename the program variable during symbolic execution. *)
Definition event_pointer_eq (sg : StableGlobVars) (eid : EventID) (actual : addr) : Prop :=
  actual = event_pool_addr sg eid.

Lemma priority_value_zero_is_free : forall sg entry pcp,
  UCOS2_state_inv sg entry -> task_priority_in_range sg pcp ->
  priority_value sg entry pcp = 0 -> entry.(TskState).(prioTbl) pcp = PTFree.
Proof.
  intros sg entry pcp Hvalid Hrange Hzero.
  pose proof Hvalid as [Hprofile [Htasks [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Hslots _]] _].
  specialize (Hslots pcp Hrange); unfold priority_value in Hzero.
  destruct (entry.(TskState).(prioTbl) pcp) as [| |tid] eqn:Hslot; [reflexivity|discriminate|].
  destruct Hslots as [node Hnode].
  pose proof (proj1 (proj1 Htasks)) as Hpool.
  assert (Htid : task_slot_in_range sg tid).
  { apply (proj2 (Hpool tid)); left; exists node; exact Hnode. }
  pose proof Hprofile as [Hstable _].
  pose proof (valid_stable_address_pos sg sg.(g_OSTCBTbl) Hstable) as Hbase.
  assert (Hin : In sg.(g_OSTCBTbl) (stable_global_addresses sg))
    by (unfold stable_global_addresses; simpl; tauto).
  specialize (Hbase Hin); unfold task_slot_in_range in Htid.
  cbn [prio_tbl_entry_to_addr] in Hzero; rewrite task_slot_addr_object_size in Hzero.
  assert (Hsize : task_object_size sg.(osKernelConfig) = 64).
  { apply task_object_size_tcb64; unfold selected_kernel_profile in Hprofile; tauto. }
  rewrite Hsize in Hzero; lia.
Qed.

Lemma priority_table_split_cell : forall sg entry pcp,
  0 <= pcp < 64 -> priority_table sg entry |--
  (sg.(g_OSTCBPrioTbl) + pcp * sizeof(PTR)) # Ptr |-> priority_value sg entry pcp **
  priority_table_missing sg entry pcp.
Proof. intros; apply store_prio_tbl_split_cell; assumption. Qed.

Lemma priority_table_merge_cell : forall sg entry pcp,
  0 <= pcp < 64 ->
  (sg.(g_OSTCBPrioTbl) + pcp * sizeof(PTR)) # Ptr |-> priority_value sg entry pcp **
  priority_table_missing sg entry pcp |-- priority_table sg entry.
Proof. intros; apply store_prio_tbl_merge_cell; assumption. Qed.

Lemma priority_table_merge_reserved_cell : forall sg entry pcp,
  0 <= pcp < 64 -> pcp <> sg.(osPrioMutexCeilDis) ->
  (sg.(g_OSTCBPrioTbl) + pcp * sizeof(PTR)) # Ptr |-> 1 **
  priority_table_missing sg entry pcp |-- reserved_priority_table sg entry pcp.
Proof.
  intros sg entry pcp Hrange Henabled; unfold reserved_priority_table.
  cbn [mutex_create_priority_state prioTbl].
  rewrite (proj2 (Z.eqb_neq _ _) Henabled).
  exact (store_prio_tbl_merge_updated_cell sg entry.(TskState).(prioTbl) pcp PTReserved Hrange).
Qed.

Lemma reserved_priority_table_disabled : forall sg entry pcp,
  pcp = sg.(osPrioMutexCeilDis) -> reserved_priority_table sg entry pcp = priority_table sg entry.
Proof.
  intros; unfold reserved_priority_table, priority_table.
  rewrite MutexCreateFull.priority_state_disabled by assumption; reflexivity.
Qed.

Lemma reserved_priority_table_split_cell : forall sg entry pcp,
  0 <= pcp < 64 -> pcp <> sg.(osPrioMutexCeilDis) ->
  reserved_priority_table sg entry pcp |--
  (sg.(g_OSTCBPrioTbl) + pcp * sizeof(PTR)) # Ptr |-> 1 **
    reserved_priority_table_missing sg entry pcp.
Proof.
  intros sg entry pcp Hrange Henabled.
  unfold reserved_priority_table, reserved_priority_table_missing.
  pose proof (store_prio_tbl_split_cell sg
    (mutex_create_priority_state sg pcp entry.(TskState)).(prioTbl) pcp Hrange) as Hsplit.
  cbn [mutex_create_priority_state prioTbl] in Hsplit |- *.
  rewrite (proj2 (Z.eqb_neq _ _) Henabled) in Hsplit |- *.
  rewrite update_prio_tbl_same in Hsplit; exact Hsplit.
Qed.

Lemma reserved_priority_table_rollback_cell : forall sg entry pcp,
  0 <= pcp < 64 -> pcp <> sg.(osPrioMutexCeilDis) -> slot_available sg entry pcp ->
  (sg.(g_OSTCBPrioTbl) + pcp * sizeof(PTR)) # Ptr |-> 0 **
    reserved_priority_table_missing sg entry pcp |-- priority_table sg entry.
Proof.
  intros sg entry pcp Hrange Henabled [Hdisabled|Hfree]; [contradiction|].
  unfold reserved_priority_table_missing, priority_table.
  eapply derivable1_trans; [apply (store_prio_tbl_merge_updated_cell sg
    (mutex_create_priority_state sg pcp entry.(TskState)).(prioTbl) pcp PTFree Hrange)|].
  cbn [mutex_create_priority_state prioTbl].
  rewrite (proj2 (Z.eqb_neq _ _) Henabled), update_prio_tbl_overwrite.
  rewrite <- Hfree at 1; rewrite update_prio_tbl_put_back; reflexivity.
Qed.

Lemma free_head_empty_iff : forall sg entry,
  UCOS2_state_inv sg entry ->
  (free_head sg entry = 0 <-> entry.(EventState).(unUsedEventStates) = []).
Proof.
  intros sg entry Hvalid; unfold free_head.
  destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead;
    [split; reflexivity|].
  split; [|discriminate]; intro Hzero.
  pose proof Hvalid as [Hprofile [_ [_ [[Hpool _] _]]]].
  pose proof (proj1 (event_pool_free_unallocated sg entry.(EventState) eid Hpool
    ltac:(rewrite Hhead; left; reflexivity))) as Hnone.
  assert (Hid : valid_event_id sg eid).
  { exact (proj1 (proj2 (proj1 Hpool)) eid ltac:(rewrite Hhead; left; reflexivity)). }
  pose proof Hprofile as [Hstable _].
  pose proof (valid_stable_address_pos sg sg.(g_OSEventTbl) Hstable) as Hbase.
  assert (Hin : In sg.(g_OSEventTbl) (stable_global_addresses sg))
    by (unfold stable_global_addresses; simpl; tauto).
  specialize (Hbase Hin); unfold valid_event_id in Hid.
  cbn [hd_error event_encode_pool_link] in Hzero.
  unfold event_pool_addr, event_object_size in Hzero.
  destruct sg.(osKernelConfig).(cfgEventNames); lia.
Qed.

Definition free_head_facts (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (eid : EventID) (rest : list EventID) (image : EventStorage) : Prop :=
  entry.(EventState).(unUsedEventStates) = eid :: rest /\
  entry.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image /\
  valid_event_id sg eid /\
  free_head sg entry = event_pool_addr sg eid /\
  image EventPtrField = Some (event_encode_pool_link sg (hd_error rest)) /\
  image EventTypeField = Some 0.

Lemma head_residual_open_free_head : forall sg entry,
  UCOS2_state_inv sg entry -> free_head sg entry <> 0 ->
  MutexCreateFull.head_residual sg entry |--
    EX eid rest image, coq_prop (free_head_facts sg entry eid rest image) &&
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
     MutexCreateFull.node_residual sg entry eid).
Proof.
  intros sg entry Hvalid Hnonempty.
  destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  { exfalso; apply Hnonempty; unfold free_head; rewrite Hhead; reflexivity. }
  pose proof Hvalid as [_ [_ [_ [[Hpool [[Hdomain [Hlinks Htypes]] _]] _]]]].
  assert (Hin : In eid entry.(EventState).(unUsedEventStates))
    by (rewrite Hhead; left; reflexivity).
  destruct (proj2 (Hdomain eid) Hin) as [image Himage].
  assert (Hid : valid_event_id sg eid) by (exact (proj1 (proj2 (proj1 Hpool)) eid Hin)).
  assert (Hnext : image EventPtrField = Some (event_encode_pool_link sg (hd_error rest))).
  { pose proof (Hlinks eid image Himage) as Hptr.
    rewrite Hhead in Hptr; cbn [kernel_list_next] in Hptr.
    destruct (Z.eq_dec eid eid); [exact Hptr|contradiction]. }
  assert (Hfacts : free_head_facts sg entry eid rest image).
  { unfold free_head_facts; split; [exact Hhead|]. split; [exact Himage|].
    split; [exact Hid|]. split; [unfold free_head; rewrite Hhead; reflexivity|].
    split; [exact Hnext|exact (Htypes eid image Himage)]. }
  Exists eid rest image.
  sep_apply_l_atomic (MutexCreateFull.head_residual_split_node sg entry eid image Himage).
  entailer!.
Qed.

Lemma head_residual_merge_node : forall sg entry eid image,
  entry.(EventState).(eventLifecycle).(eventFreeStorage) eid = Some image ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
    MutexCreateFull.node_residual sg entry eid |-- MutexCreateFull.head_residual sg entry.
Proof.
  intros sg entry eid image Himage.
  unfold MutexCreateFull.node_residual, MutexCreateFull.head_residual.
  sep_apply_l_atomic (event_free_storage_merge_eid sg entry.(EventState) eid image Himage).
  entailer!.
Qed.

Lemma node_merge_detached_inv : forall sg entry pcp eid rest image,
  UCOS2_state_inv sg entry -> free_head_facts sg entry eid rest image ->
  valid_mutex_pcp sg pcp -> slot_available sg entry pcp ->
  (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
   MutexCreateFull.node_residual sg entry eid) ** reserved_priority_table sg entry pcp **
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) |--
  event_private_storage_rep sg eid (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp) **
  UCOS2_inv sg (mutex_create_detached_state sg pcp eid rest entry).
Proof.
  intros sg entry pcp eid rest image Hvalid [Hhead [Himage Hrest]] Hpcp Hslot.
  sep_apply_l_atomic (head_residual_merge_node sg entry eid image Himage).
  unfold reserved_priority_table.
  sep_apply_l_atomic (MutexCreateFull.head_merge_detached_inv sg entry pcp eid rest image
    Hvalid Hhead Himage Hpcp Hslot); entailer!.
Qed.

Lemma private_stores_global_frame : forall sg eid writes before result after,
  event_create_private_stores eid writes before result after ->
  UCOS2_inv sg before |-- UCOS2_inv sg after.
Proof.
  intros sg eid writes; induction writes as [|[field stored] rest IH]; intros before result after Hsteps.
  - destruct Hsteps as [_ ->]; reflexivity.
  - destruct Hsteps as [allocation [Hget Htail]].
    eapply derivable1_trans; [apply UCOS2_event_private_write_global_frame; exact Hget|].
    eapply IH; exact Htail.
Qed.

Lemma private_initialization_merge : forall sg eid pcp before allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_create_image false 4 (pcp * 256 + 255) 0 0 allocation.(eventPrivateStorage)) **
  UCOS2_inv sg before |--
  EX after final,
    coq_prop (event_create_private_initialization eid false 4 (pcp * 256 + 255) 0 0 before tt after /\
      after.(EventState).(eventLifecycle).(eventPrivate) eid = Some final) &&
    (event_private_storage_rep sg eid final ** UCOS2_inv sg after).
Proof.
  intros sg eid pcp before allocation Hget.
  destruct (event_create_private_stores_exists eid
    (event_create_initialization_fields false 4 (pcp * 256 + 255) 0 0) before allocation Hget)
    as [after Hsteps].
  destruct (event_create_private_initialization_post eid false 4 (pcp * 256 + 255) 0 0
    before tt after allocation Hget Hsteps) as [final [Hfinal [_ [_ [_ Himage]]]]].
  Exists after final; unfold event_private_storage_rep; rewrite Himage.
  sep_apply_l_atomic (private_stores_global_frame sg eid _ before tt after Hsteps); entailer!.
Qed.

End MutexCreateSpatial.


Module MutexCreateInitialization.

Definition initialization_padding (base : addr) (image : EventStorage) : Assertion :=
  event_cell base EventPadding1 (image EventPadding1) **
  event_cell base EventPadding2 (image EventPadding2) **
  event_cell base EventPadding3 (image EventPadding3) **
  event_cell base EventPadding19 (image EventPadding19).

Lemma initialization_storage_split : forall base image,
  event_storage_rep false base image |--
    (base + 0) # UChar |->_ ** (base + 8) # UShort |->_ ** (base + 4) # Ptr |->_ **
    event_wait_list_init_pre (base + 10) (base + 11) ** initialization_padding base image.
Proof.
  intros base image; sep_apply_l_atomic (event_wait_list_init_storage_split false base image).
  assert (Hforget : forall field,
    event_cell base field (image field) |-- event_cell base field None).
  { intro field; destruct field; cbn [event_cell];
      match goal with |- context [image ?field] => destruct (image field) end;
      first [apply store_uchar_undef_store_uchar | apply store_ptr_undef_store_ptr |
        apply store_ushort_undef_store_ushort | entailer!]. }
  unfold event_wait_list_init_storage_frame.
  sep_apply_l_atomic (Hforget EventTypeField).
  sep_apply_l_atomic (Hforget EventPtrField).
  sep_apply_l_atomic (Hforget EventCntField).
  unfold initialization_padding; cbn [event_cell event_field_offset]; entailer!.
Qed.

Lemma initialization_storage_merge : forall base image pcp,
  (base + 0) # UChar |-> 4 ** (base + 8) # UShort |-> (pcp * 256 + 255) **
  (base + 4) # Ptr |-> 0 ** event_wait_list_init_post (base + 10) (base + 11) **
  initialization_padding base image |--
  event_storage_rep false base (event_create_image false 4 (pcp * 256 + 255) 0 0 image).
Proof.
  intros base image pcp; unfold event_create_image.
  eapply derivable1_trans; [|apply event_wait_list_init_storage_merge].
  unfold event_wait_list_init_storage_frame, initialization_padding.
  cbn [event_payload_init_image event_write field_update EventField_eq_dec
    event_cell event_field_offset].
  unfold event_write, field_update; simpl.
  entailer!.
Qed.

End MutexCreateInitialization.

Module MutexCreatePrivateContext.

Lemma event_interval_trans : forall critical sg task_invocation event_invocation first middle last,
  critical_region_event_interval critical sg task_invocation event_invocation first middle ->
  critical_region_event_interval critical sg task_invocation event_invocation middle last ->
  critical_region_event_interval critical sg task_invocation event_invocation first last.
Proof.
  intros critical sg task_invocation event_invocation first middle last Hfirst Hlast.
  eapply KernelResumptionTraceSegment with (stopped1 := false) (stopped2 := false).
  - eapply kernel_resumption_resource_trace_erases; exact Hfirst.
  - eapply kernel_resumption_resource_trace_timer_projection; exact Hfirst.
  - exact Hlast.
Qed.

Lemma private_stores_followed_by_environment :
  forall critical sg task_invocation event_invocation eid writes first current last,
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid writes first tt current ->
  critical_region_event_interval critical sg task_invocation event_invocation current last ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid writes first tt last.
Proof.
  intros critical sg task_invocation event_invocation eid writes.
  induction writes as [|[field stored] rest IH]; intros first current last Hstores Hinterval.
  - destruct Hstores as [_ Hfirst]; split; [reflexivity|eapply event_interval_trans; eassumption].
  - destruct Hstores as [entry [allocation [Hentry [Hget [Hinv Htail]]]]].
    exists entry, allocation; split; [exact Hentry|]; split; [exact Hget|].
    split; [exact Hinv|]; eapply IH; eassumption.
Qed.

Lemma private_stores_append_store :
  forall critical sg task_invocation event_invocation eid writes first current allocation field stored,
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid writes first tt current ->
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid
    (writes ++ [(field, stored)]) first tt
    (replace_EventS (event_private_write current.(EventState) eid allocation field (Some stored)) current).
Proof.
  intros critical sg task_invocation event_invocation eid writes.
  induction writes as [|[head_field head_value] rest IH];
    intros first current allocation field stored Hstores Hget Hinv.
  - destruct Hstores as [_ Hinterval]; exists current, allocation.
    split; [exact Hinterval|]. split; [exact Hget|]. split; [exact Hinv|].
    split; [reflexivity|constructor].
  - destruct Hstores as [entry [head_allocation [Hentry [Hhead [Hhead_inv Htail]]]]].
    exists entry, head_allocation; split; [exact Hentry|]. split; [exact Hhead|].
    split; [exact Hhead_inv|]; eapply IH; eassumption.
Qed.

Lemma stores_image_append_store : forall image writes field stored,
  event_create_stores_image image (writes ++ [(field, stored)]) =
  event_write (event_create_stores_image image writes) field (Some stored).
Proof. intros; unfold event_create_stores_image; rewrite fold_left_app; reflexivity. Qed.

(** One shared region with a current state, not an invariant frozen at
    Restore. The private bytes are owned separately by the caller. *)
Definition private_store_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (task_invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (eid : EventID) (initial : UCOS2_Verify_State) (allocation : EventPrivateAllocation)
  (writes : list (EventField * Z)) : Assertion :=
  EX current,
    coq_prop (sem_create_private_stores_interleaved critical sg task_invocation
      allocation.(eventPrivateInvocation) eid writes initial tt current) &&
    MutexCreateCall.closed platform critical sg task_invocation origin mask current.

Lemma private_store_context_begin : forall platform critical sg task_invocation origin mask eid initial allocation,
  MutexCreateCall.closed platform critical sg task_invocation origin mask initial |--
  private_store_context platform critical sg task_invocation origin mask eid initial allocation [].
Proof.
  intros; unfold private_store_context; Exists initial.
  assert (Hnil : sem_create_private_stores_interleaved critical sg task_invocation
    allocation.(eventPrivateInvocation) eid [] initial tt initial)
    by (split; [reflexivity|constructor]).
  entailer!.
Qed.

(** The new heap is an INPUT. A pure environment trace does not turn the
    old heap into changed global bytes; the CPU/CSL environment boundary
    must supply its actual current raw representation. *)
Lemma private_store_context_after_environment :
  forall platform critical sg task_invocation origin mask eid initial allocation writes current after,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  sem_create_private_stores_interleaved critical sg task_invocation
    allocation.(eventPrivateInvocation) eid writes initial tt current ->
  critical_region_event_interval critical sg task_invocation allocation.(eventPrivateInvocation) current after ->
  interrupt_platform_running platform task_invocation origin mask ** UCOS2_raw_rep sg after |--
  private_store_context platform critical sg task_invocation origin mask eid initial allocation writes.
Proof.
  intros platform critical sg task_invocation origin mask eid initial allocation writes current after
    Hvalid Hget Hstores Hinterval.
  pose proof (private_stores_followed_by_environment critical sg task_invocation
    allocation.(eventPrivateInvocation) eid writes initial current after Hstores Hinterval) as Hafter.
  pose proof (proj1 (sem_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ _ Hvalid Hget eq_refl Hafter)) as HvalidAfter.
  unfold private_store_context; Exists after.
  rewrite MutexCreateCall.closed_equiv; unfold UCOS2_inv; entailer!.
Qed.

Lemma private_store_context_open :
  forall platform critical sg task_invocation origin mask eid initial allocation writes,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  private_store_context platform critical sg task_invocation origin mask eid initial allocation writes |--
  EX current final,
    coq_prop (sem_create_private_stores_interleaved critical sg task_invocation
      allocation.(eventPrivateInvocation) eid writes initial tt current /\
      current.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
      final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
      final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
      final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
      final.(eventPrivateMutexPCP) = allocation.(eventPrivateMutexPCP) /\
      final.(eventPrivateStorage) = event_create_stores_image allocation.(eventPrivateStorage) writes) &&
    (interrupt_platform_running platform task_invocation origin mask ** UCOS2_inv sg current).
Proof.
  intros platform critical sg task_invocation origin mask eid initial allocation writes Hvalid Hget.
  unfold private_store_context; Intros current.
  match goal with Hsteps : sem_create_private_stores_interleaved _ _ _ _ _ _ _ _ _ |- _ =>
    pose proof Hsteps as Hstores end.
  destruct (sem_create_private_stores_interleaved_post
    _ _ _ _ _ _ _ _ _ _ Hvalid Hget eq_refl Hstores)
    as [Hcurrent [final [Hfinal [Hinv [Hgen [Hqueue Himage]]]]]].
  pose proof (sem_create_private_stores_interleaved_mutex_pcp_eq
    _ _ _ _ _ _ _ _ _ _ _ Hvalid Hget eq_refl Hstores Hfinal) as Hpcp.
  Exists current final; rewrite MutexCreateCall.closed_equiv; entailer!.
Qed.

Lemma private_store_context_merge_written_field :
  forall platform critical sg task_invocation origin mask eid initial allocation writes field stored,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_cell (event_pool_addr sg eid) field (Some stored) **
    private_store_context platform critical sg task_invocation origin mask eid initial allocation writes |--
  event_cell (event_pool_addr sg eid) field (Some stored) **
    private_store_context platform critical sg task_invocation origin mask eid initial allocation
      (writes ++ [(field, stored)]).
Proof.
  intros platform critical sg task_invocation origin mask eid initial allocation writes field stored
    Hvalid Hget.
  sep_apply_l_atomic (private_store_context_open platform critical sg task_invocation origin mask
    eid initial allocation writes Hvalid Hget).
  Intros current final.
  match goal with Hfacts : _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ =>
    destruct Hfacts as [Hstores [Hfinal [Hinv [Hgen [Hqueue [Hpcp Himage]]]]]] end.
  sep_apply_l_atomic (UCOS2_event_private_write_global_frame sg current eid final field (Some stored) Hfinal).
  unfold private_store_context; Exists
    (replace_EventS (event_private_write current.(EventState) eid final field (Some stored)) current).
  assert (Hafter : sem_create_private_stores_interleaved critical sg task_invocation
    allocation.(eventPrivateInvocation) eid (writes ++ [(field, stored)]) initial tt
    (replace_EventS (event_private_write current.(EventState) eid final field (Some stored)) current)).
  { eapply private_stores_append_store; eassumption. }
  rewrite MutexCreateCall.closed_equiv; entailer!.
Qed.

Lemma private_stores_append_private_stores :
  forall critical sg task_invocation event_invocation eid additional writes initial current last allocation,
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid writes initial tt current ->
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateInvocation) = event_invocation ->
  event_create_private_stores eid additional current tt last ->
  sem_create_private_stores_interleaved critical sg task_invocation event_invocation eid
    (writes ++ additional) initial tt last.
Proof.
  intros critical sg task_invocation event_invocation eid additional.
  induction additional as [|[field stored] rest IH]; intros writes initial current last allocation
    Hprefix Hget Hinv Htail.
  - destruct Htail as [_ ->]; rewrite app_nil_r; exact Hprefix.
  - destruct Htail as [current_allocation [Hcurrent Htail]].
    assert (current_allocation = allocation) by congruence; subst current_allocation.
    replace (writes ++ (field, stored) :: rest) with ((writes ++ [(field, stored)]) ++ rest)
      by (rewrite <- app_assoc; reflexivity).
    eapply (IH _ _ _ _
      {| eventPrivateInvocation := allocation.(eventPrivateInvocation);
         eventPrivateGeneration := allocation.(eventPrivateGeneration);
         eventPrivateQueue := allocation.(eventPrivateQueue);
         eventPrivateMutexPCP := allocation.(eventPrivateMutexPCP);
         eventPrivateStorage := event_write allocation.(eventPrivateStorage) field (Some stored) |}).
    + eapply private_stores_append_store; eassumption.
    + apply kernel_map_set_same.
    + exact Hinv.
    + exact Htail.
Qed.

Definition wait_list_stores : list (EventField * Z) :=
  [(EventGrpField, 0)] ++ map (fun row => (event_table_field (Z.of_nat row), 0)) (seq 0 8).

(** The helper contract supplies all nine written bytes.  This lemma updates
    the private image in the supplied current context; it does not establish
    stability of that physical frame across C environment steps.  Such a
    step must supply the resumed heap to [private_store_context_after_environment].
    The public helper still owns and writes exactly the bitmap bytes. *)
Lemma private_store_context_merge_wait_list :
  forall platform critical sg task_invocation origin mask eid initial allocation writes,
  UCOS2_state_inv sg initial ->
  initial.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    private_store_context platform critical sg task_invocation origin mask eid initial allocation writes |--
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    private_store_context platform critical sg task_invocation origin mask eid initial allocation
      (writes ++ wait_list_stores).
Proof.
  intros platform critical sg task_invocation origin mask eid initial allocation writes Hvalid Hget.
  sep_apply_l_atomic (private_store_context_open platform critical sg task_invocation origin mask
    eid initial allocation writes Hvalid Hget).
  Intros current final.
  match goal with Hfacts : _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ =>
    destruct Hfacts as [Hstores [Hfinal [Hinv [Hgen [Hqueue [Hpcp Himage]]]]]] end.
  destruct (event_create_private_stores_exists eid wait_list_stores current final Hfinal)
    as [after Htail].
  sep_apply_l_atomic (MutexCreateSpatial.private_stores_global_frame sg eid wait_list_stores current tt after Htail).
  unfold private_store_context; Exists after.
  assert (Hafter : sem_create_private_stores_interleaved critical sg task_invocation
    allocation.(eventPrivateInvocation) eid (writes ++ wait_list_stores) initial tt after).
  { eapply private_stores_append_private_stores; eassumption. }
  rewrite MutexCreateCall.closed_equiv; entailer!.
Qed.

Definition initialization_prefix (pcp phase : Z) : list (EventField * Z) :=
  if phase =? 0 then [] else
  if phase =? 1 then [(EventTypeField, 4)] else
  if phase =? 2 then [(EventTypeField, 4); (EventCntField, pcp * 256 + 255)] else
  if phase =? 3 then [(EventTypeField, 4); (EventCntField, pcp * 256 + 255); (EventPtrField, 0)] else
  event_create_initialization_fields false 4 (pcp * 256 + 255) 0 0.

Definition initialization_facts (sg : StableGlobVars) (entry : UCOS2_Verify_State)
  (pcp : Priority) (eid : EventID) (rest : list EventID) (image : EventStorage) : Prop :=
  UCOS2_state_inv sg entry /\ MutexCreateSpatial.free_head_facts sg entry eid rest image /\
  valid_mutex_pcp sg pcp /\ MutexCreateSpatial.slot_available sg entry pcp.

Lemma initialization_facts_detached : forall sg entry pcp eid rest image,
  initialization_facts sg entry pcp eid rest image ->
  UCOS2_state_inv sg (mutex_create_detached_state sg pcp eid rest entry) /\
  (mutex_create_detached_state sg pcp eid rest entry).(EventState).(eventLifecycle).(eventPrivate) eid =
    Some (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp).
Proof.
  intros sg entry pcp eid rest image [Hvalid [Hfacts [Hpcp Hslot]]].
  destruct Hfacts as [Hhead [Himage Hrest]].
  split.
  - apply MutexCreateFull.detached_state_preserves_validity; assumption.
  - cbn [mutex_create_detached_state replace_EventS EventState replace_TskS].
    rewrite MutexCreateFull.detached_private_lookup.
    unfold mutex_create_storage; rewrite Himage; reflexivity.
Qed.

Definition initialization_context (platform : InterruptPlatformResources)
  (critical : CriticalRegionResources) (sg : StableGlobVars)
  (task_invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (entry : UCOS2_Verify_State) (pcp : Priority) (eid : EventID)
  (rest : list EventID) (image : EventStorage) (phase : Z) : Assertion :=
  coq_prop (initialization_facts sg entry pcp eid rest image) &&
  private_store_context platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    (initialization_prefix pcp phase).

Lemma initialization_context_begin : forall platform critical sg task_invocation origin mask entry pcp eid rest image,
  initialization_facts sg entry pcp eid rest image ->
  MutexCreateCall.closed platform critical sg task_invocation origin mask
    (mutex_create_detached_state sg pcp eid rest entry) |--
  initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 0.
Proof.
  intros; unfold initialization_context; unfold initialization_prefix.
  sep_apply_l_atomic (private_store_context_begin platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)); entailer!.
Qed.

(** Conditional transport of the initialization prefix.  This rule consumes
    the actual resumed heap, not the old one.  The source-execution boundary
    still has to produce that heap and invoke this rule between unmasked
    stores/helper steps; the ordinary C frame rule does not do so.
    The registered event interval preserves allocation identity, pending
    PCP, generation and the already executed image prefix. *)
Lemma initialization_context_after_environment :
  forall platform critical sg task_invocation origin mask entry pcp eid rest image phase current after,
  initialization_facts sg entry pcp eid rest image ->
  sem_create_private_stores_interleaved critical sg task_invocation
    entry.(EventState).(eventLifecycle).(eventNextInvocation) eid
    (initialization_prefix pcp phase) (mutex_create_detached_state sg pcp eid rest entry) tt current ->
  critical_region_event_interval critical sg task_invocation
    entry.(EventState).(eventLifecycle).(eventNextInvocation) current after ->
  interrupt_platform_running platform task_invocation origin mask ** UCOS2_raw_rep sg after |--
  initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image phase.
Proof.
  intros platform critical sg task_invocation origin mask entry pcp eid rest image phase current after
    Hfacts Hstores Hinterval.
  destruct (initialization_facts_detached _ _ _ _ _ _ Hfacts) as [Hvalid Hget].
  unfold initialization_context.
  sep_apply_l_atomic (private_store_context_after_environment platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    (initialization_prefix pcp phase) current after Hvalid Hget Hstores Hinterval).
  entailer!.
Qed.

Lemma initialization_context_merge_type : forall platform critical sg task_invocation origin mask entry pcp eid rest image,
  (event_pool_addr sg eid + 0) # UChar |-> 4 **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 0 |--
  (event_pool_addr sg eid + 0) # UChar |-> 4 **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 1.
Proof.
  intros; unfold initialization_context; Intros.
  match goal with Hfacts : initialization_facts _ _ _ _ _ _ |- _ =>
    destruct (initialization_facts_detached _ _ _ _ _ _ Hfacts) as [Hvalid Hget] end.
  sep_apply_l_atomic (private_store_context_merge_written_field platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    [] EventTypeField 4 Hvalid Hget); entailer!.
Qed.

Lemma initialization_context_merge_count : forall platform critical sg task_invocation origin mask entry pcp eid rest image,
  (event_pool_addr sg eid + 8) # UShort |-> (pcp * 256 + 255) **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 1 |--
  (event_pool_addr sg eid + 8) # UShort |-> (pcp * 256 + 255) **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 2.
Proof.
  intros; unfold initialization_context; Intros.
  match goal with Hfacts : initialization_facts _ _ _ _ _ _ |- _ =>
    destruct (initialization_facts_detached _ _ _ _ _ _ Hfacts) as [Hvalid Hget] end.
  sep_apply_l_atomic (private_store_context_merge_written_field platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    [(EventTypeField, 4)] EventCntField (pcp * 256 + 255) Hvalid Hget); entailer!.
Qed.

Lemma initialization_context_merge_pointer : forall platform critical sg task_invocation origin mask entry pcp eid rest image,
  (event_pool_addr sg eid + 4) # Ptr |-> 0 **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 2 |--
  (event_pool_addr sg eid + 4) # Ptr |-> 0 **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 3.
Proof.
  intros; unfold initialization_context; Intros.
  match goal with Hfacts : initialization_facts _ _ _ _ _ _ |- _ =>
    destruct (initialization_facts_detached _ _ _ _ _ _ Hfacts) as [Hvalid Hget] end.
  sep_apply_l_atomic (private_store_context_merge_written_field platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    [(EventTypeField, 4); (EventCntField, pcp * 256 + 255)] EventPtrField 0 Hvalid Hget); entailer!.
Qed.

Lemma initialization_context_merge_wait_list : forall platform critical sg task_invocation origin mask entry pcp eid rest image,
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 3 |--
  event_wait_list_init_post (event_pool_addr sg eid + 10) (event_pool_addr sg eid + 11) **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 4.
Proof.
  intros; unfold initialization_context; Intros.
  match goal with Hfacts : initialization_facts _ _ _ _ _ _ |- _ =>
    destruct (initialization_facts_detached _ _ _ _ _ _ Hfacts) as [Hvalid Hget] end.
  sep_apply_l_atomic (private_store_context_merge_wait_list platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    (initialization_prefix pcp 3) Hvalid Hget); entailer!.
Qed.

Lemma initialization_context_publish :
  forall platform critical sg task_invocation origin mask before entry pcp eid rest image,
  critical_region_interval critical sg task_invocation before entry ->
  before.(IntrState).(intNesting) <= 0 ->
  event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 4 (pcp * 256 + 255) 0 0 image) **
    initialization_context platform critical sg task_invocation origin mask entry pcp eid rest image 4 |--
  EX after,
    coq_prop (MutexCreateCall.result_prop critical sg task_invocation pcp before after
      (event_pool_addr sg eid) 0) &&
    MutexCreateCall.closed platform critical sg task_invocation origin mask after.
Proof.
  intros platform critical sg task_invocation origin mask before entry pcp eid rest image Hentry Hnesting.
  unfold initialization_context; Intros.
  match goal with Hfacts : initialization_facts _ _ _ _ _ _ |- _ =>
    pose proof Hfacts as [Hvalid [Hheadfacts [Hpcp Hslot]]];
    destruct (initialization_facts_detached _ _ _ _ _ _ Hfacts) as [Hdetached Hget] end.
  pose proof Hheadfacts as [Hhead [Hfreeimage Hrest]].
  sep_apply_l_atomic (private_store_context_open platform critical sg task_invocation origin mask eid
    (mutex_create_detached_state sg pcp eid rest entry)
    (MutexCreateFull.detached_allocation sg entry.(EventState) image pcp)
    (initialization_prefix pcp 4) Hdetached Hget).
  Intros current final.
  match goal with Hfacts : _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ =>
    destruct Hfacts as [Hstores [Hfinal [Hinv [Hgen [Hqueue [Hlease Himage]]]]]] end.
  change (initialization_prefix pcp 4) with
    (event_create_initialization_fields false 4 (pcp * 256 + 255) 0 0) in Hstores, Himage.
  rewrite event_create_stores_image_initialization_eq in Himage.
  cbn [MutexCreateFull.detached_allocation eventPrivateStorage eventPrivateQueue eventPrivateMutexPCP] in Himage, Hqueue, Hlease.
  assert (Hcurrent : UCOS2_state_inv sg current).
  { eapply (proj1 (sem_create_private_stores_interleaved_post
      _ _ _ _ _ _ _ _ _ _ Hdetached Hget eq_refl Hstores)). }
  assert (Hnames : cfgEventNames (osKernelConfig sg) = false).
  { destruct Hcurrent as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  assert (Hallocation : MutexCreateCall.allocation_pcp sg pcp final) by exact Hlease.
  assert (Hrejected : MutexCreateCall.priority_rejected sg pcp = false).
  { unfold MutexCreateCall.priority_rejected; destruct (pcp =? osPrioMutexCeilDis sg) eqn:Hdisabled.
    - reflexivity.
    - apply Z.eqb_neq in Hdisabled; destruct Hpcp as [Hbad|[_ Hlt]]; [contradiction|].
      apply Z.leb_gt in Hlt; rewrite Hlt; reflexivity. }
  assert (Hnotisr : (0 <? intNesting (IntrState before)) = false) by (apply Z.ltb_ge; exact Hnesting).
  assert (Hbusy : MutexCreateCall.priority_slot_busy sg pcp entry = false).
  { apply MutexCreateCall.priority_slot_available_iff; exact Hslot. }
  set (published := replace_EventS
    (event_publish current.(EventState) eid (MutexCreateCall.initialized_event pcp final)) current).
  assert (Hresult : MutexCreateCall.result_prop critical sg task_invocation pcp before published
    (event_pool_addr sg eid) 0).
  { exists (OS_ERR_NONE, Some eid); split.
    - unfold MutexCreateCall.call_relation; rewrite Hrejected, Hnotisr.
      exists entry, (mutex_create_detached_state sg pcp eid rest entry), (OS_ERR_NONE, Some (eid, image)).
      split; [exact Hentry|]; split.
      + unfold MutexCreateCall.allocate_critical; rewrite Hbusy, Hhead.
        exists image; split; [exact Hfreeimage|]; split; reflexivity.
      + exists current, final; split; [exact Hstores|].
        split; [exact Hfinal|]; split; reflexivity.
    - split; reflexivity. }
  assert (Hstorage : event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 4 (pcp * 256 + 255) 0 0 image) |-- event_private_storage_rep sg eid final).
  { unfold event_private_storage_rep; rewrite Hnames, Himage; reflexivity. }
  sep_apply_l_atomic Hstorage.
  rewrite (UCOS2_inv_split_event_queue sg current); Intros.
  Exists published; rewrite MutexCreateCall.closed_equiv.
  eapply derivable1_trans with (y :=
    interrupt_platform_running platform task_invocation origin mask ** UCOS2_inv sg published).
  2: { entailer!. }
  unfold published.
  eapply derivable1_trans.
  2: { apply derivable1_sepcon_mono; [reflexivity|exact (MutexCreateCall.publish_merge sg current eid final image pcp
    Hcurrent Hfinal Hqueue Hallocation Hpcp Himage)]. }
  entailer!.
Qed.

End MutexCreatePrivateContext.
