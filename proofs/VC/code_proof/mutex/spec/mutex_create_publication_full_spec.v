Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia Coq.Logic.FunctionalExtensionality.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Ucos2Verify.lib.stable_glob_vars.
Require Import Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib.
Require Import Ucos2Verify.lib.ucos2_spatial.
Require Import Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.lib.task.
Require Import Ucos2Verify.lib.task_storage.
Require Import Ucos2Verify.lib.task_stack.
Require Import Ucos2Verify.lib.event.
Require Import Ucos2Verify.lib.event_registration.
Require Import Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.atomic_ops_lib.
Require Import Ucos2Verify.lib.error_codes.
Require Import Ucos2Verify.lib.event_pool.
Require Import Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_resources.
Require Import Ucos2Verify.lib.kernel_names.
Require Export Ucos2Verify.lib.kernel_literal_resources.
Require Import Ucos2Verify.lib.cross_module_invariants.
Require Import Ucos2Verify.lib.queue_core.
Require Import Ucos2Verify.lib.sched.
Require Import Ucos2Verify.lib.mutex_create_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_call_spec.
Require Import Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.mutex_create_call_spec.
Require Import Ucos2Verify.VC.code.mutex.spec.full_interrupt_localization.
Import UCOS2_C_Rules ListNotations TaskStateDef EventStateDef EventFieldStorage.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope sac_scope.

Module MutexCreatePublicationFull.

(** Original full-profile [struct os_event] has the optional pointer at
    byte 20. This extends the existing source/ABI address binding, not an
    assumption about the value of any caller argument. *)
Definition named_event_table_layout (sg : StableGlobVars) : Prop :=
  event_table_layout_prop sg /\ forall eid, valid_event_id sg eid ->
    (&(((event_pool_addr sg eid)) # "os_event" ->ₛ "OSEventName")) = event_pool_addr sg eid + 20.

Lemma named_event_table_layout_core : forall sg eid,
  named_event_table_layout sg -> valid_event_id sg eid -> event_object_layout_prop sg eid.
Proof. intros sg eid [Hcore _] Hid; exact (Hcore eid Hid). Qed.

(** A source-program resource binding, not an application input-domain
    restriction and not a consequence of generic kernel validity.  Its
    initialization must consume the actual compiled literal's bytes. *)
Definition static_literal_bound (state : UCOS2_Verify_State)
  (LitMap : string -> addr) : Prop :=
  state.(NameState).(nameBytes) (LitMap "?"%string) = Some 63 /\
  state.(NameState).(nameBytes) (LitMap "?"%string + 1) = Some 0.

Definition static_program_inv (sg : StableGlobVars) (state : UCOS2_Verify_State)
  (LitMap : string -> addr) : Assertion :=
  coq_prop (static_literal_bound state LitMap) &&
    (UCOS2_full_inv sg state ** GlobalStrings_missing LitMap ["?"%string]).

Lemma static_literal_bound_readable : forall state LitMap,
  static_literal_bound state LitMap -> readable_name state.(NameState) (LitMap "?"%string) [63].
Proof.
  intros state LitMap [Hchar Hnul].
  unfold readable_name; split.
  - repeat constructor; lia.
  - split.
    + intros i byte Hnth; destruct i; simpl in Hnth;
        [injection Hnth as Hbyte; subst byte|destruct i; discriminate].
      simpl; replace (LitMap "?"%string + 0) with (LitMap "?"%string) by lia; exact Hchar.
    + simpl; exact Hnul.
Qed.

(** The optional source store changes the live Name field.  It does not
    create the bytes of the literal or register their ownership by fiat. *)
Definition publication_events (pcp : Priority) (eid : EventID)
  (rest : list EventID) (name : addr) (events : Glob_EventAbstractState)
  : Glob_EventAbstractState :=
  let image := mutex_create_storage events eid in
  event_publish (event_detach_head events eid rest image) eid
    (event_set_name
      (mutex_create_node pcp events.(eventLifecycle).(eventNextGeneration) image) name).

Definition publication_state (sg : StableGlobVars) (pcp : Priority)
  (eid : EventID) (rest : list EventID) (name : addr)
  (before : UCOS2_Verify_State) : UCOS2_Verify_State :=
  replace_EventS (publication_events pcp eid rest name before.(EventState))
    (replace_TskS (mutex_create_priority_state sg pcp before.(TskState)) before).

Definition critical_operation (sg : StableGlobVars) (pcp : Priority) (name : addr)
  : program UCOS2_Verify_State (OSErrCode * option EventID) :=
  fun entry result checkpoint =>
    if MutexCreateCall.priority_slot_busy sg pcp entry then
      result = (OS_ERR_PRIO_EXIST, None) /\ checkpoint = entry
    else match entry.(EventState).(unUsedEventStates) with
    | [] => result = (OS_ERR_PEVENT_NULL, None) /\ checkpoint = entry
    | eid :: rest => result = (OS_ERR_NONE, Some eid) /\
        checkpoint = publication_state sg pcp eid rest name entry
    end.

Definition call_relation (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (name : addr) (before : UCOS2_Verify_State)
  (result : OSErrCode * option EventID) (after : UCOS2_Verify_State) : Prop :=
  if MutexCreateCall.priority_rejected sg pcp then
    result = (OS_ERR_PRIO_INVALID, None) /\ after = before
  else if 0 <? before.(IntrState).(intNesting) then
    result = (OS_ERR_CREATE_ISR, None) /\ after = before
  else exists entry checkpoint,
    critical_region_interval critical sg invocation before entry /\
    critical_operation sg pcp name entry result checkpoint /\
    critical_region_interval critical sg invocation checkpoint after.

Definition publication_call_program (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (name : addr) : program UCOS2_Verify_State addr :=
  fun before pointer after => exists result,
    call_relation critical sg invocation pcp name before result after /\
    pointer = event_encode_pool_link sg (snd result).

Definition publication_result_prop (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (pcp : Priority) (name : addr) (before after : UCOS2_Verify_State)
  (pointer error : Z) : Prop := exists result,
    call_relation critical sg invocation pcp name before result after /\
    pointer = event_encode_pool_link sg (snd result) /\
    error = encode_os_err_code (fst result).

Lemma publication_result_prop_call_program : forall critical sg invocation pcp name before after pointer error,
  publication_result_prop critical sg invocation pcp name before after pointer error ->
  publication_call_program critical sg invocation pcp name before pointer after.
Proof. intros * [result [Hcall [Hpointer _]]]; exists result; auto. Qed.

(** This interface states the full-profile call boundary explicitly.  No
    theorem here claims that ordinary selected-client traces establish the
    full registered invariant, or that the CPU implementation produces it. *)
Definition closed (platform : InterruptPlatformResources) (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (origin : TaskInvocationOrigin) (mask : Z)
  (state : UCOS2_Verify_State) (LitMap : string -> addr) : Assertion :=
  coq_prop (UCOS2_full_state_inv sg state /\ static_literal_bound state LitMap) &&
    (interrupt_platform_running platform invocation origin mask **
     critical_region_outside critical sg invocation state ** GlobalStrings_missing LitMap ["?"%string]).

Definition acquire_facts (critical : CriticalRegionResources) (sg : StableGlobVars)
  (invocation : nat) (mask saved : Z) (before entry : UCOS2_Verify_State) : Prop :=
  critical_region_interval critical sg invocation before entry /\
  UCOS2_full_state_inv sg entry /\ interrupt_saved_value mask saved.

Lemma closed_equiv : forall platform critical sg invocation origin mask state LitMap,
  closed platform critical sg invocation origin mask state LitMap --||--
    (interrupt_platform_running platform invocation origin mask ** static_program_inv sg state LitMap).
Proof.
  intros; unfold closed; rewrite sem_create_closed_region_equiv.
  unfold static_program_inv, UCOS2_full_inv; split; entailer!.
Qed.

Lemma static_program_inv_literal_view : forall sg state LitMap,
  static_program_inv sg state LitMap --||--
  coq_prop (static_literal_bound state LitMap) &&
    (UCOS2_full_inv_without_question_mark sg state (LitMap "?"%string) **
     store_stringLit (LitMap "?"%string) "?"%string **
     GlobalStrings_missing LitMap ["?"%string]).
Proof.
  intros sg state LitMap; unfold static_program_inv; split; pureIntros_without_rename.
  all: match goal with H : static_literal_bound ?st ?lit |- _ =>
    pose proof H as [Hchar Hnul];
    rewrite (UCOS2_full_inv_split_question_mark sg st (lit "?"%string) Hchar Hnul)
  end.
  all: entailer!.
Qed.

Lemma closed_literal_view : forall platform critical sg invocation origin mask state LitMap,
  closed platform critical sg invocation origin mask state LitMap --||--
    coq_prop (static_literal_bound state LitMap) &&
    (interrupt_platform_running platform invocation origin mask **
     UCOS2_full_inv_without_question_mark sg state (LitMap "?"%string) **
     store_stringLit (LitMap "?"%string) "?"%string **
     GlobalStrings_missing LitMap ["?"%string]).
Proof.
  intros; rewrite closed_equiv, static_program_inv_literal_view; split; entailer!.
Qed.

Lemma head_split_merge : forall sg s,
  UCOS2_full_inv sg s --||-- coq_prop (UCOS2_full_state_inv sg s) &&
    (store_prio_tbl sg s.(TskState).(prioTbl) **
     event_free_root_rep sg s.(EventState) ** MutexCreateFull.head_residual sg s).
Proof.
  intros sg s.
  rewrite (UCOS2_full_inv_split_two sg s TaskModule EventModule ltac:(discriminate)).
  unfold MutexCreateFull.head_residual; cbn [UCOS2_module_rep].
  unfold task_shared_rep, event_raw_rep.
  rewrite task_public_storage_prio_tbl_equiv.
  split; entailer!.
Qed.

Definition initialization_writes (pcp : Priority) (name : addr) : list (EventField * Z) :=
  [(EventCntField, pcp * 256 + 255); (EventPtrField, 0); (EventNameField, name)] ++
  MutexCreatePrivateContext.wait_list_stores ++ [(EventTypeField, 4)].

Lemma initialization_image_eq : forall pcp name image,
  event_create_stores_image image (initialization_writes pcp name) =
    event_create_image true 4 (pcp * 256 + 255) 0 name image.
Proof.
  intros; apply functional_extensionality; intro field; destruct field; reflexivity.
Qed.

Lemma initialization_storage_split : forall base image,
  event_storage_rep true base image |--
    (base + 0) # UChar |->_ ** (base + 8) # UShort |->_ **
    (base + 4) # Ptr |->_ ** (base + 20) # Ptr |->_ **
    event_wait_list_init_pre (base + 10) (base + 11) **
    MutexCreateInitialization.initialization_padding base image.
Proof.
  intros base image; sep_apply_l_atomic (event_wait_list_init_storage_split true base image).
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
  sep_apply_l_atomic (Hforget EventNameField).
  unfold MutexCreateInitialization.initialization_padding;
    cbn [event_cell event_field_offset]; entailer!.
Qed.

Lemma initialization_storage_merge : forall base image pcp name,
  (base + 0) # UChar |-> 4 ** (base + 8) # UShort |-> (pcp * 256 + 255) **
  (base + 4) # Ptr |-> 0 ** (base + 20) # Ptr |-> name **
  event_wait_list_init_post (base + 10) (base + 11) **
  MutexCreateInitialization.initialization_padding base image |--
  event_storage_rep true base (event_create_image true 4 (pcp * 256 + 255) 0 name image).
Proof.
  intros base image pcp name; unfold event_create_image.
  eapply derivable1_trans; [|apply event_wait_list_init_storage_merge].
  unfold event_wait_list_init_storage_frame, MutexCreateInitialization.initialization_padding.
  cbn [event_payload_init_image event_write field_update EventField_eq_dec
    event_cell event_field_offset].
  unfold event_write, field_update; simpl; entailer!.
Qed.

Lemma free_head_empty_iff : forall sg entry,
  UCOS2_full_state_inv sg entry ->
  (MutexCreateSpatial.free_head sg entry = 0 <-> entry.(EventState).(unUsedEventStates) = []).
Proof.
  intros sg entry Hvalid; unfold MutexCreateSpatial.free_head.
  destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead;
    [split; reflexivity|].
  split; [|discriminate]; intro Hzero.
  pose proof Hvalid as [Hprofile [_ [_ [[Hpool _] _]]]].
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

Lemma head_residual_open_free_head : forall sg entry,
  UCOS2_full_state_inv sg entry -> MutexCreateSpatial.free_head sg entry <> 0 ->
  MutexCreateFull.head_residual sg entry |--
    EX eid rest image, coq_prop (MutexCreateSpatial.free_head_facts sg entry eid rest image) &&
    (event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image **
     MutexCreateFull.node_residual sg entry eid).
Proof.
  intros sg entry Hvalid Hnonempty.
  destruct entry.(EventState).(unUsedEventStates) as [|eid rest] eqn:Hhead.
  { exfalso; apply Hnonempty; unfold MutexCreateSpatial.free_head; rewrite Hhead; reflexivity. }
  pose proof Hvalid as [_ [_ [_ [[Hpool [[Hdomain [Hlinks Htypes]] _]] _]]]].
  assert (Hin : In eid entry.(EventState).(unUsedEventStates))
    by (rewrite Hhead; left; reflexivity).
  destruct (proj2 (Hdomain eid) Hin) as [image Himage].
  assert (Hid : valid_event_id sg eid) by (exact (proj1 (proj2 (proj1 Hpool)) eid Hin)).
  assert (Hnext : image EventPtrField = Some (event_encode_pool_link sg (hd_error rest))).
  { pose proof (Hlinks eid image Himage) as Hptr.
    rewrite Hhead in Hptr; cbn [kernel_list_next] in Hptr.
    destruct (Z.eq_dec eid eid); [exact Hptr|contradiction]. }
  assert (Hfacts : MutexCreateSpatial.free_head_facts sg entry eid rest image).
  { unfold MutexCreateSpatial.free_head_facts; split; [exact Hhead|]. split; [exact Himage|].
    split; [exact Hid|]. split; [unfold MutexCreateSpatial.free_head; rewrite Hhead; reflexivity|].
    split; [exact Hnext|exact (Htypes eid image Himage)]. }
  Exists eid rest image.
  sep_apply_l_atomic (MutexCreateFull.head_residual_split_node sg entry eid image Himage).
  entailer!.
Qed.

Lemma publication_events_preserves_registered_in_range : forall sg tasks events pcp eid rest name,
  event_registered_in_range sg tasks events -> events.(unUsedEventStates) = eid :: rest ->
  event_registered_in_range sg (mutex_create_priority_state sg pcp tasks)
    (publication_events pcp eid rest name events).
Proof.
  intros sg tasks events pcp eid rest name
    [Hpart [Hfree [Hidentity [Hfields [Hpayload [Hqueue Hwait]]]]]] Hhead.
  unfold publication_events, event_registered_in_range, event_in_range_with_wait.
  split.
  - eapply event_publish_preserves_partition.
    + eapply event_detach_head_preserves_partition; eassumption.
    + apply MutexCreateFull.detached_allocation_lookup.
  - split.
    + apply event_publish_preserves_free_storage.
      eapply event_detach_head_preserves_free_storage; eassumption.
    + split.
      * eapply event_publish_preserves_identity.
        -- apply event_detach_head_preserves_identity; exact Hidentity.
        -- apply MutexCreateFull.detached_allocation_lookup.
        -- reflexivity.
      * split.
        -- intros i e Hi; cbn [event_publish event_detach_head inUsedEventStates] in Hi.
           unfold kernel_map_set in Hi; destruct (Z.eq_dec i eid).
           ++ injection Hi as He; subst e.
              unfold event_fields_consistency, event_set_name, mutex_create_node; simpl; intuition discriminate.
           ++ eapply Hfields; exact Hi.
        -- split.
           ++ intros i e Hi; cbn [event_publish event_detach_head inUsedEventStates] in Hi.
              unfold kernel_map_set in Hi; destruct (Z.eq_dec i eid).
              ** injection Hi as He; subst e.
                 unfold event_payload_consistency, mutex_fields_consistency,
                   event_set_name, mutex_create_node; simpl; intuition.
              ** eapply Hpayload; exact Hi.
           ++ split.
              ** intros i j ei ej q Hi Hj Hqi Hqj.
                 cbn [event_publish event_detach_head inUsedEventStates] in Hi, Hj.
                 unfold kernel_map_set in Hi, Hj.
                 destruct (Z.eq_dec i eid); destruct (Z.eq_dec j eid).
                 --- congruence.
                 --- injection Hi as He; subst ei; discriminate.
                 --- injection Hj as He; subst ej; discriminate.
                 --- eapply Hqueue; eassumption.
              ** intros i e Hi.
                 cbn [event_publish event_detach_head inUsedEventStates] in Hi.
                 unfold kernel_map_set in Hi; destruct (Z.eq_dec i eid).
                 --- injection Hi as He; subst e.
                     apply event_registered_wait_entry_empty; reflexivity.
                 --- change (event_registered_wait_entry sg tasks i e).
                     eapply Hwait; exact Hi.
Qed.

Lemma publication_events_preserves_registration : forall sg tasks events pcp eid rest name,
  event_registered_in_range sg tasks events ->
  event_registration_consistency sg tasks events ->
  events.(unUsedEventStates) = eid :: rest ->
  event_registration_consistency sg (mutex_create_priority_state sg pcp tasks)
    (publication_events pcp eid rest name events).
Proof.
  intros sg tasks events pcp eid rest name Hvalid Hregistered Hhead.
  pose proof (publication_events_preserves_registered_in_range
    sg tasks events pcp eid rest name Hvalid Hhead) as Hafter.
  assert (Hnone : events.(inUsedEventStates) eid = None).
  { exact (proj1 (event_pool_free_unallocated sg events eid (proj1 Hvalid)
      ltac:(rewrite Hhead; left; reflexivity))). }
  pose proof (event_registration_free_slot_unreferenced
    sg tasks events eid Hregistered Hnone) as Hunreferenced.
  destruct Hregistered as [Hentries [Hback Hclosed]].
  split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hafter))))))|].
  split.
  - intros tid t slot node Ht Hnode Href.
    cbn [publication_events event_publish event_detach_head inUsedEventStates] in Hnode.
    unfold kernel_map_set in Hnode; destruct (Z.eq_dec slot eid) as [->|Hne].
    + exfalso; eapply Hunreferenced; eassumption.
    + eapply Hback; eassumption.
  - intros tid t slot Ht Href.
    destruct (Hclosed tid t slot Ht Href) as [node Hnode].
    exists node.
    cbn [publication_events event_publish event_detach_head inUsedEventStates].
    unfold kernel_map_set; destruct (Z.eq_dec slot eid); congruence.
Qed.

Lemma publication_state_preserves_validity : forall sg before pcp eid rest name chars,
  UCOS2_full_state_inv sg before ->
  before.(EventState).(unUsedEventStates) = eid :: rest ->
  valid_mutex_pcp sg pcp -> MutexCreateSpatial.slot_available sg before pcp ->
  readable_name before.(NameState) name chars ->
  UCOS2_full_state_inv sg (publication_state sg pcp eid rest name before).
Proof.
  intros sg before pcp eid rest name chars
    [Hprofile [Htasks [Hsched [Hevents [Hcross [Hidle [Hbits
      [Hflags [Hmemory [Htimer [Hstats [Hcontrol [Hnames [Hreferences [Hstacks Hpending]]]]]]]]]]]]]]]
    Hhead Hpcp Hslot Hread.
  destruct (event_pool_free_unallocated sg before.(EventState) eid (proj1 Hevents)
    ltac:(rewrite Hhead; left; reflexivity)) as [Hnone Hprivate].
  assert (Horigin : forall slot node,
    (publication_events pcp eid rest name before.(EventState)).(inUsedEventStates) slot = Some node ->
    exists old, (mutex_create_event_state pcp eid rest before.(EventState)).(inUsedEventStates) slot = Some old /\
      node.(eventType) = old.(eventType) /\ node.(mutexFields) = old.(mutexFields) /\ node.(waitList) = old.(waitList)).
  { intros slot node Hnode.
    cbn [publication_events event_publish event_detach_head inUsedEventStates] in Hnode.
    unfold kernel_map_set in Hnode; destruct (Z.eq_dec slot eid) as [->|Hne].
    - injection Hnode as Hnode; subst node.
      eexists; split; [apply MutexCreateFull.event_state_lookup_same|]; repeat split; reflexivity.
    - exists node; split; [rewrite MutexCreateFull.event_state_lookup_other by exact Hne; exact Hnode|].
      repeat split; reflexivity. }
  assert (Hforward : forall slot old,
    (mutex_create_event_state pcp eid rest before.(EventState)).(inUsedEventStates) slot = Some old ->
    exists node, (publication_events pcp eid rest name before.(EventState)).(inUsedEventStates) slot = Some node /\
      node.(eventType) = old.(eventType) /\ node.(mutexFields) = old.(mutexFields)).
  { intros slot old Hold.
    cbn [publication_events event_publish event_detach_head inUsedEventStates].
    unfold kernel_map_set; destruct (Z.eq_dec slot eid) as [->|Hne].
    - rewrite MutexCreateFull.event_state_lookup_same in Hold; injection Hold as Hold; subst old.
      eexists; split; [reflexivity|]; split; reflexivity.
    - rewrite MutexCreateFull.event_state_lookup_other in Hold by exact Hne.
      exists old; split; [exact Hold|]; split; reflexivity. }
  assert (HcrossAfter : cross_module_registration_consistency sg
    (publication_state sg pcp eid rest name before)).
  { destruct Hcross as [Htable [Howners [Hregistration [Hprotocol [Hunique [HflagWait HtimerInit]]]]]].
    assert (Hbase : cross_module_consistency_with_wait sg
      (mutex_create_state sg pcp eid rest before) True).
    { split; [apply MutexCreateFull.state_preserves_table_consistency; assumption|].
      split; [apply MutexCreateFull.state_preserves_owner_snapshots; assumption|].
      split; [exact I|].
      split; [apply MutexCreateFull.state_preserves_mutex_protocol; assumption|].
      split; [apply MutexCreateFull.state_preserves_pcp_unique; assumption|].
      split; assumption. }
    unfold cross_module_registration_consistency.
    change (cross_module_consistency_with_wait sg
      (replace_EventS (publication_events pcp eid rest name before.(EventState))
        (mutex_create_state sg pcp eid rest before))
      (event_registration_consistency sg (mutex_create_priority_state sg pcp before.(TskState))
        (publication_events pcp eid rest name before.(EventState)))).
    eapply cross_module_consistency_with_wait_event_mutex_transport with (waiting_before := True).
    - intros slot node Hnode _; exact (Horigin slot node Hnode).
    - intros slot old Hold _; exact (Hforward slot old Hold).
    - apply publication_events_preserves_registration; assumption.
    - reflexivity.
    - exact Hbase. }
  assert (HnamesAfter : kernel_names_valid sg (publication_state sg pcp eid rest name before)).
  { unfold publication_state.
    eapply kernel_names_valid_replace_event_add_name with (name := name).
    - exact Hreferences.
    - intros _; exists chars; exact Hread.
    - intros p Hp.
      apply event_publish_name_references in Hp.
      destruct Hp as [Hold|Hsame]; [left; exact Hold|right; exact Hsame]. }
  assert (HpendingAfter : pending_mutex_consistency sg
    (mutex_create_priority_state sg pcp before.(TskState))
    (publication_events pcp eid rest name before.(EventState))).
  { eapply pending_mutex_consistency_event_transport with
      (events := mutex_create_event_state pcp eid rest before.(EventState)).
    - reflexivity.
    - intros slot node Hnode Htype.
      destruct (Horigin slot node Hnode) as [old [Hold [Hty [Hm _]]]].
      exists old; split; [exact Hold|]; split; congruence.
    - apply MutexCreateFull.state_preserves_pending_consistency; assumption. }
  unfold UCOS2_full_state_inv, UCOS2_full_state_inv_with_ready.
  split; [exact Hprofile|].
  split; [apply MutexCreateFull.priority_state_preserves_in_range; assumption|].
  split; [exact Hsched|].
  split; [apply publication_events_preserves_registered_in_range; assumption|].
  split; [exact HcrossAfter|].
  split; [exact Hidle|]. split; [exact Hbits|].
  split; [exact Hflags|]. split; [exact Hmemory|].
  split; [exact Htimer|]. split; [exact Hstats|].
  split; [exact Hcontrol|]. split; [exact Hnames|].
  split; [exact HnamesAfter|]. split; [exact Hstacks|exact HpendingAfter].
Qed.

Lemma publication_preserves_queue_storage : forall sg before pcp eid rest name,
  before.(inUsedEventStates) eid = None ->
  before.(eventLifecycle).(eventPrivate) eid = None ->
  queue_storage_rep sg before |-- queue_storage_rep sg (publication_events pcp eid rest name before).
Proof.
  intros sg before pcp eid rest name Hnone Hprivate.
  eapply queue_storage_event_entry_frame with (before := None)
    (next := Some (event_set_name (mutex_create_node pcp before.(eventLifecycle).(eventNextGeneration)
      (mutex_create_storage before eid)) name)).
  - exact Hnone.
  - intros; discriminate.
  - intros node Hnode; injection Hnode as Hnode; subst node; reflexivity.
  - reflexivity.
  - reflexivity.
  - intro owner; unfold queue_private_owner, publication_events, event_publish, event_detach_head.
    cbn [eventLifecycle eventPrivate]; unfold kernel_map_set.
    destruct (Z.eq_dec owner eid) as [->|Hne]; [rewrite Hprivate|]; reflexivity.
Qed.

Lemma publication_preserves_untouched_rep : forall sg before pcp eid rest name,
  before.(EventState).(inUsedEventStates) eid = None ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = None ->
  UCOS2_raw_rep_missing_two sg before TaskModule EventModule |--
  UCOS2_raw_rep_missing_two sg (publication_state sg pcp eid rest name before) TaskModule EventModule.
Proof.
  intros sg before pcp eid rest name Hnone Hprivate.
  unfold UCOS2_raw_rep_missing_two, UCOS2_selected_rep.
  cbn [UCOS2_module_eq_dec UCOS2Module_rec UCOS2Module_rect UCOS2_module_rep].
  unfold publication_state.
  cbn [replace_EventS replace_TskS TskState SchedState IntrState EventState TickState
    FlagState MemoryState TimerState StatsState ControlState NameState].
  rewrite <- (sched_raw_rep_change_task_index sg before.(TskState)
    (mutex_create_priority_state sg pcp before.(TskState)) before.(SchedState) eq_refl).
  sep_apply_l_atomic (publication_preserves_queue_storage sg before.(EventState) pcp eid rest name Hnone Hprivate).
  entailer!.
Qed.

Lemma initialized_storage_merge : forall sg entry pcp eid rest image name chars,
  UCOS2_full_state_inv sg entry ->
  MutexCreateSpatial.free_head_facts sg entry eid rest image ->
  valid_mutex_pcp sg pcp -> MutexCreateSpatial.slot_available sg entry pcp ->
  readable_name entry.(NameState) name chars ->
  MutexCreateSpatial.reserved_priority_table sg entry pcp **
  sg.(g_OSEventFreeList) # Ptr |-> event_encode_pool_link sg (hd_error rest) **
  event_storage_rep true (event_pool_addr sg eid)
    (event_create_image true 4 (pcp * 256 + 255) 0 name image) **
  MutexCreateFull.node_residual sg entry eid |--
    UCOS2_full_inv sg (publication_state sg pcp eid rest name entry).
Proof.
  intros sg entry pcp eid rest image name chars Hvalid [Hhead [Himage Hrest]] Hpcp Hslot Hread.
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = true).
  { destruct Hvalid as [Hprofile _]; unfold full_features_kernel_profile in Hprofile; tauto. }
  assert (Hstorage : image = mutex_create_storage entry.(EventState) eid).
  { unfold mutex_create_storage; rewrite Himage; reflexivity. }
  subst image.
  pose proof (publication_state_preserves_validity
    sg entry pcp eid rest name chars Hvalid Hhead Hpcp Hslot Hread) as Hpost.
  destruct (event_pool_free_unallocated sg entry.(EventState) eid
    (proj1 (proj1 (proj2 (proj2 (proj2 Hvalid)))))
    ltac:(rewrite Hhead; left; reflexivity)) as [Hnone Hprivate].
  set (tasks := mutex_create_priority_state sg pcp entry.(TskState)).
  set (node := event_set_name
    (mutex_create_node pcp entry.(EventState).(eventLifecycle).(eventNextGeneration)
      (mutex_create_storage entry.(EventState) eid)) name).
  set (events := publication_events pcp eid rest name entry.(EventState)).
  assert (Hrepr : event_storage_rep true (event_pool_addr sg eid)
      (event_create_image true 4 (pcp * 256 + 255) 0 name (mutex_create_storage entry.(EventState) eid)) =
    used_event_rep sg tasks eid node).
  { unfold used_event_rep; rewrite Hnames.
    apply event_storage_rep_ext; intros field Hin; destruct field; reflexivity. }
  rewrite Hrepr; unfold MutexCreateFull.node_residual.
  assert (Hused : used_event_rep sg entry.(TskState) = used_event_rep sg tasks).
  { apply functional_extensionality; intro other.
    apply functional_extensionality; intro e; unfold used_event_rep.
    assert (Himg : event_image sg entry.(TskState) e = event_image sg tasks e).
    { destruct (event_wait_encoding_priority_ext e.(waitList) entry.(TskState)
        tasks ltac:(intros; reflexivity)) as [Hgrp Htbl].
      apply functional_extensionality; intro field; unfold event_image.
      destruct field; try reflexivity; f_equal; [exact Hgrp|..]; apply Htbl. }
    rewrite Himg; reflexivity. }
  rewrite Hused.
  sep_apply_l_atomic (proj1 (event_free_storage_remove_eid_equiv sg entry.(EventState) events eid
    ltac:(apply kernel_map_set_same)
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
  sep_apply_l_atomic (store_map_equiv_store_map_missing
    (used_event_rep sg tasks) entry.(EventState).(inUsedEventStates) eid Hnone).
  sep_apply_l_atomic (proj1 (store_map_missing_i_equiv
    (used_event_rep sg tasks) entry.(EventState).(inUsedEventStates) events.(inUsedEventStates) eid
    ltac:(intros; symmetry; apply kernel_map_set_other; assumption))).
  sep_apply_l_atomic (store_map_merge (used_event_rep sg tasks) eid node events.(inUsedEventStates)
    ltac:(apply kernel_map_set_same)).
  sep_apply_l_atomic (publication_preserves_untouched_rep sg entry pcp eid rest name Hnone Hprivate).
  rewrite (UCOS2_full_inv_split_two sg (publication_state sg pcp eid rest name entry)
    TaskModule EventModule ltac:(discriminate)).
  cbn [UCOS2_module_rep].
  unfold task_shared_rep; rewrite task_public_storage_prio_tbl_equiv.
  unfold event_raw_rep, event_free_root_rep.
  change (event_encode_pool_link sg (hd_error rest)) with
    (event_encode_pool_link sg (hd_error events.(unUsedEventStates))).
  unfold MutexCreateSpatial.reserved_priority_table.
  change (task_public_storage_without_prio_tbl sg tasks) with
    (task_public_storage_without_prio_tbl sg entry.(TskState)).
  cbn [publication_state replace_EventS replace_TskS TskState EventState parkedTaskStacks].
  assert (Htaskrep : task_public_storage_without_prio_tbl sg
      (mutex_create_priority_state sg pcp entry.(TskState)) =
    task_public_storage_without_prio_tbl sg entry.(TskState)) by reflexivity.
  rewrite Htaskrep.
  fold tasks events.
  change (parkedTaskStacks tasks) with (parkedTaskStacks entry.(TskState)).
  entailer!.
Qed.

Lemma UCOS2_full_inv_split_os_int_nesting : forall sg s,
  UCOS2_full_inv sg s --||--
    coq_prop (UCOS2_full_state_inv sg s) &&
    (UCOS2_inv_os_int_nesting_cell sg s.(IntrState) **
     UCOS2_inv_without_os_int_nesting sg s).
Proof.
  intros sg s.
  rewrite (UCOS2_full_inv_split_module sg s InterruptModule).
  unfold UCOS2_inv_without_os_int_nesting, UCOS2_inv_os_int_nesting_cell.
  cbn [UCOS2_module_rep].
  unfold interrupt_inv, interrupt_inv_no_int_nesting, store_int_state.
  split; entailer!.
Qed.

Lemma priority_value_zero_is_free : forall sg entry pcp,
  UCOS2_full_state_inv sg entry -> task_priority_in_range sg pcp ->
  MutexCreateSpatial.priority_value sg entry pcp = 0 -> entry.(TskState).(prioTbl) pcp = PTFree.
Proof.
  intros sg entry pcp Hvalid Hrange Hzero.
  pose proof Hvalid as [Hprofile [Htasks [_ [_ [Hcross _]]]]].
  destruct Hcross as [[_ [Hslots _]] _].
  specialize (Hslots pcp Hrange); unfold MutexCreateSpatial.priority_value in Hzero.
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
  rewrite (proj2 (full_features_kernel_profile_event_layout sg Hprofile)) in Hzero; lia.
Qed.

Definition node_residual_without_question_mark (sg : StableGlobVars)
  (state : UCOS2_Verify_State) (eid : EventID) (p : addr) : Assertion :=
  task_public_storage_without_prio_tbl sg state.(TskState) **
  store_parked_stacks state.(TskState).(parkedTaskStacks) **
  store_map (used_event_rep sg state.(TskState)) state.(EventState).(inUsedEventStates) **
  event_free_storage_without_eid sg state.(EventState) eid **
  store_name_bytes_without_question_mark state.(NameState) p **
  UCOS2_selected_rep sg state
    (fun candidate => if UCOS2_module_eq_dec candidate NamesModule then false
      else if UCOS2_module_eq_dec candidate EventModule then false
      else if UCOS2_module_eq_dec candidate TaskModule then false else true).

Lemma node_residual_split_question_mark : forall sg state eid LitMap,
  static_literal_bound state LitMap ->
  MutexCreateFull.node_residual sg state eid --||--
    store_stringLit (LitMap "?"%string) "?"%string **
    node_residual_without_question_mark sg state eid (LitMap "?"%string).
Proof.
  intros sg state eid LitMap [Hchar Hnul].
  unfold MutexCreateFull.node_residual, UCOS2_raw_rep_missing_two,
    node_residual_without_question_mark.
  rewrite (UCOS2_selected_rep_split_module sg state
    (fun candidate => if UCOS2_module_eq_dec candidate EventModule then false
      else if UCOS2_module_eq_dec candidate TaskModule then false else true)
    NamesModule eq_refl).
  cbn [UCOS2_module_rep].
  split.
  - sep_apply_l_atomic (store_name_bytes_split_question_mark state.(NameState)
      (LitMap "?"%string) Hchar Hnul); entailer!.
  - sep_apply_l_atomic (store_name_bytes_merge_question_mark state.(NameState)
      (LitMap "?"%string) Hchar Hnul); entailer!.
Qed.

End MutexCreatePublicationFull.
