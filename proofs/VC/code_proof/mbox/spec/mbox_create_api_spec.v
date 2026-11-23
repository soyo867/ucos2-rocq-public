Require Export Ucos2Verify.VC.code.mbox.spec.mbox_create_spec.
Require Export Ucos2Verify.VC.code.queue.spec.q_create_proof_helpers.
Require Export Ucos2Verify.VC.code.event.spec.event_wait_list_init_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia Coq.Strings.String.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.event Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.mbox Ucos2Verify.lib.queue_core Ucos2Verify.lib.kernel_names.
Require Import Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** Parser-facing constant for the empty additional call resource. *)
Definition mbox_create_call_frame : Assertion := emp.

(** The selected names-disabled source writes Type, Cnt and Ptr before
    calling the already verified bitmap initializer.  This frame owns the
    four untouched padding bytes of the SAME detached image.  In particular
    it does not own application memory through the message pointer. *)
Definition mbox_create_initialization_frame (base : addr)
  (image : EventStorage) : Assertion :=
  event_cell base EventPadding1 (image EventPadding1) **
  event_cell base EventPadding2 (image EventPadding2) **
  event_cell base EventPadding3 (image EventPadding3) **
  event_cell base EventPadding19 (image EventPadding19).

Lemma mbox_create_storage_split_initialization : forall base image,
  event_storage_rep false base image |--
  base # UChar |->_ ** (base + 8) # UShort |->_ **
  (base + 4) # Ptr |->_ **
  event_wait_list_init_pre (base + 10) (base + 11) **
  mbox_create_initialization_frame base image.
Proof.
  intros base image.
  sep_apply_l_atomic (event_wait_list_init_storage_split false base image).
  unfold event_wait_list_init_storage_frame, mbox_create_initialization_frame.
  assert (Htype : event_cell base EventTypeField (image EventTypeField) |--
    base # UChar |->_).
  { unfold event_cell, event_field_offset.
    rewrite Z.add_0_r; destruct (image EventTypeField);
      [apply store_uchar_undef_store_uchar|entailer!]. }
  assert (Hcount : event_cell base EventCntField (image EventCntField) |--
    (base + 8) # UShort |->_).
  { unfold event_cell, event_field_offset; destruct (image EventCntField);
      [apply store_ushort_undef_store_ushort|entailer!]. }
  assert (Hpointer : event_cell base EventPtrField (image EventPtrField) |--
    (base + 4) # Ptr |->_).
  { unfold event_cell, event_field_offset; destruct (image EventPtrField);
      [apply store_ptr_undef_store_ptr|entailer!]. }
  sep_apply_l_atomic Htype; sep_apply_l_atomic Hcount;
    sep_apply_l_atomic Hpointer; entailer!.
Qed.

Lemma mbox_create_storage_merge_initialization : forall base image message,
  base # UChar |-> 1 ** (base + 8) # UShort |-> 0 **
  (base + 4) # Ptr |-> message **
  event_wait_list_init_post (base + 10) (base + 11) **
  mbox_create_initialization_frame base image |--
  event_storage_rep false base (event_create_image false 1 0 message 0 image).
Proof.
  intros base image message.
  unfold event_create_image.
  sep_apply_r_atomic (event_wait_list_init_storage_merge false base
    (event_payload_init_image false 1 0 message 0 image)).
  unfold mbox_create_initialization_frame, event_wait_list_init_storage_frame,
    event_cell, event_field_offset, event_payload_init_image, event_write.
  cbn beta iota zeta.
  repeat first [rewrite field_update_same |
    rewrite field_update_other by discriminate].
  rewrite Z.add_0_r; entailer!.
Qed.

(** The C consumer must instantiate the existing OS_EVENT ABI premise.
    No field-address equation is inferred from a numeric address bound. *)
Lemma mbox_create_storage_split_initialization_layout : forall sg eid image,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  event_object_layout_prop sg eid ->
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid) image |--
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) # UChar |->_ **
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) # UShort |->_ **
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |->_ **
  event_wait_list_init_pre
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl")) **
  mbox_create_initialization_frame (event_pool_addr sg eid) image.
Proof.
  intros sg eid image Hnames [[Htype [Hptr Hcnt]] [Hgrp Htbl]].
  rewrite Hnames, Htype, Hptr, Hcnt, Hgrp, Htbl.
  unfold OSEventType_off, OSEventPtr_off, OSEventCnt_off,
    OSEventGrp_off, OSEventTbl_off; rewrite Z.add_0_r.
  apply mbox_create_storage_split_initialization.
Qed.

Lemma mbox_create_storage_merge_initialization_layout : forall sg eid image message,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  event_object_layout_prop sg eid ->
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) # UChar |-> 1 **
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) # UShort |-> 0 **
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> message **
  event_wait_list_init_post
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl")) **
  mbox_create_initialization_frame (event_pool_addr sg eid) image |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_create_image sg.(osKernelConfig).(cfgEventNames) 1 0 message 0 image).
Proof.
  intros sg eid image message Hnames [[Htype [Hptr Hcnt]] [Hgrp Htbl]].
  rewrite Hnames, Htype, Hptr, Hcnt, Hgrp, Htbl.
  unfold OSEventType_off, OSEventPtr_off, OSEventCnt_off,
    OSEventGrp_off, OSEventTbl_off; rewrite Z.add_0_r.
  apply mbox_create_storage_merge_initialization.
Qed.

(** These are pure consequences of the existing ordered initializer.
    They do not supply a Restore history, manufacture the actual private
    image, or claim that an unmasked source interval has no interference. *)
Lemma mbox_create_initialization_allocation :
  forall sg eid message name before result initialized allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  mbox_create_private_initialization sg eid message name before result initialized ->
  exists final,
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
    final.(eventPrivateMutexPCP) = allocation.(eventPrivateMutexPCP) /\
    final.(eventPrivateStorage) = event_create_image
      sg.(osKernelConfig).(cfgEventNames) 1 0 message name allocation.(eventPrivateStorage).
Proof.
  intros sg eid message name before result initialized allocation Hget Hsteps.
  destruct (event_create_private_initialization_post eid
    sg.(osKernelConfig).(cfgEventNames) 1 0 message name before result initialized
    allocation Hget Hsteps) as [final [Hfinal [Hinv [Hgen [Hqueue Himage]]]]].
  exists final; split; [exact Hfinal|].
  split; [exact Hinv|]. split; [exact Hgen|]. split; [exact Hqueue|].
  split; [|exact Himage].
  eapply event_create_private_stores_mutex_pcp_eq; eassumption.
Qed.

Lemma mbox_create_initialization_publication_validity :
  forall sg eid message before result initialized allocation,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  UCOS2_state_inv sg before ->
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  allocation.(eventPrivateMutexPCP) = None ->
  mbox_create_private_initialization sg eid message 0 before result initialized ->
  exists final,
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateStorage) = event_create_image false 1 0 message 0
      allocation.(eventPrivateStorage) /\
    UCOS2_state_inv sg (replace_EventS
      (event_publish initialized.(EventState) eid (mbox_create_event final message 0)) initialized).
Proof.
  intros sg eid message before result initialized allocation Hnames Hvalid Hget Hmutex Hsteps.
  destruct (mbox_create_initialization_allocation sg eid message 0 before result initialized
    allocation Hget Hsteps) as [final [Hfinal [Hinv [Hgen [Hqueue [Hpcp Himage]]]]]].
  rewrite Hnames in Himage.
  exists final; split; [exact Hfinal|]. split; [exact Hinv|].
  split; [exact Hgen|]. split; [exact Himage|].
  eapply mbox_create_publish_preserves_validity; [|exact Hfinal| |congruence].
  - eapply event_create_private_stores_preserves_validity; eassumption.
  - apply event_name_valid_disabled; exact Hnames.
Qed.

Lemma mbox_create_initialized_publish_merge :
  forall sg current eid final image message,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  UCOS2_state_inv sg current ->
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  final.(eventPrivateQueue) = None -> final.(eventPrivateMutexPCP) = None ->
  final.(eventPrivateStorage) = event_create_image false 1 0 message 0 image ->
  event_private_storage_rep sg eid final ** UCOS2_inv sg current |--
  UCOS2_inv sg (replace_EventS
    (event_publish current.(EventState) eid (mbox_create_event final message 0)) current).
Proof.
  intros sg current eid final image message Hnames Hvalid Hget Hqueue Hmutex Himage.
  rewrite (UCOS2_inv_split_event_queue sg current); Intros.
  sep_apply_r_atomic (mbox_create_publish_merge sg current eid final image message 0
    Hvalid Hget Hqueue ltac:(rewrite Hnames; exact Himage)
    (event_name_valid_disabled sg current.(NameState) _ Hnames) Hmutex).
  entailer!.
Qed.

Lemma mbox_create_publication_observations : forall current eid allocation message,
  let published := replace_EventS
    (event_publish current.(EventState) eid (mbox_create_event allocation message 0)) current in
  published.(EventState).(inUsedEventStates) eid =
    Some (mbox_create_event allocation message 0) /\
  published.(EventState).(eventLifecycle).(eventPrivate) eid = None /\
  (mbox_create_event allocation message 0).(eventGeneration) = allocation.(eventPrivateGeneration) /\
  (mbox_create_event allocation message 0).(waitList) = [] /\
  (mbox_create_event allocation message 0).(mboxFields) = Some (mbox_message_from_ptr message) /\
  mbox_message_ptr (mbox_message_from_ptr message) = message.
Proof.
  intros current eid allocation message.
  cbn [replace_EventS EventState event_publish eventLifecycle
    inUsedEventStates eventPrivate mbox_create_event eventGeneration waitList mboxFields].
  rewrite !kernel_map_set_same; repeat split; apply mbox_message_ptr_from_ptr.
Qed.


(** The public operation keeps the source order and the actual returned
    world.  A private interval is the existing ordinary history plus the
    same allocation lookup at its endpoints, not a new Event observer. *)
Definition mbox_create_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (message : addr)
  : program UCOS2_Verify_State addr :=
  fun before result after =>
    if Z.ltb 0 before.(IntrState).(intNesting)
    then result = 0 /\ after = before
    else exists entry allocated detached,
      critical_region_interval critical sg invocation before entry /\
      event_create_allocate_critical entry allocated detached /\
      match allocated with
      | None => result = 0 /\
          critical_region_interval critical sg invocation detached after
      | Some (eid, image) => exists resumed initialized allocation,
          q_create_private_interval critical sg invocation eid detached resumed /\
          q_create_private_stores_interleaved critical sg invocation eid
            (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames)
              1 0 message 0) resumed tt initialized /\
          initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
          result = event_pool_addr sg eid /\
          after = replace_EventS
            (event_publish initialized.(EventState) eid
              (mbox_create_event allocation message 0)) initialized
      end.

Definition mbox_create_safe critical sg invocation message initial
  (X : addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq initial) (mbox_create_program critical sg invocation message) X.

Lemma mbox_create_safe_return :
  forall critical sg invocation message before result current X,
  mbox_create_program critical sg invocation message before result current ->
  mbox_create_safe critical sg invocation message before X ->
  safeExec (eq current) (StateRelMonad.ret result) X.
Proof.
  intros critical sg invocation message before result current X Hprogram Hsafe.
  unfold mbox_create_safe in Hsafe.
  eapply (highstependret_derive
    (mbox_create_program critical sg invocation message) (eq before)
    result (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma mbox_create_program_isr_return :
  forall critical sg invocation message before,
  0 < before.(IntrState).(intNesting) ->
  mbox_create_program critical sg invocation message before 0 before.
Proof.
  intros; unfold mbox_create_program.
  rewrite (proj2 (Z.ltb_lt _ _) H); split; reflexivity.
Qed.

Lemma mbox_create_program_exhausted_return :
  forall critical sg invocation message before entry detached current,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry None detached ->
  critical_region_interval critical sg invocation detached current ->
  mbox_create_program critical sg invocation message before 0 current.
Proof.
  intros critical sg invocation message before entry detached current Hnest Henter Hpop Hreturn.
  unfold mbox_create_program; rewrite (proj2 (Z.ltb_ge _ _) Hnest).
  exists entry, None, detached; auto.
Qed.

Lemma mbox_create_program_published_return :
  forall critical sg invocation message before entry eid image detached resumed initialized allocation,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry (Some (eid, image)) detached ->
  q_create_private_interval critical sg invocation eid detached resumed ->
  q_create_private_stores_interleaved critical sg invocation eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 1 0 message 0)
    resumed tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  mbox_create_program critical sg invocation message before (event_pool_addr sg eid)
    (replace_EventS (event_publish initialized.(EventState) eid
      (mbox_create_event allocation message 0)) initialized).
Proof.
  intros critical sg invocation message before entry eid image detached resumed initialized allocation
    Hnest Henter Hpop Hreturn Hstores Hget.
  unfold mbox_create_program; rewrite (proj2 (Z.ltb_ge _ _) Hnest).
  exists entry, (Some (eid, image)), detached; split; [exact Henter|].
  split; [exact Hpop|]. exists resumed, initialized, allocation; auto.
Qed.

Definition mbox_create_source_binding sg : Prop :=
  sem_create_source_binding sg /\ event_table_layout_prop sg.

Definition mbox_create_input_facts critical sg call initial message X : Prop :=
  mbox_create_source_binding sg /\
  mbox_create_safe critical sg call.(os_sched_call_invocation) message initial X.

Definition mbox_create_call_pre environment critical sg call mask initial message X : Assertion :=
  coq_prop (mbox_create_input_facts critical sg call initial message X) &&
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask initial.

Definition mbox_create_call_post environment critical sg original mask result X : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      q_create_return_safe current result X) &&
    q_create_save_input environment critical QCreateNoPrivate emp sg returned mask current.

Definition mbox_create_allocation_cut environment critical sg original initial mask saved pointer : Assertion :=
  EX call entry result allocated,
    coq_prop (q_create_first_facts critical sg original initial mask saved call entry /\
      event_create_allocate_critical entry result allocated /\
      pointer = event_create_return_ptr sg result) &&
    q_create_restore_input environment critical (q_create_allocated_owner entry result)
      emp sg call saved entry allocated.

Definition mbox_create_exhaustion_history critical sg invocation initial current : Prop :=
  initial.(IntrState).(intNesting) <= 0 /\ exists entry detached,
    critical_region_interval critical sg invocation initial entry /\
    event_create_allocate_critical entry None detached /\
    critical_region_interval critical sg invocation detached current.

Definition mbox_create_allocation_return environment critical sg original initial mask pointer : Assertion :=
  EX returned current,
    coq_prop (task_tcb_init_stack_same_call returned original) &&
    (if Z.eq_dec pointer 0 then
      (coq_prop (mbox_create_exhaustion_history critical sg
        original.(os_sched_call_invocation) initial current) &&
       q_create_save_input environment critical QCreateNoPrivate emp sg returned mask current)
    else
      (EX eid allocation,
        coq_prop (pointer = event_pool_addr sg eid /\ 0 < pointer /\
          q_create_event_history critical sg original.(os_sched_call_invocation)
            initial eid allocation current) &&
        q_create_save_input environment critical (QCreatePrivateEvent eid allocation)
          emp sg returned mask current)).

(** The exact post-Restore context remains on the same heap as the
    separately owned ECB image. Only this invocation's private image is
    initialized; no application-message ownership is acquired. *)
Definition mbox_create_initialization_context environment critical sg original initial mask
  eid allocation current : Assertion :=
  EX returned,
    coq_prop (task_tcb_init_stack_same_call returned original /\
      q_create_event_history critical sg original.(os_sched_call_invocation)
        initial eid allocation current) &&
    (q_create_current_control environment sg returned mask current ** UCOS2_inv sg current).

Lemma mbox_create_save_input_split_nesting :
  forall environment critical owned buffer sg call mask state,
  mbox_create_source_binding sg ->
  q_create_save_input environment critical owned buffer sg call mask state --||--
  &("OSIntNesting") # UChar |-> state.(IntrState).(intNesting) **
    q_create_without_nesting environment owned buffer sg call mask state.
Proof.
  intros environment critical owned buffer sg call mask state [[Haddress Hrest] Htable].
  rewrite q_create_save_input_open, UCOS2_inv_split_interrupt.
  unfold q_create_without_nesting, interrupt_inv, store_int_state, interrupt_inv_no_int_nesting.
  rewrite Haddress; split; entailer!.
Qed.

Lemma mbox_create_isr_return :
  forall environment critical sg call mask initial message X,
  0 < initial.(IntrState).(intNesting) ->
  mbox_create_call_pre environment critical sg call mask initial message X |--
  mbox_create_call_post environment critical sg call mask 0 X.
Proof.
  intros environment critical sg call mask initial message X Hnest.
  unfold mbox_create_call_pre; Intros.
  assert (Hsafe : mbox_create_safe critical sg call.(os_sched_call_invocation) message initial X)
    by (unfold mbox_create_input_facts in *; tauto).
  pose proof (mbox_create_safe_return critical sg call.(os_sched_call_invocation) message
    initial 0 initial X (mbox_create_program_isr_return _ _ _ _ _ Hnest) Hsafe) as Hreturn.
  unfold mbox_create_call_post; Exists call initial.
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.

Lemma mbox_create_private_stores_task_state_eq :
  forall eid writes before result after,
  event_create_private_stores eid writes before result after ->
  after.(TskState) = before.(TskState).
Proof.
  intros eid writes; induction writes as [|[field value] rest IH]; intros before result after Hstores.
  - destruct Hstores as [_ ->]; reflexivity.
  - destruct Hstores as [allocation [Hget Htail]].
    exact (IH _ _ _ Htail).
Qed.

Lemma mbox_create_private_stores_global_frame :
  forall sg eid writes before result after,
  event_create_private_stores eid writes before result after ->
  UCOS2_inv sg before |-- UCOS2_inv sg after.
Proof.
  intros sg eid writes; induction writes as [|[field value] rest IH]; intros before result after Hstores.
  - destruct Hstores as [_ ->]; entailer!.
  - destruct Hstores as [allocation [Hget Htail]].
    sep_apply_l_atomic (UCOS2_event_private_write_global_frame sg before eid allocation field (Some value) Hget).
    apply (IH _ _ _ Htail).
Qed.


Lemma mbox_create_private_input_lookup :
  forall environment critical buffer sg call mask state eid allocation,
  q_create_save_input environment critical (QCreatePrivateEvent eid allocation) buffer
    sg call mask state |--
  coq_prop (state.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation).
Proof.
  intros; rewrite q_create_save_input_open; unfold q_create_owned; entailer!.
Qed.

Lemma mbox_create_allocation_restore :
  forall environment critical sg original initial mask saved call entry allocated result pointer,
  mbox_create_source_binding sg ->
  q_create_first_facts critical sg original initial mask saved call entry ->
  event_create_allocate_critical entry result allocated ->
  pointer = event_create_return_ptr sg result ->
  q_create_restore_output environment critical (q_create_allocated_owner entry result)
    emp sg call saved allocated |--
  mbox_create_allocation_return environment critical sg original initial mask pointer.
Proof.
  intros environment critical sg original initial mask saved call entry allocated result pointer
    [Hsource Htable] [Hnest [Henter [Hsame [Hsaved Hvalid]]]] Hpop Hpointer.
  sep_apply_l_atomic (q_create_restore_output_observation environment critical
    (q_create_allocated_owner entry result) emp sg call saved allocated).
  Intros returned current.
  assert (Hnormal : kernel_call_normal_return call allocated returned current) by tauto.
  assert (Hinterval : critical_region_interval critical sg
    call.(os_sched_call_invocation) allocated current) by tauto.
  assert (Hmask : armv7a_irq_fiq_mask saved = mask) by (exact (proj2 Hsaved)).
  rewrite Hmask.
  assert (Hsame' : task_tcb_init_stack_same_call returned original).
  { destruct Hnormal as [[Hi [Ho Hstack]] _].
    destruct Hsame as [Hi' [Ho' Hstack']].
    unfold task_tcb_init_stack_same_call; repeat split; congruence. }
  assert (Hinvocation : call.(os_sched_call_invocation) = original.(os_sched_call_invocation))
    by exact (proj1 Hsame).
  rewrite Hinvocation in Hinterval.
  unfold mbox_create_allocation_return; Exists returned current.
  destruct result as [[eid image]|].
  - cbn [event_create_return_ptr] in Hpointer; subst pointer.
    assert (Hfacts : sem_create_allocation_facts sg entry allocated eid image)
      by (split; assumption).
    pose proof (sem_create_allocated_id_valid _ _ _ _ _ Hfacts) as Hrange.
    destruct Hsource as [_ [_ [_ Hlayout]]].
    destruct (Hlayout eid Hrange) as [[Hpositive Hupper] Hlink].
    destruct (Z.eq_dec (event_pool_addr sg eid) 0) as [Hzero|Hnonnull]; [lia|].
    cbn [q_create_allocated_owner].
    prop_apply (mbox_create_private_input_lookup environment critical emp sg returned mask current
      eid (sem_create_allocation_identity entry image)); Intros.
    assert (Hlookup : current.(EventState).(eventLifecycle).(eventPrivate) eid =
      Some (sem_create_allocation_identity entry image)) by tauto.
    assert (Hprivate : q_create_private_interval critical sg
      original.(os_sched_call_invocation) eid allocated current).
    { split; [exact Hinterval|].
      exists (sem_create_allocation_identity entry image); split; [|exact Hlookup].
      exact (proj2 (event_create_allocate_critical_private_result _ _ _ _ Hpop)). }
    assert (Hhistory : q_create_event_history critical sg original.(os_sched_call_invocation)
      initial eid (sem_create_allocation_identity entry image) current).
    { split; [exact Hnest|]. exists entry, image, allocated.
      split; [exact Hvalid|]. split; [exact Henter|]. split; [exact Hpop|].
      split; [reflexivity|exact Hprivate]. }
    Exists eid (sem_create_allocation_identity entry image); entailer!.
  - cbn [event_create_return_ptr] in Hpointer; subst pointer.
    destruct (Z.eq_dec 0 0); [|contradiction].
    cbn [q_create_allocated_owner].
    assert (Hhistory : mbox_create_exhaustion_history critical sg
      original.(os_sched_call_invocation) initial current).
    { split; [exact Hnest|]. exists entry, allocated; auto. }
    entailer!.
Qed.

Lemma mbox_create_exhausted_return :
  forall environment critical sg original initial mask message X,
  mbox_create_input_facts critical sg original initial message X ->
  mbox_create_allocation_return environment critical sg original initial mask 0 |--
  mbox_create_call_post environment critical sg original mask 0 X.
Proof.
  intros environment critical sg original initial mask message X [Hsource Hsafe].
  unfold mbox_create_allocation_return; Intros returned current.
  destruct (Z.eq_dec 0 0); [|contradiction]; Intros.
  assert (Hhistory : mbox_create_exhaustion_history critical sg
    original.(os_sched_call_invocation) initial current) by tauto.
  destruct Hhistory as [Hnest [entry [detached [Henter [Hpop Hrestore]]]]].
  pose proof (mbox_create_program_exhausted_return critical sg
    original.(os_sched_call_invocation) message initial entry detached current
    Hnest Henter Hpop Hrestore) as Hprogram.
  pose proof (mbox_create_safe_return _ _ _ _ _ _ _ _ Hprogram Hsafe) as Hreturn.
  unfold mbox_create_call_post; Exists returned current; entailer!.
Qed.

Lemma mbox_create_initialized_return :
  forall environment critical sg original initial mask eid allocation current message X,
  mbox_create_input_facts critical sg original initial message X ->
  event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 1 0 message 0 allocation.(eventPrivateStorage)) **
    mbox_create_initialization_context environment critical sg original initial mask eid allocation current |--
  mbox_create_call_post environment critical sg original mask (event_pool_addr sg eid) X.
Proof.
  intros environment critical sg original initial mask eid allocation current message X
    [Hsource Hsafe].
  unfold mbox_create_initialization_context; Intros returned.
  assert (Hhistory : q_create_event_history critical sg original.(os_sched_call_invocation)
    initial eid allocation current) by tauto.
  destruct (q_create_event_history_private_facts _ _ _ _ _ _ _ Hhistory)
    as [Hqueue [Hmutex [Htype Hget]]].
  assert (Hvalid : UCOS2_state_inv sg current).
  { destruct Hhistory as [_ [entry [image [detached
      [Hentry [Henter [Hpop [Hallocation Hrestore]]]]]]]].
    exact (proj1 (critical_region_interval_transports_resources _ _ _ _ _ (proj1 Hrestore)
      (event_create_allocate_critical_preserves_validity _ _ _ _ Hentry Hpop))). }
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hvalid as [Hprofile _]; unfold selected_kernel_profile in Hprofile; tauto. }
  destruct (event_create_private_stores_exists eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 1 0 message 0)
    current allocation Hget) as [initialized Hstores].
  destruct (mbox_create_initialization_allocation sg eid message 0 current tt initialized
    allocation Hget Hstores) as [final [Hfinal [Hinv [Hgen [Hqueue' [Hmutex' Himage]]]]]].
  assert (Hinitialized : UCOS2_state_inv sg initialized)
    by (eapply event_create_private_stores_preserves_validity; eassumption).
  assert (Htasks : initialized.(TskState) = current.(TskState))
    by (eapply mbox_create_private_stores_task_state_eq; eassumption).
  rewrite Hnames in Himage.
  assert (Hstorage :
    event_storage_rep false (event_pool_addr sg eid)
      (event_create_image false 1 0 message 0 allocation.(eventPrivateStorage)) =
    event_private_storage_rep sg eid final).
  { unfold event_private_storage_rep; rewrite Hnames, Himage; reflexivity. }
  rewrite Hstorage.
  sep_apply_l_atomic (mbox_create_private_stores_global_frame sg eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 1 0 message 0)
    current tt initialized Hstores).
  sep_apply_l_atomic (mbox_create_initialized_publish_merge sg initialized eid final
    allocation.(eventPrivateStorage) message Hnames Hinitialized Hfinal
    ltac:(congruence) ltac:(congruence) Himage).
  assert (Hprogram : mbox_create_program critical sg original.(os_sched_call_invocation)
    message initial (event_pool_addr sg eid)
    (replace_EventS (event_publish initialized.(EventState) eid
      (mbox_create_event final message 0)) initialized)).
  { destruct Hhistory as [Hnest [entry [image [detached
      [Hentry [Henter [Hpop [Hallocation Hrestore]]]]]]]].
    eapply mbox_create_program_published_return; try eassumption.
    eapply q_create_private_stores_without_interference; eassumption. }
  pose proof (mbox_create_safe_return _ _ _ _ _ _ _ _ Hprogram Hsafe) as Hreturn.
  unfold mbox_create_call_post.
  Exists returned (replace_EventS (event_publish initialized.(EventState) eid
    (mbox_create_event final message 0)) initialized).
  rewrite q_create_save_input_open.
  unfold q_create_owned, q_create_current_control.
  cbn [replace_EventS TskState]; rewrite Htasks; entailer!.
Qed.


Lemma mbox_create_nonnull_initialization :
  forall environment critical sg original initial mask pointer,
  mbox_create_source_binding sg -> pointer <> 0 ->
  mbox_create_allocation_return environment critical sg original initial mask pointer |--
  EX eid allocation current,
    coq_prop (pointer = event_pool_addr sg eid) &&
    (mbox_create_initialization_context environment critical sg original initial mask
       eid allocation current **
     (&((pointer) # "os_event" ->ₛ "OSEventType")) # UChar |->_ **
     (&((pointer) # "os_event" ->ₛ "OSEventCnt")) # UShort |->_ **
     (&((pointer) # "os_event" ->ₛ "OSEventPtr")) # Ptr |->_ **
     event_wait_list_init_pre
       (&((pointer) # "os_event" ->ₛ "OSEventGrp"))
       (&((pointer) # "os_event" ->ₛ "OSEventTbl")) **
     mbox_create_initialization_frame pointer allocation.(eventPrivateStorage)).
Proof.
  intros environment critical sg original initial mask pointer [Hsource Htable] Hnonnull.
  unfold mbox_create_allocation_return; Intros returned current.
  destruct (Z.eq_dec pointer 0); [contradiction|].
  Intros eid allocation.
  assert (Hpointer : pointer = event_pool_addr sg eid) by tauto; subst pointer.
  assert (Hhistory : q_create_event_history critical sg original.(os_sched_call_invocation)
    initial eid allocation current) by tauto.
  assert (Hrange : valid_event_id sg eid).
  { destruct Hhistory as [_ [entry [image [detached
      [Hvalid [Henter [Hpop Htail]]]]]]].
    apply (sem_create_allocated_id_valid sg entry detached eid image); split; assumption. }
  assert (Hnames : sg.(osKernelConfig).(cfgEventNames) = false).
  { destruct Hhistory as [_ [entry [image [detached [[Hprofile Hvalid] Htail]]]]].
    unfold selected_kernel_profile in Hprofile; tauto. }
  pose proof (event_table_layout_select sg eid Htable Hrange) as Hlayout.
  rewrite q_create_save_input_open; unfold q_create_owned; Intros.
  unfold event_private_storage_rep.
  sep_apply_l_atomic (mbox_create_storage_split_initialization_layout sg eid
    allocation.(eventPrivateStorage) Hnames Hlayout).
  Exists eid allocation current.
  unfold mbox_create_initialization_context; Exists returned.
  unfold q_create_current_control; entailer!.
Qed.



