Require Export Ucos2Verify.VC.code.sem.spec.sem_create_spec.
Require Export Ucos2Verify.VC.code.mbox.spec.mbox_create_api_spec.
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.micromega.Lia Coq.Strings.String.
From SimpleC.SL Require Import Mem ConAssertion.
From MonadLib Require Import Monad.
From MonadLib.StateRelMonad Require Import StateRelBasic safeexec_lib.
Require Import Ucos2Verify.lib.stable_glob_vars Ucos2Verify.lib.ucos2_verify_state_def.
Require Import Ucos2Verify.lib.ucos2_rules_lib Ucos2Verify.lib.ucos2_verify_inv.
Require Import Ucos2Verify.lib.event_pool Ucos2Verify.lib.event Ucos2Verify.lib.field_storage.
Require Import Ucos2Verify.lib.kernel_names Ucos2Verify.lib.kernel_resources Ucos2Verify.lib.interrupt.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_call_modular_spec.
Require Import Ucos2Verify.VC.code.sched.spec.sched_spec.
Require Import Ucos2Verify.VC.code.sched.spec.kernel_continuation_world_spec.
Require Import Ucos2Verify.VC.code.task.spec.task_tcb_init_stack_interface_spec.
Require Import Ucos2Verify.VC.code.sem.spec.sem_create_source_spec.

Import UCOS2_C_Rules ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope sac_scope.

(** The imported Mailbox allocation cut, Restore result, initialization
    context and padding frame are payload-independent ECB resource views.
    They do not mention a mailbox value, Queue buffer or semaphore count.
    Reuse their proved split/transport rules without duplicating lifecycle
    semantics. Only the payload stores, publication and public program below
    are specific to OSSemCreate. *)
Lemma sem_create_api_storage_merge_initialization : forall base image count,
  base # UChar |-> 3 ** (base + 8) # UShort |-> count **
  (base + 4) # Ptr |-> 0 **
  event_wait_list_init_post (base + 10) (base + 11) **
  mbox_create_initialization_frame base image |--
  event_storage_rep false base (event_create_image false 3 count 0 0 image).
Proof.
  intros base image count.
  unfold event_create_image.
  sep_apply_r_atomic (event_wait_list_init_storage_merge false base
    (event_payload_init_image false 3 count 0 0 image)).
  unfold mbox_create_initialization_frame, event_wait_list_init_storage_frame,
    event_cell, event_field_offset, event_payload_init_image, event_write.
  cbn beta iota zeta.
  repeat first [rewrite field_update_same |
    rewrite field_update_other by discriminate].
  rewrite Z.add_0_r; entailer!.
Qed.

Lemma sem_create_api_storage_merge_initialization_layout : forall sg eid image count,
  sg.(osKernelConfig).(cfgEventNames) = false ->
  event_object_layout_prop sg eid ->
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventType")) # UChar |-> 3 **
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventCnt")) # UShort |-> count **
  (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventPtr")) # Ptr |-> 0 **
  event_wait_list_init_post
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventGrp"))
    (&(((event_addr (sg) (eid))) # "os_event" ->ₛ "OSEventTbl")) **
  mbox_create_initialization_frame (event_pool_addr sg eid) image |--
  event_storage_rep sg.(osKernelConfig).(cfgEventNames) (event_pool_addr sg eid)
    (event_create_image sg.(osKernelConfig).(cfgEventNames) 3 count 0 0 image).
Proof.
  intros sg eid image count Hnames [[Htype [Hptr Hcnt]] [Hgrp Htbl]].
  rewrite Hnames, Htype, Hptr, Hcnt, Hgrp, Htbl.
  unfold OSEventType_off, OSEventPtr_off, OSEventCnt_off,
    OSEventGrp_off, OSEventTbl_off; rewrite Z.add_0_r.
  apply sem_create_api_storage_merge_initialization.
Qed.

Lemma sem_create_api_initialization_allocation :
  forall sg eid count name before result initialized allocation,
  before.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  sem_create_private_initialization sg eid count name before result initialized ->
  exists final,
    initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some final /\
    final.(eventPrivateInvocation) = allocation.(eventPrivateInvocation) /\
    final.(eventPrivateGeneration) = allocation.(eventPrivateGeneration) /\
    final.(eventPrivateQueue) = allocation.(eventPrivateQueue) /\
    final.(eventPrivateMutexPCP) = allocation.(eventPrivateMutexPCP) /\
    final.(eventPrivateStorage) = event_create_image
      sg.(osKernelConfig).(cfgEventNames) 3 count 0 name allocation.(eventPrivateStorage).
Proof.
  intros sg eid count name before result initialized allocation Hget Hsteps.
  destruct (event_create_private_initialization_post eid
    sg.(osKernelConfig).(cfgEventNames) 3 count 0 name before result initialized
    allocation Hget Hsteps) as [final [Hfinal [Hinv [Hgen [Hqueue Himage]]]]].
  exists final; split; [exact Hfinal|].
  split; [exact Hinv|]. split; [exact Hgen|]. split; [exact Hqueue|].
  split; [|exact Himage].
  eapply event_create_private_stores_mutex_pcp_eq; eassumption.
Qed.

Lemma sem_create_api_initialized_publish_merge :
  forall sg current eid final image count,
  0 <= count <= 65535 ->
  sg.(osKernelConfig).(cfgEventNames) = false ->
  UCOS2_state_inv sg current ->
  current.(EventState).(eventLifecycle).(eventPrivate) eid = Some final ->
  final.(eventPrivateQueue) = None -> final.(eventPrivateMutexPCP) = None ->
  final.(eventPrivateStorage) = event_create_image false 3 count 0 0 image ->
  event_private_storage_rep sg eid final ** UCOS2_inv sg current |--
  UCOS2_inv sg (replace_EventS
    (event_publish current.(EventState) eid (sem_create_event final count 0)) current).
Proof.
  intros sg current eid final image count Hcount Hnames Hvalid Hget Hqueue Hmutex Himage.
  rewrite (UCOS2_inv_split_event_queue sg current); Intros.
  sep_apply_r_atomic (sem_create_publish_merge sg current eid final image count 0
    Hvalid Hget Hqueue ltac:(rewrite Hnames; exact Himage) Hcount
    (event_name_valid_disabled sg current.(NameState) _ Hnames) Hmutex).
  entailer!.
Qed.

Definition sem_create_api_program (critical : CriticalRegionResources)
  (sg : StableGlobVars) (invocation : nat) (count : Z)
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
              3 count 0 0) resumed tt initialized /\
          initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation /\
          result = event_pool_addr sg eid /\
          after = replace_EventS
            (event_publish initialized.(EventState) eid
              (sem_create_event allocation count 0)) initialized
      end.

Definition sem_create_api_safe critical sg invocation count initial
  (X : addr -> UCOS2_Verify_State -> Prop) : Prop :=
  safeExec (eq initial) (sem_create_api_program critical sg invocation count) X.

Lemma sem_create_api_safe_return :
  forall critical sg invocation count before result current X,
  sem_create_api_program critical sg invocation count before result current ->
  sem_create_api_safe critical sg invocation count before X ->
  safeExec (eq current) (StateRelMonad.ret result) X.
Proof.
  intros critical sg invocation count before result current X Hprogram Hsafe.
  unfold sem_create_api_safe in Hsafe.
  eapply (highstependret_derive
    (sem_create_api_program critical sg invocation count) (eq before)
    result (fun _ => eq current)); [|exact Hsafe].
  intros state Hstate; subst state; exists current; split; assumption || reflexivity.
Qed.

Lemma sem_create_api_program_isr_return :
  forall critical sg invocation count before,
  0 < before.(IntrState).(intNesting) ->
  sem_create_api_program critical sg invocation count before 0 before.
Proof.
  intros; unfold sem_create_api_program.
  rewrite (proj2 (Z.ltb_lt _ _) H); split; reflexivity.
Qed.

Lemma sem_create_api_program_exhausted_return :
  forall critical sg invocation count before entry detached current,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry None detached ->
  critical_region_interval critical sg invocation detached current ->
  sem_create_api_program critical sg invocation count before 0 current.
Proof.
  intros critical sg invocation count before entry detached current Hnest Henter Hpop Hreturn.
  unfold sem_create_api_program; rewrite (proj2 (Z.ltb_ge _ _) Hnest).
  exists entry, None, detached; auto.
Qed.

Lemma sem_create_api_program_published_return :
  forall critical sg invocation count before entry eid image detached resumed initialized allocation,
  before.(IntrState).(intNesting) <= 0 ->
  critical_region_interval critical sg invocation before entry ->
  event_create_allocate_critical entry (Some (eid, image)) detached ->
  q_create_private_interval critical sg invocation eid detached resumed ->
  q_create_private_stores_interleaved critical sg invocation eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 3 count 0 0)
    resumed tt initialized ->
  initialized.(EventState).(eventLifecycle).(eventPrivate) eid = Some allocation ->
  sem_create_api_program critical sg invocation count before (event_pool_addr sg eid)
    (replace_EventS (event_publish initialized.(EventState) eid
      (sem_create_event allocation count 0)) initialized).
Proof.
  intros critical sg invocation count before entry eid image detached resumed initialized allocation
    Hnest Henter Hpop Hreturn Hstores Hget.
  unfold sem_create_api_program; rewrite (proj2 (Z.ltb_ge _ _) Hnest).
  exists entry, (Some (eid, image)), detached; split; [exact Henter|].
  split; [exact Hpop|]. exists resumed, initialized, allocation; auto.
Qed.

Definition sem_create_api_input_facts critical sg call initial count X : Prop :=
  mbox_create_source_binding sg /\ 0 <= count <= 65535 /\
  sem_create_api_safe critical sg call.(os_sched_call_invocation) count initial X.

Definition sem_create_api_call_pre environment critical sg call mask initial count X : Assertion :=
  coq_prop (sem_create_api_input_facts critical sg call initial count X) &&
  q_create_save_input environment critical QCreateNoPrivate emp sg call mask initial.

(** Same-call identity, actual returned resources and the same arbitrary X.
    The result is the exact C ECB pointer; no caller heap is projected into X. *)
Definition sem_create_api_call_post := mbox_create_call_post.

Lemma sem_create_api_isr_return :
  forall environment critical sg call mask initial count X,
  0 < initial.(IntrState).(intNesting) ->
  sem_create_api_call_pre environment critical sg call mask initial count X |--
  sem_create_api_call_post environment critical sg call mask 0 X.
Proof.
  intros environment critical sg call mask initial count X Hnest.
  unfold sem_create_api_call_pre; Intros.
  assert (Hsafe : sem_create_api_safe critical sg call.(os_sched_call_invocation) count initial X)
    by (unfold sem_create_api_input_facts in *; tauto).
  pose proof (sem_create_api_safe_return critical sg call.(os_sched_call_invocation) count
    initial 0 initial X (sem_create_api_program_isr_return _ _ _ _ _ Hnest) Hsafe) as Hreturn.
  unfold sem_create_api_call_post, mbox_create_call_post; Exists call initial.
  unfold task_tcb_init_stack_same_call; entailer!.
Qed.

Lemma sem_create_api_exhausted_return :
  forall environment critical sg original initial mask count X,
  sem_create_api_input_facts critical sg original initial count X ->
  mbox_create_allocation_return environment critical sg original initial mask 0 |--
  sem_create_api_call_post environment critical sg original mask 0 X.
Proof.
  intros environment critical sg original initial mask count X [Hsource [Hcount Hsafe]].
  unfold mbox_create_allocation_return; Intros returned current.
  destruct (Z.eq_dec 0 0); [|contradiction]; Intros.
  assert (Hhistory : mbox_create_exhaustion_history critical sg
    original.(os_sched_call_invocation) initial current) by tauto.
  destruct Hhistory as [Hnest [entry [detached [Henter [Hpop Hrestore]]]]].
  pose proof (sem_create_api_program_exhausted_return critical sg
    original.(os_sched_call_invocation) count initial entry detached current
    Hnest Henter Hpop Hrestore) as Hprogram.
  pose proof (sem_create_api_safe_return _ _ _ _ _ _ _ _ Hprogram Hsafe) as Hreturn.
  unfold sem_create_api_call_post, mbox_create_call_post; Exists returned current; entailer!.
Qed.

Lemma sem_create_api_initialized_return :
  forall environment critical sg original initial mask eid allocation current count X,
  sem_create_api_input_facts critical sg original initial count X ->
  event_storage_rep false (event_pool_addr sg eid)
    (event_create_image false 3 count 0 0 allocation.(eventPrivateStorage)) **
    mbox_create_initialization_context environment critical sg original initial mask eid allocation current |--
  sem_create_api_call_post environment critical sg original mask (event_pool_addr sg eid) X.
Proof.
  intros environment critical sg original initial mask eid allocation current count X
    [Hsource [Hcount Hsafe]].
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
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 3 count 0 0)
    current allocation Hget) as [initialized Hstores].
  destruct (sem_create_api_initialization_allocation sg eid count 0 current tt initialized
    allocation Hget Hstores) as [final [Hfinal [Hinv [Hgen [Hqueue' [Hmutex' Himage]]]]]].
  assert (Hinitialized : UCOS2_state_inv sg initialized)
    by (eapply event_create_private_stores_preserves_validity; eassumption).
  assert (Htasks : initialized.(TskState) = current.(TskState))
    by (eapply mbox_create_private_stores_task_state_eq; eassumption).
  rewrite Hnames in Himage.
  assert (Hstorage :
    event_storage_rep false (event_pool_addr sg eid)
      (event_create_image false 3 count 0 0 allocation.(eventPrivateStorage)) =
    event_private_storage_rep sg eid final).
  { unfold event_private_storage_rep; rewrite Hnames, Himage; reflexivity. }
  rewrite Hstorage.
  sep_apply_l_atomic (mbox_create_private_stores_global_frame sg eid
    (event_create_initialization_fields sg.(osKernelConfig).(cfgEventNames) 3 count 0 0)
    current tt initialized Hstores).
  sep_apply_l_atomic (sem_create_api_initialized_publish_merge sg initialized eid final
    allocation.(eventPrivateStorage) count Hcount Hnames Hinitialized Hfinal
    ltac:(congruence) ltac:(congruence) Himage).
  assert (Hprogram : sem_create_api_program critical sg original.(os_sched_call_invocation)
    count initial (event_pool_addr sg eid)
    (replace_EventS (event_publish initialized.(EventState) eid
      (sem_create_event final count 0)) initialized)).
  { destruct Hhistory as [Hnest [entry [image [detached
      [Hentry [Henter [Hpop [Hallocation Hrestore]]]]]]]].
    eapply sem_create_api_program_published_return; try eassumption.
    eapply q_create_private_stores_without_interference; eassumption. }
  pose proof (sem_create_api_safe_return _ _ _ _ _ _ _ _ Hprogram Hsafe) as Hreturn.
  unfold sem_create_api_call_post, mbox_create_call_post.
  Exists returned (replace_EventS (event_publish initialized.(EventState) eid
    (sem_create_event final count 0)) initialized).
  rewrite q_create_save_input_open.
  unfold q_create_owned, q_create_current_control.
  cbn [replace_EventS TskState]; rewrite Htasks; entailer!.
Qed.
